use std::collections::{BTreeMap, HashMap};
use std::error::Error;

use chrono::offset::FixedOffset;
use chrono::DateTime;

use sophia::api::dataset::Dataset;
use sophia::api::ns::Namespace;
use sophia::api::prelude::{Any, MutableDataset, Quad, QuadSource};
use sophia::api::quad;
use sophia::api::term::matcher::TermMatcher;
use sophia::api::term::{BnodeId, TermKind};
use sophia::api::term::{SimpleTerm, Term};
use sophia::c14n::rdfc10::normalize;
use sophia::inmem::index::{SimpleTermIndex, TermIndex};
use sophia::iri::IriRef;
use sophia::turtle::parser::trig;

use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use blake2::Blake2b512;
use dock_crypto_utils::hashing_utils::field_elem_from_try_and_incr;

use crate::zkp4rdf::desiri;

use super::quads_list::QuadsList;

type Fr = <Bls12_381 as Pairing>::ScalarField;
/// Generate a Field Element from a byte array.
fn generate_fr(bytes: &[u8]) -> Fr {
    field_elem_from_try_and_incr::<Fr, Blake2b512>(bytes)
}

//
//
//

pub trait Rdf2FrEncoder {
    fn encode_term<T: Term>(&mut self, term: T) -> Result<Fr, Box<dyn Error>>;
    fn quads_to_field_representations(
        &mut self,
        dataset: &QuadsList<SimpleTermIndex<u32>>,
    ) -> Result<Vec<Fr>, Box<dyn Error>>;
    fn quads_to_response_values<W: Dataset>(
        &mut self,
        dataset_searchable: &W,
        quads_list: &QuadsList<SimpleTermIndex<u32>>, // TODO make quad list searchable, then we do not need the dataset_searchable anymore
    ) -> Result<
        (
            BTreeMap<usize, Fr>,          // indicies to hide
            BTreeMap<usize, Fr>,          // indicies to reveal
            BTreeMap<String, Vec<usize>>, // index equal to others
        ),
        Box<dyn Error>,
    >;
}

///
///
///
/// Model Theory
///
///
///

pub struct Rdf2FrInMemoryEncoder {
    map: HashMap<String, Fr>,
}

impl Rdf2FrInMemoryEncoder {
    pub fn new() -> Self {
        Rdf2FrInMemoryEncoder {
            map: HashMap::new(),
        }
    }
}

impl Rdf2FrEncoder for Rdf2FrInMemoryEncoder {
    /// Encode an RDF term to field element. Use memory of encoded terms.
    /// Returns an Error if encoding the input term is not supported.
    /// This might be the case for unsupported term types such as quoted triples or
    /// certain RDF Literals such as decimals, negative integers, ...
    fn encode_term<T: Term>(&mut self, term: T) -> Result<Fr, Box<dyn Error>> {
        let term_value = match term.kind() {
            TermKind::Literal => term.lexical_form().unwrap().to_string(),
            TermKind::Iri => term.iri().unwrap().to_string(),
            TermKind::BlankNode => term.bnode_id().unwrap().to_string(),
            _ => return Err(format!("Unsupported term kind: {:?}", term.kind()).into()),
        };
        if self.map.contains_key(&term_value) {
            return Ok(self.map.get(&term_value).unwrap().clone());
        }
        let encoding_result = match term.datatype() {
            None => Ok(generate_fr(term_value.as_bytes())),
            Some(datatype) => match datatype.as_str() {
                "http://www.w3.org/2001/XMLSchema#string" => Ok(generate_fr(term_value.as_bytes())),
                "http://www.w3.org/2001/XMLSchema#integer" => {
                    let numeric_value: u64 = term_value.parse()?;
                    Ok(Fr::from(numeric_value))
                }
                "http://www.w3.org/2001/XMLSchema#dateTimeStamp" => {
                    let datetime: DateTime<FixedOffset> = term_value.parse()?;
                    Ok(Fr::from(datetime.timestamp()))
                }
                unsupported_literal => {
                    return Err(format!("Unsupported Literal: {}", unsupported_literal).into())
                }
            },
        };
        encoding_result.and_then(|encoded_term| {
            self.map.insert(term_value.clone(), encoded_term);
            Ok(encoded_term)
        })
    }

    /// Convert an RDF dataset to a list of field elements (for signing or signature verification).
    /// Uses memory from encoding hash map.
    fn quads_to_field_representations(
        &mut self,
        dataset: &QuadsList<SimpleTermIndex<u32>>,
    ) -> Result<Vec<Fr>, Box<dyn Error>> {
        let term_list = self
            .quads_to_term_option_list(dataset)
            .map(|options| self.term_options_to_term_or_default(options))?;
        self.terms_to_field_representations(&term_list)
    }

    /// Convert a list of quads to a list of field elements (for proof verification).
    /// Blankn nodes are mapped to their Schnorr response values. IRIs and Literals are encoded.
    /// Uses memory from encoding hash map.
    fn quads_to_response_values<W: Dataset>(
        &mut self,
        dataset_searchable: &W,
        quads_list: &QuadsList<SimpleTermIndex<u32>>, // TODO make quad list searchable, then we do not need the dataset_searchable anymore
    ) -> Result<
        (
            BTreeMap<usize, Fr>,          // indicies to hide
            BTreeMap<usize, Fr>,          // indicies to reveal
            BTreeMap<String, Vec<usize>>, // index equal to others
        ),
        Box<dyn Error>,
    > {
        let term_options = self.quads_to_term_option_list(quads_list)?;
        let term_list = self.term_options_to_term_or_default(term_options.clone());

        let mut revealed_messages = BTreeMap::<usize, Fr>::new();
        let mut hidden_message_responses = BTreeMap::<usize, Fr>::new();
        let mut equal_indicies = BTreeMap::<String, Vec<usize>>::new();

        for (index, term) in term_options.iter().enumerate() {
            match term {
                Some(t) => {
                    if t.kind() == TermKind::BlankNode {
                        // get response value of hidden message
                        let bid = t.bnode_id().unwrap().as_str().to_string();
                        equal_indicies
                            .entry(bid)
                            .or_insert_with(Vec::new)
                            .push(index);
                        let value_t_resp =
                            get_response_value_for_term(&dataset_searchable, t).unwrap();
                        hidden_message_responses.insert(index, value_t_resp);
                    } else {
                        // encode revealed message
                        let value_t_enc = self.encode_term(t).unwrap();
                        revealed_messages.insert(index, value_t_enc);
                    }
                }
                None => {
                    if index % 5 == 3 {
                        // object type is None
                        let object_value_term = term_list.get(index - 1).unwrap();
                        let suffix_t_resp = get_response_value_for_term_suffix(
                            &dataset_searchable,
                            object_value_term,
                        );
                        match suffix_t_resp {
                            Some(resp) => {
                                hidden_message_responses.insert(index, resp);
                            }
                            None => {
                                // there was not suffix in the presentation for this object
                                let value_t_enc = self.encode_term("").unwrap();
                                revealed_messages.insert(index, value_t_enc);
                            }
                        }
                    } else {
                        // graph name is None
                        let value_t_enc = self.encode_term("").unwrap();
                        revealed_messages.insert(index, value_t_enc);
                    }
                }
            }
        }
        Ok((hidden_message_responses, revealed_messages, equal_indicies))
    }
}

// ? helper functions for Rdf2FrEncoder
impl Rdf2FrInMemoryEncoder {
    /// Convert an RDF dataset to a list of field elements (for signing).
    /// Uses memory from encoding hash map.
    fn quads_to_term_option_list<'a>(
        &mut self,
        dataset: &'a QuadsList<SimpleTermIndex<u32>>,
    ) -> Result<Vec<Option<SimpleTerm<'a>>>, Box<dyn Error>> {
        let mut results = vec![];
        for quad in dataset.quads() {
            let q = quad?;
            let s = Some(q.s().as_simple());
            let p = Some(q.p().as_simple());
            let o = Some(q.o().as_simple());
            let ov = Some(q.o().as_simple());
            let ot = q.o().datatype().map(|dt| SimpleTerm::Iri(dt).into());
            let g = q.g().map(|gn| gn.as_simple());
            let result = [s, p, ov, ot, g];
            results.push(result);
        }
        Ok(results.concat())
    }

    fn term_options_to_term_or_default<'a>(
        &mut self,
        term_options: Vec<Option<SimpleTerm<'a>>>,
    ) -> Vec<SimpleTerm<'a>> {
        term_options
            .iter()
            .map(|option| {
                option.as_ref().cloned().unwrap_or(
                    SimpleTerm::Iri(IriRef::new_unchecked("".into())).into(),
                    // ? as default value, an empty IRI, which is a hack to generate an empty string as SimpleTerm
                )
            })
            .collect::<Vec<_>>() // ? and collect the term values
    }

    fn terms_to_field_representations(
        &mut self,
        terms: &Vec<SimpleTerm>,
    ) -> Result<Vec<Fr>, Box<dyn Error>> {
        let result = terms
            .iter()
            .map(|term| self.encode_term(term))
            .collect::<Result<Vec<Fr>, Box<dyn Error>>>()?;
        Ok(result)
    }
}

fn get_response_value_for_term<'a, W: Dataset, T: Term>(
    presentation_dataset: &'a W,
    s: &'a T,
) -> Option<Fr>
where
    [&'a T; 1]: TermMatcher,
{
    let ns_spok = Namespace::new_unchecked("https://ex.org/spok/v0#");
    let quads_s_resp = presentation_dataset
        .quads_matching([s], [ns_spok.get("hasSchnorrResponse").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    if quads_s_resp.is_empty() {
        return None;
    }
    let term_s_resp = quads_s_resp[0].o();
    let result = desiri::<Fr>(term_s_resp.lexical_form().unwrap().to_string()).unwrap();
    Some(result)
}

fn get_response_value_for_term_suffix<'a, W: Dataset, T: Term>(
    presentation_dataset: &'a W,
    s: &'a T,
) -> Option<Fr>
where
    [&'a T; 1]: TermMatcher,
{
    let ns_spok = Namespace::new_unchecked("https://ex.org/spok/v0#");
    let quads_s_resp = presentation_dataset
        .quads_matching(
            [s],
            [ns_spok.get("hasSchnorrResponseForSuffix").unwrap()],
            Any,
            Any,
        )
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    if quads_s_resp.is_empty() {
        return None;
    }
    let term_s_resp = quads_s_resp[0].o();
    let result = desiri::<Fr>(term_s_resp.lexical_form().unwrap().to_string()).unwrap();
    Some(result)
}

///
///
///
/// Model Theory trimmed
///
///
///

pub struct Rdf2FrInMemoryEncoderTrimmed {
    map: HashMap<String, Fr>,
}

impl Rdf2FrInMemoryEncoderTrimmed {
    pub fn new() -> Self {
        Rdf2FrInMemoryEncoderTrimmed {
            map: HashMap::new(),
        }
    }
}

impl Rdf2FrEncoder for Rdf2FrInMemoryEncoderTrimmed {
    /// Encode an RDF term to field element. Use memory of encoded terms.
    /// Returns an Error if encoding the input term is not supported.
    /// This might be the case for unsupported term types such as quoted triples or
    /// certain RDF Literals such as decimals, negative integers, ...
    fn encode_term<T: Term>(&mut self, term: T) -> Result<Fr, Box<dyn Error>> {
        let term_value = match term.kind() {
            TermKind::Literal => term.lexical_form().unwrap().to_string(),
            TermKind::Iri => term.iri().unwrap().to_string(),
            TermKind::BlankNode => term.bnode_id().unwrap().to_string(),
            _ => return Err(format!("Unsupported term kind: {:?}", term.kind()).into()),
        };
        if self.map.contains_key(&term_value) {
            return Ok(self.map.get(&term_value).unwrap().clone());
        }
        let encoding_result = match term.datatype() {
            None => Ok(generate_fr(term_value.as_bytes())),
            Some(datatype) => match datatype.as_str() {
                "http://www.w3.org/2001/XMLSchema#string" => Ok(generate_fr(term_value.as_bytes())),
                "http://www.w3.org/2001/XMLSchema#integer" => {
                    let numeric_value: u64 = term_value.parse()?;
                    Ok(Fr::from(numeric_value))
                }
                "http://www.w3.org/2001/XMLSchema#dateTimeStamp" => {
                    let datetime: DateTime<FixedOffset> = term_value.parse()?;
                    Ok(Fr::from(datetime.timestamp()))
                }
                unsupported_literal => {
                    return Err(format!("Unsupported Literal: {}", unsupported_literal).into())
                }
            },
        };
        encoding_result.and_then(|encoded_term| {
            self.map.insert(term_value.clone(), encoded_term);
            Ok(encoded_term)
        })
    }

    /// Convert an RDF dataset to a list of field elements (for signing or signature verification).
    /// Uses memory from encoding hash map.
    fn quads_to_field_representations(
        &mut self,
        dataset: &QuadsList<SimpleTermIndex<u32>>,
    ) -> Result<Vec<Fr>, Box<dyn Error>> {
        let term_list = self
            .quads_to_term_option_list(dataset)
            .map(|options| self.term_options_to_term_or_default(options))?;
        self.terms_to_field_representations(&term_list)
    }

    /// Convert a list of quads to a list of field elements (for proof verification).
    /// Blankn nodes are mapped to their Schnorr response values. IRIs and Literals are encoded.
    /// Uses memory from encoding hash map.
    fn quads_to_response_values<W: Dataset>(
        &mut self,
        dataset_searchable: &W,
        quads_list: &QuadsList<SimpleTermIndex<u32>>, // TODO make quad list searchable, then we do not need the dataset_searchable anymore
    ) -> Result<
        (
            BTreeMap<usize, Fr>,          // indicies to hide
            BTreeMap<usize, Fr>,          // indicies to reveal
            BTreeMap<String, Vec<usize>>, // index equal to others
        ),
        Box<dyn Error>,
    > {
        let term_options = self.quads_to_term_option_list(quads_list)?;
        let term_list = self.term_options_to_term_or_default(term_options.clone());

        let mut revealed_messages = BTreeMap::<usize, Fr>::new();
        let mut hidden_message_responses = BTreeMap::<usize, Fr>::new();
        let mut equal_indicies = BTreeMap::<String, Vec<usize>>::new();

        // ! here is a difference between "Model Theory" and "Model Theory Trimmed"
        for (index, t) in term_list.iter().enumerate() {
            if t.kind() == TermKind::BlankNode {
                // get response value of hidden message
                let value_t_resp = get_response_value_for_term(&dataset_searchable, t);
                match value_t_resp {
                    Some(resp) => {
                        let current_index =
                            revealed_messages.len() + hidden_message_responses.len();
                        hidden_message_responses.insert(
                            current_index, // ! current overall index
                            resp,
                        );
                        let bid = t.bnode_id().unwrap().as_str().to_string();
                        equal_indicies
                            .entry(bid)
                            .or_insert_with(Vec::new)
                            .push(current_index); // ! current overall index
                    }
                    None => {}
                }
                // try for object suffix
                let suffix_t_resp = get_response_value_for_term_suffix(&dataset_searchable, t);
                match suffix_t_resp {
                    Some(resp) => {
                        hidden_message_responses.insert(
                            revealed_messages.len() + hidden_message_responses.len(), // ! current overall index
                            resp,
                        );
                    }
                    None => {}
                }
            } else {
                // encode revealed message
                let value_t_enc = self.encode_term(t).unwrap();
                revealed_messages.insert(
                    revealed_messages.len() + hidden_message_responses.len(),
                    value_t_enc,
                );
            }
        }
        Ok((hidden_message_responses, revealed_messages, equal_indicies))
    }
}

// ? helper functions for Rdf2FrEncoder
impl Rdf2FrInMemoryEncoderTrimmed {
    /// Convert an RDF dataset to a list of field elements (for signing).
    /// Uses memory from encoding hash map.
    fn quads_to_term_option_list<'a>(
        &mut self,
        dataset: &'a QuadsList<SimpleTermIndex<u32>>,
    ) -> Result<Vec<Option<SimpleTerm<'a>>>, Box<dyn Error>> {
        let mut results = vec![];
        for quad in dataset.quads() {
            let q = quad?;
            let s = Some(q.s().as_simple());
            let p = Some(q.p().as_simple());
            let o = Some(q.o().as_simple());
            let ov = Some(q.o().as_simple());
            let ot = q.o().datatype().map(|dt| SimpleTerm::Iri(dt).into());
            let g = q.g().map(|gn| gn.as_simple());
            let result = [s, p, ov, ot, g];
            results.push(result);
        }
        Ok(results.concat())
    }

    // ! here is a difference between "Model Theory" and "Model Theory Trimmed"
    fn term_options_to_term_or_default<'a>(
        &mut self,
        term_options: Vec<Option<SimpleTerm<'a>>>,
    ) -> Vec<SimpleTerm<'a>> {
        term_options
            .into_iter() // !
            .filter_map(|option| option) // !
            .collect::<Vec<_>>() // ? and collect the term values
    }

    fn terms_to_field_representations(
        &mut self,
        terms: &Vec<SimpleTerm>,
    ) -> Result<Vec<Fr>, Box<dyn Error>> {
        let result = terms
            .iter()
            .map(|term| self.encode_term(term))
            .collect::<Result<Vec<Fr>, Box<dyn Error>>>()?;
        Ok(result)
    }
}

///
///
///
/// Schema
///
///
///

pub struct Rdf2FrInMemoryEncoderSchema {
    map: HashMap<String, Fr>,
}

impl Rdf2FrInMemoryEncoderSchema {
    pub fn new() -> Self {
        Rdf2FrInMemoryEncoderSchema {
            map: HashMap::new(),
        }
    }
}

impl Rdf2FrEncoder for Rdf2FrInMemoryEncoderSchema {
    /// Encode an RDF term to field element. Use memory of encoded terms.
    /// Returns an Error if encoding the input term is not supported.
    /// This might be the case for unsupported term types such as quoted triples or
    /// certain RDF Literals such as decimals, negative integers, ...
    fn encode_term<T: Term>(&mut self, term: T) -> Result<Fr, Box<dyn Error>> {
        let term_value = match term.kind() {
            TermKind::Literal => term.lexical_form().unwrap().to_string(),
            TermKind::Iri => term.iri().unwrap().to_string(),
            TermKind::BlankNode => term.bnode_id().unwrap().to_string(),
            _ => return Err(format!("Unsupported term kind: {:?}", term.kind()).into()),
        };
        if self.map.contains_key(&term_value) {
            return Ok(self.map.get(&term_value).unwrap().clone());
        }
        let encoding_result = match term.datatype() {
            None => Ok(generate_fr(term_value.as_bytes())),
            Some(datatype) => match datatype.as_str() {
                "http://www.w3.org/2001/XMLSchema#string" => Ok(generate_fr(term_value.as_bytes())),
                "http://www.w3.org/2001/XMLSchema#integer" => {
                    let numeric_value: u64 = term_value.parse()?;
                    Ok(Fr::from(numeric_value))
                }
                "http://www.w3.org/2001/XMLSchema#dateTimeStamp" => {
                    let datetime: DateTime<FixedOffset> = term_value.parse()?;
                    Ok(Fr::from(datetime.timestamp()))
                }
                unsupported_literal => {
                    return Err(format!("Unsupported Literal: {}", unsupported_literal).into())
                }
            },
        };
        encoding_result.and_then(|encoded_term| {
            self.map.insert(term_value.clone(), encoded_term);
            Ok(encoded_term)
        })
    }

    /// Convert an RDF dataset to a list of field elements (for signing or signature verification).
    /// Uses memory from encoding hash map.
    fn quads_to_field_representations(
        &mut self,
        dataset: &QuadsList<SimpleTermIndex<u32>>,
    ) -> Result<Vec<Fr>, Box<dyn Error>> {
        let term_list = self
            .quads_to_term_option_list(dataset)
            .map(|options| self.term_options_to_term_or_default(options))?;
        self.terms_to_field_representations(&term_list)
    }

    /// Convert a list of quads to a list of field elements (for proof verification).
    /// Blankn nodes are mapped to their Schnorr response values. IRIs and Literals are encoded.
    /// Uses memory from encoding hash map.
    fn quads_to_response_values<W: Dataset>(
        &mut self,
        dataset_searchable: &W,
        quads_list: &QuadsList<SimpleTermIndex<u32>>, // TODO make quad list searchable, then we do not need the dataset_searchable anymore
    ) -> Result<
        (
            BTreeMap<usize, Fr>,          // indicies to hide
            BTreeMap<usize, Fr>,          // indicies to reveal
            BTreeMap<String, Vec<usize>>, // index equal to others
        ),
        Box<dyn Error>,
    > {
        let term_options = self.quads_to_term_option_list(quads_list)?;
        let term_list = self.term_options_to_term_or_default(term_options.clone());

        let mut revealed_messages = BTreeMap::<usize, Fr>::new();
        let mut hidden_message_responses = BTreeMap::<usize, Fr>::new();
        let mut equal_indicies = BTreeMap::<String, Vec<usize>>::new();

        for (index, t) in term_list.iter().enumerate() {
            if t.kind() == TermKind::BlankNode {
                // get response value of hidden message
                let value_t_resp = get_response_value_for_term(&dataset_searchable, t);
                match value_t_resp {
                    Some(resp) => {
                        let current_index =
                            revealed_messages.len() + hidden_message_responses.len();
                        hidden_message_responses.insert(
                            current_index, // ! current overall index
                            resp,
                        );
                        let bid = t.bnode_id().unwrap().as_str().to_string();
                        equal_indicies
                            .entry(bid)
                            .or_insert_with(Vec::new)
                            .push(current_index); // ! current overall index
                    }
                    None => {}
                }
            } else {
                // encode revealed message
                let value_t_enc = self.encode_term(t).unwrap();
                revealed_messages.insert(
                    revealed_messages.len() + hidden_message_responses.len(),
                    value_t_enc,
                );
            }
        }
        Ok((hidden_message_responses, revealed_messages, equal_indicies))
    }
}

// ? helper functions for Rdf2FrEncoder
impl Rdf2FrInMemoryEncoderSchema {
    /// Convert an RDF dataset to a list of field elements (for signing).
    /// Uses memory from encoding hash map.
    fn quads_to_term_option_list<'a>(
        &mut self,
        dataset: &'a QuadsList<SimpleTermIndex<u32>>,
    ) -> Result<Vec<Option<SimpleTerm<'a>>>, Box<dyn Error>> {
        let mut results = vec![];
        // ! just a hack for PoC
        let cred_id = Some(dataset.quads().next().unwrap().unwrap().s().as_simple());
        results.push([cred_id]);
        for quad in dataset.quads() {
            let q = quad?;
            let ov = Some(q.o().as_simple());
            let result = [ov];
            results.push(result);
        }
        Ok(results.concat())
    }

    fn term_options_to_term_or_default<'a>(
        &mut self,
        term_options: Vec<Option<SimpleTerm<'a>>>,
    ) -> Vec<SimpleTerm<'a>> {
        term_options
            .into_iter() // !
            .filter_map(|option| option) // !
            .collect::<Vec<_>>() // ? and collect the term values
    }

    fn terms_to_field_representations(
        &mut self,
        terms: &Vec<SimpleTerm>,
    ) -> Result<Vec<Fr>, Box<dyn Error>> {
        let result = terms
            .iter()
            .map(|term| self.encode_term(term))
            .collect::<Result<Vec<Fr>, Box<dyn Error>>>()?;
        Ok(result)
    }
}

///
///
///
///
///
///
///
/// TEST
///
///
///
///
///
///
///

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::BigInt;
    use sophia::{
        api::{
            ns::{xsd, Namespace},
            term::{BnodeId, IriRef},
        },
        inmem::dataset::LightDataset,
        turtle::parser::gtrig,
    };

    #[test]
    fn test_encode_iri() {
        let term = IriRef::new_unchecked("http://example.org");
        let encoded = Rdf2FrInMemoryEncoder::new().encode_term(term).unwrap();
        let expected = field_elem_from_try_and_incr::<Fr, Blake2b512>(term.as_bytes());
        assert_eq!(encoded, expected);
    }

    #[test]
    fn test_encode_bn() {
        let term = BnodeId::new_unchecked("x");
        let encoded = Rdf2FrInMemoryEncoder::new().encode_term(term).unwrap();
        let expected = field_elem_from_try_and_incr::<Fr, Blake2b512>(term.as_bytes());
        assert_eq!(encoded, expected);
    }

    #[test]
    fn test_encode_string() {
        let term = "some string";
        let encoded = Rdf2FrInMemoryEncoder::new().encode_term(term).unwrap();
        let expected = field_elem_from_try_and_incr::<Fr, Blake2b512>(term.as_bytes());
        assert_eq!(encoded, expected);
    }

    #[test]
    fn test_encode_integer() {
        let term = 123;
        let encoded = Rdf2FrInMemoryEncoder::new().encode_term(term).unwrap();
        let expected = Fr::from(term);
        assert_eq!(encoded, expected);
    }

    #[test]
    fn test_encode_datetime_utc() {
        let time = "2004-04-12T18:20:00Z";
        let ns = Namespace::new(xsd::PREFIX).unwrap();
        let term = time * ns.get("dateTimeStamp").unwrap();
        let encoded = Rdf2FrInMemoryEncoder::new().encode_term(term).unwrap();
        let datetime: DateTime<FixedOffset> = time.parse().unwrap();
        let expected = Fr::from(datetime.timestamp());
        assert_eq!(encoded, expected);
    }

    #[test]
    fn test_encode_datetime_offset() {
        let time = "2004-04-12T13:20:00-05:00";
        let ns = Namespace::new(xsd::PREFIX).unwrap();
        let term = time * ns.get("dateTimeStamp").unwrap();
        let encoded = Rdf2FrInMemoryEncoder::new().encode_term(term).unwrap();
        let datetime: DateTime<FixedOffset> = time.parse().unwrap();
        let expected = Fr::from(datetime.timestamp());
        assert_eq!(encoded, expected);
    }

    #[test]
    fn test_dataset_to_termlist() {
        let example = r#"
            @prefix cred:   <https://www.w3.org/2018/credentials#> .
            @prefix exCred: <http://example.org/credentials#> .
            @prefix exOrg: <http://example.org/organisations#> .
            @prefix exUser: <http://example.org/users#> .
            @prefix org:    <http://www.w3.org/ns/org#> .
            @prefix xsd:    <http://www.w3.org/2001/XMLSchema#> .
            # claims
            exUser:userId org:memberOf exOrg:aCompany . 
            exUser:userId org:headOf   exOrg:aCompany .
            # credential metadata
            exCred:credId cred:issuer            exOrg:aCompany ;
                          cred:credentialSubject exUser:userId ;
                          cred:validUntil        "2023-11-07T13:20:00Z"^^xsd:dateTimeStamp ;
                          cred:credentialStatus  <http://example.org/revocation#accumulatorId> ;
                          cred:proof             _:signatureGraph .
        "#;

        // Parse the example dataset
        let mut dataset: LightDataset = trig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let mut output = Vec::<u8>::new();
        normalize(&dataset, &mut output).unwrap();
        let normalised_nquads = String::from_utf8(output).unwrap();

        let mut canon_dataset: QuadsList<SimpleTermIndex<u32>> =
            trig::parse_str(normalised_nquads.as_str())
                .collect_quads()
                .map_err(|e| println!("Error: {}", e))
                .expect("The example string should be valid RDF");

        // credential and claims
        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoder::new();
        let result = rdf2fr_encoder
            .quads_to_term_option_list(&canon_dataset)
            .unwrap()
            .iter()
            .map(|option| {
                option.as_ref().cloned().unwrap_or(
                    // as default value, an empty IRI, which is a hack to generate an empty string as SimpleTerm
                    SimpleTerm::Iri(IriRef::new_unchecked("".into())).into(),
                )
            })
            .map(|term| match term.kind() {
                TermKind::Literal => term.lexical_form().unwrap().to_string(),
                TermKind::Iri => term.iri().unwrap().unwrap().to_string(),
                TermKind::BlankNode => term.bnode_id().unwrap().to_string(),
                _ => "ERR".to_string(),
            })
            .collect::<Vec<_>>();

        let expected = [
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#credentialStatus",
            "http://example.org/revocation#accumulatorId",
            "",
            "",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#credentialSubject",
            "http://example.org/users#userId",
            "",
            "",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#issuer",
            "http://example.org/organisations#aCompany",
            "",
            "",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#proof",
            "c14n0",
            "",
            "",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#validUntil",
            "2023-11-07T13:20:00Z",
            "http://www.w3.org/2001/XMLSchema#dateTimeStamp",
            "",
            "http://example.org/users#userId",
            "http://www.w3.org/ns/org#headOf",
            "http://example.org/organisations#aCompany",
            "",
            "",
            "http://example.org/users#userId",
            "http://www.w3.org/ns/org#memberOf",
            "http://example.org/organisations#aCompany",
            "",
            "",
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_dataset_to_termlist_trimmed() {
        let example = r#"
            @prefix cred:   <https://www.w3.org/2018/credentials#> .
            @prefix exCred: <http://example.org/credentials#> .
            @prefix exOrg: <http://example.org/organisations#> .
            @prefix exUser: <http://example.org/users#> .
            @prefix org:    <http://www.w3.org/ns/org#> .
            @prefix xsd:    <http://www.w3.org/2001/XMLSchema#> .
            # claims
            exUser:userId org:memberOf exOrg:aCompany . 
            exUser:userId org:headOf   exOrg:aCompany .
            # credential metadata
            exCred:credId cred:issuer            exOrg:aCompany ;
                          cred:credentialSubject exUser:userId ;
                          cred:validUntil        "2023-11-07T13:20:00Z"^^xsd:dateTimeStamp ;
                          cred:credentialStatus  <http://example.org/revocation#accumulatorId> ;
                          cred:proof             _:signatureGraph .
        "#;

        // Parse the example dataset
        let mut dataset: LightDataset = trig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let mut output = Vec::<u8>::new();
        normalize(&dataset, &mut output).unwrap();
        let normalised_nquads = String::from_utf8(output).unwrap();

        let mut canon_dataset: QuadsList<SimpleTermIndex<u32>> =
            trig::parse_str(normalised_nquads.as_str())
                .collect_quads()
                .map_err(|e| println!("Error: {}", e))
                .expect("The example string should be valid RDF");

        // credential and claims
        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoderTrimmed::new();
        let result = rdf2fr_encoder
            .quads_to_term_option_list(&canon_dataset)
            .map(|options| rdf2fr_encoder.term_options_to_term_or_default(options))
            .unwrap()
            .iter()
            .map(|term| match term.kind() {
                TermKind::Literal => term.lexical_form().unwrap().to_string(),
                TermKind::Iri => term.iri().unwrap().unwrap().to_string(),
                TermKind::BlankNode => term.bnode_id().unwrap().to_string(),
                _ => "ERR".to_string(),
            })
            .collect::<Vec<_>>();

        let expected = [
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#credentialStatus",
            "http://example.org/revocation#accumulatorId",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#credentialSubject",
            "http://example.org/users#userId",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#issuer",
            "http://example.org/organisations#aCompany",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#proof",
            "c14n0",
            "http://example.org/credentials#credId",
            "https://www.w3.org/2018/credentials#validUntil",
            "2023-11-07T13:20:00Z",
            "http://www.w3.org/2001/XMLSchema#dateTimeStamp",
            "http://example.org/users#userId",
            "http://www.w3.org/ns/org#headOf",
            "http://example.org/organisations#aCompany",
            "http://example.org/users#userId",
            "http://www.w3.org/ns/org#memberOf",
            "http://example.org/organisations#aCompany",
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_dataset_to_termlist_schema() {
        let example = r#"
            @prefix cred:   <https://www.w3.org/2018/credentials#> .
            @prefix exCred: <http://example.org/credentials#> .
            @prefix exOrg: <http://example.org/organisations#> .
            @prefix exUser: <http://example.org/users#> .
            @prefix org:    <http://www.w3.org/ns/org#> .
            @prefix xsd:    <http://www.w3.org/2001/XMLSchema#> .
            # claims
            exUser:userId org:memberOf exOrg:aCompany . 
            exUser:userId org:headOf   exOrg:aCompany .
            # credential metadata
            exCred:credId cred:issuer            exOrg:aCompany ;
                          cred:credentialSubject exUser:userId ;
                          cred:validUntil        "2023-11-07T13:20:00Z"^^xsd:dateTimeStamp ;
                          cred:credentialStatus  <http://example.org/revocation#accumulatorId> ;
                          cred:proof             _:signatureGraph .
        "#;

        // Parse the example dataset
        let mut dataset: LightDataset = trig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let mut output = Vec::<u8>::new();
        normalize(&dataset, &mut output).unwrap();
        let normalised_nquads = String::from_utf8(output).unwrap();

        let mut canon_dataset: QuadsList<SimpleTermIndex<u32>> =
            trig::parse_str(normalised_nquads.as_str())
                .collect_quads()
                .map_err(|e| println!("Error: {}", e))
                .expect("The example string should be valid RDF");

        // credential and claims
        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoderSchema::new();
        let result = rdf2fr_encoder
            .quads_to_term_option_list(&canon_dataset)
            .map(|options| rdf2fr_encoder.term_options_to_term_or_default(options))
            .unwrap()
            .iter()
            .map(|term| match term.kind() {
                TermKind::Literal => term.lexical_form().unwrap().to_string(),
                TermKind::Iri => term.iri().unwrap().unwrap().to_string(),
                TermKind::BlankNode => term.bnode_id().unwrap().to_string(),
                _ => "ERR".to_string(),
            })
            .collect::<Vec<_>>();

        let expected = [
            "http://example.org/credentials#credId",
            "http://example.org/revocation#accumulatorId",
            "http://example.org/users#userId",
            "http://example.org/organisations#aCompany",
            "c14n0",
            "2023-11-07T13:20:00Z",
            "http://example.org/organisations#aCompany",
            "http://example.org/organisations#aCompany",
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_dataset_to_field_representations() {
        let example = r#"
        @prefix cred:   <https://www.w3.org/2018/credentials#> .
        @prefix exCred: <http://example.org/credentials#> .
        @prefix exOrg: <http://example.org/organisations#> .
        @prefix exUser: <http://example.org/users#> .
        @prefix org:    <http://www.w3.org/ns/org#> .
        @prefix xsd:    <http://www.w3.org/2001/XMLSchema#> .
        # claims
        exUser:userId org:memberOf exOrg:aCompany . 
        exUser:userId org:headOf   exOrg:aCompany .
        # credential metadata
        exCred:credId cred:issuer            exOrg:aCompany ;
                      cred:credentialSubject exUser:userId ;
                      cred:validUntil        "2023-11-07T13:20:00Z"^^xsd:dateTimeStamp ;
                      cred:credentialStatus  <http://example.org/revocation#accumulatorId> ;
                      cred:proof             _:signatureGraph .
    "#;

        // Parse the example dataset
        let mut dataset: LightDataset = trig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let mut output = Vec::<u8>::new();
        normalize(&dataset, &mut output).unwrap();
        let normalised_nquads = String::from_utf8(output).unwrap();

        let mut canon_dataset: QuadsList<SimpleTermIndex<u32>> =
            trig::parse_str(normalised_nquads.as_str())
                .collect_quads()
                .map_err(|e| println!("Error: {}", e))
                .expect("The example string should be valid RDF");

        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoder::new();
        let result = rdf2fr_encoder
            .quads_to_field_representations(&canon_dataset)
            .unwrap();

        let expected = [
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                12128200784307151646,
                6239862291845800445,
                7794544965875761465,
                2256911646900887038,
            ])),
            Fr::from(BigInt([
                7312873495776744533,
                8114177336775667406,
                4613950413849816819,
                6586411640486648583,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                13479492388325692125,
                8774317675204352409,
                9473803180199958296,
                48045467206693763,
            ])),
            Fr::from(BigInt([
                2527993771139348481,
                17031324069223192505,
                10395630042359995808,
                3622571238833603864,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                16510617979322594564,
                12015788767324311352,
                7271166171282263051,
                6933608981523975618,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                6758836589927077269,
                7229384904706123409,
                624532561690313309,
                895390781479257653,
            ])),
            Fr::from(BigInt([
                7233805586443071084,
                2742125060316549915,
                10773642635746952364,
                5737394731741332253,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                8584643261987331863,
                16200755082649097329,
                12337835172712087143,
                3707653408865982187,
            ])),
            Fr::from(BigInt([1699363200, 0, 0, 0])),
            Fr::from(BigInt([
                14331371267239541313,
                13838815834460655229,
                403256623361020970,
                7767904050521896485,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                2527993771139348481,
                17031324069223192505,
                10395630042359995808,
                3622571238833603864,
            ])),
            Fr::from(BigInt([
                3888581659953996850,
                8070905985068228063,
                13487950908503776509,
                6971898906731903570,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                2527993771139348481,
                17031324069223192505,
                10395630042359995808,
                3622571238833603864,
            ])),
            Fr::from(BigInt([
                17277122902210706885,
                10933249048245759994,
                9697185051640140087,
                2078422620467228261,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_dataset_to_field_representations_trimmed() {
        let example = r#"
        @prefix cred:   <https://www.w3.org/2018/credentials#> .
        @prefix exCred: <http://example.org/credentials#> .
        @prefix exOrg: <http://example.org/organisations#> .
        @prefix exUser: <http://example.org/users#> .
        @prefix org:    <http://www.w3.org/ns/org#> .
        @prefix xsd:    <http://www.w3.org/2001/XMLSchema#> .
        # claims
        exUser:userId org:memberOf exOrg:aCompany . 
        exUser:userId org:headOf   exOrg:aCompany .
        # credential metadata
        exCred:credId cred:issuer            exOrg:aCompany ;
                      cred:credentialSubject exUser:userId ;
                      cred:validUntil        "2023-11-07T13:20:00Z"^^xsd:dateTimeStamp ;
                      cred:credentialStatus  <http://example.org/revocation#accumulatorId> ;
                      cred:proof             _:signatureGraph .
    "#;

        // Parse the example dataset
        let mut dataset: LightDataset = trig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let mut output = Vec::<u8>::new();
        normalize(&dataset, &mut output).unwrap();
        let normalised_nquads = String::from_utf8(output).unwrap();

        let mut canon_dataset: QuadsList<SimpleTermIndex<u32>> =
            trig::parse_str(normalised_nquads.as_str())
                .collect_quads()
                .map_err(|e| println!("Error: {}", e))
                .expect("The example string should be valid RDF");

        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoderTrimmed::new();
        let result = rdf2fr_encoder
            .quads_to_field_representations(&canon_dataset)
            .unwrap();

        let expected = [
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                12128200784307151646,
                6239862291845800445,
                7794544965875761465,
                2256911646900887038,
            ])),
            Fr::from(BigInt([
                7312873495776744533,
                8114177336775667406,
                4613950413849816819,
                6586411640486648583,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                13479492388325692125,
                8774317675204352409,
                9473803180199958296,
                48045467206693763,
            ])),
            Fr::from(BigInt([
                2527993771139348481,
                17031324069223192505,
                10395630042359995808,
                3622571238833603864,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                16510617979322594564,
                12015788767324311352,
                7271166171282263051,
                6933608981523975618,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                6758836589927077269,
                7229384904706123409,
                624532561690313309,
                895390781479257653,
            ])),
            Fr::from(BigInt([
                7233805586443071084,
                2742125060316549915,
                10773642635746952364,
                5737394731741332253,
            ])),
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                8584643261987331863,
                16200755082649097329,
                12337835172712087143,
                3707653408865982187,
            ])),
            Fr::from(BigInt([1699363200, 0, 0, 0])),
            Fr::from(BigInt([
                14331371267239541313,
                13838815834460655229,
                403256623361020970,
                7767904050521896485,
            ])),
            Fr::from(BigInt([
                2527993771139348481,
                17031324069223192505,
                10395630042359995808,
                3622571238833603864,
            ])),
            Fr::from(BigInt([
                3888581659953996850,
                8070905985068228063,
                13487950908503776509,
                6971898906731903570,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
            Fr::from(BigInt([
                2527993771139348481,
                17031324069223192505,
                10395630042359995808,
                3622571238833603864,
            ])),
            Fr::from(BigInt([
                17277122902210706885,
                10933249048245759994,
                9697185051640140087,
                2078422620467228261,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_dataset_to_field_representations_schema() {
        let example = r#"
        @prefix cred:   <https://www.w3.org/2018/credentials#> .
        @prefix exCred: <http://example.org/credentials#> .
        @prefix exOrg: <http://example.org/organisations#> .
        @prefix exUser: <http://example.org/users#> .
        @prefix org:    <http://www.w3.org/ns/org#> .
        @prefix xsd:    <http://www.w3.org/2001/XMLSchema#> .
        # claims
        exUser:userId org:memberOf exOrg:aCompany . 
        exUser:userId org:headOf   exOrg:aCompany .
        # credential metadata
        exCred:credId cred:issuer            exOrg:aCompany ;
                      cred:credentialSubject exUser:userId ;
                      cred:validUntil        "2023-11-07T13:20:00Z"^^xsd:dateTimeStamp ;
                      cred:credentialStatus  <http://example.org/revocation#accumulatorId> ;
                      cred:proof             _:signatureGraph .
    "#;

        // Parse the example dataset
        let mut dataset: LightDataset = trig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let mut output = Vec::<u8>::new();
        normalize(&dataset, &mut output).unwrap();
        let normalised_nquads = String::from_utf8(output).unwrap();

        let mut canon_dataset: QuadsList<SimpleTermIndex<u32>> =
            trig::parse_str(normalised_nquads.as_str())
                .collect_quads()
                .map_err(|e| println!("Error: {}", e))
                .expect("The example string should be valid RDF");

        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoderSchema::new();
        let result = rdf2fr_encoder
            .quads_to_field_representations(&canon_dataset)
            .unwrap();

        let expected = [
            Fr::from(BigInt([
                11118909164102399284,
                10583697895882196775,
                7868950742256514620,
                1422412078274040775,
            ])),
            Fr::from(BigInt([
                7312873495776744533,
                8114177336775667406,
                4613950413849816819,
                6586411640486648583,
            ])),
            Fr::from(BigInt([
                2527993771139348481,
                17031324069223192505,
                10395630042359995808,
                3622571238833603864,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
            Fr::from(BigInt([
                7233805586443071084,
                2742125060316549915,
                10773642635746952364,
                5737394731741332253,
            ])),
            Fr::from(BigInt([1699363200, 0, 0, 0])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_dataset_to_respone_values() {
        let example = r#"
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> 
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> 
PREFIX org: <http://www.w3.org/ns/org#> 
PREFIX bbsp16: <https://ex.org/bbs+/v0#> 
PREFIX lg16: <https://ex.org/lg16/v0#> 
PREFIX spok: <https://ex.org/spok/v0#> 
PREFIX uacc: <https://ex.org/uacc/v0#> 
PREFIX zkp: <https://ex.org/zkp/v0#> 
PREFIX cred: <https://www.w3.org/2018/credentials#> 

GRAPH _:4 {
	_:0 cred:credentialStatus <http://example.org/revocation#accumulatorId> .
	_:0 cred:credentialSubject _:7 .
	_:0 cred:issuer <http://example.org/organisations#aCompany> .
	_:0 _:16 _:17 .
	_:0 cred:validUntil _:22 .
	_:25 _:26 _:27 .
	_:7 org:memberOf <http://example.org/organisations#aCompany> .
}
GRAPH _:presentationProofGraph {
	_:cproof rdf:type zkp:CompositeProof .
	_:cproof zkp:hasComponent _:p0 .
	_:cproof zkp:hasComponent _:p1 .
	_:cproof zkp:hasComponent _:p2 .
	_:p0 rdf:type bbsp16:PoKS16 .
	_:p0 bbsp16:hasVerificationKey <http://example.org/keys#aCompanyKey> .
	_:p0 bbsp16:isProofOfKnowledgeOfSignatureOverGraph _:4 .
	_:p0 bbsp16:A_prime "og4GMdVXTPRV0BaP0uSo66QfLh8M/Otvnf5iJ+Lyf4a5XTAdVBumssaUFDy30pqe"^^xsd:base64Binary .
	_:p0 bbsp16:A_bar "oh2fnqQZ87TahtbGV+Te7UsjPt+GjCeSbo4cdVMVKCTKeVvtZtWP9K4Dk75DdicZ"^^xsd:base64Binary .
	_:p0 bbsp16:d "ihCgpycMsxkNeT9vnlRv8QqxxLMkadL1GHCOnzC2/kVltRIoqJrBpMV5pA84c8WO"^^xsd:base64Binary .
	_:p0 bbsp16:pi _:p0_spk1 .
	_:p0 bbsp16:pi _:p0_spk2 .
	_:4 spok:hasSchnorrResponse "zuN2DSmUsaqYiuafuIkEmqZ4sDZ26eBmpCptaTAWsA4="^^xsd:base64Binary .
	_:p0_spk1 rdf:type bbsp16:SPK1 .
	_:p0_spk1 spok:hasCommitmentToRandomness "gi01T28bCib+BSSHBWZvVAG+0ToQkDYnwD4euqtize1BouR+ENFwsLh8z1lZ35cz"^^xsd:base64Binary .
	_:p0_spk1 bbsp16:hasResponseValueFor_e "U2RteF5hv0+UpJmCP61A+YL/1e7kj5xLLNzWi1Pxt1E="^^xsd:base64Binary .
	_:p0_spk1 bbsp16:hasResponseValueFor_r2 "VrS/w+c3u9qLzM/tqo2axNa2ROUypxdTkFrFUj9L/Vo="^^xsd:base64Binary .
	_:p0_spk2 rdf:type bbsp16:SPK2 .
	_:p0_spk2 spok:hasCommitmentToRandomness "jWnoZyLUClhCBjGCZur/s1hNULJr7mSjW5hEuxbhm5scx8SVU4H6Aka1Ie7HzezL"^^xsd:base64Binary .
	_:p0_spk2 bbsp16:hasResponseValueFor_r3 "6fh2iSnq0+thhRHFWL8uuzTaDPjz1ZQmSTOxvdlBsCU="^^xsd:base64Binary .
	_:p0_spk2 bbsp16:hasResponseValueFor_s_prime "vUfqWkf8RDq3e58Abk81ORkg+hasy6loYnMxoeYd5AA="^^xsd:base64Binary .
	_:0 spok:hasSchnorrResponse "YT+CO0ZpZQGaDM28HFPOEOROWYzLt9G3MPwbO2+SywI="^^xsd:base64Binary .
	_:7 spok:hasSchnorrResponse "QW+HbSMojOgMiXBe6BOGUqL+qA1qhGerDo/uRpsXbw8="^^xsd:base64Binary .
	_:7 spok:hasSchnorrResponseForSuffix "m761hnHRdyrzR1ERS0SG8xj92/B2AZTc543JfRA3yTE="^^xsd:base64Binary .
	_:16 spok:hasSchnorrResponse "CphilYnVqzWW3X1OavlC98VH/wwvPDL23ZjdxHjVmF0="^^xsd:base64Binary .
	_:17 spok:hasSchnorrResponse "XJlQbfTDFizoVwJfnJJ+K5RWZr4KXI+MimMrMt7hqiM="^^xsd:base64Binary .
	_:17 spok:hasSchnorrResponseForSuffix "4dnHTvyhtr+fKiJSu5mCfFgU3ysTwrCcrYStanMt6g8="^^xsd:base64Binary .
	_:22 spok:hasSchnorrResponse "vD31XyvF7penDuF+XMd2qkIkIre7yTBZVIIhRgMSLUg="^^xsd:base64Binary .
	_:22 spok:hasSchnorrResponseForSuffix "dIr+YUK5hS9wZ2iSjwz6bQze4NBqIyi1Eo5vF5auEjQ="^^xsd:base64Binary .
	_:25 spok:hasSchnorrResponse "NWb862k4JRtPuJOh23Q+cVlatYCZkUgfjNZunUzFu0I="^^xsd:base64Binary .
	_:26 spok:hasSchnorrResponse "KD+DJVv+tAy0OuOKteMFzSf7w+Yx5S08Ghve7h4+IEI="^^xsd:base64Binary .
	_:27 spok:hasSchnorrResponse "hU3NlMHWPSGMDuzSsgYD0Ge3B2hPMWO4E6ZzkrdSu2Y="^^xsd:base64Binary .
	_:27 spok:hasSchnorrResponseForSuffix "CGUG+Nl4oBcHgBV2YfdmaElSaI8rat5H1suTuyJexxs="^^xsd:base64Binary .
	_:p1 rdf:type lg16:LegoGroth16ProofOfRangeMembership .
	_:p1 lg16:hasVerificationKey <http://example.org/keys#verifierLg16VerificationKey> .
	_:p1 lg16:hasWitness _:22 .
	_:p1 lg16:hasLowerBound "1383830400"^^xsd:nonNegativeInteger .
	_:p1 lg16:hasUpperBound "18446744073709551615"^^xsd:nonNegativeInteger .
	_:p1 lg16:hasProofValue _:p1_lg16pv .
	_:p1 lg16:pok _:p1_lg16sp .
	_:p1_lg16pv lg16:A "gHXauzK+2McFjmesHb3v/CYLYcOFUSWT1Mvl/9FQh6LbM8Kkl75wMZMlnJMrstxg"^^xsd:base64Binary .
	_:p1_lg16pv lg16:B "g/NpgGnqNIq7nuXvaZGBNaHNss77zsxIMCepqj5hBFbvwniPEoXRjSF9c8TMQuy8DVKPOG8KAiOmAFE5VlpTbcgSdSyMqImgcC4oLvqRUmC/DuOylZ3FE4wW2pSC51mn"^^xsd:base64Binary .
	_:p1_lg16pv lg16:C "sp4wRHTCFy7lZS5RsMj5Ynb/XDqED8cTg6ShxhE738QcyqTIYpkEclc3a0icd8bC"^^xsd:base64Binary .
	_:p1_lg16pv lg16:D "tocygVl+VS8ZjfnaQhJHYPLwC1Q28F5sL6RXwGEq3jRr7hXmUsGE+rhz6Q06+CTk"^^xsd:base64Binary .
	_:p1_lg16sp spok:hasCommitmentToRandomness "h+QEdFhILqMAlv8/G6CJPU9N3/7bChBJ0iAC/LXbr/VWIcl6gx93lUjb3dwdr6Lq"^^xsd:base64Binary .
	_:p1_lg16sp lg16:hasResponseValueFor_opening "JsKWf5EDO2C5JahAGi3GP4hpXU9dLfDFqWb6kySq/zU="^^xsd:base64Binary .
	_:p2 rdf:type uacc:UniversalAccumulatorProofOfNonMembership .
	_:p2 uacc:hasAccumulator <http://example.org/revocation#accumulatorId> .
	_:p2 uacc:hasWitness _:0 .
	_:p2 uacc:hasProvingKey <http://example.org/keys#proverUaccProvingKey> .
	_:p2 uacc:hasRandomizedWitness _:p2_uacc_rw .
	_:p2 uacc:hasCommitments _:p2_uacc_sc .
	_:p2 uacc:hasResponses _:p2_uacc_sr .
	_:p2_uacc_rw uacc:E_C "jzMh9OH6acxKJFYVrKtc3rng3vFmnPARdHD5OYxUd1RM9mMwwRfH4qaRHHqGmIcs"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:E_d "oWkf7nO8AzKE1NgyBzc0PZVUez4AwlAqkS6qXdhwn+IhV2Og/KM8yPBxSjj0QOZw"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:E_d_inv "tzZWdVuzwZAyiWbHfpcGuLiXk8Lqcp4bM1I5C33UEiQrHAmuHrpHZlraKRJZO2o6"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:commitment_to_randomness_T_sigma "kVvPlOqOEAEvl1rj7wa34x/LgcUE7BKl4KXXiHvfi04nUwv/t9C2PJ9x1ijPstLo"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:commitment_to_randomness_T_rho "oi5+VdRlGzq7eOt14WBpgkBSluMj7cgCM3uorL22O1LMc2RGFyaJb0dlS/7+4S1f"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_E "LKHwQoXU0kHz5QOoTrMXsJvGHELkL2z1mvZy9pH0JdL63ouA4EwOmwVTMeqkDvgDRHrZECz6knfuwwuQtChh0R/xkoPKbuF77qpWqwHVwLEtkPl76Z8SF2XRLkRRDG8BYFCXlUVm6Ur5O0MKSZfUi467sNupDPcYt3jf6ahevaFI6F6iF3kMHPAabbeMl68TdwkoKsObF3jD1OsuluJfMpTAD0MoRVZVDUV7dZ8gEPNej2U6+iC1kUrp1sOVkysY618/vUq61dGJarwN4USPcS5hbhXXVyBSPD3UUSEy02IssoTkjTqFz8P6zH80kr4WjaML4DBenoxeyqPK3g3pcOGKsAnIAxCmKMrZYXZkqS3XrrwcF/GyToCGXzu8h9EB2j+7VeMKLET8+El6qJNFU4WzRUFoFUhF2s83WmmDcDzZEWaORL1F5sOv7auTuk8OiQQVLEU7H3K1W/MID+7J57iEZ7Ubh2xE5KEbad8Hp5K8TXlX6Cm9e/YLvfvkDP8RR1tratW5coVVIkk9nbERWV6UxDXWMwXtSiAzUNv+MOZXiNgPeiiVR7dtKR/l2uAXI/IUrb/Okph5i8wLALl2mjV5o3xPpXEK3JUr28XCI7Q796n1MZaWmbbFMMeDpG4QOqC3QBpNUBIvfINOlBeEZRYgE/UNhflY/2GfZvLL+UyxmjnrBB9PfEiz0hpnh8kLpFreN7l+N5ircZwU6iGegmtiZI5o8iZsPgLbpq49JoerwN+Oori0atz1tCMUyIMV"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_sigma "ksoz+jdpnXqam3RfAW4hr7d/gGDB0hhRgHxZJXk+lJzJqTOsb3y1BSASJlIK94p5"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_rho "hXJoGVpQSUM1cu9G4ZTUaWjKfs+Pu3z7C/E3RFWn9LnWy/KAGz7eoCp6Sle2Vsv9"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_delta_sigma "oC1efA+qqqBw1EJzL5nc+b8DpKVtJBffCVJjkQmGDnQ68OTYASiRw7LqoAul/14a"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_delta_rho "g/WuGixc0MdB3kx1WdVM0u2svGW7mSll4F6fbkLSSE97G2IwEF5s/f214VfNrim2"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_A "hQo27wETk9fSABtW1iFXMLMt++I3IybfXSzPU29YUF7l67jmls5uZOxzleB++OkB"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_B "iWLp6SxwyW8L16ovEBvMO1U3uFeS7hONIcIxCo0Duwp0NN8nHelgjXMNwkGT7vJv"^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_sigma "6ZydiHp1n/3tYG0nSPh+f+U1jxB6sbD3GiN9SVVLiFU="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_rho "+06dP3GuFXlKRbkIBWP3lFrAPEuDN+Yqwd8l0/iknVY="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_delta_sigma "FigWlsvWYFsuM7p0wKLjekBv1nt/vb2lfk9Oh+rYixQ="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_delta_rho "vHKHBkiVphhxkA9OTldiIJ6kpwVkEgVBhfSyKysIpEw="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_u "vV/dK1OzKv1w/vUCIee5qIkxXvM9NedT9DgszdlRnCE="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_v "rv8+KJRmlz2Oc9HVtxO0mTE9VMdO0fbITQia+lAs/As="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_w "5R0AtIe0BJFX6FxmOCsRcQ7UC1IiY7bsFV7yURtEejw="^^xsd:base64Binary .
}
    "#;

        // Parse the example dataset
        let mut dataset: LightDataset = gtrig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");
        // Parse the example dataset
        let mut quads_list: QuadsList<SimpleTermIndex<u32>> = gtrig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let wit_graph_id = BnodeId::new_unchecked("4");

        let mut credential_quads_list = QuadsList::<SimpleTermIndex<u32>>::new();
        for quad in quads_list.quads() {
            let q = quad.unwrap();
            if wit_graph_id.into_term::<SimpleTerm<'_>>() == q.g().unwrap() {
                credential_quads_list.insert(q.s(), q.p(), q.o(), q.g());
            }
        }
        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoder::new();
        let (result_hidden_message_responses, result_revealed_messages, result_equal_indicies) =
            rdf2fr_encoder
                .quads_to_response_values(&dataset, &credential_quads_list)
                .unwrap();

        let mut expected_hidden_message_responses = BTreeMap::<usize, Fr>::new();
        let mut expected_revealed_messages = BTreeMap::<usize, Fr>::new();
        let mut expected_equal_indicies = BTreeMap::<String, Vec<usize>>::new();

        expected_hidden_message_responses.insert(
            0,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            4,
            Fr::from(BigInt([
                12299774961366000590,
                11098146807797418648,
                7413181680584784038,
                1058370309615069860,
            ])),
        );
        expected_hidden_message_responses.insert(
            5,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            7,
            Fr::from(BigInt([
                16756812446165331777,
                5946462246727092492,
                12350986094117453474,
                1112133588661210894,
            ])),
        );
        expected_hidden_message_responses.insert(
            8,
            Fr::from(BigInt([
                3060144757343108763,
                17547788087299491827,
                15894330595256040728,
                3587459122146676199,
            ])),
        );
        expected_hidden_message_responses.insert(
            9,
            Fr::from(BigInt([
                12299774961366000590,
                11098146807797418648,
                7413181680584784038,
                1058370309615069860,
            ])),
        );
        expected_hidden_message_responses.insert(
            10,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            14,
            Fr::from(BigInt([
                12299774961366000590,
                11098146807797418648,
                7413181680584784038,
                1058370309615069860,
            ])),
        );
        expected_hidden_message_responses.insert(
            15,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            16,
            Fr::from(BigInt([
                3867419491921205258,
                17817077310809824662,
                17740308054944991173,
                6744375156662966493,
            ])),
        );
        expected_hidden_message_responses.insert(
            17,
            Fr::from(BigInt([
                3176942041729898844,
                3134103591002986472,
                10128415288193341076,
                2570114881808982922,
            ])),
        );
        expected_hidden_message_responses.insert(
            18,
            Fr::from(BigInt([
                13814407012031125985,
                8971902437491354271,
                11290737653414040664,
                1146779028853458093,
            ])),
        );
        expected_hidden_message_responses.insert(
            19,
            Fr::from(BigInt([
                12299774961366000590,
                11098146807797418648,
                7413181680584784038,
                1058370309615069860,
            ])),
        );
        expected_hidden_message_responses.insert(
            20,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            22,
            Fr::from(BigInt([
                10947904534268427708,
                12283224233779203751,
                6426858476326233154,
                5200832949953593940,
            ])),
        );
        expected_hidden_message_responses.insert(
            23,
            Fr::from(BigInt([
                3424346786448181876,
                7924660305087981424,
                13053722461611286028,
                3752253399214558738,
            ])),
        );
        expected_hidden_message_responses.insert(
            24,
            Fr::from(BigInt([
                12299774961366000590,
                11098146807797418648,
                7413181680584784038,
                1058370309615069860,
            ])),
        );
        expected_hidden_message_responses.insert(
            25,
            Fr::from(BigInt([
                1956031640744257077,
                8160088061499390031,
                2254211701974325849,
                4808653959997609612,
            ])),
        );
        expected_hidden_message_responses.insert(
            26,
            Fr::from(BigInt([
                915636291687890728,
                14773464521517513396,
                4336374018715417383,
                4764876708335459098,
            ])),
        );
        expected_hidden_message_responses.insert(
            27,
            Fr::from(BigInt([
                2395306703744486789,
                14988831349931773580,
                13286517542790608743,
                7402601360903087635,
            ])),
        );
        expected_hidden_message_responses.insert(
            28,
            Fr::from(BigInt([
                1702493536710452488,
                7522972225534001159,
                5178693356844765769,
                2001672062658399190,
            ])),
        );
        expected_hidden_message_responses.insert(
            29,
            Fr::from(BigInt([
                12299774961366000590,
                11098146807797418648,
                7413181680584784038,
                1058370309615069860,
            ])),
        );
        expected_hidden_message_responses.insert(
            30,
            Fr::from(BigInt([
                16756812446165331777,
                5946462246727092492,
                12350986094117453474,
                1112133588661210894,
            ])),
        );
        expected_hidden_message_responses.insert(
            34,
            Fr::from(BigInt([
                12299774961366000590,
                11098146807797418648,
                7413181680584784038,
                1058370309615069860,
            ])),
        );

        expected_revealed_messages.insert(
            1,
            Fr::from(BigInt([
                12128200784307151646,
                6239862291845800445,
                7794544965875761465,
                2256911646900887038,
            ])),
        );
        expected_revealed_messages.insert(
            2,
            Fr::from(BigInt([
                7312873495776744533,
                8114177336775667406,
                4613950413849816819,
                6586411640486648583,
            ])),
        );
        expected_revealed_messages.insert(
            3,
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
        );
        expected_revealed_messages.insert(
            6,
            Fr::from(BigInt([
                13479492388325692125,
                8774317675204352409,
                9473803180199958296,
                48045467206693763,
            ])),
        );
        expected_revealed_messages.insert(
            11,
            Fr::from(BigInt([
                16510617979322594564,
                12015788767324311352,
                7271166171282263051,
                6933608981523975618,
            ])),
        );
        expected_revealed_messages.insert(
            12,
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        );
        expected_revealed_messages.insert(
            13,
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
        );
        expected_revealed_messages.insert(
            21,
            Fr::from(BigInt([
                8584643261987331863,
                16200755082649097329,
                12337835172712087143,
                3707653408865982187,
            ])),
        );
        expected_revealed_messages.insert(
            31,
            Fr::from(BigInt([
                17277122902210706885,
                10933249048245759994,
                9697185051640140087,
                2078422620467228261,
            ])),
        );
        expected_revealed_messages.insert(
            32,
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        );
        expected_revealed_messages.insert(
            33,
            Fr::from(BigInt([
                241225442164632184,
                8273765786548291270,
                7009669069494759313,
                1825118895109998218,
            ])),
        );
        expected_equal_indicies.insert("0".to_string(), vec![0, 5, 10, 15, 20]);
        expected_equal_indicies.insert("16".to_string(), vec![16]);
        expected_equal_indicies.insert("17".to_string(), vec![17]);
        expected_equal_indicies.insert("22".to_string(), vec![22]);
        expected_equal_indicies.insert("25".to_string(), vec![25]);
        expected_equal_indicies.insert("26".to_string(), vec![26]);
        expected_equal_indicies.insert("27".to_string(), vec![27]);
        expected_equal_indicies.insert("4".to_string(), vec![4, 9, 14, 19, 24, 29, 34]);
        expected_equal_indicies.insert("7".to_string(), vec![7, 30]);

        assert_eq!(
            result_hidden_message_responses,
            expected_hidden_message_responses
        );
        assert_eq!(result_revealed_messages, expected_revealed_messages);
        assert_eq!(result_equal_indicies, expected_equal_indicies);
    }

    #[test]
    fn test_dataset_to_respone_values_trimmed() {
        let example = r#"
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> 
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> 
PREFIX org: <http://www.w3.org/ns/org#> 
PREFIX bbsp16: <https://ex.org/bbs+/v0#> 
PREFIX lg16: <https://ex.org/lg16/v0#> 
PREFIX spok: <https://ex.org/spok/v0#> 
PREFIX uacc: <https://ex.org/uacc/v0#> 
PREFIX zkp: <https://ex.org/zkp/v0#> 
PREFIX cred: <https://www.w3.org/2018/credentials#> 

GRAPH _:4 {
	_:0 cred:credentialStatus <http://example.org/revocation#accumulatorId> .
	_:0 cred:credentialSubject _:7 .
	_:0 cred:issuer <http://example.org/organisations#aCompany> .
	_:0 _:16 _:17 .
	_:0 cred:validUntil _:22 .
	_:25 _:26 _:27 .
	_:7 org:memberOf <http://example.org/organisations#aCompany> .
}
GRAPH _:presentationProofGraph {
	_:cproof rdf:type zkp:CompositeProof .
	_:cproof zkp:hasComponent _:p0 .
	_:cproof zkp:hasComponent _:p1 .
	_:cproof zkp:hasComponent _:p2 .
	_:p0 rdf:type bbsp16:PoKS16 .
	_:p0 bbsp16:hasVerificationKey <http://example.org/keys#aCompanyKey> .
	_:p0 bbsp16:isProofOfKnowledgeOfSignatureOverGraph _:4 .
	_:p0 bbsp16:A_prime "og4GMdVXTPRV0BaP0uSo66QfLh8M/Otvnf5iJ+Lyf4a5XTAdVBumssaUFDy30pqe"^^xsd:base64Binary .
	_:p0 bbsp16:A_bar "oh2fnqQZ87TahtbGV+Te7UsjPt+GjCeSbo4cdVMVKCTKeVvtZtWP9K4Dk75DdicZ"^^xsd:base64Binary .
	_:p0 bbsp16:d "ihCgpycMsxkNeT9vnlRv8QqxxLMkadL1GHCOnzC2/kVltRIoqJrBpMV5pA84c8WO"^^xsd:base64Binary .
	_:p0 bbsp16:pi _:p0_spk1 .
	_:p0 bbsp16:pi _:p0_spk2 .
	_:p0_spk1 rdf:type bbsp16:SPK1 .
	_:p0_spk1 spok:hasCommitmentToRandomness "gi01T28bCib+BSSHBWZvVAG+0ToQkDYnwD4euqtize1BouR+ENFwsLh8z1lZ35cz"^^xsd:base64Binary .
	_:p0_spk1 bbsp16:hasResponseValueFor_e "U2RteF5hv0+UpJmCP61A+YL/1e7kj5xLLNzWi1Pxt1E="^^xsd:base64Binary .
	_:p0_spk1 bbsp16:hasResponseValueFor_r2 "VrS/w+c3u9qLzM/tqo2axNa2ROUypxdTkFrFUj9L/Vo="^^xsd:base64Binary .
	_:p0_spk2 rdf:type bbsp16:SPK2 .
	_:p0_spk2 spok:hasCommitmentToRandomness "jWnoZyLUClhCBjGCZur/s1hNULJr7mSjW5hEuxbhm5scx8SVU4H6Aka1Ie7HzezL"^^xsd:base64Binary .
	_:p0_spk2 bbsp16:hasResponseValueFor_r3 "6fh2iSnq0+thhRHFWL8uuzTaDPjz1ZQmSTOxvdlBsCU="^^xsd:base64Binary .
	_:p0_spk2 bbsp16:hasResponseValueFor_s_prime "vUfqWkf8RDq3e58Abk81ORkg+hasy6loYnMxoeYd5AA="^^xsd:base64Binary .
	_:0 spok:hasSchnorrResponse "YT+CO0ZpZQGaDM28HFPOEOROWYzLt9G3MPwbO2+SywI="^^xsd:base64Binary .
	_:7 spok:hasSchnorrResponse "QW+HbSMojOgMiXBe6BOGUqL+qA1qhGerDo/uRpsXbw8="^^xsd:base64Binary .
	_:16 spok:hasSchnorrResponse "CphilYnVqzWW3X1OavlC98VH/wwvPDL23ZjdxHjVmF0="^^xsd:base64Binary .
	_:17 spok:hasSchnorrResponse "XJlQbfTDFizoVwJfnJJ+K5RWZr4KXI+MimMrMt7hqiM="^^xsd:base64Binary .
	_:22 spok:hasSchnorrResponse "vD31XyvF7penDuF+XMd2qkIkIre7yTBZVIIhRgMSLUg="^^xsd:base64Binary .
	_:22 spok:hasSchnorrResponseForSuffix "dIr+YUK5hS9wZ2iSjwz6bQze4NBqIyi1Eo5vF5auEjQ="^^xsd:base64Binary .
	_:25 spok:hasSchnorrResponse "NWb862k4JRtPuJOh23Q+cVlatYCZkUgfjNZunUzFu0I="^^xsd:base64Binary .
	_:26 spok:hasSchnorrResponse "KD+DJVv+tAy0OuOKteMFzSf7w+Yx5S08Ghve7h4+IEI="^^xsd:base64Binary .
	_:27 spok:hasSchnorrResponse "hU3NlMHWPSGMDuzSsgYD0Ge3B2hPMWO4E6ZzkrdSu2Y="^^xsd:base64Binary .
	_:p1 rdf:type lg16:LegoGroth16ProofOfRangeMembership .
	_:p1 lg16:hasVerificationKey <http://example.org/keys#verifierLg16VerificationKey> .
	_:p1 lg16:hasWitness _:22 .
	_:p1 lg16:hasLowerBound "1383830400"^^xsd:nonNegativeInteger .
	_:p1 lg16:hasUpperBound "18446744073709551615"^^xsd:nonNegativeInteger .
	_:p1 lg16:hasProofValue _:p1_lg16pv .
	_:p1 lg16:pok _:p1_lg16sp .
	_:p1_lg16pv lg16:A "gHXauzK+2McFjmesHb3v/CYLYcOFUSWT1Mvl/9FQh6LbM8Kkl75wMZMlnJMrstxg"^^xsd:base64Binary .
	_:p1_lg16pv lg16:B "g/NpgGnqNIq7nuXvaZGBNaHNss77zsxIMCepqj5hBFbvwniPEoXRjSF9c8TMQuy8DVKPOG8KAiOmAFE5VlpTbcgSdSyMqImgcC4oLvqRUmC/DuOylZ3FE4wW2pSC51mn"^^xsd:base64Binary .
	_:p1_lg16pv lg16:C "sp4wRHTCFy7lZS5RsMj5Ynb/XDqED8cTg6ShxhE738QcyqTIYpkEclc3a0icd8bC"^^xsd:base64Binary .
	_:p1_lg16pv lg16:D "tocygVl+VS8ZjfnaQhJHYPLwC1Q28F5sL6RXwGEq3jRr7hXmUsGE+rhz6Q06+CTk"^^xsd:base64Binary .
	_:p1_lg16sp spok:hasCommitmentToRandomness "h+QEdFhILqMAlv8/G6CJPU9N3/7bChBJ0iAC/LXbr/VWIcl6gx93lUjb3dwdr6Lq"^^xsd:base64Binary .
	_:p1_lg16sp lg16:hasResponseValueFor_opening "JsKWf5EDO2C5JahAGi3GP4hpXU9dLfDFqWb6kySq/zU="^^xsd:base64Binary .
	_:p2 rdf:type uacc:UniversalAccumulatorProofOfNonMembership .
	_:p2 uacc:hasAccumulator <http://example.org/revocation#accumulatorId> .
	_:p2 uacc:hasWitness _:0 .
	_:p2 uacc:hasProvingKey <http://example.org/keys#proverUaccProvingKey> .
	_:p2 uacc:hasRandomizedWitness _:p2_uacc_rw .
	_:p2 uacc:hasCommitments _:p2_uacc_sc .
	_:p2 uacc:hasResponses _:p2_uacc_sr .
	_:p2_uacc_rw uacc:E_C "jzMh9OH6acxKJFYVrKtc3rng3vFmnPARdHD5OYxUd1RM9mMwwRfH4qaRHHqGmIcs"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:E_d "oWkf7nO8AzKE1NgyBzc0PZVUez4AwlAqkS6qXdhwn+IhV2Og/KM8yPBxSjj0QOZw"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:E_d_inv "tzZWdVuzwZAyiWbHfpcGuLiXk8Lqcp4bM1I5C33UEiQrHAmuHrpHZlraKRJZO2o6"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:commitment_to_randomness_T_sigma "kVvPlOqOEAEvl1rj7wa34x/LgcUE7BKl4KXXiHvfi04nUwv/t9C2PJ9x1ijPstLo"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:commitment_to_randomness_T_rho "oi5+VdRlGzq7eOt14WBpgkBSluMj7cgCM3uorL22O1LMc2RGFyaJb0dlS/7+4S1f"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_E "LKHwQoXU0kHz5QOoTrMXsJvGHELkL2z1mvZy9pH0JdL63ouA4EwOmwVTMeqkDvgDRHrZECz6knfuwwuQtChh0R/xkoPKbuF77qpWqwHVwLEtkPl76Z8SF2XRLkRRDG8BYFCXlUVm6Ur5O0MKSZfUi467sNupDPcYt3jf6ahevaFI6F6iF3kMHPAabbeMl68TdwkoKsObF3jD1OsuluJfMpTAD0MoRVZVDUV7dZ8gEPNej2U6+iC1kUrp1sOVkysY618/vUq61dGJarwN4USPcS5hbhXXVyBSPD3UUSEy02IssoTkjTqFz8P6zH80kr4WjaML4DBenoxeyqPK3g3pcOGKsAnIAxCmKMrZYXZkqS3XrrwcF/GyToCGXzu8h9EB2j+7VeMKLET8+El6qJNFU4WzRUFoFUhF2s83WmmDcDzZEWaORL1F5sOv7auTuk8OiQQVLEU7H3K1W/MID+7J57iEZ7Ubh2xE5KEbad8Hp5K8TXlX6Cm9e/YLvfvkDP8RR1tratW5coVVIkk9nbERWV6UxDXWMwXtSiAzUNv+MOZXiNgPeiiVR7dtKR/l2uAXI/IUrb/Okph5i8wLALl2mjV5o3xPpXEK3JUr28XCI7Q796n1MZaWmbbFMMeDpG4QOqC3QBpNUBIvfINOlBeEZRYgE/UNhflY/2GfZvLL+UyxmjnrBB9PfEiz0hpnh8kLpFreN7l+N5ircZwU6iGegmtiZI5o8iZsPgLbpq49JoerwN+Oori0atz1tCMUyIMV"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_sigma "ksoz+jdpnXqam3RfAW4hr7d/gGDB0hhRgHxZJXk+lJzJqTOsb3y1BSASJlIK94p5"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_rho "hXJoGVpQSUM1cu9G4ZTUaWjKfs+Pu3z7C/E3RFWn9LnWy/KAGz7eoCp6Sle2Vsv9"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_delta_sigma "oC1efA+qqqBw1EJzL5nc+b8DpKVtJBffCVJjkQmGDnQ68OTYASiRw7LqoAul/14a"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_delta_rho "g/WuGixc0MdB3kx1WdVM0u2svGW7mSll4F6fbkLSSE97G2IwEF5s/f214VfNrim2"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_A "hQo27wETk9fSABtW1iFXMLMt++I3IybfXSzPU29YUF7l67jmls5uZOxzleB++OkB"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_B "iWLp6SxwyW8L16ovEBvMO1U3uFeS7hONIcIxCo0Duwp0NN8nHelgjXMNwkGT7vJv"^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_sigma "6ZydiHp1n/3tYG0nSPh+f+U1jxB6sbD3GiN9SVVLiFU="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_rho "+06dP3GuFXlKRbkIBWP3lFrAPEuDN+Yqwd8l0/iknVY="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_delta_sigma "FigWlsvWYFsuM7p0wKLjekBv1nt/vb2lfk9Oh+rYixQ="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_delta_rho "vHKHBkiVphhxkA9OTldiIJ6kpwVkEgVBhfSyKysIpEw="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_u "vV/dK1OzKv1w/vUCIee5qIkxXvM9NedT9DgszdlRnCE="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_v "rv8+KJRmlz2Oc9HVtxO0mTE9VMdO0fbITQia+lAs/As="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_w "5R0AtIe0BJFX6FxmOCsRcQ7UC1IiY7bsFV7yURtEejw="^^xsd:base64Binary .
}
    "#;

        // Parse the example dataset
        let mut dataset: LightDataset = gtrig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");
        // Parse the example dataset
        let mut quads_list: QuadsList<SimpleTermIndex<u32>> = gtrig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let wit_graph_id = BnodeId::new_unchecked("4");

        let mut credential_quads_list = QuadsList::<SimpleTermIndex<u32>>::new();
        for quad in quads_list.quads() {
            let q = quad.unwrap();
            if wit_graph_id.into_term::<SimpleTerm<'_>>() == q.g().unwrap() {
                credential_quads_list.insert(q.s(), q.p(), q.o(), q.g());
            }
        }
        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoderTrimmed::new();
        let (result_hidden_message_responses, result_revealed_messages, result_equal_indicies) =
            rdf2fr_encoder
                .quads_to_response_values(&dataset, &credential_quads_list)
                .unwrap();

        let mut expected_hidden_message_responses = BTreeMap::<usize, Fr>::new();
        let mut expected_revealed_messages = BTreeMap::<usize, Fr>::new();
        let mut expected_equal_indicies = BTreeMap::<String, Vec<usize>>::new();

        expected_hidden_message_responses.insert(
            0,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            3,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            5,
            Fr::from(BigInt([
                16756812446165331777,
                5946462246727092492,
                12350986094117453474,
                1112133588661210894,
            ])),
        );
        expected_hidden_message_responses.insert(
            6,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            9,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            10,
            Fr::from(BigInt([
                3867419491921205258,
                17817077310809824662,
                17740308054944991173,
                6744375156662966493,
            ])),
        );
        expected_hidden_message_responses.insert(
            11,
            Fr::from(BigInt([
                3176942041729898844,
                3134103591002986472,
                10128415288193341076,
                2570114881808982922,
            ])),
        );
        expected_hidden_message_responses.insert(
            12,
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            14,
            Fr::from(BigInt([
                10947904534268427708,
                12283224233779203751,
                6426858476326233154,
                5200832949953593940,
            ])),
        );
        expected_hidden_message_responses.insert(
            15,
            Fr::from(BigInt([
                3424346786448181876,
                7924660305087981424,
                13053722461611286028,
                3752253399214558738,
            ])),
        );
        expected_hidden_message_responses.insert(
            16,
            Fr::from(BigInt([
                1956031640744257077,
                8160088061499390031,
                2254211701974325849,
                4808653959997609612,
            ])),
        );
        expected_hidden_message_responses.insert(
            17,
            Fr::from(BigInt([
                915636291687890728,
                14773464521517513396,
                4336374018715417383,
                4764876708335459098,
            ])),
        );
        expected_hidden_message_responses.insert(
            18,
            Fr::from(BigInt([
                2395306703744486789,
                14988831349931773580,
                13286517542790608743,
                7402601360903087635,
            ])),
        );
        expected_hidden_message_responses.insert(
            19,
            Fr::from(BigInt([
                16756812446165331777,
                5946462246727092492,
                12350986094117453474,
                1112133588661210894,
            ])),
        );

        expected_revealed_messages.insert(
            1,
            Fr::from(BigInt([
                12128200784307151646,
                6239862291845800445,
                7794544965875761465,
                2256911646900887038,
            ])),
        );
        expected_revealed_messages.insert(
            2,
            Fr::from(BigInt([
                7312873495776744533,
                8114177336775667406,
                4613950413849816819,
                6586411640486648583,
            ])),
        );
        expected_revealed_messages.insert(
            4,
            Fr::from(BigInt([
                13479492388325692125,
                8774317675204352409,
                9473803180199958296,
                48045467206693763,
            ])),
        );
        expected_revealed_messages.insert(
            7,
            Fr::from(BigInt([
                16510617979322594564,
                12015788767324311352,
                7271166171282263051,
                6933608981523975618,
            ])),
        );
        expected_revealed_messages.insert(
            8,
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        );
        expected_revealed_messages.insert(
            13,
            Fr::from(BigInt([
                8584643261987331863,
                16200755082649097329,
                12337835172712087143,
                3707653408865982187,
            ])),
        );
        expected_revealed_messages.insert(
            20,
            Fr::from(BigInt([
                17277122902210706885,
                10933249048245759994,
                9697185051640140087,
                2078422620467228261,
            ])),
        );
        expected_revealed_messages.insert(
            21,
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        );
        // bn id -> index in graph
        expected_equal_indicies.insert("0".to_string(), vec![0, 3, 6, 9, 12]);
        expected_equal_indicies.insert("16".to_string(), vec![10]);
        expected_equal_indicies.insert("17".to_string(), vec![11]);
        expected_equal_indicies.insert("22".to_string(), vec![14]);
        expected_equal_indicies.insert("25".to_string(), vec![16]);
        expected_equal_indicies.insert("26".to_string(), vec![17]);
        expected_equal_indicies.insert("27".to_string(), vec![18]);
        expected_equal_indicies.insert("7".to_string(), vec![5, 19]);

        assert_eq!(
            result_hidden_message_responses,
            expected_hidden_message_responses
        );
        assert_eq!(result_revealed_messages, expected_revealed_messages);
        assert_eq!(result_equal_indicies, expected_equal_indicies);
    }

    #[test]
    fn test_dataset_to_respone_values_schema() {
        let example = r#"
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> 
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> 
PREFIX org: <http://www.w3.org/ns/org#> 
PREFIX bbsp16: <https://ex.org/bbs+/v0#> 
PREFIX lg16: <https://ex.org/lg16/v0#> 
PREFIX spok: <https://ex.org/spok/v0#> 
PREFIX uacc: <https://ex.org/uacc/v0#> 
PREFIX zkp: <https://ex.org/zkp/v0#> 
PREFIX cred: <https://www.w3.org/2018/credentials#> 

GRAPH _:4 {
	_:0 cred:credentialStatus <http://example.org/revocation#accumulatorId> .
	_:0 cred:credentialSubject _:7 .
	_:0 cred:issuer <http://example.org/organisations#aCompany> .
	_:0 _:16 _:17 .
	_:0 cred:validUntil _:22 .
	_:25 _:26 _:27 .
	_:7 org:memberOf <http://example.org/organisations#aCompany> .
}
GRAPH _:presentationProofGraph {
	_:cproof rdf:type zkp:CompositeProof .
	_:cproof zkp:hasComponent _:p0 .
	_:cproof zkp:hasComponent _:p1 .
	_:cproof zkp:hasComponent _:p2 .
	_:p0 rdf:type bbsp16:PoKS16 .
	_:p0 bbsp16:hasVerificationKey <http://example.org/keys#aCompanyKey> .
	_:p0 bbsp16:isProofOfKnowledgeOfSignatureOverGraph _:4 .
	_:p0 bbsp16:A_prime "og4GMdVXTPRV0BaP0uSo66QfLh8M/Otvnf5iJ+Lyf4a5XTAdVBumssaUFDy30pqe"^^xsd:base64Binary .
	_:p0 bbsp16:A_bar "oh2fnqQZ87TahtbGV+Te7UsjPt+GjCeSbo4cdVMVKCTKeVvtZtWP9K4Dk75DdicZ"^^xsd:base64Binary .
	_:p0 bbsp16:d "ihCgpycMsxkNeT9vnlRv8QqxxLMkadL1GHCOnzC2/kVltRIoqJrBpMV5pA84c8WO"^^xsd:base64Binary .
	_:p0 bbsp16:pi _:p0_spk1 .
	_:p0 bbsp16:pi _:p0_spk2 .
	_:p0_spk1 rdf:type bbsp16:SPK1 .
	_:p0_spk1 spok:hasCommitmentToRandomness "gi01T28bCib+BSSHBWZvVAG+0ToQkDYnwD4euqtize1BouR+ENFwsLh8z1lZ35cz"^^xsd:base64Binary .
	_:p0_spk1 bbsp16:hasResponseValueFor_e "U2RteF5hv0+UpJmCP61A+YL/1e7kj5xLLNzWi1Pxt1E="^^xsd:base64Binary .
	_:p0_spk1 bbsp16:hasResponseValueFor_r2 "VrS/w+c3u9qLzM/tqo2axNa2ROUypxdTkFrFUj9L/Vo="^^xsd:base64Binary .
	_:p0_spk2 rdf:type bbsp16:SPK2 .
	_:p0_spk2 spok:hasCommitmentToRandomness "jWnoZyLUClhCBjGCZur/s1hNULJr7mSjW5hEuxbhm5scx8SVU4H6Aka1Ie7HzezL"^^xsd:base64Binary .
	_:p0_spk2 bbsp16:hasResponseValueFor_r3 "6fh2iSnq0+thhRHFWL8uuzTaDPjz1ZQmSTOxvdlBsCU="^^xsd:base64Binary .
	_:p0_spk2 bbsp16:hasResponseValueFor_s_prime "vUfqWkf8RDq3e58Abk81ORkg+hasy6loYnMxoeYd5AA="^^xsd:base64Binary .
	_:0 spok:hasSchnorrResponse "YT+CO0ZpZQGaDM28HFPOEOROWYzLt9G3MPwbO2+SywI="^^xsd:base64Binary .
	_:7 spok:hasSchnorrResponse "QW+HbSMojOgMiXBe6BOGUqL+qA1qhGerDo/uRpsXbw8="^^xsd:base64Binary .
	_:16 spok:hasSchnorrResponse "CphilYnVqzWW3X1OavlC98VH/wwvPDL23ZjdxHjVmF0="^^xsd:base64Binary .
	_:17 spok:hasSchnorrResponse "XJlQbfTDFizoVwJfnJJ+K5RWZr4KXI+MimMrMt7hqiM="^^xsd:base64Binary .
	_:22 spok:hasSchnorrResponse "vD31XyvF7penDuF+XMd2qkIkIre7yTBZVIIhRgMSLUg="^^xsd:base64Binary .
	_:22 spok:hasSchnorrResponseForSuffix "dIr+YUK5hS9wZ2iSjwz6bQze4NBqIyi1Eo5vF5auEjQ="^^xsd:base64Binary .
	_:25 spok:hasSchnorrResponse "NWb862k4JRtPuJOh23Q+cVlatYCZkUgfjNZunUzFu0I="^^xsd:base64Binary .
	_:26 spok:hasSchnorrResponse "KD+DJVv+tAy0OuOKteMFzSf7w+Yx5S08Ghve7h4+IEI="^^xsd:base64Binary .
	_:27 spok:hasSchnorrResponse "hU3NlMHWPSGMDuzSsgYD0Ge3B2hPMWO4E6ZzkrdSu2Y="^^xsd:base64Binary .
	_:p1 rdf:type lg16:LegoGroth16ProofOfRangeMembership .
	_:p1 lg16:hasVerificationKey <http://example.org/keys#verifierLg16VerificationKey> .
	_:p1 lg16:hasWitness _:22 .
	_:p1 lg16:hasLowerBound "1383830400"^^xsd:nonNegativeInteger .
	_:p1 lg16:hasUpperBound "18446744073709551615"^^xsd:nonNegativeInteger .
	_:p1 lg16:hasProofValue _:p1_lg16pv .
	_:p1 lg16:pok _:p1_lg16sp .
	_:p1_lg16pv lg16:A "gHXauzK+2McFjmesHb3v/CYLYcOFUSWT1Mvl/9FQh6LbM8Kkl75wMZMlnJMrstxg"^^xsd:base64Binary .
	_:p1_lg16pv lg16:B "g/NpgGnqNIq7nuXvaZGBNaHNss77zsxIMCepqj5hBFbvwniPEoXRjSF9c8TMQuy8DVKPOG8KAiOmAFE5VlpTbcgSdSyMqImgcC4oLvqRUmC/DuOylZ3FE4wW2pSC51mn"^^xsd:base64Binary .
	_:p1_lg16pv lg16:C "sp4wRHTCFy7lZS5RsMj5Ynb/XDqED8cTg6ShxhE738QcyqTIYpkEclc3a0icd8bC"^^xsd:base64Binary .
	_:p1_lg16pv lg16:D "tocygVl+VS8ZjfnaQhJHYPLwC1Q28F5sL6RXwGEq3jRr7hXmUsGE+rhz6Q06+CTk"^^xsd:base64Binary .
	_:p1_lg16sp spok:hasCommitmentToRandomness "h+QEdFhILqMAlv8/G6CJPU9N3/7bChBJ0iAC/LXbr/VWIcl6gx93lUjb3dwdr6Lq"^^xsd:base64Binary .
	_:p1_lg16sp lg16:hasResponseValueFor_opening "JsKWf5EDO2C5JahAGi3GP4hpXU9dLfDFqWb6kySq/zU="^^xsd:base64Binary .
	_:p2 rdf:type uacc:UniversalAccumulatorProofOfNonMembership .
	_:p2 uacc:hasAccumulator <http://example.org/revocation#accumulatorId> .
	_:p2 uacc:hasWitness _:0 .
	_:p2 uacc:hasProvingKey <http://example.org/keys#proverUaccProvingKey> .
	_:p2 uacc:hasRandomizedWitness _:p2_uacc_rw .
	_:p2 uacc:hasCommitments _:p2_uacc_sc .
	_:p2 uacc:hasResponses _:p2_uacc_sr .
	_:p2_uacc_rw uacc:E_C "jzMh9OH6acxKJFYVrKtc3rng3vFmnPARdHD5OYxUd1RM9mMwwRfH4qaRHHqGmIcs"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:E_d "oWkf7nO8AzKE1NgyBzc0PZVUez4AwlAqkS6qXdhwn+IhV2Og/KM8yPBxSjj0QOZw"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:E_d_inv "tzZWdVuzwZAyiWbHfpcGuLiXk8Lqcp4bM1I5C33UEiQrHAmuHrpHZlraKRJZO2o6"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:commitment_to_randomness_T_sigma "kVvPlOqOEAEvl1rj7wa34x/LgcUE7BKl4KXXiHvfi04nUwv/t9C2PJ9x1ijPstLo"^^xsd:base64Binary .
	_:p2_uacc_rw uacc:commitment_to_randomness_T_rho "oi5+VdRlGzq7eOt14WBpgkBSluMj7cgCM3uorL22O1LMc2RGFyaJb0dlS/7+4S1f"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_E "LKHwQoXU0kHz5QOoTrMXsJvGHELkL2z1mvZy9pH0JdL63ouA4EwOmwVTMeqkDvgDRHrZECz6knfuwwuQtChh0R/xkoPKbuF77qpWqwHVwLEtkPl76Z8SF2XRLkRRDG8BYFCXlUVm6Ur5O0MKSZfUi467sNupDPcYt3jf6ahevaFI6F6iF3kMHPAabbeMl68TdwkoKsObF3jD1OsuluJfMpTAD0MoRVZVDUV7dZ8gEPNej2U6+iC1kUrp1sOVkysY618/vUq61dGJarwN4USPcS5hbhXXVyBSPD3UUSEy02IssoTkjTqFz8P6zH80kr4WjaML4DBenoxeyqPK3g3pcOGKsAnIAxCmKMrZYXZkqS3XrrwcF/GyToCGXzu8h9EB2j+7VeMKLET8+El6qJNFU4WzRUFoFUhF2s83WmmDcDzZEWaORL1F5sOv7auTuk8OiQQVLEU7H3K1W/MID+7J57iEZ7Ubh2xE5KEbad8Hp5K8TXlX6Cm9e/YLvfvkDP8RR1tratW5coVVIkk9nbERWV6UxDXWMwXtSiAzUNv+MOZXiNgPeiiVR7dtKR/l2uAXI/IUrb/Okph5i8wLALl2mjV5o3xPpXEK3JUr28XCI7Q796n1MZaWmbbFMMeDpG4QOqC3QBpNUBIvfINOlBeEZRYgE/UNhflY/2GfZvLL+UyxmjnrBB9PfEiz0hpnh8kLpFreN7l+N5ircZwU6iGegmtiZI5o8iZsPgLbpq49JoerwN+Oori0atz1tCMUyIMV"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_sigma "ksoz+jdpnXqam3RfAW4hr7d/gGDB0hhRgHxZJXk+lJzJqTOsb3y1BSASJlIK94p5"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_rho "hXJoGVpQSUM1cu9G4ZTUaWjKfs+Pu3z7C/E3RFWn9LnWy/KAGz7eoCp6Sle2Vsv9"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_delta_sigma "oC1efA+qqqBw1EJzL5nc+b8DpKVtJBffCVJjkQmGDnQ68OTYASiRw7LqoAul/14a"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_delta_rho "g/WuGixc0MdB3kx1WdVM0u2svGW7mSll4F6fbkLSSE97G2IwEF5s/f214VfNrim2"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_A "hQo27wETk9fSABtW1iFXMLMt++I3IybfXSzPU29YUF7l67jmls5uZOxzleB++OkB"^^xsd:base64Binary .
	_:p2_uacc_sc uacc:R_B "iWLp6SxwyW8L16ovEBvMO1U3uFeS7hONIcIxCo0Duwp0NN8nHelgjXMNwkGT7vJv"^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_sigma "6ZydiHp1n/3tYG0nSPh+f+U1jxB6sbD3GiN9SVVLiFU="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_rho "+06dP3GuFXlKRbkIBWP3lFrAPEuDN+Yqwd8l0/iknVY="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_delta_sigma "FigWlsvWYFsuM7p0wKLjekBv1nt/vb2lfk9Oh+rYixQ="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_delta_rho "vHKHBkiVphhxkA9OTldiIJ6kpwVkEgVBhfSyKysIpEw="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_u "vV/dK1OzKv1w/vUCIee5qIkxXvM9NedT9DgszdlRnCE="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_v "rv8+KJRmlz2Oc9HVtxO0mTE9VMdO0fbITQia+lAs/As="^^xsd:base64Binary .
	_:p2_uacc_sr uacc:s_w "5R0AtIe0BJFX6FxmOCsRcQ7UC1IiY7bsFV7yURtEejw="^^xsd:base64Binary .
}
    "#;

        // Parse the example dataset
        let mut dataset: LightDataset = gtrig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");
        // Parse the example dataset
        let mut quads_list: QuadsList<SimpleTermIndex<u32>> = gtrig::parse_str(example)
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");

        let wit_graph_id = BnodeId::new_unchecked("4");

        let mut credential_quads_list = QuadsList::<SimpleTermIndex<u32>>::new();
        for quad in quads_list.quads() {
            let q = quad.unwrap();
            if wit_graph_id.into_term::<SimpleTerm<'_>>() == q.g().unwrap() {
                credential_quads_list.insert(q.s(), q.p(), q.o(), q.g());
            }
        }
        let mut rdf2fr_encoder = Rdf2FrInMemoryEncoderSchema::new();
        let (result_hidden_message_responses, result_revealed_messages, result_equal_indicies) =
            rdf2fr_encoder
                .quads_to_response_values(&dataset, &credential_quads_list)
                .unwrap();

        let mut expected_hidden_message_responses = BTreeMap::<usize, Fr>::new();
        let mut expected_revealed_messages = BTreeMap::<usize, Fr>::new();
        let mut expected_equal_indicies = BTreeMap::<String, Vec<usize>>::new();

        expected_hidden_message_responses.insert(
            0, // cred id _:0
            Fr::from(BigInt([
                100602317052723041,
                1210996732700986522,
                13245570063934246628,
                201415614778833968,
            ])),
        );
        expected_hidden_message_responses.insert(
            2, // credential subject object _:7
            Fr::from(BigInt([
                16756812446165331777,
                5946462246727092492,
                12350986094117453474,
                1112133588661210894,
            ])),
        );
        expected_hidden_message_responses.insert(
            4, // _:signatureGraph
            Fr::from(BigInt([
                3176942041729898844,
                3134103591002986472,
                10128415288193341076,
                2570114881808982922,
            ])),
        );
        expected_hidden_message_responses.insert(
            5, // expiration Date
            Fr::from(BigInt([
                10947904534268427708,
                12283224233779203751,
                6426858476326233154,
                5200832949953593940,
            ])),
        );
        expected_hidden_message_responses.insert(
            6, // object of org:headOf
            Fr::from(BigInt([
                2395306703744486789,
                14988831349931773580,
                13286517542790608743,
                7402601360903087635,
            ])),
        );



        expected_revealed_messages.insert(
            1, // accumulatorId
            Fr::from(BigInt([
                7312873495776744533,
                8114177336775667406,
                4613950413849816819,
                6586411640486648583,
            ])),
        );
        expected_revealed_messages.insert(
            3, // issuer aCompany
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        );
        expected_revealed_messages.insert(
            7, // memberOf aCompany
            Fr::from(BigInt([
                13027864682218542449,
                8423044885583638553,
                9981963879463053750,
                1629314853058170069,
            ])),
        );
        // bn id -> index in graph
        expected_equal_indicies.insert("0".to_string(), vec![0]);
        expected_equal_indicies.insert("7".to_string(), vec![2]);
        expected_equal_indicies.insert("17".to_string(), vec![4]);
        expected_equal_indicies.insert("22".to_string(), vec![5]);
        expected_equal_indicies.insert("27".to_string(), vec![6]);

        assert_eq!(
            result_hidden_message_responses,
            expected_hidden_message_responses
        );
        assert_eq!(result_revealed_messages, expected_revealed_messages);
        assert_eq!(result_equal_indicies, expected_equal_indicies);
    }
}

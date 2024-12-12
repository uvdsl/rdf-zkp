use demo_lib::rdf4zkp::quads_list::QuadsList;
use demo_lib::zkp4rdf::presentation::derive_presentation;
use sophia::api::prelude::{Dataset, QuadSerializer, QuadSource, Stringifier, TripleSerializer};
use sophia::inmem::dataset::LightDataset;
use sophia::turtle::parser::trig;
use sophia::turtle::serializer::nq::NqSerializer;
use sophia::turtle::serializer::nt::NtSerializer;

use demo_lib::rdf4zkp::encoder::{Rdf2FrEncoder, Rdf2FrInMemoryEncoder};
fn main() {
    // loading a dataset
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
              cred:credentialStatus  exOrg:revocation .
"#;
    let mut dataset = QuadsList::new();
    match trig::parse_str(example).collect_quads() {
        Ok(parsed_dataset) => {
            // Other processing logic here
            dataset = parsed_dataset;
            println!("Dataset successfully parsed!");
        }
        Err(e) => {
            println!("Error: {}", e);
            // Handle the error as needed
        }
    }

    let mut rdf2fr_encoder = Rdf2FrInMemoryEncoder::new();
    let frs = rdf2fr_encoder.quads_to_field_representations(&dataset);
    println!("{:?}", frs);

    let indices_to_hide = vec![
        0, 3, 4, 5, 7, 8, 9, 10, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29,
    ];
    let pg = derive_presentation(
        indices_to_hide,
        &|i| match i {
            0 | 5 | 10 | 15 => 0,
            7 | 25 => 7,
            4 | 9 | 14 | 19 | 24 | 29 => 4,
            _ => i,
        },
        &dataset,
    )
    .unwrap();
    // serializing the graph
    let mut nq_stringifier = NqSerializer::new_stringifier();
    let pg_str = nq_stringifier.serialize_dataset(&pg).unwrap().as_str();
    println!("The resulting graph:\n{}", pg_str);

    // serializing the graph
    let mut nt_stringifier = NtSerializer::new_stringifier();
    let pg_str = nt_stringifier
        .serialize_graph(&pg.union_graph())
        .unwrap()
        .as_str();
    println!("The resulting graph:\n{}", pg_str);
}

/*
<http://example.org/credentials#credId> https://www.w3.org/2018/credentials#credentialStatus> <http://example.org/organisations#revocation> .
<http://example.org/credentials#credId> <https://www.w3.org/2018/credentials#credentialSubject> <http://example.org/users#userId> .
<http://example.org/credentials#credId> <https://www.w3.org/2018/credentials#issuer> <http://example.org/organisations#aCompany> .
<http://example.org/credentials#credId> <https://www.w3.org/2018/credentials#validUntil> "2023-11-07T13:20:00Z"^^<http://www.w3.org/2001/XMLSchema#dateTimeStamp> .
<http://example.org/users#userId> <http://www.w3.org/ns/org#headOf> <http://example.org/organisations#aCompany> .
<http://example.org/users#userId> <http://www.w3.org/ns/org#memberOf> <http://example.org/organisations#aCompany> .
 */

// FR array len() = 30  (5 per quad)

/*
0 <https://www.w3.org/2018/credentials#credentialStatus> <http://example.org/organisations#revocation> 3 4
5 <https://www.w3.org/2018/credentials#credentialSubject> 7 8 9
10 <https://www.w3.org/2018/credentials#issuer> <http://example.org/organisations#aCompany> 13 14
15 <https://www.w3.org/2018/credentials#validUntil> 17 18 19
20 21 22 23 24
25 <http://www.w3.org/ns/org#memberOf> <http://example.org/organisations#aCompany> 28 29
 */

// hide
// 0 3 4 5  7 8 9 10 13 14 15 17 18 19 20 21 22 23 24 25 28 29

// reveal
// 1 2 6 11 12 16 26 27

// show equal
// 0 5 10
// 7 20 but not 25
// 4 | 9 | 14 | 19 | 24 | 29 => 4 graph name

// bounds
// 17

// non-member
// 0 (5 10 ? does this work?)

/* TODO ensure this ordering
_:0 <https://www.w3.org/2018/credentials#credentialStatus> <http://example.org/organisations#revocation> _:4.
_:0 <https://www.w3.org/2018/credentials#credentialSubject> _:7 _:4.
_:0 <https://www.w3.org/2018/credentials#issuer> <http://example.org/organisations#aCompany> _:4.
_:0 <https://www.w3.org/2018/credentials#validUntil> _:17 _:4.
_:20 _:21 _:22 _:4.
_:7 <http://www.w3.org/ns/org#memberOf> <http://example.org/organisations#aCompany> _:4.
 */
// ... proofs TODO!

// construct the proofs (and proof spec) from that
// verify.

// :tada:

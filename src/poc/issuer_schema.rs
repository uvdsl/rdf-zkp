use std::{collections::HashSet, fs::File, hash::Hash, io::BufWriter};

use ark_bls12_381::{Bls12_381, G1Affine};
use ark_ec::pairing::Pairing;
use ark_std::rand::{prelude::StdRng, RngCore, SeedableRng};

use bbs_plus::prelude::{KeypairG2, SignatureG1, SignatureParamsG1};

use proof_system::proof::Proof;
use vb_accumulator::{
    persistence::{InitialElementsStore, State, UniversalAccumulatorState},
    prelude::NonMembershipProvingKey,
    setup::{Keypair, SetupParams as SetupParamsAcc},
    universal::UniversalAccumulator,
};

use super::super::{
    rdf4zkp::{
        encoder::{Rdf2FrEncoder, Rdf2FrInMemoryEncoderSchema},
        quads_list::QuadsList,
    },
    zkp4rdf::{
        accumulator::{nm_uacc_to_rdf, nm_wit_to_rdf},
        signature::{signature_to_rdf, verification_key_to_rdf},
    },
};
use sophia::{
    api::{graph::Graph, triple::Triple},
    c14n::rdfc10::normalize,
    inmem::index::SimpleTermIndex,
    turtle::serializer::{nq::NqSerializer, nt::NtSerializer},
};
use sophia::{
    api::{prefix::Prefix, prelude::MutableDataset},
    iri::Iri,
    turtle::{
        parser::trig,
        serializer::trig::{TrigConfig, TrigSerializer},
    },
};
use sophia::{
    api::{prefix::PrefixMap, term::Term},
    inmem::dataset::LightDataset,
    turtle::serializer::turtle::TurtleConfig,
};
use sophia::{
    api::{
        prelude::{QuadSerializer, QuadSource, Stringifier, TripleSerializer},
        term::BnodeId,
    },
    inmem::graph::LightGraph,
    turtle::serializer::turtle::TurtleSerializer,
};

///
///
///
///
///

type Fr = <Bls12_381 as Pairing>::ScalarField;

pub fn bbs_plus_sig_setup_given_messages<R: RngCore>(
    rng: &mut R,
    messages: &[Fr],
) -> (
    SignatureParamsG1<Bls12_381>,
    KeypairG2<Bls12_381>,
    SignatureG1<Bls12_381>,
) {
    let params = SignatureParamsG1::<Bls12_381>::generate_using_rng(rng, messages.len());
    let keypair = KeypairG2::<Bls12_381>::generate_using_rng(rng, &params);
    let sig = SignatureG1::<Bls12_381>::new(rng, messages, &keypair.secret_key, &params).unwrap();
    sig.verify(messages, keypair.public_key.clone(), params.clone())
        .unwrap();
    (params, keypair, sig)
}

fn setup_universal_accum(
    rng: &mut StdRng,
    max: u64,
) -> (
    SetupParamsAcc<Bls12_381>,
    Keypair<Bls12_381>,
    UniversalAccumulator<Bls12_381>,
    InMemoryInitialElements<Fr>,
    InMemoryState<Fr>,
) {
    let params = SetupParamsAcc::<Bls12_381>::generate_using_rng(rng);
    let keypair = Keypair::<Bls12_381>::generate_using_rng(rng, &params);

    let mut initial_elements = InMemoryInitialElements::new();
    let accumulator = UniversalAccumulator::initialize_with_all_random(
        rng,
        &params,
        max,
        &keypair.secret_key,
        &mut initial_elements,
    );
    let state = InMemoryState::new();
    (params, keypair, accumulator, initial_elements, state)
}

fn save<D: MutableDataset>(dataset: &mut D) {
    let mut pm = TurtleConfig::default_prefix_map();
    pm.push((
        Prefix::new_unchecked("org".into()),
        Iri::new_unchecked("http://www.w3.org/ns/org#".into()),
    ));
    pm.push((
        Prefix::new_unchecked("cred".into()),
        Iri::new_unchecked("https://www.w3.org/2018/credentials#".into()),
    ));
    pm.push((
        Prefix::new_unchecked("zkp".into()),
        Iri::new_unchecked("https://ex.org/zkp/v0#".into()),
    ));
    pm.push((
        Prefix::new_unchecked("spok".into()),
        Iri::new_unchecked("https://ex.org/spok/v0#".into()),
    ));
    pm.push((
        Prefix::new_unchecked("bbsp16".into()),
        Iri::new_unchecked("https://ex.org/bbs+/v0#".into()),
    ));
    pm.push((
        Prefix::new_unchecked("lg16".into()),
        Iri::new_unchecked("https://ex.org/lg16/v0#".into()),
    ));
    pm.push((
        Prefix::new_unchecked("uacc".into()),
        Iri::new_unchecked("https://ex.org/uacc/v0#".into()),
    ));
    let config = TrigConfig::default()
        .with_pretty(true)
        .with_own_prefix_map(pm);
    let mut trig_stringifier = TrigSerializer::new_stringifier_with_config(config.clone());
    let pg_str = trig_stringifier
        .serialize_dataset(&dataset)
        .unwrap()
        .as_str();
    // println!("The resulting graph:\n{}", pg_str);

    // Open a file to write the serialized graph
    let file = File::create("./data/issuer_schema.trig").unwrap();
    let writer = BufWriter::new(file);
    let mut trig_stringifier = TrigSerializer::new_with_config(writer, config.clone());
    let x = trig_stringifier.serialize_dataset(&dataset).unwrap();
}

/// Issue an AVC.
pub fn issue() {
    let mut rng = StdRng::seed_from_u64(0u64);

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
    let msgs = rdf2fr_encoder
        .quads_to_field_representations(&canon_dataset)
        .unwrap();
    // println!("### All Messages ### \n{:#?} \n", msgs);

    // signature
    let (sig_params, sig_keypair, sig) = bbs_plus_sig_setup_given_messages(&mut rng, &msgs);

    // revocation via credential id == credential URI
    let max_members = 128;
    let (uni_accum_params, uni_accum_keypair, mut uni_accumulator, initial_elements, mut uni_state) =
        setup_universal_accum(&mut rng, max_members);
    // create witness to be transmitted to prover
    let accum_non_member_idx = 0;
    let accum_non_member = msgs[accum_non_member_idx];
    // println!(
    //     "### Message to be re-used in NonMember proof ### \n{:?} \n",
    //     accum_non_member
    // );
    let non_mem_wit = uni_accumulator // because accumulators are a bit special here, we need this level of indirection.
        .get_non_membership_witness(
            &accum_non_member,
            &uni_accum_keypair.secret_key,
            &uni_state,
            &uni_accum_params,
        )
        .unwrap();
    // ? TODO update info
    // Whenever addition or deletion operations occur for one or several elements (in the latter case these are called batch additions and deletions), already issued witnesses should be updated to be consistent with the new accumulator value. Ideally this should be done using a short amount of witness update data (i.e. whose cost/size is not dependent on the number of elements involved) and with only publicly available information (i.e. without knowledge of any secret accumulator parameters)
    // that is, the prover receives the wittness from the issuer on issuance
    // and then has to update that wittness using the update information (addition/deletion log of the issuer)
    // when creating a proof
    // this is the reason why we see usage of secret key here. this get_wit should be executed by issuer (as issuer assigns the credId anyway)

    // *** to RDF
    let cred_id = &Iri::new_unchecked("http://example.org/credentials#credId");

    let vk_id = &Iri::new_unchecked("http://example.org/keys#aCompanyKey"); // ! this could be a URI where the vk is provided.
    let mut g = LightGraph::new();
    verification_key_to_rdf(
        &sig_params,
        &sig_keypair.public_key,
        &vk_id.as_simple(),
        &mut g,
    );
    let vk_graph = &Iri::new_unchecked("http://example.org/keys");
    for triple in g.triples() {
        let [s, p, o] = triple.unwrap().to_spo();
        dataset.insert(s, p, o, Some(vk_graph.as_simple()));
    }
    let mut g = LightGraph::new();
    signature_to_rdf(&sig, &vk_id.as_simple(), &mut g);
    let sig_graph = &BnodeId::new_unchecked("signatureGraph");
    for triple in g.triples() {
        let [s, p, o] = triple.unwrap().to_spo();
        dataset.insert(s, p, o, Some(sig_graph.as_simple()));
    }

    let uacc_id = &Iri::new_unchecked("http://example.org/revocation#accumulatorId");
    let mut g = LightGraph::new();
    nm_uacc_to_rdf(
        &uacc_id.as_simple(),
        &uni_accumulator,
        &uni_accum_keypair.public_key,
        &uni_accum_params,
        &mut g,
    );
    let acc_graph = &Iri::new_unchecked("http://example.org/revocation");
    for triple in g.triples() {
        let [s, p, o] = triple.unwrap().to_spo();
        dataset.insert(s, p, o, Some(acc_graph.as_simple()));
    }

    let mut g = LightGraph::new();
    nm_wit_to_rdf(
        &uacc_id.as_simple(),
        &cred_id.as_simple(),
        &non_mem_wit,
        &mut g,
    );
    let wit_graph = &BnodeId::new_unchecked("witnessInfo");
    for triple in g.triples() {
        let [s, p, o] = triple.unwrap().to_spo();
        dataset.insert(s, p, o, Some(wit_graph.as_simple()));
    }

    save(&mut dataset)
}

#[derive(Clone, Debug)]
pub struct InMemoryInitialElements<T: Clone> {
    pub db: HashSet<T>,
}

impl<T: Clone> InMemoryInitialElements<T> {
    pub fn new() -> Self {
        let db = HashSet::<T>::new();
        Self { db }
    }
}

impl<T: Clone + Hash + Eq> InitialElementsStore<T> for InMemoryInitialElements<T> {
    fn add(&mut self, element: T) {
        self.db.insert(element);
    }

    fn has(&self, element: &T) -> bool {
        self.db.get(element).is_some()
    }
}

#[derive(Clone, Debug)]
pub struct InMemoryState<T: Clone> {
    pub db: HashSet<T>,
}

impl<T: Clone> InMemoryState<T> {
    pub fn new() -> Self {
        let db = HashSet::<T>::new();
        Self { db }
    }
}

impl<T: Clone + Hash + Eq + Sized> State<T> for InMemoryState<T> {
    fn add(&mut self, element: T) {
        self.db.insert(element);
    }

    fn remove(&mut self, element: &T) {
        self.db.remove(element);
    }

    fn has(&self, element: &T) -> bool {
        self.db.get(element).is_some()
    }

    fn size(&self) -> u64 {
        self.db.len() as u64
    }
}

impl<'a, T: Clone + Hash + Eq + Sized + 'a> UniversalAccumulatorState<'a, T> for InMemoryState<T> {
    type ElementIterator = std::collections::hash_set::Iter<'a, T>;

    fn elements(&'a self) -> Self::ElementIterator {
        self.db.iter()
    }
}

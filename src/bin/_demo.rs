use std::{collections::HashSet, hash::Hash, time::Instant};

use ark_bls12_381::{Bls12_381, G1Affine};
use ark_ec::pairing::Pairing;
use ark_serialize::CanonicalSerialize;
use ark_std::{
    collections::{BTreeMap, BTreeSet},
    rand::{prelude::StdRng, RngCore, SeedableRng},
};
use blake2::Blake2b512;

use proof_system::{
    prelude::{
        EqualWitnesses, MetaStatements, ProofSpec, Statement, StatementProof, Witness, WitnessRef,
        Witnesses,
    },
    proof::Proof,
    setup_params::SetupParams,
    statement::{
        accumulator::AccumulatorNonMembership as AccumulatorNonMembershipStmt,
        bbs_plus::PoKBBSSignatureG1 as PoKSignatureBBSG1Stmt,
        bound_check_legogroth16::{
            BoundCheckLegoGroth16Prover as BoundCheckProverStmt,
            BoundCheckLegoGroth16Verifier as BoundCheckVerifierStmt,
        },
        Statements,
    },
    sub_protocols::bound_check_legogroth16::generate_snark_srs_bound_check,
    witness::{NonMembership as NonMembershipWit, PoKBBSSignatureG1 as PoKSignatureBBSG1Wit},
};

use bbs_plus::prelude::{KeypairG2, SignatureG1, SignatureParamsG1};

use vb_accumulator::{
    persistence::{InitialElementsStore, State, UniversalAccumulatorState},
    prelude::{Accumulator, NonMembershipProvingKey},
    setup::{Keypair, SetupParams as SetupParamsAcc},
    universal::UniversalAccumulator,
};

use chrono::offset::FixedOffset;
use chrono::DateTime;
use demo_lib::{
    rdf4zkp::{encoder::{Rdf2FrEncoder, Rdf2FrInMemoryEncoder}, quads_list::QuadsList},
    zkp4rdf::{presentation::derive_presentation, proof::stmt_proofs_to_rdf},
};

use sophia::{c14n::rdfc10::normalize, inmem::index::SimpleTermIndex, turtle::serializer::{nq::NqSerializer, nt::NtSerializer}};
use sophia::{
    api::prelude::{QuadSerializer, QuadSource, Stringifier, TripleSerializer},
    inmem::graph::LightGraph,
};
use sophia::{
    api::{
        graph::Graph,
        prelude::MutableDataset,
        term::{BnodeId, SimpleTerm, Term},
    },
    turtle::{
        parser::trig,
        serializer::{
            trig::{TrigConfig, TrigSerializer},
            turtle::TurtleConfig,
        },
    },
};
use sophia::{inmem::dataset::LightDataset, turtle::serializer::turtle::TurtleSerializer};

///
///
///
///
///

type Fr = <Bls12_381 as Pairing>::ScalarField;
// type G1 = <Bls12_381 as Pairing>::G1Affine;
type ProofG1 = Proof<Bls12_381, G1Affine>;

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

fn select_by_indices<T: Clone>(
    original: Vec<T>,
    indices_to_select: Vec<usize>,
) -> BTreeMap<usize, T> {
    let indices_set: HashSet<_> = indices_to_select.into_iter().collect();
    original
        .into_iter()
        .enumerate()
        .filter_map(|(index, value)| {
            if indices_set.contains(&index) {
                Some((index, value.clone()))
            } else {
                None
            }
        })
        .collect::<BTreeMap<usize, _>>()
}

// Prove knowledge of BBS+ signature and certain messages satisfy some bounds.
// fn check(reuse_key: bool) { // re-use key is an optimization
fn main() {
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


    let mut rng = StdRng::seed_from_u64(0u64);

    // ISSUER
    let mut rdf2fr_encoder = Rdf2FrInMemoryEncoder::new();
    let msgs = rdf2fr_encoder.quads_to_field_representations(&canon_dataset).unwrap();
    println!("### All Messages ### \n{:#?} \n", msgs);
    let (sig_params, sig_keypair, sig) = bbs_plus_sig_setup_given_messages(&mut rng, &msgs);
    println!(
        "### Signature ### \n{}\n",
        serde_json::to_string(&sig).unwrap()
    );
    println!(
        "### Signature Parameters ### \n{}\n",
        serde_json::to_string(&sig_params).unwrap()
    );
    println!(
        "### Signature Key Public ### \n{}\n",
        serde_json::to_string(&sig_keypair.public_key).unwrap()
    );

    let max_members = 128;
    let (uni_accum_params, uni_accum_keypair, mut uni_accumulator, initial_elements, mut uni_state) =
        setup_universal_accum(&mut rng, max_members);
    // create witness to be transmitted to prover
    let accum_non_member_idx = 0;
    let accum_non_member = msgs[accum_non_member_idx];
    println!(
        "### Message to be re-used in NonMember proof ### \n{} \n",
        accum_non_member
    );
    let non_mem_wit = uni_accumulator // because accumulators are a bit special here, we need this level of indirection.
        .get_non_membership_witness(
            &accum_non_member,
            &uni_accum_keypair.secret_key,
            &uni_state,
            &uni_accum_params,
        )
        .unwrap();
    println!(
        "### Accum Witness ### \n{}\n",
        serde_json::to_string(&non_mem_wit).unwrap()
    );
    println!(
        "### Accum ### \n{}\n",
        serde_json::to_string(&uni_accumulator).unwrap()
    );
    println!("### Accum State ### \n{:#?}\n", &uni_state);
    // . TODO update info
    // Whenever addition or deletion operations occur for one or several elements (in the latter case these are called batch additions and deletions), already issued witnesses should be updated to be consistent with the new accumulator value. Ideally this should be done using a short amount of witness update data (i.e. whose cost/size is not dependent on the number of elements involved) and with only publicly available information (i.e. without knowledge of any secret accumulator parameters)
    // that is, the prover receives the wittness from the issuer on issuance
    // and then has to update that wittness using the update information (addition/deletion log of the issuer)
    // when creating a proof
    // this is the reason why we see usage of secret key here. this get_wit should be executed by issuer (as issuer assigns the credId anyway)

    // VERIFIER
    // Verifier sets up LegoGroth16 public parameters. Ideally this should be done only once per
    // verifier and can be published by the verifier for any proofs submitted to him
    let snark_pk = generate_snark_srs_bound_check::<Bls12_381, _>(&mut rng).unwrap();
    // very long
    // println!(
    //     "### Publish LegoGroth16 public parameters (snark_pk) ### \n {:#?} \n",
    //     snark_pk
    // );
    // println!("### Snark PK size ### \n{} uncompressed, {} compressed. \n",snark_pk.uncompressed_size(),snark_pk.compressed_size());
    // // let file = std::fs::File::create("test.bin").unwrap();
    // // println!(
    // // "### Publish LegoGroth16 public parameters (snark_pk) ### \n {:#?} \n",
    // // snark_pk.serialize_compressed(std::io::BufWriter::new(file))
    // // );

    // PROVER

    // PROVER - SETUP
    let reuse_key = true;
    let datetime_bound: DateTime<FixedOffset> = "2013-11-07T13:20:00Z".parse().unwrap(); // * from verifier
    let min_1 = datetime_bound.timestamp() as u64; // TODO properly figure out how to convert this i64 // * from verifier
    let max_1 = std::u64::MAX; // * from verifier
    println!("### Bounds ### \n[{},{}] \n", min_1, max_1);
    // Following messages' bounds will be checked
    let msg_idx_bounds = 17;
    let msg_bounds = msgs[msg_idx_bounds];
    println!(
        "### Message to be re-used in bound proof ### \n{:#?} \n",
        msg_bounds
    );
    let mut prover_setup_params = vec![];
    if reuse_key {
        prover_setup_params.push(SetupParams::LegoSnarkProvingKey(snark_pk.clone()));
        // * from verifier
    }
    let msg_idx_accum_non_member = 0; // overwrites the variable from issuer section // * from issuer / by convention
    let msg_accum_non_member = msgs[msg_idx_accum_non_member];
    println!(
        "### Message to be re-used in NonMember proof ### \n{} \n",
        msg_accum_non_member
    );
    let non_mem_prk: NonMembershipProvingKey<
        ark_ec::short_weierstrass::Affine<ark_bls12_381::g1::Config>,
    > = NonMembershipProvingKey::generate_using_rng(&mut rng);

    // PROVER - WITNESSES
    let indices_to_hide = vec![
        0, 3, 4, 5, 7, 8, 9, 10, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29,
    ]; // * from verifier (derived)
    let msgs_to_hide = select_by_indices(msgs.clone(), indices_to_hide.clone());
    let indices_to_reveal = vec![1, 2, 6, 11, 12, 16, 26, 27]; // * from verifier (derived)
    let msgs_to_reveal = select_by_indices(msgs.clone(), indices_to_reveal.clone());

    let mut witnesses = Witnesses::new();
    witnesses.add(PoKSignatureBBSG1Wit::new_as_witness(sig, msgs_to_hide));
    witnesses.add(Witness::BoundCheckLegoGroth16(msg_bounds));

    // Whenever addition or deletion operations occur for one or several elements (in the latter case these are called batch additions and deletions), already issued witnesses should be updated to be consistent with the new accumulator value. Ideally this should be done using a short amount of witness update data (i.e. whose cost/size is not dependent on the number of elements involved) and with only publicly available information (i.e. without knowledge of any secret accumulator parameters)
    witnesses.add(Witness::AccumulatorNonMembership(NonMembershipWit {
        element: msg_accum_non_member,
        witness: non_mem_wit.clone(),
    }));
    println!(
        "### Witnesses BbsPlus, LegoGroth16 and Accumulator ### \n{:#?} \n",
        witnesses
    );

    // PROVER - STATEMENTS
    let mut prover_statements = Statements::new();
    prover_statements.add(PoKSignatureBBSG1Stmt::new_statement_from_params(
        sig_params.clone(),
        sig_keypair.public_key.clone(),
        msgs_to_reveal.clone(),
    ));
    if reuse_key {
        prover_statements
            .add(BoundCheckProverStmt::new_statement_from_params_ref(min_1, max_1, 0).unwrap());
    } else {
        prover_statements.add(
            BoundCheckProverStmt::new_statement_from_params(min_1, max_1, snark_pk.clone())
                .unwrap(),
        );
    }
    prover_statements.add(AccumulatorNonMembershipStmt::new_statement_from_params(
        uni_accum_params.clone(),
        uni_accum_keypair.public_key.clone(),
        non_mem_prk.clone(),
        *uni_accumulator.value(),
    ));
    // println!("### Prover Statements ### \n{:#?} \n", prover_statements);
    let mut meta_statements = MetaStatements::new();
    meta_statements.add_witness_equality(EqualWitnesses(
        vec![(0, msg_idx_bounds), (1, 0)]
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));
    meta_statements.add_witness_equality(EqualWitnesses(
        vec![(0, msg_idx_accum_non_member), (2, 0)]
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));
    // show that messages in bbs+ are equal
    meta_statements.add_witness_equality(EqualWitnesses(
        vec![(0, msg_idx_accum_non_member), (0, 5), (0, 10), (0, 15)]
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));
    meta_statements.add_witness_equality(EqualWitnesses(
        vec![(0, 7), (0, 25)] // do not need to include (0, 25) as this would give too much away
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));
    meta_statements.add_witness_equality(EqualWitnesses(
        vec![(0, 4), (0, 9), (0, 14), (0, 19), (0, 24), (0, 29)]
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));

    // println!("### Meta Statements ### \n{:#?} \n", meta_statements);
    let prover_proof_spec = ProofSpec::new(
        prover_statements.clone(), // either give the proving key directly here, or you reference its index
        meta_statements.clone(),
        prover_setup_params, // and give the proving key is in this vec
        None,                // ! domain/recipient here
    );
    prover_proof_spec.validate().unwrap();
    // very long - computational load on prover
    println!(
        "### Prover Proof Spec ### \n {:#?} \n",
        prover_proof_spec.meta_statements
    );

    // PROVER - CREATE PROOF
    // let start = Instant::now();
    let (proof, _comm_rand) = ProofG1::new::<StdRng, Blake2b512>(
        &mut rng,
        prover_proof_spec.clone(),
        witnesses.clone(),
        None,
        Default::default(),
    )
    .unwrap();
    println!(
        "### Proof size ### \n{} uncompressed, {} compressed. \n",
        proof.uncompressed_size(),
        proof.compressed_size()
    );
    // println!("### Proof ### \n{:#?} \n", proof.statement_proofs);

    // println!(
    //     "Time taken to create proof of bound check of 3 messages in signature over {} messages: {:#?}",
    //     msg_count,
    //     start.elapsed()
    // );

    // test_serialization!(ProofG1, proof);

    // VERIFIER

    // VERIFIER - setup
    let mut verifier_setup_params = vec![];
    if reuse_key {
        verifier_setup_params.push(SetupParams::LegoSnarkVerifyingKey(snark_pk.vk.clone()));
        // test_serialization!(Vec<SetupParams<Bls12_381, G1Affine>>, verifier_setup_params);
    }

    let mut verifier_statements = Statements::new();
    verifier_statements.add(PoKSignatureBBSG1Stmt::new_statement_from_params(
        sig_params,
        sig_keypair.public_key.clone(),
        msgs_to_reveal.clone(), // TODO calculated yourself, dear verifier.
    ));
    if reuse_key {
        verifier_statements
            .add(BoundCheckVerifierStmt::new_statement_from_params_ref(min_1, max_1, 0).unwrap());
    } else {
        verifier_statements.add(
            BoundCheckVerifierStmt::new_statement_from_params(min_1, max_1, snark_pk.vk.clone())
                .unwrap(),
        );
    }
    verifier_statements.add(AccumulatorNonMembershipStmt::new_statement_from_params(
        uni_accum_params.clone(),
        uni_accum_keypair.public_key.clone(),
        non_mem_prk.clone(),
        *uni_accumulator.value(),
    ));
    // println!(
    //     "### Verifier Statements ### \n{:#?} \n",
    //     verifier_statements
    // );
    let verifier_proof_spec = ProofSpec::new(
        verifier_statements.clone(), // either give the verification key directly here, or you reference its index
        meta_statements.clone(),     // TODO re-using from above, should be re-constructed
        verifier_setup_params,       // and give the verification key is in this vec
        None,                        // ! domain/recipient here
    );
    verifier_proof_spec.validate().unwrap();

    // println!(
    //     "### Verifier Proof Spec ### \n{:#?} \n",
    //     verifier_proof_spec
    // );

    let start = Instant::now();
    let result = proof
        .clone()
        .verify::<StdRng, Blake2b512>(
            &mut rng,
            verifier_proof_spec.clone(),
            None,
            Default::default(),
        )
        .unwrap();
    println!(
        "Time taken to verify proof of 30 msg POKS, with 1 RANGE and 1 NON-MEMBER: {:#?}",
        start.elapsed()
    );

    println!("Verification: {:#?}", result);

    // Serialize the Proof into a JSON string
    // let json_string = serde_json::to_string(&proof).unwrap();
    // println!("{}", json_string);

    // presentation
    // ! PROVIDE PRESENTATION
    let stmts_and_proofs: Vec<(
        &Statement<Bls12_381, G1Affine>,
        &StatementProof<Bls12_381, G1Affine>,
    )> = prover_statements
        .0
        .iter()
        .zip(proof.statement_proofs.iter())
        .collect();

    // PoKS

    // presentation
    // (proof spec (to be derived from highlevel abstraction like shape) + input graph => avp?)
    let eqiv = |i| match i {
        // (could also be used to derive meta statements?)
        0 | 5 | 10 | 15 | 20 => 0,
        7 | 30 => 7,
        4 | 9 | 14 | 19 | 24 | 29 | 34 => 4,
        _ => i,
    };
    let mut pg = derive_presentation(indices_to_hide.clone(), &eqiv, &canon_dataset).unwrap();
    // serializing the graph

    let mut graph = LightGraph::new();
    stmt_proofs_to_rdf(stmts_and_proofs, indices_to_hide.clone(), 
    &eqiv, 
    &BnodeId::new_unchecked("4").into_term::<SimpleTerm<'_>>(), 
    &BnodeId::new_unchecked("22").into_term::<SimpleTerm<'_>>(), 
    &BnodeId::new_unchecked("0").into_term::<SimpleTerm<'_>>(), 
    &mut graph);
    let proof_graph_name =
        &BnodeId::new_unchecked("presentationProofGraph").into_term::<SimpleTerm<'_>>();
    graph.triples().for_each(|tr| {
        let t = tr.unwrap();
        let _ = pg.insert(t[0], t[1], t[2], Some(proof_graph_name));
    });

    let config = TrigConfig::default().with_pretty(true);
    let mut trig_stringifier = TrigSerializer::new_stringifier_with_config(config);
    let pg_str = trig_stringifier.serialize_dataset(&pg).unwrap().as_str();
    println!("The resulting graph:\n{}", pg_str);
}

// impl PoKBBSSignatureG1 {
// impl PoKBBSSignatureG1Proof {

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

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fs::File,
    io::BufReader,
    iter::empty,
    time::Instant,
};

use blake2::Blake2b512;
use legogroth16::VerifyingKey;
use sophia::{
    api::{
        prelude::{Dataset, MutableDataset},
        source::QuadSource,
        term::{SimpleTerm, Term},
    },
    inmem::{dataset::LightDataset, index::SimpleTermIndex},
    iri::Iri,
    turtle::parser::gtrig,
};

use ark_bls12_381::{Bls12_381, G1Affine};
use ark_ec::pairing::Pairing;
use ark_std::{
    iterable::Iterable,
    rand::{rngs::StdRng, SeedableRng},
};
use bbs_plus::setup::{PublicKeyG2 as SignaturePublicKeyG2, SignatureParamsG1};
use super::super::{
    rdf4zkp::{encoder::Rdf2FrInMemoryEncoderSchema, quads_list::QuadsList},
    zkp4rdf::{
        accumulator::nm_uacc_from_rdf,
        proof::{lg16_proof_from_rdf, nm_proof_from_rdf, poks_from_rdf},
        signature::verification_key_from_rdf,
    },
};
use proof_system::{
    prelude::{
        generate_snark_srs_bound_check, r1cs_legogroth16::ProvingKey, EqualWitnesses,
        MetaStatements, ProofSpec, SetupParams as ProofSystemSetupParams, StatementProof,
        WitnessRef,
    },
    proof::Proof,
    statement::{
        accumulator::AccumulatorNonMembership as AccumulatorNonMembershipStmt,
        bbs_plus::PoKBBSSignatureG1 as PoKSignatureBBSG1Stmt,
        bound_check_legogroth16::BoundCheckLegoGroth16Verifier as BoundCheckVerifierStmt,
        Statements,
    },
};
use vb_accumulator::{
    proofs::NonMembershipProvingKey,
    setup::{PublicKey as AccumPublicKey, SetupParams as AccumSetupParams},
};

type Fr = <Bls12_381 as Pairing>::ScalarField;

fn load_from_verifier() -> VerifyingKey<Bls12_381> {
    let mut rng = StdRng::seed_from_u64(1u64);
    let key = generate_snark_srs_bound_check::<Bls12_381, _>(&mut rng).unwrap();
    key.vk
}

fn load_from_prover() -> NonMembershipProvingKey<G1Affine> {
    let mut rng = StdRng::seed_from_u64(2u64);
    NonMembershipProvingKey::generate_using_rng(&mut rng)
}

pub fn verify() {
    let file = BufReader::new(File::open("./data/prover_schema.trig").unwrap());

    let mut quad_source = gtrig::parse_bufread(file);

    let received_quads: QuadsList<SimpleTermIndex<u32>> = quad_source.collect_quads().unwrap();

    let mut presentation_dataset = LightDataset::new();
    presentation_dataset.insert_all(received_quads.quads());

    // ! Proofs
    let mut encoder = Rdf2FrInMemoryEncoderSchema::new();
    let (
        poks,
        poks_vk_id,
        wit_graph_name,
        hidden_message_responses,
        revealed_messages,
        equivalent_indicies, // where the String is the BnodeId
        credential_dataset,
    ) = &poks_from_rdf(&presentation_dataset, &received_quads, &mut encoder)[0];

    let (lg16_proof, lg16_vk_id, lg16_wit_id, (min, max)) =
        &lg16_proof_from_rdf(&presentation_dataset)[0];

    let (uacc_proof, nm_prk_id, uacc_id, uacc_wit_id) =
        &nm_proof_from_rdf(&presentation_dataset)[0];

    // ! get public parameters like verification keys, parameters and accumulator value

    let f = BufReader::new(File::open("./data/issuer_schema.trig").unwrap());
    let public_info_dataset: LightDataset = gtrig::parse_bufread(f).collect_quads().unwrap();

    let (sig_pk, sig_params): (
        SignaturePublicKeyG2<Bls12_381>,
        SignatureParamsG1<Bls12_381>,
    ) = verification_key_from_rdf(&public_info_dataset, poks_vk_id).clone();

    // to do at some point: properly load from RDF
    let lg16_vk = load_from_verifier();
    //     lg16_verification_key_from_rdf(&public_info_dataset.graph(lg16_vk_id))[0].clone();

    let (uacc_value, uacc_pk, uacc_params): (
        <Bls12_381 as Pairing>::G1Affine,
        AccumPublicKey<Bls12_381>,
        AccumSetupParams<Bls12_381>,
    ) = nm_uacc_from_rdf(&public_info_dataset, &uacc_id).clone();

    // to do at some point: properly load from RDF
    let non_mem_prk = load_from_prover();
    //     uacc_proving_key_from_rdf(&public_info_dataset.graph(nm_prk_id))[0].clone();

    // ! verifier proof statements
    let mut verifier_statements = Statements::<Bls12_381, G1Affine>::new();
    verifier_statements.add(PoKSignatureBBSG1Stmt::new_statement_from_params(
        sig_params,
        sig_pk,
        revealed_messages.clone(),
    ));

    verifier_statements
        .add(BoundCheckVerifierStmt::new_statement_from_params(*min, *max, lg16_vk).unwrap());

    verifier_statements.add(AccumulatorNonMembershipStmt::new_statement_from_params(
        uacc_params,
        uacc_pk,
        non_mem_prk,
        uacc_value,
    ));

    // ! verifier meta statements

    // for the meta statements (from BBS+ so far)
    let mut meta_equiv = equivalent_indicies
        .into_iter()
        .map(|(key, vec)| {
            let new_vec = vec.into_iter().map(|idx| (0, *idx)).collect();
            (key, new_vec)
        })
        .collect::<BTreeMap<&String, Vec<(usize, usize)>>>();

    // now just add the statement proofs witnesses here ...
    let wit_lg16_id = lg16_wit_id.bnode_id().unwrap().to_string();
    let meta_stmt_bounds = (1, 0);
    meta_equiv
        .entry(&wit_lg16_id)
        .or_insert_with(Vec::new)
        .push(meta_stmt_bounds);

    let wit_uacc_id = uacc_wit_id.bnode_id().unwrap().to_string();
    let meta_stmt_uacc = (2, 0);
    meta_equiv
        .entry(&wit_uacc_id)
        .or_insert_with(Vec::new)
        .push(meta_stmt_uacc);

    let mut meta_statements = MetaStatements::new();
    meta_equiv
        .values()
        .filter(|v| v.len() > 1)
        .map(|v| v.iter().cloned().collect::<BTreeSet<WitnessRef>>())
        .map(|v| EqualWitnesses(v))
        .for_each(|v| {
            meta_statements.add_witness_equality(v);
        });

    // println!("{:#?}", meta_statements);

    // ! Proof Spec

    let mut verifier_setup_params = vec![]; // we do not use that here
    let verifier_proof_spec = ProofSpec::new(
        verifier_statements.clone(),
        meta_statements.clone(),
        verifier_setup_params,
        None, // * domain/recipient here
    );
    verifier_proof_spec.validate().unwrap();

    // ! the proof itself ...

    let statement_proofs = vec![
        StatementProof::<Bls12_381, G1Affine>::PoKBBSSignatureG1(poks.clone()),
        StatementProof::<Bls12_381, G1Affine>::BoundCheckLegoGroth16(lg16_proof.clone()),
        StatementProof::<Bls12_381, G1Affine>::AccumulatorNonMembership(uacc_proof.clone()),
    ];
    let proof = Proof::<Bls12_381, G1Affine> {
        statement_proofs,
        nonce: None,
        aggregated_groth16: None,
        aggregated_legogroth16: None,
    };

    // TODO construct all of the above from composite proof RDF and just give (proof spec and proof).
    // # make API nice.

    // ! verify
    let mut rng = StdRng::seed_from_u64(1111u64);
    let start = Instant::now();
    let result = proof.verify::<StdRng, Blake2b512>(
        &mut rng,
        verifier_proof_spec.clone(),
        None,
        Default::default(),
    );
    println!(
        "Time taken to verify proof of 8 msg POKS, with 1 RANGE and 1 NON-MEMBER: {:#?}, {:?}",
        start.elapsed(),
        result
    );

}

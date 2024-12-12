use ark_std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    rand::{prelude::StdRng, SeedableRng},
    time::Instant,
};
use bbs_plus::{
    prelude::SignatureG1,
    setup::{PublicKeyG2 as SignaturePublicKeyG2, SignatureParamsG1},
};
use blake2::Blake2b512;
use chrono::{DateTime, FixedOffset};
use super::super::{
    rdf4zkp::{
        encoder::{Rdf2FrEncoder, Rdf2FrInMemoryEncoder},
        quads_list::QuadsList,
    },
    zkp4rdf::{
        accumulator::{nm_uacc_from_rdf, nm_wit_from_rdf},
        presentation::derive_presentation,
        proof::stmt_proofs_to_rdf,
        signature::{signature_from_rdf, verification_key_from_rdf},
    },
};
use proof_system::{
    prelude::{
        generate_snark_srs_bound_check, r1cs_legogroth16::ProvingKey, EqualWitnesses,
        MetaStatements, ProofSpec, SetupParams as ProofSystemSetupParams, Statement,
        StatementProof, WitnessRef,
    },
    proof::Proof,
    statement::{
        accumulator::AccumulatorNonMembership as AccumulatorNonMembershipStmt,
        bbs_plus::PoKBBSSignatureG1 as PoKSignatureBBSG1Stmt,
        bound_check_legogroth16::BoundCheckLegoGroth16Prover as BoundCheckProverStmt, Statements,
    },
    witness::{
        NonMembership as NonMembershipWit, PoKBBSSignatureG1 as PoKSignatureBBSG1Wit, Witness,
        Witnesses,
    },
};
use sophia::{
    api::{
        graph::Graph,
        prefix::Prefix,
        prelude::{Dataset, MutableDataset, QuadSerializer, Stringifier},
        source::QuadSource,
        term::{BnodeId, SimpleTerm, Term},
    }, c14n::rdfc10::normalize, inmem::{dataset::LightDataset, graph::LightGraph, index::SimpleTermIndex}, iri::Iri, turtle::{
        parser::trig,
        serializer::{
            nq::{NqConfig, NqSerializer},
            trig::{TrigConfig, TrigSerializer},
        },
    }
};
use std::{
    fs::File,
    io::{BufReader, BufWriter, Write},
};

use ark_bls12_381::{g1::Config, Bls12_381, G1Affine};
use ark_ec::{pairing::Pairing, short_weierstrass::Affine};
use vb_accumulator::{
    proofs::NonMembershipProvingKey,
    setup::{PublicKey as AccumPublicKey, SetupParams as AccumSetupParams},
    witness::NonMembershipWitness,
};

fn load_from_issuer() -> (
    LightDataset,
    Vec<<Bls12_381 as Pairing>::ScalarField>,
    SignatureG1<Bls12_381>,
    SignaturePublicKeyG2<Bls12_381>,
    SignatureParamsG1<Bls12_381>,
    NonMembershipWitness<Affine<Config>>,
    G1Affine,
    AccumPublicKey<Bls12_381>,
    AccumSetupParams<Bls12_381>,
) {
    let f = BufReader::new(File::open("./data/issuer.trig").unwrap());
    let received_dataset: LightDataset = trig::parse_bufread(f).collect_quads().unwrap();

    // Credential

    let default_graph = received_dataset.graph(None::<SimpleTerm>);
    let cred_dataset: LightDataset = default_graph.as_dataset().quads().collect_quads().unwrap();
    let mut output = Vec::<u8>::new();
    normalize(&cred_dataset, &mut output).unwrap();
    let normalised_nquads = String::from_utf8(output).unwrap();
    let mut canon_cred_dataset: QuadsList<SimpleTermIndex<u32>> =
        trig::parse_str(normalised_nquads.as_str())
            .collect_quads()
            .map_err(|e| println!("Error: {}", e))
            .expect("The example string should be valid RDF");
    let mut rdf2fr_encoder = Rdf2FrInMemoryEncoder::new();
    let msgs = rdf2fr_encoder.quads_to_field_representations(&canon_cred_dataset).unwrap();

    // to do at some point: get the data below via credential graph traversal.
    let sig_graph_name =
        Some(BnodeId::new_unchecked("signatureGraph").into_term::<SimpleTerm<'_>>());

    // Signature
    let sig_graph = received_dataset.graph(sig_graph_name);
    let (signature, poks_vk_id): (SignatureG1<Bls12_381>, SimpleTerm) =
        signature_from_rdf(&sig_graph)[0].clone();

    let (sig_pk, sig_params): (
        SignaturePublicKeyG2<Bls12_381>,
        SignatureParamsG1<Bls12_381>,
    ) = verification_key_from_rdf(&received_dataset, &poks_vk_id).clone();

    signature
        .verify(&msgs, sig_pk.clone(), sig_params.clone())
        .unwrap();

    // Accumulator

    let wit_graph_name = Some(BnodeId::new_unchecked("witnessInfo").into_term::<SimpleTerm<'_>>());
    let uacc_witness: NonMembershipWitness<Affine<Config>> =
        nm_wit_from_rdf(&received_dataset.graph(wit_graph_name))[0].clone();

    let uacc_id = Iri::new_unchecked("http://example.org/revocation#accumulatorId")
        .into_term::<SimpleTerm<'_>>();
    let (uacc_value, uacc_pk, uacc_params): (
        G1Affine,
        AccumPublicKey<Bls12_381>,
        AccumSetupParams<Bls12_381>,
    ) = nm_uacc_from_rdf(&received_dataset, &uacc_id).clone();

    (
        cred_dataset,
        msgs,
        signature,
        sig_pk,
        sig_params,
        uacc_witness,
        uacc_value,
        uacc_pk,
        uacc_params,
    )
}

fn load_from_verifier() -> ProvingKey<Bls12_381> {
    let mut rng = StdRng::seed_from_u64(1u64);
    generate_snark_srs_bound_check::<Bls12_381, _>(&mut rng).unwrap()
    // todo create RDF serialisation.
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

pub fn prove() {
    // ! LOAD

    let (
        cred_dataset,
        msgs,
        sig,
        sig_pk,
        sig_params,
        uacc_witness,
        uacc_value,
        uacc_pk,
        uacc_params,
    ) = load_from_issuer();

    let snark_pk = load_from_verifier();

    // set up by prover itself ...
    let mut rng = StdRng::seed_from_u64(2u64);
    let non_mem_prk: NonMembershipProvingKey<Affine<Config>> =
        NonMembershipProvingKey::generate_using_rng(&mut rng);
    // todo create RDF serialisation.

    // ! PROVER - Prelude

    // PROOF OF KNOWLEDGE OF SIGNATURE

    // to do at some point: generate
    let indices_to_hide = vec![
        0, 4, 5, 7, 8, 9, 10, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 34,
    ]; // * from verifier (derived) // remember: reveal object suffixes of revealed object values
    let indices_to_reveal = vec![1, 2, 3, 6, 11, 12, 13, 21, 31, 32, 33]; // * from verifier (derived)
    let msgs_to_hide = select_by_indices(msgs.clone(), indices_to_hide.clone());
    let msgs_to_reveal = select_by_indices(msgs.clone(), indices_to_reveal.clone());

    // RANGE PROOF
    let datetime_bound: DateTime<FixedOffset> = "2013-11-07T13:20:00Z".parse().unwrap(); // * from verifier
    let min_1 = datetime_bound.timestamp() as u64; // * from verifier // TODO properly figure out how to convert this i64
    let max_1 = std::u64::MAX; // * from verifier
    // println!("### Bounds ### \n[{},{}] \n", min_1, max_1);
    let idx_of_msg_for_bounds = 22;
    let msg_for_bounds = msgs[idx_of_msg_for_bounds];
    // println!(
    //     "### Message to be (re-)used in bound proof ### \n{:#?} \n",
    //     msg_for_bounds
    // );

    // NON-MEMBERSHIP PROOF
    let idx_of_msg_for_non_member = 0; // overwrites the variable from issuer section // * from issuer / by convention
    let msg_for_non_member = msgs[idx_of_msg_for_non_member];
    // println!(
    //     "### Message to be (re-)used in NonMember proof ### \n{} \n",
    //     msg_for_non_member
    // );

    // ! REFERENCES FOR SETUP PARAMETERS
    // to do at some point: dynamically keep track of which vk/param URI belongs to which parameter idx

    let mut prover_setup_params: Vec<ProofSystemSetupParams<Bls12_381, Affine<Config>>> = vec![];
    // poks
    let prover_setup_params_idx_of_sig_params = 0;
    prover_setup_params.insert(
        prover_setup_params_idx_of_sig_params,
        ProofSystemSetupParams::<Bls12_381, Affine<Config>>::BBSPlusSignatureParams(
            sig_params.clone(),
        ),
    );
    // bounds
    let prover_setup_params_idx_of_sig_pk = 1;
    prover_setup_params.insert(
        prover_setup_params_idx_of_sig_pk,
        ProofSystemSetupParams::<Bls12_381, Affine<Config>>::BBSPlusPublicKey(sig_pk.clone()),
    );
    let prover_setup_params_idx_of_snark_pk = 2;
    prover_setup_params.insert(
        prover_setup_params_idx_of_snark_pk,
        ProofSystemSetupParams::<Bls12_381, Affine<Config>>::LegoSnarkProvingKey(snark_pk.clone()),
    );
    // accum
    let prover_setup_params_idx_of_uacc_params = 3;
    prover_setup_params.insert(
        prover_setup_params_idx_of_uacc_params,
        ProofSystemSetupParams::<Bls12_381, Affine<Config>>::VbAccumulatorParams(
            uacc_params.clone(),
        ),
    );
    let prover_setup_params_idx_of_uacc_pk = 4;
    prover_setup_params.insert(
        prover_setup_params_idx_of_uacc_pk,
        ProofSystemSetupParams::<Bls12_381, Affine<Config>>::VbAccumulatorPublicKey(
            uacc_pk.clone(),
        ),
    );
    let prover_setup_params_idx_of_non_mem_prk = 5;
    prover_setup_params.insert(
        prover_setup_params_idx_of_non_mem_prk,
        ProofSystemSetupParams::<Bls12_381, Affine<Config>>::VbAccumulatorNonMemProvingKey(
            non_mem_prk.clone(),
        ),
    );

    // ! PROVER - WITNESSES

    let mut witnesses = Witnesses::new();
    witnesses.add(PoKSignatureBBSG1Wit::new_as_witness(sig, msgs_to_hide));
    witnesses.add(Witness::BoundCheckLegoGroth16(msg_for_bounds));

    // Whenever addition or deletion operations occur for one or several elements (in the latter case these are called batch additions and deletions), already issued witnesses should be updated to be consistent with the new accumulator value. Ideally this should be done using a short amount of witness update data (i.e. whose cost/size is not dependent on the number of elements involved) and with only publicly available information (i.e. without knowledge of any secret accumulator parameters)
    witnesses.add(Witness::AccumulatorNonMembership(NonMembershipWit {
        element: msg_for_non_member,
        witness: uacc_witness.clone(),
    }));

    // !  PROVER - STATEMENTS (w refs)
    // to do at some point: generate

    let mut prover_statements = Statements::<Bls12_381, Affine<Config>>::new();
    prover_statements.add(PoKSignatureBBSG1Stmt::new_statement_from_params_ref(
        prover_setup_params_idx_of_sig_params,
        prover_setup_params_idx_of_sig_pk,
        msgs_to_reveal.clone(),
    ));

    prover_statements.add(
        BoundCheckProverStmt::new_statement_from_params_ref(
            min_1,
            max_1,
            prover_setup_params_idx_of_snark_pk,
        )
        .unwrap(),
    );
    prover_statements.add(AccumulatorNonMembershipStmt::new_statement_from_params_ref(
        prover_setup_params_idx_of_uacc_params,
        prover_setup_params_idx_of_uacc_pk,
        prover_setup_params_idx_of_non_mem_prk,
        uacc_value,
    ));

    // to do at some point: generate

    let mut meta_statements = MetaStatements::new();
    meta_statements.add_witness_equality(EqualWitnesses(
        // expiration date
        vec![
            (0, idx_of_msg_for_bounds),
            (1, 0), // lg16
        ]
        .into_iter()
        .collect::<BTreeSet<WitnessRef>>(),
    ));
    meta_statements.add_witness_equality(EqualWitnesses(
        // credential id
        vec![
            (0, idx_of_msg_for_non_member),
            (0, 5),
            (0, 10),
            (0, 15),
            (0, 20),
            (2, 0), // accumulator
        ]
        .into_iter()
        .collect::<BTreeSet<WitnessRef>>(),
    ));
    meta_statements.add_witness_equality(EqualWitnesses(
        // credential subject
        vec![(0, 7), (0, 30)] // do not need to include (0, 25) as this would give too much away
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));
    meta_statements.add_witness_equality(EqualWitnesses(
        // all in same graph
        vec![(0, 4), (0, 9), (0, 14), (0, 19), (0, 24), (0, 29), (0, 34)]
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));

    let prover_proof_spec = ProofSpec::new(
        prover_statements.clone(), // either give the proving key directly here, or you reference its index
        meta_statements.clone(),
        prover_setup_params, // and give the proving key is in this vec
        None,                // ! domain/recipient here
    );
    prover_proof_spec.validate().unwrap();

    // ! PROVER - CREATE PROOF

    let start = Instant::now();
    let (proof, _comm_rand) = Proof::<Bls12_381, G1Affine>::new::<StdRng, Blake2b512>(
        &mut rng,
        prover_proof_spec.clone(),
        witnesses.clone(),
        None,
        Default::default(),
    )
    .unwrap();
    let end = start.elapsed();

    println!("Time taken to create proof: {:#?}", end);

    // ! PROVIDE PRESENTATION
    let stmts_and_proofs: Vec<(
        &Statement<Bls12_381, G1Affine>,
        &StatementProof<Bls12_381, G1Affine>,
    )> = prover_statements
        .0
        .iter()
        .zip(proof.statement_proofs.iter())
        .collect();

    // presentation
    // (proof spec (to be derived from highlevel abstraction like shape) + input graph => avp?)
    let eqiv = |i| match i {
        // (could also be used to derive meta statements?)
        0 | 5 | 10 | 15 | 20 => 0,
        7 | 30 => 7,
        4 | 9 | 14 | 19 | 24 | 29 | 34 => 4,
        _ => i,
    };
    let mut presentation_quads_list =
        derive_presentation(indices_to_hide.clone(), &eqiv, &cred_dataset).unwrap();
    // serializing the graph

    let mut graph = LightGraph::new(); // unordered
    stmt_proofs_to_rdf(
        stmts_and_proofs, 
        indices_to_hide.clone(), 
        &eqiv, 
        &BnodeId::new_unchecked("4").into_term::<SimpleTerm<'_>>(), 
        &BnodeId::new_unchecked(idx_of_msg_for_bounds.to_string().as_str()).into_term::<SimpleTerm<'_>>(),
        &BnodeId::new_unchecked(idx_of_msg_for_non_member.to_string().as_str()).into_term::<SimpleTerm<'_>>(),
        &mut graph);
    let proof_graph_name =
        &BnodeId::new_unchecked("presentationProofGraph").into_term::<SimpleTerm<'_>>();
    graph.triples().for_each(|tr| {
        let t = tr.unwrap();
        let _ = presentation_quads_list.insert(t[0], t[1], t[2], Some(proof_graph_name));
    });

    // serialise
    // TODO extract serialising into Serialiser

    // This is just so ugly work because the sophia trig serialisers will not preserve ordering of quads.
    let presentation = serialize_ordered_trig(presentation_quads_list);
    // println!("{}", presentation);

    // Open a file to write the serialized graph
    let mut file = File::create("./data/prover.trig").unwrap();
    let _ = file.write_all(&presentation.as_bytes());
}

fn serialize_ordered_trig(presentation_quads_list: QuadsList<SimpleTermIndex<u32>>) -> String {
    let mut prefix_map = BTreeMap::new();
    prefix_map.insert("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf");
    prefix_map.insert("http://www.w3.org/2001/XMLSchema#", "xsd");
    prefix_map.insert("http://www.w3.org/ns/org#", "org");
    prefix_map.insert("https://www.w3.org/2018/credentials#", "cred");
    prefix_map.insert("https://ex.org/zkp/v0#", "zkp");
    prefix_map.insert("https://ex.org/spok/v0#", "spok");
    prefix_map.insert("https://ex.org/bbs+/v0#", "bbsp16");
    prefix_map.insert("https://ex.org/lg16/v0#", "lg16");
    prefix_map.insert("https://ex.org/uacc/v0#", "uacc");

    let config = NqConfig::default();
    let mut quad_stringifier = NqSerializer::new_stringifier_with_config(config.clone());
    let _ = quad_stringifier.serialize_dataset(&presentation_quads_list);
    let pg_str = quad_stringifier.as_str();
    // println!("The resulting graph:\n{}", pg_str);

    let mut graphs_builder: BTreeMap<String, Vec<String>> = BTreeMap::new();

    let mut quads_builder = String::new();
    for prefix in prefix_map.keys() {
        quads_builder.push_str(
            format!(
                "PREFIX {}: <{}> \n",
                prefix_map.get(prefix).unwrap(),
                prefix
            )
            .as_str(),
        );
    }
    quads_builder.push_str("\n");
    for quad in pg_str.split(".\n") {
        if quad == "" {
            continue;
        }
        let terms = quad
            .split_whitespace()
            .map(|t| curi(t, &prefix_map).to_string())
            .collect::<Vec<_>>();
        let mut triple = terms[0..3].join(" ");
        triple.push_str(" .");
        match terms.get(3) {
            Some(graph_name) => {
                let gn_quads = graphs_builder
                    .entry(graph_name.to_string())
                    .or_insert_with(Vec::new);
                gn_quads.push(triple);
            }
            None => {
                let graph_name = "".to_string();
                let gn_quads = graphs_builder
                    .entry(graph_name.to_string())
                    .or_insert_with(Vec::new);
                gn_quads.push(triple);
            }
        }
    }
    for graph in graphs_builder.keys() {
        let triples = graphs_builder.get(graph).unwrap().join("\n\t");
        quads_builder.push_str(format!("GRAPH {} {{\n\t{}\n}}\n", graph, triples).as_str());
    }
    quads_builder
}

fn curi<'a>(term: &'a str, prefix_map: &BTreeMap<&'a str, &'a str>) -> String {
    let process_term = |term: &str| {
        for (prefix, uri) in prefix_map {
            if term.starts_with(&format!("<{}", prefix)) {
                return term[1..term.len() - 1].replace(prefix, &format!("{}:", uri));
            }
        }
        term.to_string()
    };

    if let Some(index) = term.find("^^<") {
        let (literal, datatype) = term.split_at(index);
        format!("{}^^{}", literal, process_term(&datatype[2..]))
    } else {
        process_term(term)
    }
}

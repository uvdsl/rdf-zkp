use std::collections::{BTreeMap, VecDeque};
use std::error::Error;
use std::usize;

use ark_ec::pairing::PairingOutput;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use bbs_plus::proof::PoKOfSignatureG1Proof;

use legogroth16::Proof as Lg16Proof;
use proof_system::prelude::bound_check_legogroth16::BoundCheckLegoGroth16Prover;
use proof_system::prelude::{
    BoundCheckLegoGroth16Proof, PedersenCommitmentProof, Statement, StatementProof,
};

use schnorr_pok::SchnorrResponse;
use sophia::api::graph::MutableGraph;
use sophia::api::ns::{rdf, xsd, Namespace};
use sophia::api::prelude::{Any, Dataset};
use sophia::api::prelude::{MutableDataset, Quad};
use sophia::api::term::matcher::TermMatcher;
use sophia::api::term::{BnodeId, SimpleTerm, Term, TermKind};
use sophia::api::MownStr;
use sophia::c14n::rdfc10::normalize;
use sophia::inmem::index::SimpleTermIndex;
use sophia::iri::Iri;
use sophia::turtle::parser::trig;

use ark_bls12_381::{Bls12_381, G1Affine};
use ark_ec::{pairing::Pairing, AffineRepr};
use blake2::Blake2b512;
use vb_accumulator::proofs::{
    NonMembershipProof, NonMembershipRandomizedWitness, NonMembershipSchnorrCommit,
    NonMembershipSchnorrResponse, RandomizedWitness, SchnorrCommit as NmSchnorrCommit,
    SchnorrResponse as NmSchnorrResponse,
};

type Fr = <Bls12_381 as Pairing>::ScalarField;

use crate::rdf4zkp::encoder::{Rdf2FrEncoder, Rdf2FrInMemoryEncoder};
use crate::rdf4zkp::quads_list::QuadsList;

use super::{desiri, siri};

pub fn stmt_proofs_to_rdf<E: Pairing, G: AffineRepr, F: Fn(usize) -> usize, W: MutableGraph>(
    stmts_and_proofs: Vec<(&Statement<E, G>, &StatementProof<E, G>)>,
    indices_to_hide: Vec<usize>,
    replace_index_with: &F,
    wit_graph_term:&SimpleTerm<'_>,
    wit_bounds_term:&SimpleTerm<'_>,
    wit_setmember_term:&SimpleTerm<'_>,
    writer: &mut W,
) {
    let this_id = &BnodeId::new_unchecked("cproof").into_term::<SimpleTerm<'_>>();
    let ns_zkp = Namespace::new_unchecked("https://ex.org/zkp/v0#");
    let _ = writer.insert(this_id, rdf::type_, ns_zkp.get("CompositeProof").unwrap());
    for (index, (stmt_, proof_)) in stmts_and_proofs.into_iter().enumerate() {
        let proof_id = format!("p{}", index.to_string());
        let _ = writer.insert(
            this_id,
            ns_zkp.get("hasComponent").unwrap(),
            &BnodeId::new_unchecked(proof_id.clone().as_str()).into_term::<SimpleTerm<'_>>(),
        );
        match (stmt_, proof_) {
            (Statement::PoKBBSSignatureG1(stmt), StatementProof::PoKBBSSignatureG1(proof)) => {
                let vk_id = &Iri::new_unchecked("http://example.org/keys#aCompanyKey")
                    .into_term::<SimpleTerm<'_>>();
                poks_to_rdf(
                    &proof,
                    proof_id.as_str(),
                    vk_id,          // TODO get from reference map
                    wit_graph_term, // TODO get from reference map
                    indices_to_hide.clone(),
                    replace_index_with,
                    writer,
                );
            }
            (
                Statement::BoundCheckLegoGroth16Prover(stmt),
                StatementProof::BoundCheckLegoGroth16(proof),
            ) => {
                let vk_id =
                    &Iri::new_unchecked("http://example.org/keys#verifierLg16VerificationKey")
                        .into_term::<SimpleTerm<'_>>();
                lg16_proof_to_rdf(
                    &proof,
                    proof_id.as_str(),
                    vk_id,  // TODO get from reference map
                    wit_bounds_term, // TODO get from reference map
                    stmt.min,
                    stmt.max,
                    writer,
                );
            }
            (
                Statement::AccumulatorNonMembership(stmt),
                StatementProof::AccumulatorNonMembership(proof),
            ) => {
                let uacc_id = &Iri::new_unchecked("http://example.org/revocation#accumulatorId")
                    .into_term::<SimpleTerm<'_>>();
                let nm_prk_id = &Iri::new_unchecked("http://example.org/keys#proverUaccProvingKey")
                    .into_term::<SimpleTerm<'_>>();
                nm_proof_to_rdf(
                    &proof,
                    proof_id.as_str(),
                    uacc_id,   // TODO get from reference map
                    nm_prk_id, // TODO get from reference map
                    wit_setmember_term,    // TODO get from reference map
                    writer,
                );
            }
            _ => println!("Function for _"),
        }
    }
}

pub fn poks_to_rdf<E: Pairing, F: Fn(usize) -> usize, W: MutableGraph>(
    poks: &PoKOfSignatureG1Proof<E>,
    proof_bn_id: &str,
    vk_id: &SimpleTerm,
    wit_graph_name: &SimpleTerm,
    indices_to_hide: Vec<usize>,
    replace_index_with: &F,
    writer: &mut W,
) {
    let poks_id = &BnodeId::new_unchecked(proof_bn_id);
    let ns_bbs = Namespace::new_unchecked("https://ex.org/bbs+/v0#");
    let ns_spok = Namespace::new_unchecked("https://ex.org/spok/v0#");

    // BBS+
    let _ = writer.insert(poks_id, rdf::type_, ns_bbs.get("PoKS16").unwrap());
    let _ = writer.insert(poks_id, ns_bbs.get("hasVerificationKey").unwrap(), vk_id);
    let _ = writer.insert(
        poks_id,
        ns_bbs
            .get("isProofOfKnowledgeOfSignatureOverGraph")
            .unwrap(),
        wit_graph_name,
    );
    let base64_string = siri(&poks.A_prime).unwrap(); // poks.A_prime; // E::G1Affine,
    let _ = writer.insert(
        poks_id,
        ns_bbs.get("A_prime").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    let base64_string = siri(&poks.A_bar).unwrap(); // poks.A_bar; // E::G1Affine,
    let _ = writer.insert(
        poks_id,
        ns_bbs.get("A_bar").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    let base64_string = siri(&poks.d).unwrap(); // poks.d; // E::G1Affine,
    let _ = writer.insert(
        poks_id,
        ns_bbs.get("d").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    // SPK 1
    let spk1 = &BnodeId::new_unchecked(format!("{}_spk1", proof_bn_id));
    let _ = writer.insert(poks_id, ns_bbs.get("pi").unwrap(), spk1);
    let _ = writer.insert(spk1, rdf::type_, ns_bbs.get("SPK1").unwrap());

    let base64_string = siri(&poks.T1).unwrap();
    let _ = writer.insert(
        spk1,
        ns_spok.get("hasCommitmentToRandomness").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    let base64_string = siri(&poks.sc_resp_1.0[0]).unwrap();
    let _ = writer.insert(
        spk1,
        ns_bbs.get("hasResponseValueFor_e").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    let base64_string = siri(&poks.sc_resp_1.0[1]).unwrap();
    let _ = writer.insert(
        spk1,
        ns_bbs.get("hasResponseValueFor_r2").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    // SPK 2
    let spk2 = &BnodeId::new_unchecked(format!("{}_spk2", proof_bn_id));
    let _ = writer.insert(poks_id, ns_bbs.get("pi").unwrap(), spk2);
    let _ = writer.insert(spk2, rdf::type_, ns_bbs.get("SPK2").unwrap());

    let base64_string = siri(&poks.T2).unwrap();
    let _ = writer.insert(
        spk2,
        ns_spok.get("hasCommitmentToRandomness").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    let base64_string = siri(&poks.sc_resp_2.0[0]).unwrap(); // poks.sc_resp_2; // SchnorrResponse<E::G1Affine>,
    let _ = writer.insert(
        spk2,
        ns_bbs.get("hasResponseValueFor_r3").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    let base64_string = siri(&poks.sc_resp_2.0[1]).unwrap();
    let _ = writer.insert(
        spk2,
        ns_bbs.get("hasResponseValueFor_s_prime").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    // poks.sc_resp_2; // SchnorrResponse<E::G1Affine>,
    indices_to_hide
        .into_iter()
        .enumerate()
        .for_each(|(i, to_hide)| {
            // if to_hide != replace_index_with(to_hide) then already visited that response blank node.
            let hide_index = replace_index_with(to_hide);
            if hide_index != to_hide {
                return;
            }
            let base64_string = siri(&poks.sc_resp_2.0[i + 2]).unwrap();
            if hide_index % 5 == 3 {
                let _ = writer.insert(
                    BnodeId::new_unchecked((hide_index - 1).to_string()),
                    ns_spok.get("hasSchnorrResponseForSuffix").unwrap(),
                    base64_string.as_str() * xsd::base64Binary,
                );
            } else {
                let _ = writer.insert(
                    BnodeId::new_unchecked((hide_index).to_string()),
                    ns_spok.get("hasSchnorrResponse").unwrap(),
                    base64_string.as_str() * xsd::base64Binary,
                );
            }
        });
}

pub fn poks_from_rdf<'a, W: Dataset, E: Rdf2FrEncoder>(
    dataset_searchable: &'a W,
    quads_list: &'a QuadsList<SimpleTermIndex<u32>>, // TODO make quad list searchable, then we do not need the dataset_searchable anymore
    encoder: &mut E // ! HERE IS AN ISSUE
) -> Vec<(
    PoKOfSignatureG1Proof<Bls12_381>,
    SimpleTerm<'a>,               // vk id
    SimpleTerm<'a>,               // wit graph name
    BTreeMap<usize, Fr>,          // indicies to hide
    BTreeMap<usize, Fr>,          // indicies to reveal
    BTreeMap<String, Vec<usize>>, // index equal to others
    QuadsList<SimpleTermIndex<u32>>,
)> {
    let ns_bbs = Namespace::new_unchecked("https://ex.org/bbs+/v0#");
    let ns_spok = Namespace::new_unchecked("https://ex.org/spok/v0#");
    let mut results: Vec<(
        PoKOfSignatureG1Proof<Bls12_381>,
        SimpleTerm,                   // vk id
        SimpleTerm,                   // wit graph name
        BTreeMap<usize, Fr>,          // indicies to hide
        BTreeMap<usize, Fr>,          // indicies to reveal
        BTreeMap<String, Vec<usize>>, // index equal to others
        QuadsList<SimpleTermIndex<u32>>,
    )> = vec![];

    // PoKS16
    for quadsresult_proof in
        dataset_searchable.quads_matching(Any, [rdf::type_], [ns_bbs.get("PoKS16").unwrap()], Any)
    {
        // get the proof id
        let term_proof = quadsresult_proof.unwrap();
        let poks_id = term_proof.s();

        // hasVerificationKey
        let quads_vk = dataset_searchable
            .quads_matching(
                [poks_id],
                [ns_bbs.get("hasVerificationKey").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let vk_id = quads_vk[0].o();

        // isProofOfKnowledgeOfSignatureOverGraph
        let quads_g = dataset_searchable
            .quads_matching(
                [poks_id],
                [ns_bbs
                    .get("isProofOfKnowledgeOfSignatureOverGraph")
                    .unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let wit_graph_id = quads_g[0].o();

        // A_prime
        let quads_a_prime = dataset_searchable
            .quads_matching([poks_id], [ns_bbs.get("A_prime").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_a_prime = quads_a_prime[0].o();
        let a_prime = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_a_prime.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // A_bar
        let quads_a_bar = dataset_searchable
            .quads_matching([poks_id], [ns_bbs.get("A_bar").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_a_bar = quads_a_bar[0].o();
        let a_bar = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_a_bar.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // d
        let quads_d = dataset_searchable
            .quads_matching([poks_id], [ns_bbs.get("d").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_d = quads_d[0].o();
        let d =
            desiri::<<Bls12_381 as Pairing>::G1Affine>(term_d.lexical_form().unwrap().to_string())
                .unwrap();

        // Pi
        let quads_pi = dataset_searchable
            .quads_matching([poks_id], [ns_bbs.get("pi").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let mut quads_spk1 = vec![];
        let mut quads_spk2 = vec![];
        for quad_pi in quads_pi.iter() {
            let term_spok = quad_pi.o();
            let new_quads_spk1 = dataset_searchable
                .quads_matching(
                    [term_spok],
                    [rdf::type_],
                    [ns_bbs.get("SPK1").unwrap()],
                    Any,
                )
                .map(|r| r.unwrap())
                .collect::<Vec<W::Quad<'_>>>();
            if !new_quads_spk1.is_empty() {
                quads_spk1 = new_quads_spk1;
                continue;
            }
            let new_quads_spk2 = dataset_searchable
                .quads_matching(
                    [term_spok],
                    [rdf::type_],
                    [ns_bbs.get("SPK2").unwrap()],
                    Any,
                )
                .map(|r| r.unwrap())
                .collect::<Vec<W::Quad<'_>>>();
            if !new_quads_spk2.is_empty() {
                quads_spk2 = new_quads_spk2;
                continue;
            }
        }
        let term_spk1 = quads_spk1[0].s();
        let term_spk2 = quads_spk2[0].s();

        // SPK1

        // hasCommitmentToRandomness
        let quads_t1 = dataset_searchable
            .quads_matching(
                [term_spk1],
                [ns_spok.get("hasCommitmentToRandomness").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_t1 = quads_t1[0].o();
        let t1 =
            desiri::<<Bls12_381 as Pairing>::G1Affine>(term_t1.lexical_form().unwrap().to_string())
                .unwrap();

        // hasResponseValueFor_e
        let quads_resp_e = dataset_searchable
            .quads_matching(
                [term_spk1],
                [ns_bbs.get("hasResponseValueFor_e").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_resp_e = quads_resp_e[0].o();
        let resp_e = desiri::<Fr>(term_resp_e.lexical_form().unwrap().to_string()).unwrap();

        // hasResponseValueFor_r2
        let quads_resp_r_2 = dataset_searchable
            .quads_matching(
                [term_spk1],
                [ns_bbs.get("hasResponseValueFor_r2").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_resp_r_2 = quads_resp_r_2[0].o();
        let resp_r_2 = desiri::<Fr>(term_resp_r_2.lexical_form().unwrap().to_string()).unwrap();

        let sc_resps_1 = vec![resp_e, resp_r_2];
        let sc_resp_1 = SchnorrResponse(sc_resps_1);

        // SPK 2

        // hasCommitmentToRandomness
        let quads_t2 = dataset_searchable
            .quads_matching(
                [term_spk2],
                [ns_spok.get("hasCommitmentToRandomness").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_t2 = quads_t2[0].o();
        let t2 =
            desiri::<<Bls12_381 as Pairing>::G1Affine>(term_t2.lexical_form().unwrap().to_string())
                .unwrap();

        // hasResponseValueFor_r3
        let quads_resp_r_3 = dataset_searchable
            .quads_matching(
                [term_spk2],
                [ns_bbs.get("hasResponseValueFor_r3").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_resp_r_3 = quads_resp_r_3[0].o();
        let resp_r_3 = desiri::<Fr>(term_resp_r_3.lexical_form().unwrap().to_string()).unwrap();

        // hasResponseValueFor_s_prime
        let quads_resp_s_prime = dataset_searchable
            .quads_matching(
                [term_spk2],
                [ns_bbs.get("hasResponseValueFor_s_prime").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_resp_s_prime = quads_resp_s_prime[0].o();
        let resp_s_prime =
            desiri::<Fr>(term_resp_s_prime.lexical_form().unwrap().to_string()).unwrap();

        // poks.sc_resp_2;

        let mut credential_quads_list = QuadsList::<SimpleTermIndex<u32>>::new();
        for quad in quads_list.quads() {
            let q = quad.unwrap();
            if wit_graph_id.into_term::<SimpleTerm<'_>>() == q.g().unwrap() {
                credential_quads_list.insert(q.s(), q.p(), q.o(), q.g());
            }
        }
        let (hidden_message_responses, revealed_messages, equal_indicies) = encoder
            .quads_to_response_values(dataset_searchable, &credential_quads_list)
            .unwrap();

        let mut sc_resps_2 = vec![resp_r_3, resp_s_prime];
        sc_resps_2.extend(hidden_message_responses.values());
        let sc_resp_2 = SchnorrResponse(sc_resps_2);

        let poks = PoKOfSignatureG1Proof {
            A_prime: a_prime,
            A_bar: a_bar,
            d,
            T1: t1,
            sc_resp_1,
            T2: t2,
            sc_resp_2,
        };
        results.push((
            poks,
            vk_id.into_term::<SimpleTerm<'_>>(),
            wit_graph_id.into_term::<SimpleTerm<'_>>(),
            hidden_message_responses,
            revealed_messages,
            equal_indicies,
            credential_quads_list,
        ))
    }
    results
}

pub fn lg16_proof_to_rdf<E: Pairing, W: MutableGraph>(
    lg16_proof: &BoundCheckLegoGroth16Proof<E>,
    proof_bn_id: &str,
    vk_id: &SimpleTerm,
    witness_id: &SimpleTerm,
    min: u64,
    max: u64,
    writer: &mut W,
) {
    let lg16p_id = &BnodeId::new_unchecked(proof_bn_id);
    let ns_lg16 = Namespace::new_unchecked("https://ex.org/lg16/v0#");
    let ns_spok = Namespace::new_unchecked("https://ex.org/spok/v0#");
    //
    let _ = writer.insert(
        lg16p_id,
        rdf::type_,
        ns_lg16.get("LegoGroth16ProofOfRangeMembership").unwrap(),
    );
    let _ = writer.insert(lg16p_id, ns_lg16.get("hasVerificationKey").unwrap(), vk_id);
    let _ = writer.insert(lg16p_id, ns_lg16.get("hasWitness").unwrap(), witness_id);
    let _ = writer.insert(
        lg16p_id,
        ns_lg16.get("hasLowerBound").unwrap(),
        min.to_string().as_str() * xsd::nonNegativeInteger,
    );
    let _ = writer.insert(
        lg16p_id,
        ns_lg16.get("hasUpperBound").unwrap(),
        max.to_string().as_str() * xsd::nonNegativeInteger,
    );

    // pub snark_proof // legogroth16::Proof<E>,
    let lg16pv = &BnodeId::new_unchecked(format!("{}_lg16pv", proof_bn_id));
    let _ = writer.insert(lg16p_id, ns_lg16.get("hasProofValue").unwrap(), lg16pv);

    let base64_string = siri(&lg16_proof.snark_proof.a).unwrap();
    let _ = writer.insert(
        lg16pv,
        ns_lg16.get("A").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&lg16_proof.snark_proof.b).unwrap();
    let _ = writer.insert(
        lg16pv,
        ns_lg16.get("B").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&lg16_proof.snark_proof.c).unwrap();
    let _ = writer.insert(
        lg16pv,
        ns_lg16.get("C").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&lg16_proof.snark_proof.d).unwrap();
    let _ = writer.insert(
        lg16pv,
        ns_lg16.get("D").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    // pub sp // PedersenCommitmentProof<E::G1Affine>,
    let lg16sp = &BnodeId::new_unchecked(format!("{}_lg16sp", proof_bn_id));
    let _ = writer.insert(lg16p_id, ns_lg16.get("pok").unwrap(), lg16sp);
    let base64_string = siri(&lg16_proof.sp.t).unwrap();
    let _ = writer.insert(
        lg16sp,
        ns_spok.get("hasCommitmentToRandomness").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&lg16_proof.sp.response.0[1]).unwrap();
    let _ = writer.insert(
        lg16sp,
        ns_lg16.get("hasResponseValueFor_opening").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
}

pub fn lg16_proof_from_rdf<'a, W: Dataset>(
    dataset_searchable: &'a W,
) -> Vec<(
    BoundCheckLegoGroth16Proof<Bls12_381>,
    SimpleTerm, // vk_id:
    SimpleTerm, // witness_id
    (u64, u64), // (min,max)
)> {
    let ns_lg16 = Namespace::new_unchecked("https://ex.org/lg16/v0#");
    let ns_spok = Namespace::new_unchecked("https://ex.org/spok/v0#");

    let mut results: Vec<(
        BoundCheckLegoGroth16Proof<Bls12_381>,
        SimpleTerm, // vk_id:
        SimpleTerm, // witness_id
        (u64, u64), // (min,max)
    )> = vec![];

    // LG16
    for quadsresult_proof in dataset_searchable.quads_matching(
        Any,
        [rdf::type_],
        [ns_lg16.get("LegoGroth16ProofOfRangeMembership").unwrap()],
        Any,
    ) {
        // get the proof id
        let term_proof = quadsresult_proof.unwrap();
        let lg16_id = term_proof.s();

        // hasVerificationKey
        let quads_vk = dataset_searchable
            .quads_matching(
                [lg16_id],
                [ns_lg16.get("hasVerificationKey").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let vk_id = quads_vk[0].o().into_term::<SimpleTerm<'_>>();

        // hasWitness
        let quads_wit = dataset_searchable
            .quads_matching([lg16_id], [ns_lg16.get("hasWitness").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let wit_id = quads_wit[0].o().into_term::<SimpleTerm<'_>>();

        // hasLowerBound
        let quads_min = dataset_searchable
            .quads_matching([lg16_id], [ns_lg16.get("hasLowerBound").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_min = quads_min[0].o();
        let min = term_min
            .lexical_form()
            .unwrap()
            .to_string()
            .parse::<u64>()
            .unwrap();

        // hasUpperBound
        let quads_max = dataset_searchable
            .quads_matching([lg16_id], [ns_lg16.get("hasUpperBound").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_max = quads_max[0].o();
        let max = term_max
            .lexical_form()
            .unwrap()
            .to_string()
            .parse::<u64>()
            .unwrap();

        // hasProofValue
        let quads_pv = dataset_searchable
            .quads_matching([lg16_id], [ns_lg16.get("hasProofValue").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let pv_id = quads_pv[0].o();

        // hasProofValue A
        let quads_pv_a = dataset_searchable
            .quads_matching([pv_id], [ns_lg16.get("A").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_pv_a = quads_pv_a[0].o();
        let pv_a = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_pv_a.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // hasProofValue B
        let quads_pv_b = dataset_searchable
            .quads_matching([pv_id], [ns_lg16.get("B").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_pv_b = quads_pv_b[0].o();
        let pv_b = desiri::<<Bls12_381 as Pairing>::G2Affine>(
            term_pv_b.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // hasProofValue C
        let quads_pv_c = dataset_searchable
            .quads_matching([pv_id], [ns_lg16.get("C").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_pv_c = quads_pv_c[0].o();
        let pv_c = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_pv_c.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // hasProofValue D
        let quads_pv_d = dataset_searchable
            .quads_matching([pv_id], [ns_lg16.get("D").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_pv_d = quads_pv_d[0].o();
        let pv_d = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_pv_d.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // pok
        let quads_pok = dataset_searchable
            .quads_matching([lg16_id], [ns_lg16.get("pok").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let pok_id = quads_pok[0].o();

        // hasCommitmentToRandomness
        let quads_t = dataset_searchable
            .quads_matching(
                [pok_id],
                [ns_spok.get("hasCommitmentToRandomness").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_t = quads_t[0].o();
        let t =
            desiri::<<Bls12_381 as Pairing>::G1Affine>(term_t.lexical_form().unwrap().to_string())
                .unwrap();

        // hasCommitmentToRandomness
        let quads_resp_o = dataset_searchable
            .quads_matching(
                [pok_id],
                [ns_lg16.get("hasResponseValueFor_opening").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_resp_o = quads_resp_o[0].o();
        let resp_o = desiri::<Fr>(term_resp_o.lexical_form().unwrap().to_string()).unwrap();

        let resp_wit = get_response_value_for_term(dataset_searchable, &wit_id).unwrap();

        let proof = BoundCheckLegoGroth16Proof {
            snark_proof: Lg16Proof {
                a: pv_a,
                b: pv_b,
                c: pv_c,
                d: pv_d,
            },
            sp: PedersenCommitmentProof {
                t,
                response: SchnorrResponse(vec![resp_wit, resp_o]),
            },
        };

        let result = (proof, vk_id, wit_id, (min, max));
        results.push(result);
    }
    results
}

pub fn nm_proof_to_rdf<E: Pairing, W: MutableGraph>(
    nm_proof: &NonMembershipProof<E>,
    proof_bn_id: &str,
    uacc_id: &SimpleTerm,
    nm_prk_id: &SimpleTerm,
    witness_id: &SimpleTerm,
    writer: &mut W,
) {
    let nmp_id = &BnodeId::new_unchecked(proof_bn_id);
    let ns_uacc = Namespace::new_unchecked("https://ex.org/uacc/v0#");
    //
    let _ = writer.insert(
        nmp_id,
        rdf::type_,
        ns_uacc
            .get("UniversalAccumulatorProofOfNonMembership")
            .unwrap(),
    );
    let _ = writer.insert(nmp_id, ns_uacc.get("hasAccumulator").unwrap(), uacc_id);
    let _ = writer.insert(nmp_id, ns_uacc.get("hasWitness").unwrap(), witness_id);
    let _ = writer.insert(nmp_id, ns_uacc.get("hasProvingKey").unwrap(), nm_prk_id);

    // pub randomized_witness: NonMembershipRandomizedWitness<E::G1Affine>,
    // randomized_witness: { // witness (C,d)
    //     C: { // C = (f_V(α)−d)/(y+α)P
    //       E_C: [],      // commitment C + (σ + ρ)Z ~ C*Z^(σ*ρ)

    //       T_sigma: [], // commitment to randomness Tσ = σX,
    //       T_rho: [],   // commitment to randomness Tρ = ρY
    //     },
    //     E_d: [],       // commitment to d E_d = dP + aK
    //     E_d_inv: [],   // commitment to d E_d_inv = d−1P + bK
    //   },
    let uacc_rw = &BnodeId::new_unchecked(format!("{}_uacc_rw", proof_bn_id));
    let _ = writer.insert(
        nmp_id,
        ns_uacc.get("hasRandomizedWitness").unwrap(),
        uacc_rw,
    );
    let base64_string = siri(&nm_proof.randomized_witness.C.E_C).unwrap();
    let _ = writer.insert(
        uacc_rw,
        ns_uacc.get("E_C").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.randomized_witness.E_d).unwrap();
    let _ = writer.insert(
        uacc_rw,
        ns_uacc.get("E_d").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.randomized_witness.E_d_inv).unwrap();
    let _ = writer.insert(
        uacc_rw,
        ns_uacc.get("E_d_inv").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.randomized_witness.C.T_sigma).unwrap();
    let _ = writer.insert(
        uacc_rw,
        ns_uacc.get("commitment_to_randomness_T_sigma").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.randomized_witness.C.T_rho).unwrap();
    let _ = writer.insert(
        uacc_rw,
        ns_uacc.get("commitment_to_randomness_T_rho").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    // pub schnorr_commit: NonMembershipSchnorrCommit<E>,
    // prover picks blindings r
    //   schnorr_commit: { // commitment to randomness?
    //     C: {
    //       R_E: [], // e(EC , ˜P )^r_y e(Z, ˜P )^−r_δ_σ
    //       R_sigma: [], // randomness
    //       R_rho: [], // randomness
    //       R_delta_sigma: [], // randomness
    //       R_delta_rho: [], // randomness
    //     },
    //     R_A: [], // r_u * P + r_v * K       // randomness
    //     R_B: [], // r_u * E_d−1 + r_w * K   // randomness
    //   },
    let uacc_sc = &BnodeId::new_unchecked(format!("{}_uacc_sc", proof_bn_id));
    let _ = writer.insert(nmp_id, ns_uacc.get("hasCommitments").unwrap(), uacc_sc);
    let base64_string = siri(&nm_proof.schnorr_commit.C.R_E).unwrap();
    let _ = writer.insert(
        uacc_sc,
        ns_uacc.get("R_E").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_commit.C.R_sigma).unwrap();
    let _ = writer.insert(
        uacc_sc,
        ns_uacc.get("R_sigma").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_commit.C.R_rho).unwrap();
    let _ = writer.insert(
        uacc_sc,
        ns_uacc.get("R_rho").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_commit.C.R_delta_sigma).unwrap();
    let _ = writer.insert(
        uacc_sc,
        ns_uacc.get("R_delta_sigma").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_commit.C.R_delta_rho).unwrap();
    let _ = writer.insert(
        uacc_sc,
        ns_uacc.get("R_delta_rho").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_commit.R_A).unwrap();
    let _ = writer.insert(
        uacc_sc,
        ns_uacc.get("R_A").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_commit.R_B).unwrap();
    let _ = writer.insert(
        uacc_sc,
        ns_uacc.get("R_B").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );

    // pub schnorr_response: NonMembershipSchnorrResponse<E::ScalarField>,
    //   schnorr_response: {
    //     C: {
    //       s_y: [], // ry + cy with *y secret value* where w=(C,d) is the witness of that value y.
    //       s_sigma: [],
    //       s_rho: [],
    //       s_delta_sigma: [],
    //       s_delta_rho: [],
    //     },
    //     s_u: [], // su = ru + cd
    //     s_v: [],
    //     s_w: [],
    let uacc_sr = &BnodeId::new_unchecked(format!("{}_uacc_sr", proof_bn_id));
    let _ = writer.insert(nmp_id, ns_uacc.get("hasResponses").unwrap(), uacc_sr);
    // s_y as witness.
    let base64_string = siri(&nm_proof.schnorr_response.C.s_sigma).unwrap();
    let _ = writer.insert(
        uacc_sr,
        ns_uacc.get("s_sigma").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_response.C.s_rho).unwrap();
    let _ = writer.insert(
        uacc_sr,
        ns_uacc.get("s_rho").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_response.C.s_delta_sigma).unwrap();
    let _ = writer.insert(
        uacc_sr,
        ns_uacc.get("s_delta_sigma").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_response.C.s_delta_rho).unwrap();
    let _ = writer.insert(
        uacc_sr,
        ns_uacc.get("s_delta_rho").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_response.s_u).unwrap();
    let _ = writer.insert(
        uacc_sr,
        ns_uacc.get("s_u").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_response.s_v).unwrap();
    let _ = writer.insert(
        uacc_sr,
        ns_uacc.get("s_v").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&nm_proof.schnorr_response.s_w).unwrap();
    let _ = writer.insert(
        uacc_sr,
        ns_uacc.get("s_w").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
}

pub fn nm_proof_from_rdf<'a, W: Dataset>(
    dataset_searchable: &'a W,
) -> Vec<(
    NonMembershipProof<Bls12_381>,
    SimpleTerm, // prk_id:
    SimpleTerm, // acc_id:
    SimpleTerm, // witness_id
)> {
    let ns_uacc = Namespace::new_unchecked("https://ex.org/uacc/v0#");

    let mut results: Vec<(
        NonMembershipProof<Bls12_381>,
        SimpleTerm, // prk_id:
        SimpleTerm, // acc_id:
        SimpleTerm, // witness_id
    )> = vec![];

    // UACC
    for quadsresult_proof in dataset_searchable.quads_matching(
        Any,
        [rdf::type_],
        [ns_uacc
            .get("UniversalAccumulatorProofOfNonMembership")
            .unwrap()],
        Any,
    ) {
        // get the proof id
        let term_proof = quadsresult_proof.unwrap();
        let uacc_id = term_proof.s();

        // hasProvingKey
        let quads_prk = dataset_searchable
            .quads_matching([uacc_id], [ns_uacc.get("hasProvingKey").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let prk_id = quads_prk[0].o().into_term::<SimpleTerm<'_>>();

        // hasWitness
        let quads_wit = dataset_searchable
            .quads_matching([uacc_id], [ns_uacc.get("hasWitness").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let wit_id = quads_wit[0].o().into_term::<SimpleTerm<'_>>();

        // hasAccumulator
        let quads_acc = dataset_searchable
            .quads_matching(
                [uacc_id],
                [ns_uacc.get("hasAccumulator").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let acc_id = quads_acc[0].o().into_term::<SimpleTerm<'_>>();

        // hasRandomizedWitness
        let quads_rand_wit = dataset_searchable
            .quads_matching(
                [uacc_id],
                [ns_uacc.get("hasRandomizedWitness").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let rand_wit_id = quads_rand_wit[0].o();

        // E_C
        let quads_e_c = dataset_searchable
            .quads_matching([rand_wit_id], [ns_uacc.get("E_C").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_e_c = quads_e_c[0].o();
        let e_c = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_e_c.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // E_d
        let quads_e_d = dataset_searchable
            .quads_matching([rand_wit_id], [ns_uacc.get("E_d").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_e_d = quads_e_d[0].o();
        let e_d = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_e_d.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // E_d_inv
        let quads_e_d_inv = dataset_searchable
            .quads_matching([rand_wit_id], [ns_uacc.get("E_d_inv").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_e_d_inv = quads_e_d_inv[0].o();
        let e_d_inv = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_e_d_inv.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // T_sigma
        let quads_t_sigma = dataset_searchable
            .quads_matching(
                [rand_wit_id],
                [ns_uacc.get("commitment_to_randomness_T_sigma").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_t_sigma = quads_t_sigma[0].o();
        let t_sigma = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_t_sigma.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // T_rho
        let quads_t_rho = dataset_searchable
            .quads_matching(
                [rand_wit_id],
                [ns_uacc.get("commitment_to_randomness_T_rho").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_t_rho = quads_t_rho[0].o();
        let t_rho = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_t_rho.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // hasCommitments
        let quads_commits = dataset_searchable
            .quads_matching(
                [uacc_id],
                [ns_uacc.get("hasCommitments").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let commits_id = quads_commits[0].o();

        // R_E
        let quads_r_e = dataset_searchable
            .quads_matching([commits_id], [ns_uacc.get("R_E").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_r_e = quads_r_e[0].o();
        let r_e = desiri::<PairingOutput<Bls12_381>>(term_r_e.lexical_form().unwrap().to_string())
            .unwrap();

        // R_sigma
        let quads_r_sigma = dataset_searchable
            .quads_matching([commits_id], [ns_uacc.get("R_sigma").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_r_sigma = quads_r_sigma[0].o();
        let r_sigma = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_r_sigma.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // R_rho
        let quads_r_rho = dataset_searchable
            .quads_matching([commits_id], [ns_uacc.get("R_rho").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_r_rho = quads_r_rho[0].o();
        let r_rho = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_r_rho.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // R_delta_sigma
        let quads_r_delta_sigma = dataset_searchable
            .quads_matching(
                [commits_id],
                [ns_uacc.get("R_delta_sigma").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_r_delta_sigma = quads_r_delta_sigma[0].o();
        let r_delta_sigma = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_r_delta_sigma.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // R_delta_rho
        let quads_r_delta_rho = dataset_searchable
            .quads_matching(
                [commits_id],
                [ns_uacc.get("R_delta_rho").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_r_delta_rho = quads_r_delta_rho[0].o();
        let r_delta_rho = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_r_delta_rho.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // R_A
        let quads_r_a = dataset_searchable
            .quads_matching([commits_id], [ns_uacc.get("R_A").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_r_a = quads_r_a[0].o();
        let r_a = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_r_a.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // R_B
        let quads_r_b = dataset_searchable
            .quads_matching([commits_id], [ns_uacc.get("R_B").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_r_b = quads_r_b[0].o();
        let r_b = desiri::<<Bls12_381 as Pairing>::G1Affine>(
            term_r_b.lexical_form().unwrap().to_string(),
        )
        .unwrap();

        // hasResponses
        let quads_resps = dataset_searchable
            .quads_matching([uacc_id], [ns_uacc.get("hasResponses").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let resps_id = quads_resps[0].o();

        // s_sigma
        let quads_s_sigma = dataset_searchable
            .quads_matching([resps_id], [ns_uacc.get("s_sigma").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_s_sigma = quads_s_sigma[0].o();
        let s_sigma = desiri::<Fr>(term_s_sigma.lexical_form().unwrap().to_string()).unwrap();

        // s_rho
        let quads_s_rho = dataset_searchable
            .quads_matching([resps_id], [ns_uacc.get("s_rho").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_s_rho = quads_s_rho[0].o();
        let s_rho = desiri::<Fr>(term_s_rho.lexical_form().unwrap().to_string()).unwrap();

        // s_delta_sigma
        let quads_s_delta_sigma = dataset_searchable
            .quads_matching(
                [resps_id],
                [ns_uacc.get("s_delta_sigma").unwrap()],
                Any,
                Any,
            )
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_s_delta_sigma = quads_s_delta_sigma[0].o();
        let s_delta_sigma =
            desiri::<Fr>(term_s_delta_sigma.lexical_form().unwrap().to_string()).unwrap();

        // s_delta_rho
        let quads_s_delta_rho = dataset_searchable
            .quads_matching([resps_id], [ns_uacc.get("s_delta_rho").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_s_delta_rho = quads_s_delta_rho[0].o();
        let s_delta_rho =
            desiri::<Fr>(term_s_delta_rho.lexical_form().unwrap().to_string()).unwrap();

        // s_u
        let quads_s_u = dataset_searchable
            .quads_matching([resps_id], [ns_uacc.get("s_u").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_s_u = quads_s_u[0].o();
        let s_u = desiri::<Fr>(term_s_u.lexical_form().unwrap().to_string()).unwrap();

        // s_v
        let quads_s_v = dataset_searchable
            .quads_matching([resps_id], [ns_uacc.get("s_v").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_s_v = quads_s_v[0].o();
        let s_v = desiri::<Fr>(term_s_v.lexical_form().unwrap().to_string()).unwrap();

        // s_w
        let quads_s_w = dataset_searchable
            .quads_matching([resps_id], [ns_uacc.get("s_w").unwrap()], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_s_w = quads_s_w[0].o();
        let s_w = desiri::<Fr>(term_s_w.lexical_form().unwrap().to_string()).unwrap();

        // s_y
        let s_y = get_response_value_for_term(dataset_searchable, &wit_id).unwrap();

        // proof

        let proof = NonMembershipProof {
            randomized_witness: NonMembershipRandomizedWitness {
                C: RandomizedWitness {
                    E_C: e_c,
                    T_sigma: t_sigma,
                    T_rho: t_rho,
                },
                E_d: e_d,
                E_d_inv: e_d_inv,
            },
            schnorr_commit: NonMembershipSchnorrCommit {
                C: NmSchnorrCommit {
                    R_E: r_e,
                    R_sigma: r_sigma,
                    R_rho: r_rho,
                    R_delta_sigma: r_delta_sigma,
                    R_delta_rho: r_delta_rho,
                },
                R_A: r_a,
                R_B: r_b,
            },
            schnorr_response: NonMembershipSchnorrResponse {
                C: NmSchnorrResponse {
                    s_y,
                    s_sigma,
                    s_rho,
                    s_delta_sigma,
                    s_delta_rho,
                },
                s_u,
                s_v,
                s_w,
            },
        };
        let result = (proof, prk_id, acc_id, wit_id);
        results.push(result);
    }
    results
}

fn get_response_value_for_term<'a, W: Dataset, T: Term + 'static>(
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

fn get_response_value_for_term_suffix<'a, W: Dataset, T: Term + 'static>(
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

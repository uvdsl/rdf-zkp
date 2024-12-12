use ark_bls12_381::G1Affine;
use ark_ec::pairing::Pairing;
use bbs_plus::{
    prelude::SignatureG1,
    setup::{PublicKeyG2, SignatureParamsG1},
};
use sophia::api::{
    graph::{Graph, MutableGraph},
    ns::{rdf, xsd, Namespace},
    prelude::{Any, Dataset, Term, Triple},
    quad::Quad,
    term::{BnodeId, SimpleTerm},
};

use super::desiri;
use super::siri;

pub fn verification_key_to_rdf<'a, E: Pairing, W: MutableGraph>(
    params: &SignatureParamsG1<E>,
    pk: &PublicKeyG2<E>,
    vk_id: &SimpleTerm,
    writer: &'a mut W,
) -> &'a W {
    let ns_bbs = Namespace::new_unchecked("https://ex.org/bbs+/v0#");
    let _ = writer.insert(vk_id, rdf::type_, ns_bbs.get("PublicKey").unwrap());
    // pk value
    let base64_string = siri(&pk.0).unwrap();
    let _ = writer.insert(
        vk_id,
        ns_bbs.get("w").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    // insert parameter triples
    let sig_params = &BnodeId::new_unchecked("params");
    let _ = writer.insert(vk_id, ns_bbs.get("hasSignatureParams").unwrap(), sig_params);
    let base64_string = siri(&params.g1).unwrap();
    let _ = writer.insert(
        sig_params,
        ns_bbs.get("g1").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&params.g2).unwrap();
    let _ = writer.insert(
        sig_params,
        ns_bbs.get("g2").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&params.h_0).unwrap();
    let _ = writer.insert(
        sig_params,
        ns_bbs.get("h_0").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    // create list
    let _ = writer.insert(
        sig_params,
        ns_bbs.get("h_i").unwrap(),
        &BnodeId::new_unchecked("h_0"),
    );
    let last_index = params.h.len() - 1;
    for (i, e) in params.h.iter().enumerate() {
        let current_node = &BnodeId::new_unchecked(format!("h_{}", i));
        let item = siri(e).unwrap();
        writer
            .insert(current_node, rdf::first, item.as_str() * xsd::base64Binary)
            .unwrap();
        if i != last_index {
            let next_node = &BnodeId::new_unchecked(format!("h_{}", i + 1));
            let _ = writer.insert(current_node, rdf::rest, next_node).unwrap();
        } else {
            let _ = writer.insert(current_node, rdf::rest, rdf::nil).unwrap();
        }
    }
    writer
}

pub fn verification_key_from_rdf<W: Dataset, E: Pairing>(
    dataset: &W,
    vk_id: &SimpleTerm,
) -> (PublicKeyG2<E>, SignatureParamsG1<E>) {
    let ns_bbs = Namespace::new_unchecked("https://ex.org/bbs+/v0#");
    // public key ~ w
    let quads_w = dataset
        .quads_matching([vk_id], [ns_bbs.get("w").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let term_w = quads_w[0].o();
    let w = desiri::<E::G2Affine>(term_w.lexical_form().unwrap().to_string()).unwrap();
    let pk = PublicKeyG2::<E> { 0: w };

    // get params
    let quads_params = dataset
        .quads_matching(
            [vk_id],
            [ns_bbs.get("hasSignatureParams").unwrap()],
            Any,
            Any,
        )
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let term_params = quads_params[0].o();

    // get g1
    let quads_g1 = dataset
        .quads_matching([term_params], [ns_bbs.get("g1").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let term_g1 = quads_g1[0].o();
    let g1 = desiri::<E::G1Affine>(term_g1.lexical_form().unwrap().to_string()).unwrap();

    // get g2
    let quads_g2 = dataset
        .quads_matching([term_params], [ns_bbs.get("g2").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let term_g2 = quads_g2[0].o();
    let g2 = desiri::<E::G2Affine>(term_g2.lexical_form().unwrap().to_string()).unwrap();

    // get h_0
    let quads_h_0 = dataset
        .quads_matching([term_params], [ns_bbs.get("h_0").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let term_h_0 = quads_h_0[0].o();
    let h_0 = desiri::<E::G1Affine>(term_h_0.lexical_form().unwrap().to_string()).unwrap();

    // get h_i
    let mut h_i = vec![];
    let quads_h_i = dataset
        .quads_matching([term_params], [ns_bbs.get("h_i").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let mut term_h_i = quads_h_i[0].o().into_term::<SimpleTerm<'_>>();

    while !Term::eq(&term_h_i, rdf::nil) {
        let quads_h_i_first = dataset
            .quads_matching([term_h_i.clone()], [rdf::first], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        let term_h_i_first = quads_h_i_first[0].o();
        let h_i_first =
            desiri::<E::G1Affine>(term_h_i_first.lexical_form().unwrap().to_string()).unwrap();
        h_i.push(h_i_first);

        let quads_h_i_rest = dataset
            .quads_matching([term_h_i.clone()], [rdf::rest], Any, Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Quad<'_>>>();
        term_h_i = quads_h_i_rest[0].o().into_term::<SimpleTerm<'_>>();
    }

    let params = SignatureParamsG1::<E> {
        g1,
        g2,
        h_0,
        h: h_i,
    };
    (pk, params)
}

pub fn signature_to_rdf<'a, E: Pairing, W: MutableGraph>(
    signature: &SignatureG1<E>,
    vk_id: &SimpleTerm,
    writer: &'a mut W,
) -> &'a W {
    let ns_bbs = Namespace::new_unchecked("https://ex.org/bbs+/v0#");
    let ns_cred = Namespace::new_unchecked("https://www.w3.org/2018/credentials#");
    let sig = &BnodeId::new_unchecked("signature");
    let _ = writer.insert(sig, rdf::type_, ns_bbs.get("BbbsPlus16GLDS").unwrap());
    let _ = writer.insert(sig, ns_cred.get("verificationMethod").unwrap(), vk_id);
    let sig_val = &BnodeId::new_unchecked("value");
    let _ = writer.insert(sig, ns_cred.get("proofValue").unwrap(), sig_val);
    let base64_string = siri(&signature.A).unwrap();
    let _ = writer.insert(
        sig_val,
        ns_bbs.get("A").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&signature.e).unwrap();
    let _ = writer.insert(
        sig_val,
        ns_bbs.get("e").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&signature.s).unwrap();
    let _ = writer.insert(
        sig_val,
        ns_bbs.get("s").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    writer
}

pub fn signature_from_rdf<W: Graph, E: Pairing>(graph: &W) -> Vec<(SignatureG1<E>, SimpleTerm)> {
    let ns_bbs = Namespace::new_unchecked("https://ex.org/bbs+/v0#");
    let ns_cred = Namespace::new_unchecked("https://www.w3.org/2018/credentials#");
    let mut results: Vec<(SignatureG1<E>, SimpleTerm)> = vec![];

    for tr_sig in graph.triples_matching(Any, [rdf::type_], [ns_bbs.get("BbbsPlus16GLDS").unwrap()])
    {
        // get the sig id
        let t = tr_sig.unwrap();
        let s_id = t.s();

        // verificationMethod
        let graph_vk = graph
            .triples_matching([s_id], [ns_cred.get("verificationMethod").unwrap()], Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Triple<'_>>>();
        let term_vk = graph_vk[0].o().into_term::<SimpleTerm<'_>>();

        // proof value
        let g_pv = graph
            .triples_matching([s_id], [ns_cred.get("proofValue").unwrap()], Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Triple<'_>>>();
        let t_pv = g_pv[0].o();

        // get the signature (A,_,_)
        let g_a = graph
            .triples_matching([t_pv], [ns_bbs.get("A").unwrap()], Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Triple<'_>>>();
        let t_a = g_a[0].o();
        let v_a = desiri::<E::G1Affine>(t_a.lexical_form().unwrap().to_string()).unwrap();

        // get the signature (_,e,_)
        let g_e = graph
            .triples_matching([t_pv], [ns_bbs.get("e").unwrap()], Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Triple<'_>>>();
        let t_e = g_e[0].o();
        let v_e = desiri::<E::ScalarField>(t_e.lexical_form().unwrap().to_string()).unwrap();

        // get the signature (_,_,s)
        let g_s = graph
            .triples_matching([t_pv], [ns_bbs.get("s").unwrap()], Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Triple<'_>>>();
        let t_s = g_s[0].o();
        let v_s = desiri::<E::ScalarField>(t_s.lexical_form().unwrap().to_string()).unwrap();

        let signature = SignatureG1::<E> {
            A: v_a,
            e: v_e,
            s: v_s,
        };
        let result = (signature, term_vk);
        results.push(result);
    }
    results
}

use ark_ec::{pairing::Pairing, AffineRepr};
use sophia::api::{
    graph::{Graph, MutableGraph}, ns::{rdf, xsd, Namespace}, prelude::{Any, Dataset, Triple, TripleSource}, quad::Quad, term::{BnodeId, SimpleTerm, Term}
};
use vb_accumulator::{
    prelude::UniversalAccumulator,
    proofs::NonMembershipProvingKey,
    setup::{PublicKey, SetupParams},
    witness::NonMembershipWitness,
};

use super::desiri;
use super::siri;

pub fn nm_uacc_to_rdf<'a, E: Pairing, W: MutableGraph>(
    uacc_id: &SimpleTerm,
    uacc: &UniversalAccumulator<E>,
    pk: &PublicKey<E>,
    params: &SetupParams<E>,
    writer: &'a mut W,
) -> &'a W {
    let ns_uacc = Namespace::new_unchecked("https://ex.org/ns_uacc/v0#");

    let _ = writer.insert(
        uacc_id,
        rdf::type_,
        ns_uacc.get("UniversalAccumulator").unwrap(),
    );
    let base64_string = siri(&uacc.V).unwrap();
    let _ = writer.insert(
        uacc_id,
        ns_uacc.get("hasValue").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let _ = writer.insert(
        uacc_id,
        ns_uacc.get("hasMaxSize").unwrap(),
        uacc.max_size.to_string().as_str() * xsd::nonNegativeInteger,
    );
    // pk
    let pk_id = &BnodeId::new_unchecked("uacc_pk");
    let _ = writer.insert(uacc_id, ns_uacc.get("hasPublicKey").unwrap(), pk_id);
    let base64_string = siri(&pk.0).unwrap();
    let _ = writer.insert(
        pk_id,
        rdf::value,
        base64_string.as_str() * xsd::base64Binary,
    );
    // params
    let params_id = &BnodeId::new_unchecked("uacc_params");
    let _ = writer.insert(uacc_id, ns_uacc.get("hasParameters").unwrap(), params_id);
    let base64_string = siri(&params.P).unwrap();
    let _ = writer.insert(
        params_id,
        ns_uacc.get("P").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&params.P_tilde).unwrap();
    let _ = writer.insert(
        params_id,
        ns_uacc.get("P_tilde").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    writer
}

pub fn nm_uacc_from_rdf<W: Dataset, E: Pairing>(
    dataset: &W,
    uacc_id: &SimpleTerm,
) -> (E::G1Affine, PublicKey<E>, SetupParams<E>) {
    let ns_uacc = Namespace::new_unchecked("https://ex.org/ns_uacc/v0#");

    // get the value V
    let g_v = dataset
        .quads_matching([uacc_id], [ns_uacc.get("hasValue").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let t_v = g_v[0].o();
    let uacc_v = desiri::<E::G1Affine>(t_v.lexical_form().unwrap().to_string()).unwrap();

    // get the PK
    let g_pk = dataset
        .quads_matching([uacc_id], [ns_uacc.get("hasPublicKey").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let id_pk = g_pk[0].o();
    let g_v_pk = dataset
        .quads_matching([id_pk], [rdf::value], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let t_v_pk = g_v_pk[0].o();
    let uacc_pk = desiri::<PublicKey<E>>(t_v_pk.lexical_form().unwrap().to_string()).unwrap();

    // get the params
    let g_params = dataset
        .quads_matching([uacc_id], [ns_uacc.get("hasParameters").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let id_params = g_params[0].o();
    // P
    let g_params_p = dataset
        .quads_matching([id_params], [ns_uacc.get("P").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let t_params_p = g_params_p[0].o();
    let uacc_params_p =
        desiri::<E::G1Affine>(t_params_p.lexical_form().unwrap().to_string()).unwrap();
    // P_tile
    let g_params_pt = dataset
        .quads_matching([id_params], [ns_uacc.get("P_tilde").unwrap()], Any, Any)
        .map(|r| r.unwrap())
        .collect::<Vec<W::Quad<'_>>>();
    let t_params_pt = g_params_pt[0].o();
    let uacc_params_pt =
        desiri::<E::G2Affine>(t_params_pt.lexical_form().unwrap().to_string()).unwrap();
    // param
    let uacc_params = SetupParams::<E> {
        P: uacc_params_p,
        P_tilde: uacc_params_pt,
    };
    (uacc_v, uacc_pk, uacc_params)
}

pub fn nm_wit_to_rdf<'a, G: AffineRepr, W: MutableGraph>(
    uacc_id: &SimpleTerm,
    cred_id: &SimpleTerm,
    witness: &NonMembershipWitness<G>,
    writer: &'a mut W,
) -> &'a W {
    let ns_uacc = Namespace::new_unchecked("https://ex.org/ns_uacc/v0#");

    let nm_wit_id = &BnodeId::new_unchecked("nm_wit");
    let _ = writer.insert(
        nm_wit_id,
        rdf::type_,
        ns_uacc.get("NonMembershipWitness").unwrap(),
    );
    let _ = writer.insert(nm_wit_id, ns_uacc.get("isWitnessOf").unwrap(), cred_id);
    let _ = writer.insert(
        nm_wit_id,
        ns_uacc.get("witnessesNotMemberOf").unwrap(),
        uacc_id,
    );
    let base64_string = siri(&witness.d).unwrap();
    let _ = writer.insert(
        nm_wit_id,
        ns_uacc.get("d").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    let base64_string = siri(&witness.C).unwrap();
    let _ = writer.insert(
        nm_wit_id,
        ns_uacc.get("C").unwrap(),
        base64_string.as_str() * xsd::base64Binary,
    );
    writer
}

pub fn nm_wit_from_rdf<W: Graph, G: AffineRepr>(graph: &W) -> Vec<NonMembershipWitness<G>> {
    let ns_uacc = Namespace::new_unchecked("https://ex.org/ns_uacc/v0#");
    let mut witnesses = vec![];

    for tr_nmw in graph.triples_matching(
        Any,
        [rdf::type_],
        [ns_uacc.get("NonMembershipWitness").unwrap()],
    ) {
        // get the witness id
        let t = tr_nmw.unwrap();
        let s = t.s();

        // get the witness (d,_)
        let g_d = graph
            .triples_matching([s], [ns_uacc.get("d").unwrap()], Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Triple<'_>>>();
        let t_d = g_d[0].o();
        let v_d = desiri::<G::ScalarField>(t_d.lexical_form().unwrap().to_string()).unwrap();

        // get the witness (_,C)
        let g_c = graph
            .triples_matching([s], [ns_uacc.get("C").unwrap()], Any)
            .map(|r| r.unwrap())
            .collect::<Vec<W::Triple<'_>>>();
        let t_c = g_c[0].o();
        let v_c = desiri::<G>(t_c.lexical_form().unwrap().to_string()).unwrap();

        let w = NonMembershipWitness::<G> { d: v_d, C: v_c };
        witnesses.push(w);
    }
    witnesses
}

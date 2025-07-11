use std::collections::VecDeque;
use std::error::Error;
use std::usize;

use sophia::api::dataset::Dataset;
use sophia::api::graph::MutableGraph;
use sophia::api::ns::{rdf, xsd, Namespace};
use sophia::api::prelude::{MutableDataset, Quad, QuadSource};
use sophia::api::term::TermKind;
use sophia::api::term::{BnodeId, SimpleTerm, Term};
use sophia::c14n::rdfc10::normalize;
use sophia::inmem::dataset::LightDataset;
use sophia::inmem::index::SimpleTermIndex;
use sophia::turtle::parser::trig;

use crate::rdf4zkp::quads_list::QuadsList;

/// Replaces nodes from a dataset with blank nodes, given a list of term/atom indicies and a replacement closure.
/// Example:
/// ```
/// let indices_to_hide = vec![0, 3, 4, 5, 7, 8, 9, 10, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29];
/// let replace_index_with = |i| match i {
///                                         0 | 5 | 10 | 15 => 0,
///                                         7 | 25 => 7,
///                                         _ => i,
///                                      };
/// ```
/// This way, the function does not need to keep track of which terms are repalced with which blank node.
/// The mapping is externally defined through the provided closure.
///
/// TODO keep canonical ordering. Datasets do not preserve ordering of qudas but re-order canonically, it seems.
/// TODO in canon parse, give result quad into string builder?
/// maybe do give list of quads...
pub fn derive_presentation<F: Fn(usize) -> usize, W: Dataset>(
    indices_to_hide: Vec<usize>,
    replace_index_with: &F,
    writer: &W,
) -> Result<QuadsList<SimpleTermIndex<u32>>, Box<dyn Error>> {
    // Canonicalise, just to be sure.
    let mut output = Vec::<u8>::new();
    normalize(writer, &mut output).unwrap();
    let normalised_nquads = match String::from_utf8(output) {
        Ok(s) => s,
        Err(e) => return Err(format!("Failed to read UTF-8 sequence: {:?}", e).into()),
    };
    // here we rely on the streaming quality of the parser to keep the ordering of quads
    let canon_quads_list: QuadsList<SimpleTermIndex<u32>> = trig::parse_str(normalised_nquads.as_str())
        .collect_quads()
        .unwrap();
    let mut presentation_quads_list = QuadsList::<SimpleTermIndex<u32>>::new();
    let mut indices_to_hide_queue: VecDeque<[Option<usize>; 5]> = VecDeque::new();
    for index_to_hide in indices_to_hide.into_iter() {
        if index_to_hide % 5 == 0 { // subject of a quad
            indices_to_hide_queue.push_back([None; 5]); // start new quad term counting round
        }
        let last_array_index = &indices_to_hide_queue.len() - 1;
        indices_to_hide_queue[last_array_index][index_to_hide % 5] =
            Some(replace_index_with(index_to_hide));
    }
    for q in canon_quads_list.quads() {
        let ([s, p, o], g) = q?.to_spog();
        let current_indicies_to_hide: [Option<usize>; 5] = match indices_to_hide_queue.pop_front() {
            Some(v) => v,
            None => [None; 5],
        };
        if current_indicies_to_hide[2].is_some() && current_indicies_to_hide[3].is_none() {
            return Err(format!(
                "Datatype to be revealed on hidden object (index: {})",
                current_indicies_to_hide[2].unwrap()
            )
            .into());
        }
        let s0 = match current_indicies_to_hide[0] {
            Some(i) => BnodeId::new_unchecked(i.to_string()).into_term::<SimpleTerm<'_>>(),
            None => s.clone(),
        };
        let p0 = match current_indicies_to_hide[1] {
            Some(i) => BnodeId::new_unchecked(i.to_string()).into_term::<SimpleTerm<'_>>(),
            None => p.clone(),
        };
        let o0 = match current_indicies_to_hide[2] {
            Some(i) => BnodeId::new_unchecked(i.to_string()).into_term::<SimpleTerm<'_>>(),
            None => o.clone(),
        };
        let g0 = match current_indicies_to_hide[4] {
            Some(i) => Some(BnodeId::new_unchecked(i.to_string()).into_term::<SimpleTerm<'_>>()),
            None => None,
        };
        presentation_quads_list
            .insert(&s0, &p0, &o0, g0.as_ref().or(g))
            .unwrap();
    }
    Ok(presentation_quads_list)
}

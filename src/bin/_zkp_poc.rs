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
    prelude::{EqualWitnesses, MetaStatements, ProofSpec, Witness, WitnessRef, Witnesses},
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

// Prove knowledge of BBS+ signature and certain messages satisfy some bounds.
// fn check(reuse_key: bool) { // re-use key is an optimization
fn main() {
    let mut rng = StdRng::seed_from_u64(0u64);

    // ISSUER
    let msg_count = 5;
    let msgs = (0..msg_count)
        .map(|i| Fr::from(101u64 + i as u64))
        .collect::<Vec<_>>();
    println!("### All Messages ### \n{:#?} \n", msgs);
    let (sig_params, sig_keypair, sig) = bbs_plus_sig_setup_given_messages(&mut rng, &msgs);
    println!("### Signature ### \n{}\n",serde_json::to_string(&sig).unwrap());
    println!("### Signature Parameters ### \n{}\n",serde_json::to_string(&sig_params).unwrap());
    println!("### Signature Key Public ### \n{}\n",serde_json::to_string(&sig_keypair.public_key).unwrap());

    let max_members = 128;
    let (uni_accum_params, uni_accum_keypair, mut uni_accumulator, initial_elements, mut uni_state) =
        setup_universal_accum(&mut rng, max_members);
    let non_mem_prk = NonMembershipProvingKey::generate_using_rng(&mut rng);
    // create witness to be transmitted to prover
    let accum_non_member_idx = 3;
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
    println!("### Accum Witness ### \n{}\n",serde_json::to_string(&non_mem_wit).unwrap());
    println!("### Accum ### \n{}\n",serde_json::to_string(&uni_accumulator).unwrap()); 
    println!("### Accum State ### \n{:#?}\n",&uni_state);
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
    let min_1 = 50;
    let max_1 = 200; // 101 does not work, as msg_index 1 is 102;
    println!("### Bounds ### \n[{},{}] \n", min_1, max_1);
    // Following messages' bounds will be checked
    let msg_idx_1 = 1;
    let msg_1 = msgs[msg_idx_1];
    println!(
        "### Message to be re-used in bound proof ### \n{:#?} \n",
        msg_1
    );
    let mut prover_setup_params = vec![];
    if reuse_key {
        prover_setup_params.push(SetupParams::LegoSnarkProvingKey(snark_pk.clone()));
    }
    let accum_non_member_idx = 3;
    let accum_non_member = msgs[accum_non_member_idx];
    println!(
        "### Message to be re-used in NonMember proof ### \n{} \n",
        accum_non_member
    );
    println!(
        "### messages hidden ### \n{:#?} \n",
        msgs.clone()
            .into_iter()
            .enumerate()
            .filter_map(|(index, value)| {
                if index != 0 {
                    Some((index, value.clone()))
                } else {
                    None
                }
            })
            .collect::<BTreeMap<usize, _>>()
    );

    // PROVER - WITNESSES
    let mut witnesses = Witnesses::new();
    witnesses.add(PoKSignatureBBSG1Wit::new_as_witness(
        sig,
        msgs.clone()
            .into_iter()
            .enumerate()
            .filter_map(|(index, value)| {
                if index == 0 {
                    return None;
                }
                return Some((index, value.clone()));
            })
            .collect(),
    ));
    witnesses.add(Witness::BoundCheckLegoGroth16(msg_1));
    
    // Whenever addition or deletion operations occur for one or several elements (in the latter case these are called batch additions and deletions), already issued witnesses should be updated to be consistent with the new accumulator value. Ideally this should be done using a short amount of witness update data (i.e. whose cost/size is not dependent on the number of elements involved) and with only publicly available information (i.e. without knowledge of any secret accumulator parameters)
    witnesses.add(Witness::AccumulatorNonMembership(NonMembershipWit {
        element: accum_non_member,
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
        BTreeMap::from_iter(vec![(0, Fr::from(101u64))]),
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
        vec![(0, msg_idx_1), (1, 0)]
            .into_iter()
            .collect::<BTreeSet<WitnessRef>>(),
    ));
    meta_statements.add_witness_equality(EqualWitnesses(
        vec![(0, accum_non_member_idx), (2, 0)]
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
    // println!("### Prover Proof Spec ### \n {:#?} \n",prover_proof_spec);

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
    println!("### Proof ### \n{:#?} \n", proof);

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
        BTreeMap::from_iter(vec![(0, Fr::from(101u64))]),
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
        meta_statements.clone(),     // ? re-using from above, should be re-constructed
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
        "Time taken to verify proof of 5 msg POKS, with 1 RANGE and 1 NON-MEMBER: {:#?}",
        start.elapsed()
    );

    println!("Verification: {:#?}", result);

    // Serialize the Proof into a JSON string
    let json_string = serde_json::to_string(&proof).unwrap();
    println!("{}", json_string);
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

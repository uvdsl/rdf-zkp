use std::error::Error;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

pub mod signature;
pub mod accumulator;
pub mod presentation;
pub mod proof;


pub fn siri<T>(x: &T) -> Result<String, Box<dyn Error>>
where
    T: CanonicalSerialize,
{
    let mut w = Vec::new();
    x.serialize_compressed(&mut w)?;
    Ok(base64::encode(&w))
}

pub fn desiri<T>(x: String) -> Result<T, Box<dyn Error>>
where
    T: CanonicalDeserialize,
{
    let decoded_bytes = base64::decode(&x)?;
    T::deserialize_compressed(&decoded_bytes[..]).map_err(|e| Box::new(e) as Box<dyn Error>)
}

// let deserialized_data: G1Affine = desiri(base64_string).unwrap();
// println!("A_prime\t{:?}", deserialized_data);
// println!();

// let deserialized_data: Fr = desiri(base64_string).unwrap();
// println!("{:?}\t{:?}", to_hide, deserialized_data);
// println!();

// let x = siri(&self.snark_proof.a).unwrap();
//         println!("{:?}", x);
//         let z: G1Affine = desiri(x).unwrap();

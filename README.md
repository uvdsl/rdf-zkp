# Combining Zero-Knowledge Proofs on RDF graphs (W3C Verifiable Credentials)
_based on the cryptographic work of [Lovesh Harchandani](https://github.com/lovesh)_


We use [dock/crypto](https://github.com/docknetwork/crypto) as a submodule for proof of knowledge of BBS+ signature, LegoGroth16 range proof and Accumulator non-membership.


## Repository Structure

- [benches/](benches/) a sample benchmark of of the MT-based and schema-based approach.
- [data/](data/) the Verifiable Credential (VC) and Verifiable Presentation (VP) that are being generated when running the examples.
- [dock/crypto/](dock/crypto/) the submodule that provides the cryptographic functions.
- [src/](src/) source code.
    - [bin/](src/bin/) examples that you can execute.
    - [poc/](src/poc/) proof of concept implementations of the different procedures (issue,prove,verify) in two versions: model theory (MT)-based (no suffix) and schema-based ("_schema" suffix).
    - [rdf4zkp](src/rdf4zkp/) functions for encoding RDF to field representations.
    - [zkp4rdf](src/zkp4rdf/) functions for transforming zkp related variables and values to RDF.
- [vocab/](vocab/) the vocabulary used to describe the proofs.
    - [zkp-o.ttl](vocab/zkp-o.ttl) general terms for zero-knowledge proofs.
    - [zkp-o-spok.ttl](vocab/zkp-o-spok.ttl) terms for Schnorr proofs of knowledge (of discrete log).
    - [zkp-o-bbs.ttl](vocab/zkp-o-bbs.ttl) terms for BBS+ proof of knowledge of signature.
    - [zkp-o-lg16.ttl](vocab/zkp-o-lg16.ttl) terms for LegoGroth16 proof of numeric bounds.
    - [zkp-o-uacc.ttl](vocab/zkp-o-uacc.ttl) terms for Univeral Accumulator proof of set (non-)membership.

## Run it yourself
```sh
# set up the repo
git clone <repo-url>
cd <repo>
git submodule update --init --recursive

# using RDF model theory (MT)-based transformation
cargo run --bin issuer
cargo run --bin prover
cargo run --bin verifier

# using schema-based transformation
cargo run --bin issuer_schema
cargo run --bin prover_schema
cargo run --bin verifier_schema

# benchmark the performance difference
cargo bench
```
We used the rust compiler `rustc 1.66.0 (69f9c33d7 2022-12-12)`.
Just in case that is relevant at some point in time.

---

This is a proof of concept, not a library.

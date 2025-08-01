# Combining Zero-Knowledge Proofs on RDF graphs (W3C Verifiable Credentials)
_based on the cryptographic work of [Lovesh Harchandani](https://github.com/lovesh)_


We use [dock/crypto](https://github.com/docknetwork/crypto) for proof of knowledge of BBS+ signature, LegoGroth16 range proof and Accumulator non-membership.


## Repository Structure

- [benches/](benches/) a sample benchmark of of the MT-based and schema-based approach.
- [data/](data/) the Verifiable Credential (VC) and Verifiable Presentation (VP) that are being generated when running the examples.
- [src/](src/) source code.
    - [bin/](src/bin/) examples that you can execute.
    - [poc/](src/poc/) proof of concept implementations of the different procedures (issue,prove,verify) in two versions: schema-free (no suffix) and schema-based ("_schema" suffix).
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

# using schema-free transformation
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
We used the rust compiler `rustc 1.88.0 (6b00bc388 2025-06-23)`.
Just in case that is relevant at some point in time.

---

This is a proof of concept, not a library.

---

Please cite this work by referring to

`Christoph H.-J. Braun, Tobias Käfer: RDF-Based Semantics for Selective Disclosure and Zero-Knowledge Proofs on Verifiable Credentials. ESWC (1) 2025: 383-402`

or use the following BibTeX record
```
@inproceedings{DBLP:conf/esws/BraunK25,
  author       = {Christoph H.{-}J. Braun and
                  Tobias K{\"{a}}fer},
  editor       = {Edward Curry and
                  Maribel Acosta and
                  Mar{\'{\i}}a Poveda{-}Villal{\'{o}}n and
                  Marieke van Erp and
                  Adegboyega K. Ojo and
                  Katja Hose and
                  Cogan Shimizu and
                  Pasquale Lisena},
  title        = {RDF-Based Semantics for Selective Disclosure and Zero-Knowledge Proofs
                  on Verifiable Credentials},
  booktitle    = {The Semantic Web - 22nd European Semantic Web Conference, {ESWC} 2025,
                  Portoroz, Slovenia, June 1-5, 2025, Proceedings, Part {I}},
  series       = {Lecture Notes in Computer Science},
  volume       = {15718},
  pages        = {383--402},
  publisher    = {Springer},
  year         = {2025},
  url          = {https://doi.org/10.1007/978-3-031-94575-5\_21},
  doi          = {10.1007/978-3-031-94575-5\_21},
  timestamp    = {Fri, 04 Jul 2025 22:06:19 +0200},
  biburl       = {https://dblp.org/rec/conf/esws/BraunK25.bib},
  bibsource    = {dblp computer science bibliography, https://dblp.org}
}
```
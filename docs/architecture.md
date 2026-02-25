# Architecture

This repository contains two coupled layers:

1. Proof and extraction layer (`proofs/flocq_engine/`)
2. OCaml sealing and verification layer (`src/`)

The proof layer is responsible for producing trustworthy computational artefacts and extracted code where applicable.

The OCaml layer is responsible for:
- constructing an auditable verification report shape
- generating an integrity seal that can be recomputed
- verifying the seal and rejecting tampered outputs

The public intent is demonstration of:
- build discipline
- trace integrity
- verifiability under tamper

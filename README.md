# VeriBound Rocq Seal

This repository contains a small, buildable slice of VeriBound focused on audit-grade trace integrity:

- Rocq or Coq proof artefacts and extraction sources (Flocq-based work)
- OCaml implementation of sealing and verification
- a demonstrable tamper check workflow

The scope here is narrow on purpose. It is intended to be reviewed and built.

## What this demonstrates

### 1. Formal verification artefacts
The `proofs/` folder contains Rocq or Coq sources supporting an extracted classification core (Flocq-based), along with extracted OCaml artefacts.

### 2. Seal generation with an irrational marker
The sealing layer generates an "irrational marker" derived from the trace, intended as an audit-visible integrity token.

### 3. Hash-based seal and verifier
A second seal mechanism uses a hash-derived seal and includes a verifier that detects tampering.

## Repository layout

- `src/`  
  OCaml implementation: sealing, verification, and integration code.

- `proofs/flocq_engine/`  
  Rocq or Coq sources and extraction artefacts related to Flocq.

- `test/`  
  OCaml tests for the seal and verifier logic.

- `examples/`  
  Minimal example JSON files and a short walkthrough.

- `docs/`  
  Architecture notes and a simple threat model.

## Quick start

### Prerequisites
You will need:
- OCaml toolchain
- Dune
- (optional) Rocq or Coq if you want to rebuild proof artefacts

### Build
From the repository root:

1. Build:
   - `dune build`

2. Run tests:
   - `dune runtest`

If your environment uses opam, install dependencies as you normally would for a dune project.

## Tamper check demo

See `examples/README.md`.

The demo uses three files:
- `input.json` (original)
- `sealed.json` (after sealing)
- `tampered.json` (a deliberately modified version)

The verifier should accept `sealed.json` and reject `tampered.json`.

## Non-goals

This repository is not:
- a complete product release
- a full regulatory template system
- a production hardening effort

It is a coherent, buildable demonstration of formal artefacts plus seal and verification logic.

## Contact

Duston Moore, PhD  
Email: dhwcmoore@gmail.com

## Licence

MIT, see `LICENSE`.

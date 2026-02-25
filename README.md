# VeriBound Rocq Seal

A Rocq or Coq plus OCaml implementation demonstrating formal artefacts, extraction, and audit-grade trace integrity via deterministic sealing and verification.

The repository is intentionally narrow and buildable. It exposes a minimal verification core together with explicit seal and tamper-detection logic.

---

## Scope

This repository contains two coupled layers:

1. Proof and extraction artefacts (Rocq or Coq, Flocq-based)
2. OCaml implementation of seal construction and verification

All behaviour is deterministic and reproducible.

---

## Components

### Formal artefacts

The `proofs/` directory contains Rocq or Coq sources supporting an extracted computational core. Extracted OCaml artefacts are included where applicable.

The formal layer is limited in scope and intended as a verification-bearing kernel rather than a full specification system.

---

### Seal construction

Two seal mechanisms are implemented:

* An irrational-marker seal derived deterministically from the verification trace
* A hash-derived seal suitable for recomputation and comparison

Both are explicit transformations over structured data.

---

### Verification

A verifier recomputes seal values and rejects modified artefacts.

The intent is to demonstrate:

* trace integrity
* recomputability
* tamper detection under ordinary modification

---

## Repository layout

* `src/`
  OCaml implementation of sealing, verification, and integration logic.

* `proofs/flocq_engine/`
  Rocq or Coq sources and related extraction artefacts.

* `test/`
  Unit and integration tests for seal and verification logic.

* `examples/`
  Minimal JSON artefacts illustrating sealing and tamper detection.

* `docs/`
  Architecture notes and a minimal threat model.

---

## Build

Prerequisites:

* OCaml toolchain
* Dune
* Optional: Rocq or Coq for rebuilding proof artefacts

From the repository root:

```
dune build
dune runtest
```

---

## Tamper demonstration

The `examples/` folder contains:

* `input.json`
* `sealed.json`
* `tampered.json`

Expected behaviour:

* Verifier accepts `sealed.json`
* Verifier rejects `tampered.json`

---

## Non-goals

This repository does not attempt to provide:

* Key management
* Production hardening
* Regulatory template completeness
* Secure deployment guarantees

It demonstrates a deterministic verification trace coupled to explicit integrity markers.

---

## Licence

MIT

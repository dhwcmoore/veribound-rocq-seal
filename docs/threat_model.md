# Threat model

This is a minimal threat model suitable for a public demonstration repository.

## Attacker capabilities
- can modify stored output files
- can attempt to edit fields inside a sealed JSON artefact
- can attempt replay of an old sealed artefact

## What the verifier aims to detect
- modification of sealed fields
- modification of the underlying payload without updating the seal

## What this demo does not claim
- secure key management
- secure distribution of trusted templates
- resistance to a compromised execution environment

This repository demonstrates integrity checking under ordinary tampering, not full production hardening.

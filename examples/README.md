# Examples

This folder contains a minimal tamper demonstration.

## Files

- `input.json`  
  A small representative input.

- `sealed.json`  
  The result of running the sealing logic. It contains integrity fields.

- `tampered.json`  
  A modified copy of `sealed.json` that should fail verification.

## Expected behaviour

- verifier accepts `sealed.json`
- verifier rejects `tampered.json`

If you add new examples, keep the set small and reproducible.

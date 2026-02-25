(* test/test_verifier_tampered.ml *)

open Verifier

let () =
  let test_file = "examples/tampered.json" in
  let (_ok, msg) = verify_seal_from_file test_file in
  Printf.printf "Verification result for tampered file %s:\n%s\n" test_file msg

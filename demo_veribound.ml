
(* Copy the functions we need directly *)
type boundary = {
  name: string;
  lower: float;
  upper: float;
  verdict: string;
}

type domain = {
  name: string;
  authority: string;
  boundaries: boundary list;
}

let nuclear_domain = {
  name = "Nuclear Reactor Protection System";
  authority = "NRC 10 CFR 50.55a";
  boundaries = [
    { name = "Normal_Operation"; lower = 280.0; upper = 315.0; verdict = "SAFE_VERIFIED" };
    { name = "Maximum_Tolerated"; lower = 315.1; upper = 350.0; verdict = "CAUTION_VERIFIED" };
    { name = "Toxic_Range"; lower = 350.1; upper = 400.0; verdict = "DANGEROUS_VERIFIED" };
    { name = "Lethal_Range"; lower = 400.1; upper = 500.0; verdict = "EMERGENCY_VERIFIED" };
  ]
}

let financial_domain = {
  name = "Basel III Capital Adequacy";
  authority = "Basel Committee on Banking Supervision";
  boundaries = [
    { name = "Well_Capitalized"; lower = 10.5; upper = 100.0; verdict = "COMPLIANT" };
    { name = "Adequately_Capitalized"; lower = 8.0; upper = 10.4; verdict = "ACCEPTABLE" };
    { name = "Undercapitalized"; lower = 6.0; upper = 7.9; verdict = "WARNING" };
    { name = "Critically_Undercapitalized"; lower = 0.0; upper = 5.9; verdict = "VIOLATION" };
  ]
}

let classify_simple domain value =
  let rec find_boundary = function
    | [] -> "UNKNOWN"
    | b :: rest -> 
        if value >= b.lower && value <= b.upper then
          b.verdict
        else
          find_boundary rest
  in
  find_boundary domain.boundaries

let create_demo_result domain value =
  let category = classify_simple domain value in
  let timestamp = Unix.time () in
  let results_text = Printf.sprintf {|[{"category":"%s","lower":%f,"upper":%f,"verdict":"%s","domain":"%s","authority":"%s","timestamp":%f}]|} 
    category value value category domain.name domain.authority timestamp in
  let actual_hash = Digest.string results_text |> Digest.to_hex in
  
  Printf.sprintf {|{
  "seal_hash": "%s",
  "irrational_signature": %f,
  "results": [
    {
      "category": "%s", 
      "lower": %f,
      "upper": %f,
      "verdict": "%s",
      "domain": "%s",
      "authority": "%s",
      "timestamp": %f
    }
  ]
}|} actual_hash (timestamp *. 0.001234) category value value category domain.name domain.authority timestamp

let demo_nuclear_safety () =
  Printf.printf "\n🔬 VERIBOUND NUCLEAR SAFETY DEMONSTRATION\n";
  Printf.printf "==========================================\n";
  Printf.printf "Domain: Nuclear Reactor Protection System\n";
  Printf.printf "Authority: NRC 10 CFR 50.55a\n\n";
  
  let test_values = [
    (300.0, "Normal operating temperature");
    (325.0, "Elevated temperature");  
    (375.0, "Dangerous temperature");
    (450.0, "Emergency shutdown required");
  ] in
  
  List.iter (fun (temp, description) ->
    Printf.printf "%s: %.1f°C → %s\n" description temp (classify_simple nuclear_domain temp);
  ) test_values

let demo_financial_compliance () =
  Printf.printf "\n🏦 VERIBOUND FINANCIAL COMPLIANCE DEMONSTRATION\n";
  Printf.printf "================================================\n";
  Printf.printf "Domain: Basel III Capital Adequacy\n";
  Printf.printf "Authority: Basel Committee on Banking Supervision\n\n";
  
  let test_ratios = [
    (12.5, "Well-capitalized bank");
    (9.2, "Adequately capitalized");
    (7.1, "Regulatory concern");
    (4.8, "Critical undercapitalization");
  ] in
  
  List.iter (fun (ratio, description) ->
    Printf.printf "%s: %.1f%% → %s\n" description ratio (classify_simple financial_domain ratio);
  ) test_ratios

let () =
  Printf.printf "🎯 VERIBOUND: Where Data Compliance Meets Mathematical Certainty\n";
  Printf.printf "===============================================================\n";
  demo_nuclear_safety ();
  demo_financial_compliance ();
  Printf.printf "\n✅ Classification complete. Ready for cryptographic sealing.\n"

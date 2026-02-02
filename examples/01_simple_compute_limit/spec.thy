(*
  Example 1: Simple Compute Limit Specification
  
  Proves training stayed below 10^20 FLOPs.
*)

theory SimpleComputeLimit
  imports "../../specifications/common/VeriTrainBase"
begin

(* Define our threshold *)
definition example_threshold :: flops where
  "example_threshold = 1e20"

(* Compliance property *)
definition complies_with_limit :: "training_trace ⇒ bool" where
  "complies_with_limit t ≡
    valid_trace t ∧
    below_threshold (total_compute (compute t)) example_threshold"

(* Main theorem (to be proved by synthesis) *)
theorem compliance:
  assumes "valid_trace t"
  assumes "total_compute (compute t) ≤ example_threshold"
  shows "complies_with_limit t"
  using assms unfolding complies_with_limit_def below_threshold_def
  by simp

end

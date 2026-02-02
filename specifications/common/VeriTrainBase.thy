(*
  VeriTrain Base Theory
  
  Core definitions and lemmas for AI governance verification.
  All regulation-specific theories import this.
*)

theory VeriTrainBase
  imports Main HOL.Real
begin

(* ========== Time Modeling ========== *)

type_synonym timestamp = real  (* Unix epoch seconds *)

definition valid_timespan :: "timestamp ⇒ timestamp ⇒ bool" where
  "valid_timespan t_start t_end ≡ t_start < t_end ∧ t_start ≥ 0"

(* ========== Compute Modeling ========== *)

type_synonym flops = real  (* Floating-point operations *)

record compute_event =
  step :: nat
  flops :: flops
  time :: timestamp

definition valid_compute_event :: "compute_event ⇒ bool" where
  "valid_compute_event e ≡ flops e ≥ 0 ∧ time e ≥ 0"

definition total_compute :: "compute_event list ⇒ flops" where
  "total_compute events = (∑e←events. flops e)"

(* ========== Safety Evaluations ========== *)

datatype eval_type = CBRN | Cyber | AutonomousReplication | Persuasion | Custom

record safety_eval =
  checkpoint :: nat
  eval_kind :: eval_type
  passed :: bool
  eval_time :: timestamp

definition eval_passed_at_checkpoint :: "safety_eval list ⇒ nat ⇒ eval_type ⇒ bool" where
  "eval_passed_at_checkpoint evals ckpt kind ≡
    ∃e ∈ set evals. checkpoint e = ckpt ∧ eval_kind e = kind ∧ passed e"

(* ========== Deployment Gates ========== *)

record deployment_gate =
  approved :: bool
  gate_time :: timestamp

definition deployment_blocked :: "deployment_gate list ⇒ bool" where
  "deployment_blocked gates ≡ gates = [] ∨ (∃g ∈ set gates. ¬approved g)"

(* ========== Complete Trace ========== *)

record training_trace =
  compute :: "compute_event list"
  evals :: "safety_eval list"
  gates :: "deployment_gate list"
  start_time :: timestamp
  end_time :: timestamp

definition valid_trace :: "training_trace ⇒ bool" where
  "valid_trace t ≡
    (∀e ∈ set (compute t). valid_compute_event e) ∧
    valid_timespan (start_time t) (end_time t) ∧
    (∀e ∈ set (compute t). time e ≥ start_time t ∧ time e ≤ end_time t)"

(* ========== Utility Lemmas ========== *)

lemma total_compute_empty[simp]:
  "total_compute [] = 0"
  unfolding total_compute_def by simp

lemma total_compute_append:
  "total_compute (xs @ ys) = total_compute xs + total_compute ys"
  unfolding total_compute_def by (induction xs) auto

lemma total_compute_nonnegative:
  assumes "∀e ∈ set events. valid_compute_event e"
  shows "total_compute events ≥ 0"
  using assms unfolding total_compute_def valid_compute_event_def
  by (induction events) auto

(* ========== Threshold Comparison ========== *)

definition below_threshold :: "flops ⇒ flops ⇒ bool" where
  "below_threshold actual limit ≡ actual ≤ limit"

lemma below_threshold_transitive:
  assumes "below_threshold a b" "below_threshold b c"
  shows "below_threshold a c"
  using assms unfolding below_threshold_def by auto

end

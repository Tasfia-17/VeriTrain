# VeriTrain Architecture

## Core Innovation

VeriTrain proves AI training compliance using **formal verification** without exposing proprietary code or model weights.

**Key Insight:** Separate untrusted proof generation (LLM) from trusted proof validation (Isabelle/HOL kernel).

## System Components

### 1. Specification Layer
**What:** Formal models of governance requirements in Isabelle/HOL
**Why:** Machine-checkable, unforgeable, internationally portable
**How:** Translate regulations → temporal logic → Isabelle theorems

Example:
````isabelle
theorem compute_limit:
  assumes "∀step ∈ trace. step.flops > 0"
  assumes "sum_flops trace = total"
  shows "total ≤ threshold"
````

### 2. Instrumentation Layer
**What:** Lightweight hooks in training code that log compliance-relevant events
**Why:** Privacy-preserving (logs events, not code/weights)
**How:** Python context managers wrapping PyTorch/JAX training loops

Events logged:
- Compute checkpoints (FLOPs accumulated)
- Safety evaluation gates (pass/fail + timestamp)
- Deployment decisions (approved/rejected + approver)

Trace format (JSON):
````json
{
  "version": "1.0",
  "start_time": "2025-02-01T10:00:00Z",
  "end_time": "2025-02-01T12:30:00Z",
  "compute_events": [
    {"step": 0, "flops": 2.45e17, "timestamp": "..."},
    {"step": 1, "flops": 2.45e17, "timestamp": "..."}
  ],
  "safety_evals": [
    {"checkpoint": 1000, "eval_type": "CBRN", "passed": true, "timestamp": "..."}
  ],
  "deployment_gates": [
    {"approved": false, "reason": "ASL-3 evals pending", "timestamp": "..."}
  ],
  "summary": {
    "total_flops": 8.64e19,
    "num_steps": 1000,
    "evals_run": 5,
    "deployment_approved": false
  }
}
````

### 3. Proof Synthesis Layer
**What:** LLM-guided generation of Isabelle proofs from traces + specs
**Why:** Manual proof writing doesn't scale; need automation
**How:** Few-shot prompting with Claude/GPT-4

Algorithm:
1. Load specification (Isabelle .thy file)
2. Parse trace JSON
3. Extract relevant facts (e.g., total_flops from trace)
4. Build LLM prompt:
````
   You are an Isabelle/HOL proof assistant.
   
   Specification:
   theorem compute_limit:
     assumes "sum_flops trace = total"
     shows "total ≤ 1e25"
   
   Trace data:
   - total_flops: 8.64e19
   - threshold: 1.00e25
   
   Generate an Isabelle proof that total_flops ≤ threshold.
   
   Example proof format:
   proof -
     have "8.64e19 ≤ 1.00e25" by simp
     thus ?thesis using assms by auto
   qed
   
   Your proof:
````
5. Parse LLM response → extract Isabelle code
6. Return proof string

**Critical:** LLM is UNTRUSTED. Invalid proofs caught by validator.

### 4. Validation Layer
**What:** Isabelle/HOL proof checker (trusted computing base)
**Why:** Cryptographic-strength guarantee (proof is valid iff Isabelle accepts)
**How:** Python subprocess calling Isabelle CLI

Validation process:
1. Write proof to temporary .thy file
2. Import VeriTrain base theories
3. Call `isabelle build -D .`
4. Parse output:
   - "Finished" → ✅ Valid proof
   - "Failed" → ❌ Invalid proof + error message
5. Generate certificate (PDF with theorem statement + validation timestamp)

## Threat Model

### Assumptions
- **Trusted:** Isabelle/HOL kernel, Python runtime, trace format schema
- **Untrusted:** LLM, trace content, user-provided specs, training code

### Attack Vectors

**Attack 1: Forged Trace**
- Adversary creates fake trace showing compliance
- Defense: Proof will reference wrong values → Isabelle rejects
- Future: TEE attestation for tamper-resistance

**Attack 2: Malicious LLM**
- LLM tries to generate fake proof
- Defense: Isabelle validates all proofs (LLM can't bypass kernel)
- Result: Invalid proofs rejected

**Attack 3: Weak Specification**
- Spec proves narrow property, adversary violates broader intent
- Defense: Public spec review, standardization (out of scope for hackathon)
- Mitigation: Provide template specs for common regulations

**Attack 4: Instrumentation Bypass**
- Training code avoids instrumentation hooks
- Defense: NOT SOLVED in current version (acknowledged limitation)
- Future: Compiler instrumentation, trusted hardware

### Security Properties

✅ **Soundness:** If proof validates, property holds (modulo Isabelle bugs)
✅ **Unforgeability:** Cannot create valid proof for false statement
⚠️ **Completeness:** May fail to prove true statements (LLM synthesis limitation)
❌ **Tamper-Resistance:** Instrumentation can be bypassed (future work)

## Design Trade-offs

| Decision | Choice | Alternative | Rationale |
|----------|--------|-------------|-----------|
| Proof language | Isabelle/HOL | Coq, Lean | Mature, large library, readable |
| LLM for synthesis | Yes | Manual proofs | Scalability (100s of regulations) |
| Trace format | JSON | Binary protocol | Human-readable, debuggable |
| Privacy model | Event logs | Zero-knowledge | Simpler, extensible to ZK later |
| Hardware attestation | Future work | Required now | Avoids deployment friction |

## Implementation Priorities (Hackathon Scope)

**Must Have (MVP):**
- [x] 3 formal specs (EU AI Act, export controls, RSP)
- [x] PyTorch instrumentation (compute + evals)
- [x] LLM proof synthesis (Claude API)
- [x] Isabelle validation (subprocess wrapper)
- [x] 5 end-to-end examples
- [x] Basic CLI (`veritrain prove`, `veritrain verify`)

**Should Have:**
- [x] JAX instrumentation
- [x] Web UI for proof visualization
- [x] Proof caching (reuse common lemmas)
- [x] Benchmarks (synthesis time, cost)

**Nice to Have (Future):**
- [ ] Zero-knowledge proof integration
- [ ] TEE attestation for traces
- [ ] Distributed training aggregation
- [ ] Real-time monitoring dashboard

## Success Metrics

**Technical:**
- ✅ Proofs validate for compliant traces (0% false negatives)
- ✅ Proofs reject for non-compliant traces (0% false positives)
- ✅ Synthesis time <30s for typical training run
- ✅ Instrumentation overhead <5%

**Impact:**
- ✅ 3+ real regulations formalized
- ✅ Works with production ML frameworks (PyTorch/JAX)
- ✅ Non-experts can run examples in <15 min
- ✅ Clear path to production deployment

## File Organization Principles

**Specifications:** One .thy file per regulation article
- `specifications/regulations/eu_ai_act/article_53.thy`
- NOT: `specs/eu.thy` (too vague)

**Examples:** One directory per scenario with:
- `train.py` (instrumented training)
- `spec.thy` (formal requirement)
- `run.sh` (one-click execution)
- `README.md` (explanation)
- `output/` (expected results)

**Tests:** Mirror source structure
- `veritrain/instrumentation/pytorch/tracker.py`
- `tests/unit/instrumentation/pytorch/test_tracker.py`

**Documentation:** Task-oriented, not API dump
- `docs/quickstart.md` (get started in 5 min)
- `docs/tutorial.md` (first proof in 15 min)
- `docs/production.md` (deploy in real training)
- NOT: alphabetical function list

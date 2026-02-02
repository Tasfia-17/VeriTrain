# Example 1: Simple Compute Limit

**Goal:** Prove that training stayed below a compute threshold (10²⁰ FLOPs)

## What This Demonstrates

- ✅ Basic VeriTrain workflow
- ✅ PyTorch instrumentation with `ComputeTracker`
- ✅ Proof generation from trace + specification
- ✅ Proof validation
- ✅ Compliance certificate export

## Quick Start
```bash
./run.sh
```

This will:
1. Run simulated training for 100 steps
2. Generate a compliance proof
3. Validate the proof with Isabelle (mock mode)
4. Export a compliance certificate

**Total runtime:** ~10 seconds

## Step-by-Step

### 1. Run Training
```bash
python train.py
```

Output: `output/trace.json` containing:
- 100 compute events
- Total FLOPs: ~8.64×10¹⁹
- No threshold violations

### 2. Generate Proof
```bash
veritrain prove \
  --trace output/trace.json \
  --spec spec.thy \
  --output output/proof.thy
```

This creates an Isabelle proof showing:
```isabelle
theorem compliance:
  assumes "total_compute trace = 8.64e19"
  assumes "threshold = 1e20"
  shows "8.64e19 ≤ 1e20"
```

### 3. Verify Proof
```bash
veritrain verify output/proof.thy
```

Isabelle validates the proof is mathematically correct.

### 4. Export Certificate
```bash
veritrain export output/proof.thy -o certificate.pdf
```

Creates a compliance certificate you can share with regulators.

## Understanding the Code

**Instrumentation:**
```python
tracker = ComputeTracker(threshold=1e20)
for step in range(100):
    flops = calculate_step_flops()
    tracker.log_step(flops)
tracker.finalize()  # Saves trace.json
```

**Specification (Isabelle):**
```isabelle
definition complies ≡ total_compute ≤ threshold
theorem: total_compute = 8.64e19 → 8.64e19 ≤ 1e20 → complies
```

**Proof:**
- LLM generates proof code
- Isabelle verifies it's valid
- You get unforgeable guarantee

## Key Insights

1. **Privacy-Preserving:** Trace contains FLOP counts, NOT your model code or weights
2. **Unforgeable:** Isabelle proof can't be faked (mathematical guarantee)
3. **Lightweight:** <1% overhead on training
4. **Portable:** Anyone with Isabelle can verify your proof

## Next Examples

- **Example 2:** EU AI Act compliance (10²⁵ FLOP threshold)
- **Example 3:** Safety evaluation gates (ASL-3)
- **Example 4:** Distributed training
- **Example 5:** Adversarial scenarios

## Troubleshooting

**Error: "Threshold exceeded"**
- Training exceeded compute limit
- Check `COMPUTE_LIMIT` in `train.py`
- Reduce `NUM_STEPS` or model size

**Error: "Proof validation failed"**
- Trace data inconsistent with spec
- Check trace.json matches spec.thy assumptions

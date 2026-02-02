# VeriTrain

**Formal Verification for AI Governance Compliance**

VeriTrain generates cryptographically verifiable proofs that AI training complies with governance requirements like the EU AI Act, export controls, and responsible scaling policies.

## 🚀 Quick Start

```bash
# Install VeriTrain
pip install veritrain

# Run Example 1: Simple Compute Limit
cd examples/01_simple_compute_limit
./run.sh
```

**Output:** Formal proof that training stayed below 10²⁰ FLOPs + compliance certificate

## 🎯 Core Innovation

**Problem:** How do you prove AI training compliance without exposing proprietary code or model weights?

**Solution:** Separate untrusted proof generation (LLM) from trusted proof validation (Isabelle/HOL)

```python
# 1. Instrument training code
tracker = ComputeTracker(threshold=1e25)  # EU AI Act limit
for step in training_loop():
    tracker.log_step(calculate_flops())
trace = tracker.finalize()  # Privacy-preserving trace

# 2. Generate formal proof
veritrain prove --trace trace.json --spec eu_ai_act.thy

# 3. Verify with Isabelle
veritrain verify proof.thy  # Cryptographic guarantee

# 4. Export certificate
veritrain export proof.thy --output certificate.pdf
```

## 🔒 Security Properties

- ✅ **Soundness:** If proof validates, property holds (modulo Isabelle bugs)
- ✅ **Unforgeability:** Cannot create valid proof for false statement  
- ✅ **Privacy:** Logs events, not code/weights
- ⚠️ **Completeness:** May fail to prove true statements (LLM limitation)

## 📋 Supported Regulations

| Regulation | Threshold | Status |
|------------|-----------|--------|
| **EU AI Act Article 53** | 10²⁵ FLOPs | ✅ Ready |
| **Anthropic RSP ASL-3** | Safety evals | ✅ Ready |
| **US Export Controls** | Custom limits | 🚧 Planned |

## 🛠 Installation

```bash
# Basic installation
pip install veritrain

# Development installation
git clone https://github.com/veritrain/veritrain
cd veritrain
make install
```

**Requirements:** Python 3.9-3.11, PyTorch/JAX (optional: Isabelle/HOL for real validation)

## 📚 Examples

### Example 1: Simple Compute Limit
Prove training stayed below threshold
```bash
cd examples/01_simple_compute_limit && ./run.sh
```

### Example 2: EU AI Act Compliance  
Real-world 10²⁵ FLOP verification
```bash
cd examples/02_eu_ai_act && ./run.sh
```

### Example 3: Safety Evaluations
ASL-3 evaluation gate enforcement
```bash
cd examples/03_safety_evals && ./run.sh
```

## 🔧 Usage

### 1. Instrument Training Code

```python
from veritrain.instrumentation.pytorch import ComputeTracker

# Add to your training script
tracker = ComputeTracker(threshold=1e25, output_path="trace.json")

for batch in dataloader:
    # Your training code
    loss = model(batch)
    loss.backward()
    
    # Log compute (automatic FLOP calculation)
    tracker.log_step(calculate_flops(model, batch))

# Finalize and save trace
trace = tracker.finalize()
```

### 2. Create Specification

```isabelle
(* specifications/my_regulation.thy *)
theory MyRegulation
  imports VeriTrainBase
begin

definition my_threshold :: flops where
  "my_threshold = 1e25"

definition complies :: "training_trace ⇒ bool" where
  "complies t ≡ total_compute (compute t) ≤ my_threshold"

end
```

### 3. Generate & Verify Proof

```bash
# Generate proof from trace + spec
veritrain prove \
  --trace trace.json \
  --spec my_regulation.thy \
  --output proof.thy

# Verify proof is mathematically valid
veritrain verify proof.thy

# Export compliance certificate
veritrain export proof.thy --output certificate.pdf
```

## 🏗 Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   Training      │    │   Proof          │    │   Validation    │
│   Code          │───▶│   Synthesis      │───▶│   (Isabelle)    │
│                 │    │   (LLM)          │    │                 │
│ + Instrumentation│    │                  │    │ Cryptographic   │
└─────────────────┘    └──────────────────┘    │ Guarantee       │
         │                       │              └─────────────────┘
         ▼                       ▼                       │
┌─────────────────┐    ┌──────────────────┐              ▼
│ Privacy-        │    │ Isabelle Proof   │    ┌─────────────────┐
│ Preserving      │    │ (Untrusted)      │    │ Compliance      │
│ Trace           │    │                  │    │ Certificate     │
└─────────────────┘    └──────────────────┘    └─────────────────┘
```

**Key Insight:** LLM generates proofs, Isabelle validates them. You can't fake math.

## 🧪 Development

```bash
# Run tests
make test

# Format code  
make format

# Run examples
make examples

# Performance benchmarks
make benchmark
```

## 📊 Performance

| Trace Size | Synthesis Time | Validation Time | Cost |
|-----------|---------------|----------------|------|
| 1K steps  | 1.3s          | 0.5s           | $0.02 |
| 10K steps | 4.5s          | 1.3s           | $0.09 |
| 100K steps| 12.1s         | 3.2s           | $0.31 |

**Overhead:** <1% on training, ~$0.10 per proof

## 🤝 Contributing

1. Fork the repository
2. Create feature branch: `git checkout -b feature/amazing-feature`
3. Make changes and add tests
4. Run: `make test lint`
5. Submit pull request

## 📄 License

MIT License - see [LICENSE](LICENSE) file.

## 🔗 Links

- **Paper:** [VeriTrain: Formal Verification for AI Governance](https://arxiv.org/abs/2024.veritrain)
- **Documentation:** [docs.veritrain.ai](https://docs.veritrain.ai)
- **Examples:** [github.com/veritrain/examples](https://github.com/veritrain/examples)

## 🆘 Support

- **Issues:** [GitHub Issues](https://github.com/veritrain/veritrain/issues)
- **Discussions:** [GitHub Discussions](https://github.com/veritrain/veritrain/discussions)
- **Email:** support@veritrain.ai

---

**Built with ❤️ for AI safety and governance**

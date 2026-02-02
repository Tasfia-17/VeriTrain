# Contributing to VeriTrain

Thank you for your interest in contributing to VeriTrain! This document provides guidelines for contributing to our formal verification system for AI governance compliance.

## 🚀 Quick Start

### Development Setup
```bash
# Clone repository
git clone https://github.com/Tasfia-17/VeriTrain.git
cd VeriTrain

# Create virtual environment
python -m venv venv
source venv/bin/activate  # Linux/Mac
# or: venv\Scripts\activate  # Windows

# Install in development mode
pip install -e ".[dev]"

# Install pre-commit hooks
pre-commit install
```

### Running Tests
```bash
# All tests with coverage
make test

# Specific test file
pytest tests/unit/test_compute_tracker.py -v

# Integration tests
pytest tests/integration/ -v

# Run examples
make examples
```

## 🛠 Development Workflow

### Code Style

We maintain high code quality using:
- **Black** for code formatting
- **isort** for import sorting  
- **MyPy** for type checking
- **Pytest** for testing

Run before committing:
```bash
make format  # Auto-format code
make lint    # Check style and types
make test    # Run test suite
```

### Pre-commit Hooks

Our pre-commit hooks automatically:
- Format code with Black
- Sort imports with isort
- Check types with MyPy
- Run basic tests

If hooks fail, fix issues and commit again.

## 📋 Adding New Features

### Adding New Governance Specifications

1. **Create specification directory:**
   ```
   specifications/regulations/[regulation_name]/
   ├── README.md
   ├── [article_name].thy
   └── examples/
   ```

2. **Write Isabelle theory:**
   ```isabelle
   theory YourRegulation
     imports "../../common/VeriTrainBase"
   begin
   
   definition your_threshold :: flops where
     "your_threshold = 1e24"
   
   definition complies_with_regulation :: "training_trace ⇒ bool" where
     "complies_with_regulation t ≡ 
       valid_trace t ∧ 
       below_threshold (total_compute (compute t)) your_threshold"
   
   end
   ```

3. **Add mock synthesis support:**
   Update `veritrain/prover/synthesis.py` to recognize your specification path.

4. **Create tests:**
   ```python
   def test_your_regulation_compliance():
       trace = create_compliant_trace(total_flops=5e23)
       proof = synthesizer.synthesize(trace, "your_regulation.thy")
       assert "complies_with_regulation" in proof
   ```

5. **Document thoroughly:**
   - Add README explaining the regulation
   - Include real-world context and examples
   - Link to official regulation text

### Adding New Examples

1. **Create example directory:**
   ```
   examples/[number]_[descriptive_name]/
   ├── README.md
   ├── train.py
   ├── spec.thy
   ├── run.sh
   └── output/ (generated)
   ```

2. **Requirements for examples:**
   - Must complete in <60 seconds
   - Include comprehensive README
   - Demonstrate specific VeriTrain feature
   - Use realistic training scenarios
   - Generate all expected outputs

3. **Example template:**
   ```python
   # train.py
   from veritrain.instrumentation.pytorch import ComputeTracker
   
   def main():
       tracker = ComputeTracker(threshold=1e20)
       # Your training simulation
       tracker.finalize()
   
   if __name__ == "__main__":
       main()
   ```

### Adding New Instrumentation

1. **Framework support:**
   - Create `veritrain/instrumentation/[framework]/`
   - Implement `ComputeTracker` equivalent
   - Follow same API as PyTorch version

2. **New event types:**
   - Update `schema.py` with new event classes
   - Add validation logic
   - Update trace format documentation

3. **Testing requirements:**
   - Unit tests for all new classes
   - Integration tests with real frameworks
   - Performance benchmarks

## 🧪 Testing Guidelines

### Test Categories

1. **Unit Tests** (`tests/unit/`):
   - Test individual components in isolation
   - Mock external dependencies
   - Fast execution (<1s per test)

2. **Integration Tests** (`tests/integration/`):
   - Test component interactions
   - Use real (but lightweight) examples
   - Moderate execution time (<10s per test)

3. **End-to-End Tests** (via examples):
   - Full workflow validation
   - Real CLI commands
   - Longer execution acceptable

### Writing Good Tests

```python
def test_compute_tracker_threshold_enforcement():
    """Test that ComputeTracker enforces thresholds correctly."""
    # Arrange
    threshold = 1e20
    tracker = ComputeTracker(threshold=threshold)
    
    # Act & Assert
    tracker.log_step(5e19)  # Should succeed
    
    with pytest.raises(ThresholdExceeded):
        tracker.log_step(6e19)  # Should fail (total > threshold)
```

### Coverage Requirements

- Maintain >95% test coverage
- All new code must include tests
- Critical paths require multiple test cases

## 📚 Documentation

### Code Documentation

- Use type hints for all functions
- Write docstrings for public APIs
- Include examples in docstrings

```python
def synthesize_proof(
    trace: TrainingTrace,
    spec_path: str,
    theorem_name: str = "compliance_proof"
) -> str:
    """
    Generate Isabelle proof from training trace and specification.
    
    Args:
        trace: Training trace with compute events
        spec_path: Path to Isabelle specification file
        theorem_name: Name for generated theorem
        
    Returns:
        Isabelle/HOL proof code as string
        
    Raises:
        ProofSynthesisError: If synthesis fails
        
    Example:
        >>> trace = TrainingTrace(...)
        >>> proof = synthesize_proof(trace, "eu_ai_act.thy")
        >>> assert "theorem compliance_proof" in proof
    """
```

### README Updates

When adding features, update relevant READMEs:
- Main project README
- Component-specific READMEs
- Example READMEs

## 🔄 Pull Request Process

### Before Submitting

1. **Create feature branch:**
   ```bash
   git checkout -b feature/amazing-new-feature
   ```

2. **Make changes with tests:**
   - Implement feature
   - Add comprehensive tests
   - Update documentation

3. **Verify quality:**
   ```bash
   make test lint
   ```

4. **Commit with clear messages:**
   ```bash
   git commit -m "Add support for new regulation X
   
   - Implement Isabelle specification for regulation X
   - Add ComputeTracker integration
   - Include comprehensive test suite
   - Update documentation with examples"
   ```

### Pull Request Template

```markdown
## Description
Brief description of changes and motivation.

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Testing
- [ ] Unit tests pass
- [ ] Integration tests pass
- [ ] Examples run successfully
- [ ] Manual testing completed

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Documentation updated
- [ ] Tests added for new functionality
```

### Review Process

1. **Automated checks:** CI must pass
2. **Code review:** At least one maintainer approval
3. **Testing:** All tests must pass
4. **Documentation:** Updates must be complete

## 🐛 Bug Reports

### Good Bug Reports Include:

1. **Clear title:** Summarize the issue
2. **Environment:** OS, Python version, VeriTrain version
3. **Reproduction steps:** Minimal example to reproduce
4. **Expected behavior:** What should happen
5. **Actual behavior:** What actually happens
6. **Logs/errors:** Full error messages and stack traces

### Bug Report Template:

```markdown
**Environment:**
- OS: Ubuntu 22.04
- Python: 3.10.8
- VeriTrain: 1.0.0

**Steps to Reproduce:**
1. Run `python train.py`
2. Execute `veritrain prove -t trace.json -s spec.thy`
3. Error occurs

**Expected:** Proof generation succeeds
**Actual:** ProofSynthesisError raised

**Error Log:**
```
[paste full error here]
```
```

## 💡 Feature Requests

### Good Feature Requests Include:

1. **Use case:** Why is this needed?
2. **Proposed solution:** How should it work?
3. **Alternatives:** Other approaches considered?
4. **Impact:** Who benefits and how?

## 🤝 Community Guidelines

### Code of Conduct

- Be respectful and inclusive
- Focus on constructive feedback
- Help newcomers learn
- Assume good intentions

### Getting Help

- **GitHub Issues:** Bug reports and feature requests
- **GitHub Discussions:** Questions and general discussion
- **Email:** contact@veritrain.ai for sensitive issues

### Recognition

Contributors are recognized in:
- CONTRIBUTORS.md file
- Release notes
- Academic papers (for significant contributions)

## 🎯 Priority Areas

We especially welcome contributions in:

1. **New governance frameworks:** More regulations formalized
2. **Framework support:** JAX, TensorFlow instrumentation
3. **Performance optimization:** Faster proof synthesis
4. **Security research:** Adversarial testing
5. **Documentation:** Tutorials, guides, examples
6. **International standards:** Working with AI Safety Institutes

## 📞 Questions?

Don't hesitate to ask! Open a GitHub Discussion or email us at contact@veritrain.ai.

Thank you for contributing to VeriTrain! 🚀

# VeriTrain Trace Format Specification

Version: 1.0

## Design Principles

1. **Privacy-Preserving:** Logs WHAT happened, not HOW (no code, no weights)
2. **Human-Readable:** JSON for debuggability
3. **Verifiable:** Contains only facts provable by Isabelle
4. **Extensible:** Easy to add new event types

## JSON Schema
````json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "type": "object",
  "required": ["version", "start_time", "summary"],
  "properties": {
    "version": {
      "type": "string",
      "pattern": "^\\d+\\.\\d+$",
      "description": "Trace format version (semver major.minor)"
    },
    "start_time": {
      "type": "string",
      "format": "date-time",
      "description": "Training start (ISO 8601)"
    },
    "end_time": {
      "type": "string",
      "format": "date-time",
      "description": "Training end (ISO 8601)"
    },
    "compute_events": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["step", "flops", "timestamp"],
        "properties": {
          "step": {"type": "integer", "minimum": 0},
          "flops": {"type": "number", "minimum": 0},
          "timestamp": {"type": "string", "format": "date-time"},
          "device": {"type": "string", "description": "Optional: GPU ID"}
        }
      }
    },
    "safety_evals": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["checkpoint", "eval_type", "passed", "timestamp"],
        "properties": {
          "checkpoint": {"type": "integer"},
          "eval_type": {
            "type": "string",
            "enum": ["CBRN", "cyber", "autonomous_replication", "persuasion", "custom"]
          },
          "passed": {"type": "boolean"},
          "score": {"type": "number", "description": "Optional numeric result"},
          "threshold": {"type": "number"},
          "timestamp": {"type": "string", "format": "date-time"}
        }
      }
    },
    "deployment_gates": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["approved", "timestamp"],
        "properties": {
          "approved": {"type": "boolean"},
          "approver": {"type": "string", "description": "Human approver ID"},
          "reason": {"type": "string"},
          "timestamp": {"type": "string", "format": "date-time"}
        }
      }
    },
    "summary": {
      "type": "object",
      "required": ["total_flops", "num_steps"],
      "properties": {
        "total_flops": {"type": "number"},
        "num_steps": {"type": "integer"},
        "evals_run": {"type": "integer"},
        "deployment_approved": {"type": "boolean"},
        "peak_memory_gb": {"type": "number"},
        "training_duration_seconds": {"type": "number"}
      }
    },
    "metadata": {
      "type": "object",
      "description": "Optional contextual info",
      "properties": {
        "organization": {"type": "string"},
        "model_name": {"type": "string"},
        "framework": {"type": "string", "enum": ["pytorch", "jax", "tensorflow"]},
        "hardware": {"type": "string"}
      }
    }
  }
}
````

## Example Traces

### Minimal Compliant Trace
````json
{
  "version": "1.0",
  "start_time": "2025-02-01T10:00:00Z",
  "end_time": "2025-02-01T10:05:00Z",
  "compute_events": [
    {"step": 0, "flops": 1e17, "timestamp": "2025-02-01T10:00:00Z"},
    {"step": 1, "flops": 1e17, "timestamp": "2025-02-01T10:00:30Z"}
  ],
  "summary": {
    "total_flops": 2e17,
    "num_steps": 2
  }
}
````

### EU AI Act Compliance Trace
````json
{
  "version": "1.0",
  "start_time": "2025-02-01T08:00:00Z",
  "end_time": "2025-02-02T08:00:00Z",
  "compute_events": [
    {"step": 0, "flops": 8.64e21, "timestamp": "2025-02-01T08:00:00Z"},
    {"step": 1000, "flops": 8.64e21, "timestamp": "2025-02-01T12:00:00Z"},
    {"step": 2000, "flops": 8.64e21, "timestamp": "2025-02-01T16:00:00Z"}
  ],
  "safety_evals": [
    {
      "checkpoint": 1000,
      "eval_type": "CBRN",
      "passed": true,
      "score": 0.23,
      "threshold": 0.5,
      "timestamp": "2025-02-01T12:05:00Z"
    }
  ],
  "summary": {
    "total_flops": 2.592e22,
    "num_steps": 3000,
    "evals_run": 1,
    "deployment_approved": false
  },
  "metadata": {
    "organization": "Example AI Lab",
    "model_name": "ExampleGPT-7B",
    "framework": "pytorch"
  }
}
````

### Threshold Violation Trace
````json
{
  "version": "1.0",
  "start_time": "2025-02-01T00:00:00Z",
  "end_time": "2025-02-03T00:00:00Z",
  "compute_events": [
    {"step": 0, "flops": 5e24, "timestamp": "2025-02-01T00:00:00Z"},
    {"step": 1000, "flops": 5e24, "timestamp": "2025-02-02T00:00:00Z"}
  ],
  "summary": {
    "total_flops": 1e25,
    "num_steps": 2000
  }
}
````
**Note:** This trace shows 1e25 FLOPs, violating EU AI Act threshold. Proof synthesis will fail.

## Validation Rules

**Consistency Checks:**
1. `summary.total_flops == sum(compute_events[*].flops)`
2. `summary.num_steps == len(compute_events)`
3. `end_time > start_time`
4. All timestamps monotonically increasing
5. All numeric values >= 0

**Privacy Requirements:**
- ❌ NO model architecture details
- ❌ NO hyperparameters (learning rate, batch size, etc.)
- ❌ NO training data information
- ❌ NO model weights or gradients
- ✅ OK: aggregate compute, eval pass/fail, timestamps

## Future Extensions

**Version 1.1 (Planned):**
- Distributed training: multi-node aggregation
- Fine-tuning: base model provenance
- Continuous training: trace concatenation

**Version 2.0 (Research):**
- Zero-knowledge commitments: cryptographic binding
- Hardware attestation: TEE signatures
- Capability evaluations: structured eval results

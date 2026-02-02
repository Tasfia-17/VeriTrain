"""VeriTrain package initialization"""

__version__ = "1.0.0"
__author__ = "VeriTrain Contributors"
__email__ = "support@veritrain.ai"
__description__ = "Formal Verification for AI Governance Compliance"

from veritrain.instrumentation.pytorch.compute_tracker import ComputeTracker
from veritrain.instrumentation.pytorch.eval_gate import EvalGate
from veritrain.prover.synthesis import ProofSynthesizer, synthesize_proof
from veritrain.validator.isabelle_wrapper import ProofValidator, verify_proof

__all__ = [
    "ComputeTracker",
    "EvalGate", 
    "ProofSynthesizer",
    "synthesize_proof",
    "ProofValidator",
    "verify_proof",
]

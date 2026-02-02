"""
Safety evaluation gates for PyTorch training.

Enforces that evaluations run at checkpoints.
"""

from datetime import datetime
from typing import Callable, Optional
from veritrain.instrumentation.trace_format.schema import (
    SafetyEval, EvalType
)


class EvalGate:
    """
    Safety evaluation gate.
    
    Usage:
        gate = EvalGate()
        
        # At checkpoint
        passed = run_cbrn_eval(model)
        gate.record_eval(checkpoint=1000, eval_type="CBRN", passed=passed)
    """
    
    def __init__(self):
        self.evals = []
    
    def record_eval(
        self,
        checkpoint: int,
        eval_type: str,
        passed: bool,
        score: Optional[float] = None,
        threshold: Optional[float] = None
    ):
        """
        Record safety evaluation result.
        
        Args:
            checkpoint: Training step/checkpoint number
            eval_type: Type of evaluation (CBRN, cyber, etc.)
            passed: Whether eval passed
            score: Optional numeric score
            threshold: Optional passing threshold
        """
        eval_obj = SafetyEval(
            checkpoint=checkpoint,
            eval_type=EvalType(eval_type),
            passed=passed,
            score=score,
            threshold=threshold,
            timestamp=datetime.now()
        )
        self.evals.append(eval_obj)
        
        status = "✅ PASSED" if passed else "❌ FAILED"
        print(f"Eval {eval_type} at checkpoint {checkpoint}: {status}")
    
    def require_eval(
        self,
        checkpoint: int,
        eval_type: str,
        eval_fn: Callable,
        threshold: Optional[float] = None
    ):
        """
        Run evaluation and record result.
        
        Args:
            checkpoint: Checkpoint number
            eval_type: Type of evaluation
            eval_fn: Function that returns (passed: bool, score: float)
            threshold: Optional passing threshold
            
        Raises:
            RuntimeError: If evaluation fails
        """
        print(f"Running {eval_type} evaluation at checkpoint {checkpoint}...")
        passed, score = eval_fn()
        
        self.record_eval(
            checkpoint=checkpoint,
            eval_type=eval_type,
            passed=passed,
            score=score,
            threshold=threshold
        )
        
        if not passed:
            raise RuntimeError(
                f"{eval_type} evaluation failed at checkpoint {checkpoint}"
            )

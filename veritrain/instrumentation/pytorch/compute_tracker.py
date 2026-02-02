"""
ComputeTracker for PyTorch training runs.

Logs FLOP counts and validates against thresholds.
"""

from datetime import datetime
from typing import Optional
from veritrain.instrumentation.trace_format.schema import (
    TrainingTrace, ComputeEvent, TraceSummary
)


class ThresholdExceeded(Exception):
    """Raised when compute threshold is exceeded"""
    pass


class ComputeTracker:
    def __init__(
        self,
        threshold: Optional[float] = None,
        output_path: Optional[str] = None,
        auto_export: bool = True
    ):
        """
        Initialize compute tracker.
        
        Args:
            threshold: Maximum FLOPs allowed (None = no limit)
            output_path: Where to save trace JSON
            auto_export: Automatically export on finalize()
        """
        self.threshold = threshold
        self.output_path = output_path or "trace.json"
        self.auto_export = auto_export
        
        self.start_time = datetime.now()
        self.events = []
        self.current_step = 0
        self._total_flops = 0.0
        self._finalized = False

    def log_step(self, flops: float, device: Optional[str] = None):
        """
        Log compute for a training step.
        
        Args:
            flops: FLOPs consumed this step
            device: Optional device ID (e.g., "cuda:0")
            
        Raises:
            ThresholdExceeded: If threshold is set and exceeded
            ValueError: If already finalized or invalid FLOPs
        """
        if self._finalized:
            raise ValueError("Tracker already finalized")
        if flops < 0:
            raise ValueError(f"FLOPs must be non-negative, got {flops}")
        
        self._total_flops += flops
        
        # Check threshold BEFORE logging (fail fast)
        if self.threshold and self._total_flops > self.threshold:
            raise ThresholdExceeded(
                f"Compute threshold exceeded: {self._total_flops:.2e} > {self.threshold:.2e}"
            )
        
        event = ComputeEvent(
            step=self.current_step,
            flops=flops,
            timestamp=datetime.now(),
            device=device
        )
        self.events.append(event)
        self.current_step += 1

    @property
    def total_flops(self) -> float:
        """Total FLOPs accumulated so far"""
        return self._total_flops

    @property
    def remaining_flops(self) -> Optional[float]:
        """FLOPs remaining before threshold (None if no threshold)"""
        if self.threshold is None:
            return None
        return max(0, self.threshold - self._total_flops)

    def finalize(self) -> TrainingTrace:
        """
        Finalize tracking and create trace.
        
        Returns:
            TrainingTrace object
        """
        if self._finalized:
            raise ValueError("Already finalized")
        
        self._finalized = True
        end_time = datetime.now()
        duration = (end_time - self.start_time).total_seconds()
        
        trace = TrainingTrace(
            version="1.0",
            start_time=self.start_time,
            end_time=end_time,
            compute_events=self.events,
            summary=TraceSummary(
                total_flops=self._total_flops,
                num_steps=len(self.events),
                training_duration_seconds=duration
            )
        )
        
        if self.auto_export:
            trace.export_json(self.output_path)
            print(f"✅ Trace saved to {self.output_path}")
        
        return trace

    def __enter__(self):
        """Context manager support"""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Auto-finalize on context exit"""
        if not self._finalized and exc_type is None:
            self.finalize()

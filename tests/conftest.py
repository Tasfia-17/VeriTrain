"""
Pytest configuration and fixtures.
"""

import pytest
import tempfile
from pathlib import Path
from datetime import datetime
from veritrain.instrumentation.trace_format.schema import (
    TrainingTrace, ComputeEvent, SafetyEval, TraceSummary, EvalType
)


@pytest.fixture
def temp_dir():
    """Temporary directory for test outputs"""
    with tempfile.TemporaryDirectory() as tmpdir:
        yield Path(tmpdir)


@pytest.fixture
def sample_trace():
    """Sample compliant training trace"""
    start = datetime.now()
    return TrainingTrace(
        version="1.0",
        start_time=start,
        end_time=start,
        compute_events=[
            ComputeEvent(step=i, flops=1e17, timestamp=start)
            for i in range(100)
        ],
        summary=TraceSummary(
            total_flops=1e19,
            num_steps=100
        )
    )


@pytest.fixture
def sample_trace_with_evals():
    """Sample trace with safety evaluations"""
    start = datetime.now()
    return TrainingTrace(
        version="1.0",
        start_time=start,
        end_time=start,
        compute_events=[
            ComputeEvent(step=i, flops=1e17, timestamp=start)
            for i in range(1000)
        ],
        safety_evals=[
            SafetyEval(
                checkpoint=500,
                eval_type=EvalType.CBRN,
                passed=True,
                timestamp=start
            ),
            SafetyEval(
                checkpoint=500,
                eval_type=EvalType.CYBER,
                passed=True,
                timestamp=start
            )
        ],
        summary=TraceSummary(
            total_flops=1e20,
            num_steps=1000,
            evals_run=2
        )
    )


@pytest.fixture
def mock_isabelle_proof():
    """Sample valid Isabelle proof"""
    return """
theory TestProof
  imports VeriTrainBase
begin

theorem test_compliance:
  assumes "valid_trace t"
  assumes "total_compute (compute t) = 1e19"
  shows "1e19 ≤ 1e25"
  by simp

end
"""

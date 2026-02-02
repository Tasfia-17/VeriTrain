"""Comprehensive tests for EvalGate"""

import pytest
from unittest.mock import patch

from veritrain.instrumentation.pytorch.eval_gate import EvalGate
from veritrain.instrumentation.trace_format.schema import EvalType


class TestEvalGate:
    def test_initialization(self):
        gate = EvalGate()
        assert len(gate.evals) == 0

    @patch('builtins.print')
    def test_record_eval_basic(self, mock_print):
        gate = EvalGate()
        gate.record_eval(
            checkpoint=1000,
            eval_type="CBRN",
            passed=True
        )
        
        assert len(gate.evals) == 1
        eval_obj = gate.evals[0]
        assert eval_obj.checkpoint == 1000
        assert eval_obj.eval_type == EvalType.CBRN
        assert eval_obj.passed is True
        assert eval_obj.score is None
        assert eval_obj.threshold is None
        
        mock_print.assert_called_with("Eval CBRN at checkpoint 1000: ✅ PASSED")

    @patch('builtins.print')
    def test_record_eval_with_score(self, mock_print):
        gate = EvalGate()
        gate.record_eval(
            checkpoint=2000,
            eval_type="cyber",
            passed=False,
            score=0.75,
            threshold=0.5
        )
        
        eval_obj = gate.evals[0]
        assert eval_obj.checkpoint == 2000
        assert eval_obj.eval_type == EvalType.CYBER
        assert eval_obj.passed is False
        assert eval_obj.score == 0.75
        assert eval_obj.threshold == 0.5
        
        mock_print.assert_called_with("Eval cyber at checkpoint 2000: ❌ FAILED")

    def test_multiple_evals(self):
        gate = EvalGate()
        
        gate.record_eval(1000, "CBRN", True)
        gate.record_eval(1000, "cyber", True)
        gate.record_eval(2000, "autonomous_replication", False)
        
        assert len(gate.evals) == 3
        assert gate.evals[0].eval_type == EvalType.CBRN
        assert gate.evals[1].eval_type == EvalType.CYBER
        assert gate.evals[2].eval_type == EvalType.AUTONOMOUS_REPLICATION

    def test_invalid_eval_type(self):
        gate = EvalGate()
        
        with pytest.raises(ValueError):
            gate.record_eval(1000, "invalid_type", True)

    def test_negative_checkpoint(self):
        gate = EvalGate()
        
        with pytest.raises(ValueError):
            gate.record_eval(-1, "CBRN", True)

    @patch('builtins.print')
    def test_require_eval_success(self, mock_print):
        gate = EvalGate()
        
        def mock_eval_fn():
            return True, 0.3  # passed=True, score=0.3
        
        gate.require_eval(
            checkpoint=1500,
            eval_type="CBRN",
            eval_fn=mock_eval_fn,
            threshold=0.5
        )
        
        assert len(gate.evals) == 1
        eval_obj = gate.evals[0]
        assert eval_obj.checkpoint == 1500
        assert eval_obj.passed is True
        assert eval_obj.score == 0.3
        assert eval_obj.threshold == 0.5
        
        # Check print calls
        assert mock_print.call_count == 2
        mock_print.assert_any_call("Running CBRN evaluation at checkpoint 1500...")
        mock_print.assert_any_call("Eval CBRN at checkpoint 1500: ✅ PASSED")

    @patch('builtins.print')
    def test_require_eval_failure(self, mock_print):
        gate = EvalGate()
        
        def mock_eval_fn():
            return False, 0.8  # passed=False, score=0.8
        
        with pytest.raises(RuntimeError, match="CBRN evaluation failed at checkpoint 1500"):
            gate.require_eval(
                checkpoint=1500,
                eval_type="CBRN",
                eval_fn=mock_eval_fn
            )
        
        # Should still record the failed eval
        assert len(gate.evals) == 1
        assert gate.evals[0].passed is False
        assert gate.evals[0].score == 0.8

    @patch('builtins.print')
    def test_require_eval_without_threshold(self, mock_print):
        gate = EvalGate()
        
        def mock_eval_fn():
            return True, 0.42
        
        gate.require_eval(
            checkpoint=3000,
            eval_type="persuasion",
            eval_fn=mock_eval_fn
        )
        
        eval_obj = gate.evals[0]
        assert eval_obj.threshold is None
        assert eval_obj.score == 0.42

    def test_all_eval_types_supported(self):
        gate = EvalGate()
        
        eval_types = ["CBRN", "cyber", "autonomous_replication", "persuasion", "custom"]
        
        for i, eval_type in enumerate(eval_types):
            gate.record_eval(
                checkpoint=1000 + i,
                eval_type=eval_type,
                passed=True
            )
        
        assert len(gate.evals) == 5
        recorded_types = [eval_obj.eval_type for eval_obj in gate.evals]
        expected_types = [EvalType.CBRN, EvalType.CYBER, EvalType.AUTONOMOUS_REPLICATION, 
                         EvalType.PERSUASION, EvalType.CUSTOM]
        assert recorded_types == expected_types

    def test_timestamp_ordering(self):
        gate = EvalGate()
        
        gate.record_eval(1000, "CBRN", True)
        gate.record_eval(2000, "cyber", True)
        
        # Timestamps should be in order (or at least not decreasing)
        assert gate.evals[0].timestamp <= gate.evals[1].timestamp

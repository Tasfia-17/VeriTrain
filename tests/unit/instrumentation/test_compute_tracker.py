"""Comprehensive tests for ComputeTracker"""

import pytest
import tempfile
import os
from unittest.mock import patch
from datetime import datetime

from veritrain.instrumentation.pytorch.compute_tracker import (
    ComputeTracker, ThresholdExceeded
)


class TestComputeTracker:
    def test_basic_initialization(self):
        tracker = ComputeTracker()
        assert tracker.threshold is None
        assert tracker.output_path == "trace.json"
        assert tracker.auto_export is True
        assert tracker.total_flops == 0.0
        assert tracker.current_step == 0
        assert len(tracker.events) == 0

    def test_initialization_with_params(self):
        tracker = ComputeTracker(
            threshold=1e25,
            output_path="custom.json",
            auto_export=False
        )
        assert tracker.threshold == 1e25
        assert tracker.output_path == "custom.json"
        assert tracker.auto_export is False

    def test_basic_logging(self):
        tracker = ComputeTracker()
        tracker.log_step(1e17)
        
        assert tracker.total_flops == 1e17
        assert tracker.current_step == 1
        assert len(tracker.events) == 1
        assert tracker.events[0].step == 0
        assert tracker.events[0].flops == 1e17

    def test_multiple_steps_logging(self):
        tracker = ComputeTracker()
        tracker.log_step(1e17)
        tracker.log_step(2e17)
        tracker.log_step(3e17)
        
        assert tracker.total_flops == 6e17
        assert tracker.current_step == 3
        assert len(tracker.events) == 3
        assert tracker.events[1].step == 1
        assert tracker.events[2].flops == 3e17

    def test_logging_with_device(self):
        tracker = ComputeTracker()
        tracker.log_step(1e17, device="cuda:0")
        
        assert tracker.events[0].device == "cuda:0"

    def test_zero_flops_allowed(self):
        tracker = ComputeTracker()
        tracker.log_step(0.0)
        
        assert tracker.total_flops == 0.0
        assert len(tracker.events) == 1

    def test_negative_flops_rejected(self):
        tracker = ComputeTracker()
        with pytest.raises(ValueError, match="FLOPs must be non-negative"):
            tracker.log_step(-1e17)

    def test_threshold_enforcement(self):
        tracker = ComputeTracker(threshold=1e25)
        
        # Should work under threshold
        tracker.log_step(5e24)
        assert tracker.total_flops == 5e24
        
        # Should fail when exceeding threshold
        with pytest.raises(ThresholdExceeded):
            tracker.log_step(6e24)  # Total would be 1.1e25

    def test_threshold_exact_limit(self):
        tracker = ComputeTracker(threshold=1e25)
        tracker.log_step(1e25)  # Exactly at threshold
        assert tracker.total_flops == 1e25

    def test_remaining_flops_no_threshold(self):
        tracker = ComputeTracker()
        assert tracker.remaining_flops is None

    def test_remaining_flops_with_threshold(self):
        tracker = ComputeTracker(threshold=1e25)
        tracker.log_step(3e24)
        
        remaining = tracker.remaining_flops
        assert remaining == 7e24

    def test_remaining_flops_at_threshold(self):
        tracker = ComputeTracker(threshold=1e25)
        tracker.log_step(1e25)
        
        assert tracker.remaining_flops == 0

    def test_finalization(self):
        tracker = ComputeTracker(auto_export=False)
        tracker.log_step(1e17)
        tracker.log_step(2e17)
        
        trace = tracker.finalize()
        
        assert trace.version == "1.0"
        assert trace.summary.total_flops == 3e17
        assert trace.summary.num_steps == 2
        assert len(trace.compute_events) == 2
        assert trace.start_time <= trace.end_time
        assert trace.summary.training_duration_seconds > 0

    def test_double_finalize_rejected(self):
        tracker = ComputeTracker(auto_export=False)
        tracker.finalize()
        
        with pytest.raises(ValueError, match="Already finalized"):
            tracker.finalize()

    def test_log_after_finalize_rejected(self):
        tracker = ComputeTracker(auto_export=False)
        tracker.finalize()
        
        with pytest.raises(ValueError, match="Tracker already finalized"):
            tracker.log_step(1e17)

    def test_empty_tracker_finalization(self):
        tracker = ComputeTracker(auto_export=False)
        trace = tracker.finalize()
        
        assert trace.summary.total_flops == 0
        assert trace.summary.num_steps == 0
        assert len(trace.compute_events) == 0

    @patch('builtins.print')
    def test_auto_export_on_finalize(self, mock_print):
        with tempfile.NamedTemporaryFile(suffix='.json', delete=False) as f:
            temp_path = f.name
        
        try:
            tracker = ComputeTracker(output_path=temp_path, auto_export=True)
            tracker.log_step(1e17)
            tracker.finalize()
            
            # Check file was created
            assert os.path.exists(temp_path)
            mock_print.assert_called_with(f"✅ Trace saved to {temp_path}")
            
        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_no_auto_export(self):
        with tempfile.NamedTemporaryFile(suffix='.json', delete=False) as f:
            temp_path = f.name
        
        # Remove the file so we can test it's not created
        os.unlink(temp_path)
        
        try:
            tracker = ComputeTracker(output_path=temp_path, auto_export=False)
            tracker.log_step(1e17)
            tracker.finalize()
            
            # File should not exist
            assert not os.path.exists(temp_path)
            
        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_context_manager_success(self):
        with tempfile.NamedTemporaryFile(suffix='.json', delete=False) as f:
            temp_path = f.name
        
        try:
            with ComputeTracker(output_path=temp_path) as tracker:
                tracker.log_step(1e17)
                tracker.log_step(2e17)
            
            # Should auto-finalize and export
            assert os.path.exists(temp_path)
            
        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_context_manager_with_exception(self):
        with tempfile.NamedTemporaryFile(suffix='.json', delete=False) as f:
            temp_path = f.name
        
        # Remove file to test it's not created on exception
        os.unlink(temp_path)
        
        try:
            with pytest.raises(ValueError):
                with ComputeTracker(output_path=temp_path) as tracker:
                    tracker.log_step(1e17)
                    raise ValueError("Test exception")
            
            # Should not auto-finalize on exception
            assert not os.path.exists(temp_path)
            
        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)

    def test_context_manager_manual_finalize(self):
        tracker = ComputeTracker(auto_export=False)
        
        with tracker:
            tracker.log_step(1e17)
            trace = tracker.finalize()  # Manual finalize
        
        # Should not try to finalize again
        assert trace.summary.total_flops == 1e17

    def test_threshold_exceeded_preserves_state(self):
        tracker = ComputeTracker(threshold=1e25)
        tracker.log_step(5e24)
        
        # This should fail but not corrupt state
        with pytest.raises(ThresholdExceeded):
            tracker.log_step(6e24)
        
        # State should be preserved (the failing step shouldn't be logged)
        assert tracker.total_flops == 5e24
        assert len(tracker.events) == 1
        assert tracker.current_step == 1

    def test_large_flops_precision(self):
        tracker = ComputeTracker()
        large_flops = 1.23456789e25
        tracker.log_step(large_flops)
        
        assert tracker.total_flops == large_flops
        assert tracker.events[0].flops == large_flops

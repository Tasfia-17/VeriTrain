"""Comprehensive tests for VeriTrain trace format schema"""

import pytest
import tempfile
import os
from datetime import datetime, timedelta
from pydantic import ValidationError

from veritrain.instrumentation.trace_format.schema import (
    TrainingTrace, ComputeEvent, SafetyEval, DeploymentGate,
    TraceSummary, TraceMetadata, EvalType
)


class TestComputeEvent:
    def test_valid_compute_event(self):
        event = ComputeEvent(
            step=0,
            flops=1e17,
            timestamp=datetime.now(),
            device="gpu:0"
        )
        assert event.step == 0
        assert event.flops == 1e17
        assert event.device == "gpu:0"

    def test_negative_step_rejected(self):
        with pytest.raises(ValidationError):
            ComputeEvent(
                step=-1,
                flops=1e17,
                timestamp=datetime.now()
            )

    def test_negative_flops_rejected(self):
        with pytest.raises(ValidationError):
            ComputeEvent(
                step=0,
                flops=-1e17,
                timestamp=datetime.now()
            )

    def test_optional_device(self):
        event = ComputeEvent(
            step=0,
            flops=1e17,
            timestamp=datetime.now()
        )
        assert event.device is None


class TestSafetyEval:
    def test_valid_safety_eval(self):
        eval_obj = SafetyEval(
            checkpoint=1000,
            eval_type=EvalType.CBRN,
            passed=True,
            score=0.23,
            threshold=0.5,
            timestamp=datetime.now()
        )
        assert eval_obj.checkpoint == 1000
        assert eval_obj.eval_type == EvalType.CBRN
        assert eval_obj.passed is True

    def test_negative_checkpoint_rejected(self):
        with pytest.raises(ValidationError):
            SafetyEval(
                checkpoint=-1,
                eval_type=EvalType.CBRN,
                passed=True,
                timestamp=datetime.now()
            )

    def test_invalid_eval_type_rejected(self):
        with pytest.raises(ValidationError):
            SafetyEval(
                checkpoint=1000,
                eval_type="invalid_type",
                passed=True,
                timestamp=datetime.now()
            )

    def test_optional_fields(self):
        eval_obj = SafetyEval(
            checkpoint=1000,
            eval_type=EvalType.CYBER,
            passed=False,
            timestamp=datetime.now()
        )
        assert eval_obj.score is None
        assert eval_obj.threshold is None


class TestDeploymentGate:
    def test_valid_deployment_gate(self):
        gate = DeploymentGate(
            approved=True,
            approver="alice@example.com",
            reason="All evals passed",
            timestamp=datetime.now()
        )
        assert gate.approved is True
        assert gate.approver == "alice@example.com"

    def test_optional_fields(self):
        gate = DeploymentGate(
            approved=False,
            timestamp=datetime.now()
        )
        assert gate.approver is None
        assert gate.reason is None


class TestTraceSummary:
    def test_valid_summary(self):
        summary = TraceSummary(
            total_flops=2e17,
            num_steps=2,
            evals_run=1,
            deployment_approved=False
        )
        assert summary.total_flops == 2e17
        assert summary.num_steps == 2

    def test_negative_flops_rejected(self):
        with pytest.raises(ValidationError):
            TraceSummary(
                total_flops=-1e17,
                num_steps=2
            )

    def test_negative_steps_rejected(self):
        with pytest.raises(ValidationError):
            TraceSummary(
                total_flops=2e17,
                num_steps=-1
            )

    def test_optional_fields(self):
        summary = TraceSummary(
            total_flops=2e17,
            num_steps=2
        )
        assert summary.evals_run is None
        assert summary.deployment_approved is None


class TestTraceMetadata:
    def test_valid_metadata(self):
        metadata = TraceMetadata(
            organization="Example AI Lab",
            model_name="ExampleGPT-7B",
            framework="pytorch",
            hardware="8x A100"
        )
        assert metadata.framework == "pytorch"

    def test_invalid_framework_rejected(self):
        with pytest.raises(ValidationError):
            TraceMetadata(framework="invalid_framework")

    def test_all_optional(self):
        metadata = TraceMetadata()
        assert metadata.organization is None


class TestTrainingTrace:
    def create_valid_trace(self):
        start_time = datetime.now()
        return TrainingTrace(
            version="1.0",
            start_time=start_time,
            end_time=start_time + timedelta(hours=1),
            compute_events=[
                ComputeEvent(step=0, flops=1e17, timestamp=start_time),
                ComputeEvent(step=1, flops=1e17, timestamp=start_time + timedelta(minutes=30))
            ],
            summary=TraceSummary(total_flops=2e17, num_steps=2)
        )

    def test_valid_trace_creation(self):
        trace = self.create_valid_trace()
        assert trace.version == "1.0"
        assert len(trace.compute_events) == 2
        assert trace.summary.total_flops == 2e17

    def test_invalid_version_format_rejected(self):
        with pytest.raises(ValidationError):
            TrainingTrace(
                version="invalid",
                start_time=datetime.now(),
                summary=TraceSummary(total_flops=0, num_steps=0)
            )

    def test_end_time_before_start_rejected(self):
        start_time = datetime.now()
        with pytest.raises(ValidationError):
            TrainingTrace(
                version="1.0",
                start_time=start_time,
                end_time=start_time - timedelta(hours=1),
                summary=TraceSummary(total_flops=0, num_steps=0)
            )

    def test_summary_flops_mismatch_rejected(self):
        start_time = datetime.now()
        with pytest.raises(ValidationError):
            TrainingTrace(
                version="1.0",
                start_time=start_time,
                compute_events=[
                    ComputeEvent(step=0, flops=1e17, timestamp=start_time)
                ],
                summary=TraceSummary(total_flops=2e17, num_steps=1)  # Wrong total
            )

    def test_summary_steps_mismatch_rejected(self):
        start_time = datetime.now()
        with pytest.raises(ValidationError):
            TrainingTrace(
                version="1.0",
                start_time=start_time,
                compute_events=[
                    ComputeEvent(step=0, flops=1e17, timestamp=start_time)
                ],
                summary=TraceSummary(total_flops=1e17, num_steps=2)  # Wrong count
            )

    def test_empty_events_valid(self):
        trace = TrainingTrace(
            version="1.0",
            start_time=datetime.now(),
            summary=TraceSummary(total_flops=0, num_steps=0)
        )
        assert len(trace.compute_events) == 0
        assert len(trace.safety_evals) == 0
        assert len(trace.deployment_gates) == 0

    def test_no_deployment_gates_valid(self):
        start_time = datetime.now()
        trace = TrainingTrace(
            version="1.0",
            start_time=start_time,
            compute_events=[
                ComputeEvent(step=0, flops=1e17, timestamp=start_time)
            ],
            summary=TraceSummary(total_flops=1e17, num_steps=1)
        )
        assert len(trace.deployment_gates) == 0

    def test_json_export_import_roundtrip(self):
        original_trace = self.create_valid_trace()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            temp_path = f.name
        
        try:
            # Export to JSON
            original_trace.export_json(temp_path)
            
            # Import from JSON
            loaded_trace = TrainingTrace.from_json(temp_path)
            
            # Verify roundtrip
            assert loaded_trace.version == original_trace.version
            assert loaded_trace.summary.total_flops == original_trace.summary.total_flops
            assert len(loaded_trace.compute_events) == len(original_trace.compute_events)
            
        finally:
            os.unlink(temp_path)

    def test_complex_trace_with_all_fields(self):
        start_time = datetime.now()
        trace = TrainingTrace(
            version="1.0",
            start_time=start_time,
            end_time=start_time + timedelta(hours=2),
            compute_events=[
                ComputeEvent(step=0, flops=8.64e21, timestamp=start_time, device="gpu:0"),
                ComputeEvent(step=1000, flops=8.64e21, timestamp=start_time + timedelta(hours=1), device="gpu:1")
            ],
            safety_evals=[
                SafetyEval(
                    checkpoint=1000,
                    eval_type=EvalType.CBRN,
                    passed=True,
                    score=0.23,
                    threshold=0.5,
                    timestamp=start_time + timedelta(hours=1, minutes=5)
                )
            ],
            deployment_gates=[
                DeploymentGate(
                    approved=False,
                    reason="ASL-3 evals pending",
                    timestamp=start_time + timedelta(hours=2)
                )
            ],
            summary=TraceSummary(
                total_flops=1.728e22,
                num_steps=2,
                evals_run=1,
                deployment_approved=False,
                peak_memory_gb=80.0,
                training_duration_seconds=7200.0
            ),
            metadata=TraceMetadata(
                organization="Example AI Lab",
                model_name="ExampleGPT-7B",
                framework="pytorch",
                hardware="8x A100"
            )
        )
        
        assert trace.summary.evals_run == 1
        assert trace.metadata.framework == "pytorch"
        assert len(trace.safety_evals) == 1
        assert trace.safety_evals[0].eval_type == EvalType.CBRN

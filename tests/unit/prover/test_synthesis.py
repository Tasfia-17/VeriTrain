"""Comprehensive tests for proof synthesis"""

import pytest
import tempfile
import os
from datetime import datetime
from unittest.mock import patch

from veritrain.prover.synthesis import (
    ProofSynthesizer, ProofSynthesisError, synthesize_proof
)
from veritrain.instrumentation.trace_format.schema import (
    TrainingTrace, ComputeEvent, SafetyEval, TraceSummary, EvalType
)


class TestProofSynthesizer:
    def create_compliant_trace(self, total_flops: float = 8.64e19):
        """Create a trace that complies with EU AI Act"""
        start_time = datetime.now()
        return TrainingTrace(
            version="1.0",
            start_time=start_time,
            compute_events=[
                ComputeEvent(step=0, flops=total_flops, timestamp=start_time)
            ],
            summary=TraceSummary(total_flops=total_flops, num_steps=1)
        )

    def create_asl3_trace(self, num_evals: int = 3):
        """Create a trace with ASL-3 evaluations"""
        start_time = datetime.now()
        evals = []
        eval_types = [EvalType.CBRN, EvalType.CYBER, EvalType.AUTONOMOUS_REPLICATION]
        
        for i in range(num_evals):
            evals.append(SafetyEval(
                checkpoint=1000,
                eval_type=eval_types[i % len(eval_types)],
                passed=True,
                timestamp=start_time
            ))
        
        return TrainingTrace(
            version="1.0",
            start_time=start_time,
            compute_events=[
                ComputeEvent(step=0, flops=1e17, timestamp=start_time)
            ],
            safety_evals=evals,
            summary=TraceSummary(total_flops=1e17, num_steps=1)
        )

    def test_initialization_mock_mode(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        assert synthesizer.model == "claude-sonnet-4"
        assert synthesizer.api_key is None
        assert synthesizer.mock_mode is True

    def test_initialization_with_params(self):
        synthesizer = ProofSynthesizer(
            model="gpt-4",
            api_key="test-key",
            mock_mode=False
        )
        assert synthesizer.model == "gpt-4"
        assert synthesizer.api_key == "test-key"
        assert synthesizer.mock_mode is False

    def test_initialization_no_api_key_non_mock(self):
        with pytest.raises(ValueError, match="API key required when mock_mode=False"):
            ProofSynthesizer(mock_mode=False)

    def test_eu_ai_act_compliant_proof(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace(8.64e19)
        
        proof = synthesizer.synthesize(
            trace=trace,
            spec_path="specifications/regulations/eu_ai_act/article_53.thy",
            theorem_name="test_compliance"
        )
        
        assert "theory GeneratedProof" in proof
        assert "imports EUAIAct_Article53" in proof
        assert "theorem test_compliance:" in proof
        assert "8.64e19" in proof
        assert "complies_with_article_53" in proof
        assert "eu_systemic_risk_threshold" in proof

    def test_eu_ai_act_violation_error(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace(2e25)  # Exceeds 1e25 threshold
        
        with pytest.raises(ProofSynthesisError, match="Cannot prove compliance"):
            synthesizer.synthesize(
                trace=trace,
                spec_path="specifications/regulations/eu_ai_act/article_53.thy"
            )

    def test_eu_ai_act_exact_threshold(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace(1e25)  # Exactly at threshold
        
        proof = synthesizer.synthesize(
            trace=trace,
            spec_path="specifications/regulations/eu_ai_act/article_53.thy"
        )
        
        assert "1e25" in proof
        assert "complies_with_article_53" in proof

    def test_asl3_compliant_proof(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_asl3_trace(3)
        
        proof = synthesizer.synthesize(
            trace=trace,
            spec_path="specifications/regulations/anthropic_rsp/asl3_requirements.thy"
        )
        
        assert "theory GeneratedProof" in proof
        assert "imports AnthropicRSP_ASL3" in proof
        assert "complies_with_asl3" in proof
        assert "all_evals_passed" in proof
        assert "deployment_blocked" in proof

    def test_asl3_insufficient_evals_error(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_asl3_trace(2)  # Only 2 evals, need 3
        
        with pytest.raises(ProofSynthesisError, match="ASL-3 requires 3 evaluations"):
            synthesizer.synthesize(
                trace=trace,
                spec_path="specifications/regulations/anthropic_rsp/asl3_requirements.thy"
            )

    def test_generic_spec_proof(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace()
        
        proof = synthesizer.synthesize(
            trace=trace,
            spec_path="specifications/custom/unknown_spec.thy"
        )
        
        assert "theory GeneratedProof" in proof
        assert "imports VeriTrainBase" in proof
        assert "shows \"True\"" in proof

    def test_custom_theorem_name(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace()
        
        proof = synthesizer.synthesize(
            trace=trace,
            spec_path="specifications/regulations/eu_ai_act/article_53.thy",
            theorem_name="custom_proof_name"
        )
        
        assert "theorem custom_proof_name:" in proof

    def test_llm_synthesis_not_implemented(self):
        synthesizer = ProofSynthesizer(mock_mode=False, api_key="test-key")
        trace = self.create_compliant_trace()
        
        with pytest.raises(NotImplementedError, match="LLM synthesis not yet implemented"):
            synthesizer.synthesize(trace, "test.thy")

    def test_build_prompt_not_implemented(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace()
        
        with pytest.raises(NotImplementedError, match="Prompt building not yet implemented"):
            synthesizer._build_prompt(trace, "test spec")

    def test_zero_flops_trace(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace(0.0)
        
        proof = synthesizer.synthesize(
            trace=trace,
            spec_path="specifications/regulations/eu_ai_act/article_53.thy"
        )
        
        assert "0.0" in proof

    def test_large_flops_formatting(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace(1.23456789e24)
        
        proof = synthesizer.synthesize(
            trace=trace,
            spec_path="specifications/regulations/eu_ai_act/article_53.thy"
        )
        
        assert "1.23456789e+24" in proof

    def test_spec_path_detection_case_insensitive(self):
        synthesizer = ProofSynthesizer(mock_mode=True)
        trace = self.create_compliant_trace()
        
        # Test various path formats
        paths = [
            "EU_AI_ACT/article_53.thy",
            "regulations/ARTICLE_53/spec.thy",
            "ASL3_requirements.thy",
            "anthropic_RSP/test.thy"
        ]
        
        for path in paths:
            proof = synthesizer.synthesize(trace=trace, spec_path=path)
            assert "theory GeneratedProof" in proof


class TestSynthesizeProofFunction:
    def create_test_trace_file(self):
        """Create temporary trace file"""
        start_time = datetime.now()
        trace = TrainingTrace(
            version="1.0",
            start_time=start_time,
            compute_events=[
                ComputeEvent(step=0, flops=5e24, timestamp=start_time)
            ],
            summary=TraceSummary(total_flops=5e24, num_steps=1)
        )
        
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False)
        trace.export_json(temp_file.name)
        return temp_file.name

    @patch('builtins.print')
    def test_synthesize_proof_function(self, mock_print):
        trace_path = self.create_test_trace_file()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False) as proof_file:
            proof_path = proof_file.name
        
        try:
            proof = synthesize_proof(
                trace_path=trace_path,
                spec_path="specifications/regulations/eu_ai_act/article_53.thy",
                output_path=proof_path,
                mock_mode=True
            )
            
            # Check proof content
            assert "5e+24" in proof
            assert "complies_with_article_53" in proof
            
            # Check file was written
            assert os.path.exists(proof_path)
            with open(proof_path) as f:
                saved_proof = f.read()
            assert saved_proof == proof
            
            # Check print message
            mock_print.assert_called_with(f"✅ Proof generated: {proof_path}")
            
        finally:
            os.unlink(trace_path)
            if os.path.exists(proof_path):
                os.unlink(proof_path)

    def test_synthesize_proof_invalid_trace(self):
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as trace_file:
            trace_file.write('{"invalid": "json"}')
            trace_path = trace_file.name
        
        try:
            with pytest.raises(Exception):  # Should fail to parse invalid trace
                synthesize_proof(
                    trace_path=trace_path,
                    spec_path="test.thy",
                    output_path="output.thy"
                )
        finally:
            os.unlink(trace_path)

    def test_synthesize_proof_threshold_violation(self):
        # Create trace that violates threshold
        start_time = datetime.now()
        trace = TrainingTrace(
            version="1.0",
            start_time=start_time,
            compute_events=[
                ComputeEvent(step=0, flops=2e25, timestamp=start_time)
            ],
            summary=TraceSummary(total_flops=2e25, num_steps=1)
        )
        
        trace_path = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False).name
        trace.export_json(trace_path)
        
        try:
            with pytest.raises(ProofSynthesisError):
                synthesize_proof(
                    trace_path=trace_path,
                    spec_path="specifications/regulations/eu_ai_act/article_53.thy",
                    output_path="output.thy"
                )
        finally:
            os.unlink(trace_path)

"""Integration tests for CLI interface"""

import pytest
import tempfile
import os
import json
from datetime import datetime
from click.testing import CliRunner

from veritrain.cli import cli
from veritrain.instrumentation.trace_format.schema import (
    TrainingTrace, ComputeEvent, TraceSummary
)


class TestCLI:
    def setup_method(self):
        """Set up test fixtures"""
        self.runner = CliRunner()
        
    def create_test_trace(self, total_flops: float = 8.64e19):
        """Create a test trace file"""
        start_time = datetime.now()
        trace = TrainingTrace(
            version="1.0",
            start_time=start_time,
            compute_events=[
                ComputeEvent(step=0, flops=total_flops, timestamp=start_time)
            ],
            summary=TraceSummary(total_flops=total_flops, num_steps=1)
        )
        
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False)
        trace.export_json(temp_file.name)
        return temp_file.name
    
    def create_test_spec(self, spec_type: str = "eu_ai_act"):
        """Create a test specification file"""
        if spec_type == "eu_ai_act":
            content = """
theory TestSpec
  imports VeriTrainBase
begin
  (* EU AI Act specification *)
end
"""
        else:
            content = """
theory TestSpec
  imports VeriTrainBase
begin
  (* Generic specification *)
end
"""
        
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False)
        temp_file.write(content)
        temp_file.close()
        return temp_file.name
    
    def create_test_proof(self, valid: bool = True):
        """Create a test proof file"""
        if valid:
            content = """
theory TestProof
  imports VeriTrainBase
begin

theorem test_compliance:
  assumes "valid_trace t"
  shows "True"
  by simp

end
"""
        else:
            content = """
theory InvalidProof
begin
  (* Missing end statement *)
"""
        
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False)
        temp_file.write(content)
        temp_file.close()
        return temp_file.name

    def test_cli_version(self):
        """Test CLI version command"""
        result = self.runner.invoke(cli, ['--version'])
        assert result.exit_code == 0
        assert "1.0.0" in result.output

    def test_cli_help(self):
        """Test CLI help command"""
        result = self.runner.invoke(cli, ['--help'])
        assert result.exit_code == 0
        assert "VeriTrain: Formal Verification for AI Governance Compliance" in result.output
        assert "prove" in result.output
        assert "verify" in result.output
        assert "export" in result.output

    def test_prove_command_success(self):
        """Test successful proof generation"""
        trace_path = self.create_test_trace()
        spec_path = self.create_test_spec("eu_ai_act")
        
        with tempfile.NamedTemporaryFile(suffix='.thy', delete=False) as proof_file:
            proof_path = proof_file.name
        
        try:
            result = self.runner.invoke(cli, [
                'prove',
                '--trace', trace_path,
                '--spec', spec_path,
                '--output', proof_path,
                '--mock'
            ])
            
            assert result.exit_code == 0
            assert "Analyzing trace" in result.output
            assert "Using specification" in result.output
            assert "Proof generated successfully" in result.output
            assert os.path.exists(proof_path)
            
        finally:
            os.unlink(trace_path)
            os.unlink(spec_path)
            if os.path.exists(proof_path):
                os.unlink(proof_path)

    def test_prove_command_missing_trace(self):
        """Test prove command with missing trace file"""
        spec_path = self.create_test_spec()
        
        try:
            result = self.runner.invoke(cli, [
                'prove',
                '--trace', 'nonexistent.json',
                '--spec', spec_path,
                '--mock'
            ])
            
            assert result.exit_code != 0
            
        finally:
            os.unlink(spec_path)

    def test_prove_command_missing_spec(self):
        """Test prove command with missing spec file"""
        trace_path = self.create_test_trace()
        
        try:
            result = self.runner.invoke(cli, [
                'prove',
                '--trace', trace_path,
                '--spec', 'nonexistent.thy',
                '--mock'
            ])
            
            assert result.exit_code != 0
            
        finally:
            os.unlink(trace_path)

    def test_prove_command_threshold_violation(self):
        """Test prove command with threshold violation"""
        trace_path = self.create_test_trace(2e25)  # Exceeds EU AI Act threshold
        spec_path = self.create_test_spec("eu_ai_act")
        
        try:
            result = self.runner.invoke(cli, [
                'prove',
                '--trace', trace_path,
                '--spec', spec_path,
                '--mock'
            ])
            
            assert result.exit_code != 0
            assert "Proof generation failed" in result.output
            
        finally:
            os.unlink(trace_path)
            os.unlink(spec_path)

    def test_prove_command_help(self):
        """Test prove command help"""
        result = self.runner.invoke(cli, ['prove', '--help'])
        assert result.exit_code == 0
        assert "Generate compliance proof" in result.output
        assert "--trace" in result.output
        assert "--spec" in result.output

    def test_verify_command_success(self):
        """Test successful proof verification"""
        proof_path = self.create_test_proof(valid=True)
        
        try:
            result = self.runner.invoke(cli, [
                'verify',
                proof_path,
                '--mock'
            ])
            
            assert result.exit_code == 0
            assert "Validating proof" in result.output
            assert "Proof is valid!" in result.output
            assert "test_compliance" in result.output
            
        finally:
            os.unlink(proof_path)

    def test_verify_command_invalid_proof(self):
        """Test verification of invalid proof"""
        proof_path = self.create_test_proof(valid=False)
        
        try:
            result = self.runner.invoke(cli, [
                'verify',
                proof_path,
                '--mock'
            ])
            
            assert result.exit_code != 0
            assert "Proof validation failed" in result.output
            
        finally:
            os.unlink(proof_path)

    def test_verify_command_missing_file(self):
        """Test verify command with missing proof file"""
        result = self.runner.invoke(cli, [
            'verify',
            'nonexistent.thy',
            '--mock'
        ])
        
        assert result.exit_code != 0

    def test_verify_command_help(self):
        """Test verify command help"""
        result = self.runner.invoke(cli, ['verify', '--help'])
        assert result.exit_code == 0
        assert "Verify an Isabelle proof" in result.output

    def test_export_command_success(self):
        """Test successful certificate export"""
        proof_path = self.create_test_proof(valid=True)
        
        with tempfile.NamedTemporaryFile(suffix='.txt', delete=False) as cert_file:
            cert_path = cert_file.name
        
        try:
            result = self.runner.invoke(cli, [
                'export',
                proof_path,
                '--output', cert_path,
                '--format', 'txt',
                '--mock'
            ])
            
            assert result.exit_code == 0
            assert "Generating certificate" in result.output
            assert "Certificate generated" in result.output
            assert os.path.exists(cert_path)
            
        finally:
            os.unlink(proof_path)
            if os.path.exists(cert_path):
                os.unlink(cert_path)

    def test_export_command_invalid_proof(self):
        """Test export command with invalid proof"""
        proof_path = self.create_test_proof(valid=False)
        
        try:
            result = self.runner.invoke(cli, [
                'export',
                proof_path,
                '--format', 'txt',
                '--mock'
            ])
            
            assert result.exit_code != 0
            assert "Certificate generation failed" in result.output
            
        finally:
            os.unlink(proof_path)

    def test_export_command_pdf_format(self):
        """Test export command with PDF format"""
        proof_path = self.create_test_proof(valid=True)
        
        with tempfile.NamedTemporaryFile(suffix='.pdf', delete=False) as cert_file:
            cert_path = cert_file.name
        
        try:
            result = self.runner.invoke(cli, [
                'export',
                proof_path,
                '--output', cert_path,
                '--format', 'pdf',
                '--mock'
            ])
            
            assert result.exit_code == 0
            assert os.path.exists(cert_path)
            
        finally:
            os.unlink(proof_path)
            if os.path.exists(cert_path):
                os.unlink(cert_path)

    def test_export_command_help(self):
        """Test export command help"""
        result = self.runner.invoke(cli, ['export', '--help'])
        assert result.exit_code == 0
        assert "Generate compliance certificate" in result.output
        assert "--format" in result.output

    def test_full_workflow(self):
        """Test complete workflow: prove -> verify -> export"""
        trace_path = self.create_test_trace()
        spec_path = self.create_test_spec("eu_ai_act")
        
        with tempfile.NamedTemporaryFile(suffix='.thy', delete=False) as proof_file:
            proof_path = proof_file.name
        
        with tempfile.NamedTemporaryFile(suffix='.txt', delete=False) as cert_file:
            cert_path = cert_file.name
        
        try:
            # Step 1: Generate proof
            result1 = self.runner.invoke(cli, [
                'prove',
                '--trace', trace_path,
                '--spec', spec_path,
                '--output', proof_path,
                '--mock'
            ])
            assert result1.exit_code == 0
            
            # Step 2: Verify proof
            result2 = self.runner.invoke(cli, [
                'verify',
                proof_path,
                '--mock'
            ])
            assert result2.exit_code == 0
            
            # Step 3: Export certificate
            result3 = self.runner.invoke(cli, [
                'export',
                proof_path,
                '--output', cert_path,
                '--format', 'txt',
                '--mock'
            ])
            assert result3.exit_code == 0
            
            # Verify all files exist
            assert os.path.exists(proof_path)
            assert os.path.exists(cert_path)
            
        finally:
            for path in [trace_path, spec_path, proof_path, cert_path]:
                if os.path.exists(path):
                    os.unlink(path)

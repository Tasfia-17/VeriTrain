"""Comprehensive tests for Isabelle validator"""

import pytest
import tempfile
import os
from unittest.mock import patch, MagicMock

from veritrain.validator.isabelle_wrapper import (
    ProofValidator, ValidationResult, verify_proof
)


class TestValidationResult:
    def test_initialization_defaults(self):
        result = ValidationResult(valid=True)
        assert result.valid is True
        assert result.error is None
        assert result.output == ""
        assert result.theorems_proved == []

    def test_initialization_with_values(self):
        result = ValidationResult(
            valid=False,
            error="Test error",
            output="Test output",
            theorems_proved=["theorem1", "theorem2"]
        )
        assert result.valid is False
        assert result.error == "Test error"
        assert result.output == "Test output"
        assert result.theorems_proved == ["theorem1", "theorem2"]


class TestProofValidator:
    def test_initialization_mock_mode(self):
        validator = ProofValidator(mock_mode=True)
        assert validator.isabelle_path == "/usr/local/Isabelle"
        assert validator.mock_mode is True

    def test_initialization_with_path(self):
        validator = ProofValidator(
            isabelle_path="/custom/path",
            mock_mode=True
        )
        assert validator.isabelle_path == "/custom/path"

    @patch('subprocess.run')
    def test_check_isabelle_installed_success(self, mock_run):
        mock_run.return_value = MagicMock(returncode=0)
        
        validator = ProofValidator(mock_mode=False)
        # Should not raise exception
        assert validator.isabelle_path == "/usr/local/Isabelle"

    @patch('subprocess.run')
    def test_check_isabelle_installed_failure(self, mock_run):
        mock_run.return_value = MagicMock(returncode=1)
        
        with pytest.raises(RuntimeError, match="Isabelle not found"):
            ProofValidator(mock_mode=False)

    @patch('subprocess.run')
    def test_check_isabelle_not_found(self, mock_run):
        mock_run.side_effect = FileNotFoundError()
        
        with pytest.raises(RuntimeError, match="Isabelle not found"):
            ProofValidator(mock_mode=False)

    def create_valid_proof_file(self):
        """Create a valid proof file for testing"""
        proof_content = """
theory TestProof
  imports VeriTrainBase
begin

theorem test_theorem:
  assumes "valid_trace t"
  shows "True"
  by simp

end
"""
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False)
        temp_file.write(proof_content)
        temp_file.close()
        return temp_file.name

    def create_invalid_proof_file(self, content: str):
        """Create an invalid proof file for testing"""
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False)
        temp_file.write(content)
        temp_file.close()
        return temp_file.name

    def test_mock_validate_valid_proof(self):
        validator = ProofValidator(mock_mode=True)
        proof_path = self.create_valid_proof_file()
        
        try:
            result = validator.validate(proof_path)
            
            assert result.valid is True
            assert result.error is None
            assert result.output == "Mock validation passed"
            assert "test_theorem" in result.theorems_proved
            
        finally:
            os.unlink(proof_path)

    def test_mock_validate_missing_theory(self):
        validator = ProofValidator(mock_mode=True)
        proof_path = self.create_invalid_proof_file("begin\nend")
        
        try:
            result = validator.validate(proof_path)
            
            assert result.valid is False
            assert result.error == "Missing 'theory' declaration"
            
        finally:
            os.unlink(proof_path)

    def test_mock_validate_missing_end(self):
        validator = ProofValidator(mock_mode=True)
        proof_path = self.create_invalid_proof_file("theory Test\nbegin")
        
        try:
            result = validator.validate(proof_path)
            
            assert result.valid is False
            assert result.error == "Missing 'end' statement"
            
        finally:
            os.unlink(proof_path)

    def test_mock_validate_obviously_invalid(self):
        validator = ProofValidator(mock_mode=True)
        proof_content = """
theory Test
begin
obviously_invalid
end
"""
        proof_path = self.create_invalid_proof_file(proof_content)
        
        try:
            result = validator.validate(proof_path)
            
            assert result.valid is False
            assert result.error == "Proof contains invalid statement"
            assert result.theorems_proved == []
            
        finally:
            os.unlink(proof_path)

    def test_mock_validate_multiple_theorems(self):
        validator = ProofValidator(mock_mode=True)
        proof_content = """
theory Test
begin

theorem first_theorem:
  shows "True"
  by simp

theorem second_theorem:
  shows "True"
  by simp

end
"""
        proof_path = self.create_invalid_proof_file(proof_content)
        
        try:
            result = validator.validate(proof_path)
            
            assert result.valid is True
            assert len(result.theorems_proved) == 2
            assert "first_theorem" in result.theorems_proved
            assert "second_theorem" in result.theorems_proved
            
        finally:
            os.unlink(proof_path)

    def test_isabelle_validate_not_implemented(self):
        validator = ProofValidator(mock_mode=False, isabelle_path="/fake/path")
        
        with patch.object(validator, '_check_isabelle_installed'):
            with pytest.raises(NotImplementedError):
                validator._isabelle_validate("test.thy")

    def test_generate_certificate_valid_proof(self):
        validator = ProofValidator(mock_mode=True)
        proof_path = self.create_valid_proof_file()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as cert_file:
            cert_path = cert_file.name
        
        try:
            result_path = validator.generate_certificate(
                proof_path=proof_path,
                output_path=cert_path,
                format="txt"
            )
            
            assert result_path == cert_path
            assert os.path.exists(cert_path)
            
            with open(cert_path) as f:
                cert_content = f.read()
            
            assert "VERITRAIN COMPLIANCE CERTIFICATE" in cert_content
            assert "test_theorem" in cert_content
            assert "✅ PASSED" in cert_content
            
        finally:
            os.unlink(proof_path)
            if os.path.exists(cert_path):
                os.unlink(cert_path)

    def test_generate_certificate_invalid_proof(self):
        validator = ProofValidator(mock_mode=True)
        proof_path = self.create_invalid_proof_file("invalid")
        
        try:
            with pytest.raises(ValueError, match="Cannot generate certificate for invalid proof"):
                validator.generate_certificate(
                    proof_path=proof_path,
                    output_path="cert.txt",
                    format="txt"
                )
        finally:
            os.unlink(proof_path)

    def test_generate_certificate_pdf_format(self):
        validator = ProofValidator(mock_mode=True)
        proof_path = self.create_valid_proof_file()
        
        with tempfile.NamedTemporaryFile(mode='wb', suffix='.pdf', delete=False) as cert_file:
            cert_path = cert_file.name
        
        try:
            validator.generate_certificate(
                proof_path=proof_path,
                output_path=cert_path,
                format="pdf"
            )
            
            assert os.path.exists(cert_path)
            # In mock mode, PDF is just text encoded as bytes
            with open(cert_path, 'rb') as f:
                content = f.read().decode()
            assert "VERITRAIN COMPLIANCE CERTIFICATE" in content
            
        finally:
            os.unlink(proof_path)
            if os.path.exists(cert_path):
                os.unlink(cert_path)

    def test_generate_certificate_unsupported_format(self):
        validator = ProofValidator(mock_mode=True)
        proof_path = self.create_valid_proof_file()
        
        try:
            with pytest.raises(ValueError, match="Unsupported format"):
                validator.generate_certificate(
                    proof_path=proof_path,
                    output_path="cert.xml",
                    format="xml"
                )
        finally:
            os.unlink(proof_path)

    def test_generate_pdf_certificate_not_implemented(self):
        validator = ProofValidator(mock_mode=False, isabelle_path="/fake/path")
        
        with patch.object(validator, '_check_isabelle_installed'):
            with pytest.raises(NotImplementedError):
                validator._generate_pdf_certificate("test.thy", ValidationResult(valid=True))


class TestVerifyProofFunction:
    def test_verify_proof_function(self):
        proof_content = """
theory Test
begin
theorem test: shows "True" by simp
end
"""
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False)
        temp_file.write(proof_content)
        temp_file.close()
        
        try:
            result = verify_proof(temp_file.name, mock_mode=True)
            
            assert result.valid is True
            assert "test" in result.theorems_proved
            
        finally:
            os.unlink(temp_file.name)

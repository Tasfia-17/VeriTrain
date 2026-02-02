"""
VeriTrain command-line interface.

Commands:
- prove: Generate proof from trace + spec
- verify: Validate an existing proof
- export: Generate compliance certificate
"""

import click
from pathlib import Path
from veritrain.prover.synthesis import synthesize_proof
from veritrain.validator.isabelle_wrapper import verify_proof, ProofValidator


@click.group()
@click.version_option(version="1.0.0")
def cli():
    """
    VeriTrain: Formal Verification for AI Governance Compliance
    
    Generate cryptographically verifiable proofs that AI training
    complies with governance requirements.
    """
    pass


@cli.command()
@click.option(
    '--trace', '-t',
    required=True,
    type=click.Path(exists=True),
    help='Path to training trace JSON file'
)
@click.option(
    '--spec', '-s',
    required=True,
    type=click.Path(exists=True),
    help='Path to Isabelle specification (.thy file)'
)
@click.option(
    '--output', '-o',
    default='proof.thy',
    type=click.Path(),
    help='Where to save generated proof'
)
@click.option(
    '--mock/--no-mock',
    default=True,
    help='Use mock synthesis (for testing without LLM)'
)
def prove(trace, spec, output, mock):
    """
    Generate compliance proof from trace and specification.
    
    Example:
        veritrain prove -t trace.json -s eu_ai_act.thy -o proof.thy
    """
    click.echo(f"🔍 Analyzing trace: {trace}")
    click.echo(f"📋 Using specification: {spec}")
    
    try:
        proof = synthesize_proof(
            trace_path=trace,
            spec_path=spec,
            output_path=output,
            mock_mode=mock
        )
        
        click.echo(f"✅ Proof generated successfully: {output}")
        click.echo("\nNext: Run 'veritrain verify' to validate the proof")
        
    except Exception as e:
        click.echo(f"❌ Proof generation failed: {e}", err=True)
        raise click.Abort()


@cli.command()
@click.argument('proof_path', type=click.Path(exists=True))
@click.option(
    '--mock/--no-mock',
    default=True,
    help='Use mock validation (for testing without Isabelle)'
)
def verify(proof_path, mock):
    """
    Verify an Isabelle proof.
    
    Example:
        veritrain verify proof.thy
    """
    click.echo(f"🔍 Validating proof: {proof_path}")
    
    try:
        result = verify_proof(proof_path, mock_mode=mock)
        
        if result.valid:
            click.echo("✅ Proof is valid!")
            if result.theorems_proved:
                click.echo("\nTheorems proved:")
                for thm in result.theorems_proved:
                    click.echo(f"  ✓ {thm}")
        else:
            click.echo(f"❌ Proof validation failed: {result.error}", err=True)
            raise click.Abort()
            
    except Exception as e:
        click.echo(f"❌ Validation error: {e}", err=True)
        raise click.Abort()


@cli.command()
@click.argument('proof_path', type=click.Path(exists=True))
@click.option(
    '--output', '-o',
    default='certificate.pdf',
    help='Output certificate file'
)
@click.option(
    '--format', '-f',
    type=click.Choice(['pdf', 'txt', 'html']),
    default='pdf',
    help='Certificate format'
)
@click.option(
    '--mock/--no-mock',
    default=True,
    help='Use mock mode'
)
def export(proof_path, output, format, mock):
    """
    Generate compliance certificate from validated proof.
    
    Example:
        veritrain export proof.thy -o certificate.pdf
    """
    click.echo(f"📄 Generating certificate from: {proof_path}")
    
    try:
        validator = ProofValidator(mock_mode=mock)
        cert_path = validator.generate_certificate(
            proof_path=proof_path,
            output_path=output,
            format=format
        )
        
        click.echo(f"✅ Certificate generated: {cert_path}")
        
    except Exception as e:
        click.echo(f"❌ Certificate generation failed: {e}", err=True)
        raise click.Abort()


if __name__ == '__main__':
    cli()

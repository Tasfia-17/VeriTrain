.PHONY: help install test lint format clean docs examples benchmark

help:
	@echo "VeriTrain Development Commands"
	@echo "==============================="
	@echo "install    - Install package and dependencies"
	@echo "test       - Run test suite with coverage"
	@echo "lint       - Run linters (black, mypy, isort)"
	@echo "format     - Auto-format code"
	@echo "clean      - Remove build artifacts"
	@echo "docs       - Build documentation"
	@echo "examples   - Run all examples"
	@echo "benchmark  - Run performance benchmarks"

install:
	pip install -e .
	pip install -e .[dev]
	pre-commit install

test:
	pytest tests/ \
		--cov=veritrain \
		--cov-report=html \
		--cov-report=term \
		--verbose

lint:
	black --check veritrain tests
	mypy veritrain
	isort --check veritrain tests

format:
	black veritrain tests
	isort veritrain tests

docs:
	@echo "Building documentation..."
	@echo "Documentation build not yet implemented"

examples:
	@echo "Running all examples..."
	cd examples/01_simple_compute_limit && ./run.sh

benchmark:
	cd experiments/proof_synthesis_performance && python benchmark.py

clean:
	rm -rf build/
	rm -rf dist/
	rm -rf *.egg-info/
	rm -rf .pytest_cache/
	rm -rf htmlcov/
	rm -rf .coverage
	find . -type d -name __pycache__ -exec rm -rf {} +
	find . -type f -name "*.pyc" -delete

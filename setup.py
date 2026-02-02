from setuptools import setup, find_packages

setup(
    name="veritrain",
    version="1.0.0",
    packages=find_packages(),
    python_requires=">=3.9,<3.12",
    install_requires=[
        "torch>=2.0.0",
        "jax>=0.4.0",
        "anthropic>=0.18.0",
        "openai>=1.0.0",
        "pydantic>=2.0.0",
        "jsonschema>=4.0.0",
        "click>=8.0.0",
        "rich>=13.0.0",
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=4.0.0",
            "black>=23.0.0",
            "mypy>=1.0.0",
            "isort>=5.0.0",
            "pre-commit>=3.0.0",
            "pandas>=2.0.0",
            "matplotlib>=3.7.0",
        ]
    },
    entry_points={
        "console_scripts": [
            "veritrain=veritrain.cli:cli",
        ],
    },
)

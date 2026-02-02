"""JSON schema for VeriTrain trace format v1.0"""

from pydantic import BaseModel, Field, validator
from typing import List, Optional, Literal
from datetime import datetime
from enum import Enum


class EvalType(str, Enum):
    CBRN = "CBRN"
    CYBER = "cyber"
    AUTONOMOUS_REPLICATION = "autonomous_replication"
    PERSUASION = "persuasion"
    CUSTOM = "custom"


class ComputeEvent(BaseModel):
    step: int = Field(ge=0)
    flops: float = Field(ge=0)
    timestamp: datetime
    device: Optional[str] = None


class SafetyEval(BaseModel):
    checkpoint: int = Field(ge=0)
    eval_type: EvalType
    passed: bool
    score: Optional[float] = None
    threshold: Optional[float] = None
    timestamp: datetime


class DeploymentGate(BaseModel):
    approved: bool
    approver: Optional[str] = None
    reason: Optional[str] = None
    timestamp: datetime


class TraceSummary(BaseModel):
    total_flops: float = Field(ge=0)
    num_steps: int = Field(ge=0)
    evals_run: Optional[int] = None
    deployment_approved: Optional[bool] = None
    peak_memory_gb: Optional[float] = None
    training_duration_seconds: Optional[float] = None


class TraceMetadata(BaseModel):
    organization: Optional[str] = None
    model_name: Optional[str] = None
    framework: Optional[Literal["pytorch", "jax", "tensorflow"]] = None
    hardware: Optional[str] = None


class TrainingTrace(BaseModel):
    version: str = Field(regex=r"^\d+\.\d+$")
    start_time: datetime
    end_time: Optional[datetime] = None
    compute_events: List[ComputeEvent] = Field(default_factory=list)
    safety_evals: List[SafetyEval] = Field(default_factory=list)
    deployment_gates: List[DeploymentGate] = Field(default_factory=list)
    summary: TraceSummary
    metadata: Optional[TraceMetadata] = None

    @validator('end_time')
    def end_after_start(cls, v, values):
        if v and 'start_time' in values:
            if v <= values['start_time']:
                raise ValueError('end_time must be after start_time')
        return v

    @validator('summary')
    def validate_summary_consistency(cls, v, values):
        if 'compute_events' in values:
            actual_total = sum(e.flops for e in values['compute_events'])
            if abs(actual_total - v.total_flops) > 1e-6:
                raise ValueError(
                    f"summary.total_flops ({v.total_flops}) doesn't match "
                    f"sum of compute_events ({actual_total})"
                )
            if len(values['compute_events']) != v.num_steps:
                raise ValueError(
                    f"summary.num_steps ({v.num_steps}) doesn't match "
                    f"compute_events length ({len(values['compute_events'])})"
                )
        return v

    def export_json(self, filepath: str):
        """Export trace to JSON file"""
        import json
        with open(filepath, 'w') as f:
            json.dump(self.dict(), f, indent=2, default=str)

    @classmethod
    def from_json(cls, filepath: str) -> 'TrainingTrace':
        """Load trace from JSON file"""
        import json
        with open(filepath) as f:
            data = json.load(f)
        return cls(**data)

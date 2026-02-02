"""
Example 1: Simple Compute Limit Verification

Demonstrates basic VeriTrain usage:
1. Instrument training code
2. Log compute events
3. Generate compliance proof
4. Verify proof

This example trains a small transformer for 100 steps
and proves it stayed below a compute threshold.
"""

import torch
import torch.nn as nn
from veritrain.instrumentation.pytorch import ComputeTracker

# Configuration
COMPUTE_LIMIT = 1e20  # 100 quintillion FLOPs
MODEL_SIZE = 124_000_000  # Parameters (GPT-2 small)
MODEL_FLOPS_PER_TOKEN = 6 * MODEL_SIZE  # Forward + backward
BATCH_SIZE = 32
SEQ_LEN = 128
NUM_STEPS = 100

def main():
    print("=" * 60)
    print("VeriTrain Example 1: Simple Compute Limit")
    print("=" * 60)
    
    # Initialize compute tracker
    print(f"\n📊 Compute limit: {COMPUTE_LIMIT:.2e} FLOPs")
    tracker = ComputeTracker(
        threshold=COMPUTE_LIMIT,
        output_path="output/trace.json"
    )
    
    # Create model (we won't actually train, just log compute)
    print(f"🤖 Model: {MODEL_SIZE:,} parameters")
    print(f"⚙️  Batch size: {BATCH_SIZE}, Sequence length: {SEQ_LEN}")
    
    # Simulate training
    print(f"\n🚀 Starting training for {NUM_STEPS} steps...")
    
    for step in range(NUM_STEPS):
        # Calculate FLOPs for this step
        # Forward pass: batch_size * seq_len * (6 * num_params)
        # Backward pass: 2x forward
        flops_this_step = BATCH_SIZE * SEQ_LEN * MODEL_FLOPS_PER_TOKEN
        
        # Log to tracker
        tracker.log_step(flops_this_step)
        
        # Print progress
        if step % 25 == 0 or step == NUM_STEPS - 1:
            print(
                f"  Step {step:3d}: "
                f"{tracker.total_flops:.2e} / {COMPUTE_LIMIT:.2e} FLOPs "
                f"({tracker.total_flops/COMPUTE_LIMIT*100:.1f}%)"
            )
    
    # Finalize tracking
    print(f"\n✅ Training complete!")
    trace = tracker.finalize()
    
    # Summary
    print(f"\n📈 Summary:")
    print(f"   Total FLOPs: {trace.summary.total_flops:.2e}")
    print(f"   Steps: {trace.summary.num_steps}")
    print(f"   Duration: {trace.summary.training_duration_seconds:.1f}s")
    print(f"   Under threshold: {'✅ YES' if trace.summary.total_flops <= COMPUTE_LIMIT else '❌ NO'}")
    
    print(f"\n📁 Trace saved to: output/trace.json")
    print(f"\n🎯 Next steps:")
    print(f"   1. Run: ./run.sh")
    print(f"   2. Or manually: veritrain prove -t output/trace.json -s spec.thy")

if __name__ == "__main__":
    import os
    os.makedirs("output", exist_ok=True)
    main()

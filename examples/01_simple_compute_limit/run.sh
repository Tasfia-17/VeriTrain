#!/bin/bash
#
# One-click execution of Example 1
#

set -e  # Exit on error

echo "=================================="
echo "VeriTrain Example 1: Execution"
echo "=================================="

# Step 1: Run training
echo -e "\n[1/4] Running training with instrumentation..."
python train.py

# Step 2: Generate proof
echo -e "\n[2/4] Generating compliance proof..."
veritrain prove \
  --trace output/trace.json \
  --spec spec.thy \
  --output output/proof.thy \
  --mock

# Step 3: Verify proof
echo -e "\n[3/4] Verifying proof..."
veritrain verify output/proof.thy --mock

# Step 4: Generate certificate
echo -e "\n[4/4] Generating compliance certificate..."
veritrain export output/proof.thy \
  --output output/certificate.txt \
  --format txt \
  --mock

echo -e "\n=================================="
echo "✅ Example 1 Complete!"
echo "=================================="
echo ""
echo "Generated files:"
echo "  - output/trace.json (training trace)"
echo "  - output/proof.thy (formal proof)"
echo "  - output/certificate.txt (compliance certificate)"
echo ""
echo "View certificate:"
echo "  cat output/certificate.txt"

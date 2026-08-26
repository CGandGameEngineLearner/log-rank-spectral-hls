#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

python3 scripts/verify_product_johnson_logrank.py
python3 scripts/verify_general_product_protocol.py
python3 scripts/verify_multislice_product_protocol.py
python3 scripts/verify_low_degree_slice_protocol.py
python3 scripts/verify_unisolvent_sparse_columns.py

echo "all Python verification suites: PASS"

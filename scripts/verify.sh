#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification
python3 scripts/theorem_inventory.py
lake build 2>&1 | tee verification/build.txt
lake env lean Audit.lean 2>&1 | tee verification/axioms.txt
python3 scripts/check_audit.py

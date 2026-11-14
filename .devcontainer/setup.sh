#!/usr/bin/env bash
# Runs once when the container is created: installs Lean through elan, downloads the compiled
# Mathlib, and installs the Python packages of the check scripts.
set -euo pipefail
curl -sSfL https://elan.lean-lang.org/elan-init.sh \
  | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
python3 -m pip install --user -r requirements.txt
echo "Setup done. Next: lake build (the first build compiles Physlib and this library)."

#!/usr/bin/env bash
# Erdos #361 -- verification build (Linux / macOS / WSL), one module at a time.
# Usage:  bash build.sh   (from this folder). One log per step is written to logs/.
set -u
cd "$(dirname "$0")"
mkdir -p logs
export PATH="$HOME/.elan/bin:$PATH"

step() {  # step NAME CMD...
  local name="$1"; shift
  echo "=== $name : $*"
  local t0=$(date +%s)
  ( "$@" ) > "logs/$name.log" 2>&1
  local code=$?
  echo "[exit code: $code, $(( $(date +%s) - t0 )) s]" >> "logs/$name.log"
  echo "    -> exit $code (log: logs/$name.log)"
  return 0
}

if ! command -v elan >/dev/null 2>&1; then
  step 00_install_elan bash -c 'curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none'
fi
step 01_toolchain bash -c 'elan toolchain install leanprover/lean4:v4.31.0 && lean --version'
step 02_cache_get lake exe cache get
i=0
for m in Erdos361.Statement Erdos361.Core Erdos361.GoodCore Erdos361.Covering Erdos361.Freiman \
         Erdos361.InverseGlue Erdos361.InverseMain Erdos361.Asymptotics; do
  i=$((i + 1)); step "03_${i}_${m}" lake build "$m"
done
step 04_root            lake build Erdos361
step 05_challenge       lake build Challenge
step 06_solution        lake build Solution
step 07_axioms_original lake env lean CheckOriginal.lean
step 08_axioms_solution lake env lean Solution.lean
grep -nE "sorry|native_decide|^axiom " Erdos361/*.lean Solution.lean > logs/09_hygiene.log 2>&1
echo "Done. Results are in logs/."

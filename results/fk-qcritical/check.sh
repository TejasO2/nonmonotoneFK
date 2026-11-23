#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build FK
lake env lean Audit.lean | tee .lake/audit-output.txt
python3 scripts/check_audit.py Audit.lean .lake/audit-output.txt
python3 scripts/check_documentation.py
if rg -n '^\s*(axiom|unsafe)\b|:=\s*(sorry|admit)\b|by\s+(sorry|admit)\b|^\s*(sorry|admit)\s*$' \
    --glob '*.lean' --glob '!Mathlib/**' .; then
  echo "Placeholder or forbidden declaration found" >&2
  exit 1
fi

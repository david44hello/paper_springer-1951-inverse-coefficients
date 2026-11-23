#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
git ls-files --error-unmatch -- AUDIT.md >/dev/null
lake exe cache get
lake --no-cache build +Springer
python3 scripts/audit.py
git diff --exit-code HEAD -- AUDIT.md
echo "Springer verification passed."

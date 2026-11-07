#!/usr/bin/env bash
# Halt only when the recent Korenblum candidate loop is clearly stuck.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

LOG="Refinement_Log/log.jsonl"
LEMMA_TOML="lemma.toml"

python3 - "$LEMMA_TOML" <<'PY'
import pathlib
import re
import sys
import tomllib

root = pathlib.Path(".")
config_path = pathlib.Path(sys.argv[1])
raw = tomllib.loads(config_path.read_text())
allowed_exact = set(raw.get("workspace_import_policy", {}).get("allowed_exact", []))
allowed_prefixes = tuple(raw.get("workspace_import_policy", {}).get("allowed_prefixes", []))
import_re = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)

def parse_imports(text: str):
    out = []
    for m in import_re.finditer(text):
        line = m.group(1).split("--", 1)[0]
        out.extend(tok for tok in line.split() if tok)
    return out

def allowed(mod: str) -> bool:
    return mod in allowed_exact or any(mod == p or mod.startswith(p + ".") for p in allowed_prefixes)

violations = []
for lean_file in sorted(root.rglob("*.lean")):
    rel = lean_file.relative_to(root)
    for mod in parse_imports(lean_file.read_text()):
        if not allowed(mod):
            violations.append(f"{rel}: {mod}")

if violations:
    print("preflight HALT: workspace import policy violation")
    for item in violations:
        print(item)
    raise SystemExit(1)
PY

if [[ ! -f "$LOG" ]]; then
    echo "preflight: log empty (first run); proceed"
    exit 0
fi

python3 - "$LOG" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
lines = [line.strip() for line in path.read_text().splitlines() if line.strip()]
if len(lines) < 3:
    print("preflight: OK")
    raise SystemExit(0)

recent = lines[-3:]
try:
    records = [json.loads(line) for line in recent]
except Exception:
    print("preflight HALT: malformed log.jsonl")
    raise SystemExit(2)

if all(not record.get("pass", False) for record in records):
    print("preflight HALT: last 3 candidate evaluations failed; needs human review")
    raise SystemExit(1)

print("preflight: OK")
PY

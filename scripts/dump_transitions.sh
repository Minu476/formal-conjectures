#!/bin/bash
# Dump tactic-transition JSONL from FormalConjecturesForMathlib.
#
# Mechanism: the InfoTreeWalker linter (NexusDump sub-package, this branch — a module
# file wrapped in `public meta section`, the Mathlib linter idiom) registers a
# per-command linter at import time that appends transition rows when
# nexus.dumpInfoTreesPath is nonempty. Corpus files are module files and may only
# import other module files, so we temporarily inject the import into every FCM
# file, elaborate each file via `lake env lean -D ...`, and revert. Nothing lands
# in git. (`lake build` is NOT used: lake's build facade omits the in-repo path
# dependency's build dir from LEAN_PATH; `lake env` includes it.)
set -euo pipefail
cd "$(dirname "$0")/.."

OUT="${1:-/tmp/fcm-transitions.jsonl}"
IMPORT="import NexusDump.InfoTreeWalker"

trap 'git checkout -- FormalConjecturesForMathlib' EXIT

rm -f "$OUT" "$OUT.perfile"

# inject the walker import after each FCM file's `module` header
python3 - "$IMPORT" <<'EOF'
import sys, pathlib
imp = sys.argv[1]
root = pathlib.Path('FormalConjecturesForMathlib')
n = 0
for f in sorted(root.rglob('*.lean')):
    t = f.read_text()
    if imp in t:
        continue
    lines = t.split('\n')
    for i, l in enumerate(lines):
        if l.strip() == 'module':
            lines.insert(i+1, imp)
            n += 1
            break
    else:
        print(f"WARN: no module header in {f}")
        continue
    f.write_text('\n'.join(lines))
print(f"injected into {n} files")
EOF

echo "--- elaborating each FCM file with the dumper active"
for f in $(find FormalConjecturesForMathlib -name '*.lean' | sort); do
  if lake env lean -D "nexus.dumpInfoTreesPath=$OUT" "$f" >> "$OUT.perfile" 2>&1; then
    echo "OK   $f"
  else
    echo "FAIL $f"
  fi
done

echo "--- done; rows:"
wc -l "$OUT"

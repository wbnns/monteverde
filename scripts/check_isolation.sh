#!/usr/bin/env bash
# Statement isolation (design doc): each file in Monteverde/Statements/ imports only the vendored
# Clay definitions and cslib-frontier's class definitions, never a proof. Statements may also
# import Statements/Defs.lean, which itself passes this check.
set -euo pipefail
cd "$(dirname "$0")/.."
allowed=(
  "import Vendor.Millennium.Millennium"
  "import CslibFrontier.Computability.Complexity.Classes.P"
  "import CslibFrontier.Computability.Complexity.Classes.NP"
  "import Monteverde.Statements.Defs"
)
status=0
for f in Monteverde/Statements/*.lean; do
  while IFS= read -r line; do
    ok=0
    for a in "${allowed[@]}"; do [ "$line" = "$a" ] && ok=1; done
    if [ $ok -eq 0 ]; then echo "FAIL $f has a disallowed import: $line"; status=1; fi
  done < <(grep -E '^\s*(public\s+|private\s+)?(meta\s+)?import ' "$f")
done
if grep -qE '^\s*import Monteverde.Statements.Defs' Monteverde/Statements/Defs.lean; then
  echo "FAIL Statements/Defs.lean imports itself"; status=1
fi
[ $status -eq 0 ] && echo "OK   every file in Monteverde/Statements/ imports only Clay and cslib-frontier class definitions"
exit $status

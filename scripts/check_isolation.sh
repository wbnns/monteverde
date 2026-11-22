#!/usr/bin/env bash
# Statements/Defs.lean must import only cslib-frontier's class definitions (statement isolation).
set -euo pipefail
cd "$(dirname "$0")/.."
allowed=(
  "import CslibFrontier.Computability.Complexity.Classes.P"
  "import CslibFrontier.Computability.Complexity.Classes.NP"
)
status=0
while IFS= read -r line; do
  ok=0
  for a in "${allowed[@]}"; do [ "$line" = "$a" ] && ok=1; done
  if [ $ok -eq 0 ]; then echo "FAIL Statements/Defs.lean has a disallowed import: $line"; status=1; fi
done < <(grep -E '^\s*(public\s+)?import ' Monteverde/Statements/Defs.lean)
[ $status -eq 0 ] && echo "OK   Statements/Defs.lean imports only cslib-frontier class definitions"
exit $status

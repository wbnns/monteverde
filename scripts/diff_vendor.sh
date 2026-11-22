#!/usr/bin/env bash
# Checks that every vendored file differs from its pinned upstream only by the listed changes.
#
# 1. Vendor/Millennium/Millennium.lean: the diff from upstream must equal port.patch exactly.
# 2. Vendor/Millennium/MathlibCompat.lean: each BEGIN/END VERBATIM block must appear unchanged
#    in Mathlib/Computability/Encoding.lean at the Mathlib commit that upstream pins.
# 3. Vendor/CookLevin/*.lean: the combined diff must equal Vendor/CookLevin/port.patch.
#
# Needs: bash, curl, diff, python3. Exits non-zero on any mismatch.
set -euo pipefail
cd "$(dirname "$0")/.."

CLAY_COMMIT="$(cat Vendor/Millennium/UPSTREAM_COMMIT)"
CLAY_MATHLIB="fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

fetch() { # repo commit path out
  curl -fsSL --retry 3 "https://raw.githubusercontent.com/$1/$2/$3" -o "$4"
}

status=0

# 1. The Clay file.
fetch lean-dojo/LeanMillenniumPrizeProblems "$CLAY_COMMIT" Problems/PVersusNP/Millennium.lean "$tmp/clay.lean"
diff -u --label upstream/Problems/PVersusNP/Millennium.lean --label Vendor/Millennium/Millennium.lean \
  "$tmp/clay.lean" Vendor/Millennium/Millennium.lean > "$tmp/clay.patch" || true
if diff -q "$tmp/clay.patch" Vendor/Millennium/port.patch > /dev/null; then
  echo "OK   Millennium.lean differs from upstream $CLAY_COMMIT only by port.patch"
else
  echo "FAIL Millennium.lean has changes that port.patch does not list:"
  diff "$tmp/clay.patch" Vendor/Millennium/port.patch || true
  status=1
fi

# 2. The Mathlib compatibility copy.
fetch leanprover-community/mathlib4 "$CLAY_MATHLIB" Mathlib/Computability/Encoding.lean "$tmp/enc.lean"
python3 - "$tmp/enc.lean" Vendor/Millennium/MathlibCompat.lean <<'PY' || status=1
import re, sys
upstream = open(sys.argv[1], encoding="utf8").read()
compat = open(sys.argv[2], encoding="utf8").read()
blocks = re.findall(r"-- BEGIN VERBATIM [^\n]*\n(.*?)-- END VERBATIM", compat, re.S)
if not blocks:
    print("FAIL MathlibCompat.lean has no VERBATIM blocks"); sys.exit(1)
bad = [b for b in blocks if b not in upstream]
for b in bad:
    print("FAIL MathlibCompat.lean block not found verbatim in Mathlib:\n" + b)
# Outside the blocks, only the header, imports, universes and the namespace lines may appear.
rest = re.sub(r"-- BEGIN VERBATIM.*?-- END VERBATIM\n", "", compat, flags=re.S)
rest = re.sub(r"/-.*?-/\n", "", rest, flags=re.S)
extra = [l for l in rest.splitlines() if l.strip() and not re.match(
    r"^(import |universe |namespace MathlibV431$|end MathlibV431$)", l)]
for l in extra:
    print("FAIL MathlibCompat.lean has an unlisted line: " + l)
if bad or extra: sys.exit(1)
print(f"OK   MathlibCompat.lean: {len(blocks)} blocks are verbatim Mathlib fabf563")
PY

# 3. The vendored millennium-cook-levin files (Comp.lean and the Cook-Levin proof). The diffs of
#    all files, in file-name order, must equal Vendor/CookLevin/port.patch.
if [ -f Vendor/CookLevin/UPSTREAM_COMMIT ] && [ -f Vendor/CookLevin/port.patch ]; then
  CL_COMMIT="$(cat Vendor/CookLevin/UPSTREAM_COMMIT)"
  : > "$tmp/cl.patch"
  for f in $(ls Vendor/CookLevin/*.lean | LC_ALL=C sort); do
    b="$(basename "$f")"
    fetch JoshuaTan42/millennium-cook-levin "$CL_COMMIT" "$b" "$tmp/up_$b"
    diff -u --label "upstream/$b" --label "Vendor/CookLevin/$b" "$tmp/up_$b" "$f" >> "$tmp/cl.patch" || true
  done
  if diff -q "$tmp/cl.patch" Vendor/CookLevin/port.patch > /dev/null; then
    echo "OK   Vendor/CookLevin/*.lean ($(ls Vendor/CookLevin/*.lean | wc -l) files) differ from upstream $CL_COMMIT only by port.patch"
  else
    echo "FAIL Vendor/CookLevin has changes that its port.patch does not list:"
    diff "$tmp/cl.patch" Vendor/CookLevin/port.patch || true
    status=1
  fi
fi

exit $status

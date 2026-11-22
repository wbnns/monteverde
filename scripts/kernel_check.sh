#!/usr/bin/env bash
# Independent kernel check: export the headline theorems with lean4export and check the export
# with nanoda, a type checker for Lean 4 written in Rust (not the Lean kernel).
#
# Needs: a built project (lake build Audit), git, cargo. Writes into ./audit-out/.
set -euo pipefail
cd "$(dirname "$0")/.."

LEAN4EXPORT_COMMIT="df81913eee5519d5a88ae5b0fd701b5298cc29ab"
NANODA_COMMIT="0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929"
DECLS=(
  Monteverde.cslibPEqNP_iff_bits
  Monteverde.clay_iff_cslib
  Monteverde.clay_negative_iff_cslib
  Monteverde.clayP_iff_cslib
  Monteverde.clayNP_iff_cslib
)
out="$PWD/audit-out"
mkdir -p "$out"

# 1. lean4export, built with this project's toolchain so it reads our .olean files.
if [ ! -x "$out/lean4export/.lake/build/bin/lean4export" ]; then
  rm -rf "$out/lean4export"
  git clone -q https://github.com/leanprover/lean4export "$out/lean4export"
  git -C "$out/lean4export" checkout -q "$LEAN4EXPORT_COMMIT"
  cp lean-toolchain "$out/lean4export/lean-toolchain"
  (cd "$out/lean4export" && lake build)
fi

# 2. Export the headline theorems and everything they depend on.
lake env "$out/lean4export/.lake/build/bin/lean4export" Audit.ClaimCheck -- "${DECLS[@]}" \
  > "$out/export.ndjson"
echo "export: $(wc -l < "$out/export.ndjson") lines"

# 3. nanoda.
if [ ! -x "$out/nanoda_lib/target/release/nanoda_bin" ]; then
  rm -rf "$out/nanoda_lib"
  git clone -q https://github.com/ammkrn/nanoda_lib "$out/nanoda_lib"
  git -C "$out/nanoda_lib" checkout -q "$NANODA_COMMIT"
  (cd "$out/nanoda_lib" && cargo build --release)
fi
bin="$(find "$out/nanoda_lib/target/release" -maxdepth 1 -type f -perm -u+x -name 'nanoda*' | head -1)"

decls_json="$(printf '"%s",' "${DECLS[@]}")"
cat > "$out/nanoda.json" <<JSON
{
  "export_file_path": "$out/export.ndjson",
  "use_stdin": false,
  "num_threads": 4,
  "stack_size_bytes": 268435456,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": false,
  "nat_extension": true,
  "string_extension": true,
  "pp_declars": [${decls_json%,}],
  "pp_to_stdout": true,
  "print_success_message": true
}
JSON
"$bin" "$out/nanoda.json"

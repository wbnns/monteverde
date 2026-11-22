# Changes to the vendored Clay file

`Millennium.lean` is `Problems/PVersusNP/Millennium.lean` from
[LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) at the
commit in `UPSTREAM_COMMIT`. Upstream builds with Lean v4.31.0 and Mathlib `fabf563`. Monteverde
builds with Lean v4.36.0-rc2 and the Mathlib that cslib-frontier pins (`bbff295`).

The file is ported, not edited. `port.patch` holds the full diff from upstream.
`scripts/diff_vendor.sh` fails CI if the real diff differs from `port.patch` in any way. Every
change is listed here with its reason. No change touches a definition, a statement or a theorem
type.

| # | Change | Reason |
|---|--------|--------|
| 1 | One comment line at the top of the file | Apache-2.0 §4(b): a modified file must say that it was changed. |
| 2 | `import Vendor.Millennium.MathlibCompat` | Mathlib unbundled `Encoding` and deprecated `FinEncoding` on 2026-05-07. The Clay file uses the bundled structures (`ea.Γ`, `ΓFin`). `MathlibCompat.lean` copies the old Mathlib definitions verbatim (checked against Mathlib `fabf563` by `diff_vendor.sh`). |
| 3 | `open Computability` becomes `open Computability hiding Encoding FinEncoding finEncodingBoolBool` plus `open MathlibV431` | The names `FinEncoding`, `Encoding` and `finEncodingBoolBool` now resolve to the verbatim v4.31 copies instead of the new, differently shaped Mathlib names. The rest of `Computability` stays open as upstream. |
| 4 | `deriving DecidableEq, Fintype` becomes `deriving DecidableEq` plus an explicit `Fintype` instance, for `StringProjectionStack` and `StringProjectionLabel` | On this Mathlib, `deriving Fintype` fails for an inductive type inside a namespace (the generated `rw` does not fire). The explicit instance lists the same constructors. Both types stay `private`. |
| 5 | `Turing.TM2.step, Turing.TM2.stepAux` added to seven `simp` calls in the private step lemmas of the left-projection machine | Mathlib no longer unfolds these through `Turing.FinTM2.step` alone, so the old `simp` calls left the goal open. |
| 6 | In `string_projection_step_emit_work` and `string_projection_step_emit_output`, the `simp`/`congr`/`ext` proof becomes `simp only`, `congrArg some`, `show`, `congr 1`, `funext` | The old `simp` call hits the heartbeat limit on push steps with this elaborator. The new proof shows the same equation step by step. |

Changes 4 to 6 are inside `private` proofs of the left-projection machine. They do not change any
type that a public declaration mentions.

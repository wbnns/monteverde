# Changes to the vendored millennium-cook-levin files

The 13 `.lean` files here are copies of the files with the same names in
[millennium-cook-levin](https://github.com/JoshuaTan42/millennium-cook-levin) at the commit in
`UPSTREAM_COMMIT`. Upstream builds on Lean v4.31.0. Monteverde builds on v4.36.0-rc2, so the
files needed small toolchain fixes.

* `Comp.lean` proves `PvsNP.tm2ComputableInPolyTime_comp`: the composition of two
  polynomial-time TM2 machines is a polynomial-time TM2 machine. Mathlib leaves this result as a
  `proof_wanted`. The Monteverde bridges use it.
* The other 12 files are the Cook-Levin proof against the Clay definitions (`PvsNP.cook_levin`,
  `PvsNP.sat_in_np`). Only the Cook-Levin cross-check in `CrossCheck/` uses them. They are not
  part of the claim. Upstream's `Challenge.lean`, `SatInP.lean` (a `sorry`) and `Solution.lean`
  are not vendored.

`port.patch` holds the full diff from upstream, for all files in file-name order, and
`scripts/diff_vendor.sh` fails CI on any other change. No change touches a definition or a
theorem statement. (Change 9 adds a type ascription to a bound variable in a statement; the
proposition is the same term up to definitional unfolding.)

| # | File | Change | Reason |
|---|------|--------|--------|
| 1 | all 13 | One comment line at the top of the file | Apache-2.0 §4(b): a modified file must say that it was changed. |
| 2 | all that import them | `import Problems.PVersusNP.Millennium` becomes `import Vendor.Millennium.Millennium`; `import X` becomes `import Vendor.CookLevin.X` | The files live at `Vendor/CookLevin/`. |
| 3 | `Comp.lean` | In `initList_compTM` and `haltList_compTM`, `subst h; simp [mkStk, compTM]` gets a final `rfl` | On this toolchain `simp` leaves the goal `cast l = l` with a trivial cast; `rfl` closes it. |
| 4 | `Comp.lean` | In `compComputable`, `rw [initList_compTM, Option.map_some, haltList_compTM]` becomes `rw [initList_compTM]`, `change`, `rw [haltList_compTM]` | `Option.map_some` no longer matches because the configuration types are only definitionally equal. `change` states the same goal. |
| 5 | `Comp.lean` | In `compComputable`, the first `rw [iterate_add_apply, …]` becomes `erw` | Same reason as change 4. |
| 6 | `CookLevin`, `D3Acc`, `D3Fam`, `D3Init`, `D3OneHot`, `D3Shift`, `Pre` (11 enum types) | `deriving DecidableEq, Fintype` becomes `deriving DecidableEq` plus `instance : Fintype T := derive_fintype% T` | Mathlib's `Fintype` deriving handler for enum types fails on this toolchain (its generated `rw` does not type-check). `derive_fintype%` is Mathlib's other route to the same instance. Types with arguments keep `deriving Fintype`, which still works. |
| 7 | `Sit.lean` | `step_agree`, `runI_of_iterate`, `runI_halted`: `simp […]` gets a final `rfl`; `table_agree`: `rw [hs, code, na, hr]` becomes `rw [hs]; simp only [code, na]; rw [hr]`; `decRow_enc`: `rw [Nat.zero_add, E.cell_kc]` becomes `erw` | `M.Cfg` and `TM2.Cfg M.Γ M.Λ M.σ` are only definitionally equal, so some `simp` and `rw` steps stop one step early on this toolchain. |
| 8 | `D3Init.lean` | `set_option maxHeartbeats 1000000 in` before `pre_run` | The unchanged proof needs more heartbeats on this toolchain. |
| 9 | `Pkg.lean` | `haltList_g`: `fun q => if q = FK.h .out …` becomes `fun (q : FK) => …` | Instance search no longer unfolds `(gTM …).K` to `FK` to find `DecidableEq FK`. The ascription states the same type. |
| 10 | `Pkg.lean` | `run_runI`: `rw [ih e he, stepI, h']` becomes `rw [ih e he]`, `show`, `rw [h']`; `g_run`: `exact hg.mono (by unfold gB; …)` becomes `refine hg.mono ?_` then the same tactics | `rw [stepI]` no longer finds the equation; the elaboration order of the `by` block changed. |
| 11 | `Pkg.lean` | `open … Millennium Computability` becomes `open … Millennium`, `open Computability hiding Encoding FinEncoding finEncodingBoolBool`, `open MathlibV431` | Mathlib now has an unbundled `FinEncoding`. The vendored Clay file uses a bundled copy (`Vendor/Millennium/MathlibCompat.lean`); this matches it. |
| 12 | `Pkg.lean` | `v_input`: `simp [vι, veqv]; rfl` becomes `change` plus `rw [Equiv.apply_symm_apply]`; `v_correct`: `exact Iff.rfl` becomes `exact Equiv.apply_eq_iff_eq _` | `simp` does not unfold the composition, or stops one step earlier, on this toolchain. |

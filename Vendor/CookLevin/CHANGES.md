# Changes to the vendored TM2 composition file

`Comp.lean` is `Comp.lean` from
[millennium-cook-levin](https://github.com/JoshuaTan42/millennium-cook-levin) at the commit in
`UPSTREAM_COMMIT`. It proves `PvsNP.tm2ComputableInPolyTime_comp`: the composition of two
polynomial-time TM2 machines is a polynomial-time TM2 machine. Mathlib leaves this result as a
`proof_wanted`.

`port.patch` holds the full diff from upstream, and `scripts/diff_vendor.sh` fails CI on any
other change. No change touches a definition or a theorem statement.

| # | Change | Reason |
|---|--------|--------|
| 1 | One comment line at the top of the file | Apache-2.0 §4(b): a modified file must say that it was changed. |
| 2 | `import Problems.PVersusNP.Millennium` becomes `import Vendor.Millennium.Millennium` | The Clay file is vendored at `Vendor/Millennium/`. |
| 3 | In `initList_compTM` and `haltList_compTM`, `subst h; simp [mkStk, compTM]` gets a final `rfl` | On this toolchain `simp` leaves the goal `cast l = l` with a trivial cast; `rfl` closes it. |
| 4 | In `compComputable`, `rw [initList_compTM, Option.map_some, haltList_compTM]` becomes `rw [initList_compTM]`, `change`, `rw [haltList_compTM]` | `Option.map_some` no longer matches because the configuration types are only definitionally equal. `change` states the same goal. |
| 5 | In `compComputable`, the first `rw [iterate_add_apply, …]` becomes `erw` | Same reason as change 4. |

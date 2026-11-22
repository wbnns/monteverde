import Audit.Axioms
import CrossCheck.CookLevin

/-!
# Axiom check for the Cook-Levin cross-check

The same allowlist as `Audit/Axioms.lean`: only `propext`, `Classical.choice` and `Quot.sound`.
-/

open Lean Elab Command

/-- Fail unless every cross-check theorem uses only the allowed axioms. -/
elab "#check_crosscheck_axioms" : command => do
  for n in [``PvsNP.cook_levin, ``PvsNP.sat_in_np, ``PvsNP.comp,
      ``Monteverde.CrossCheck.clay_P_subset_NP,
      ``Monteverde.CrossCheck.mcl_SAT_mem_NP, ``Monteverde.CrossCheck.mcl_SAT_mem_P_iff,
      ``Monteverde.CrossCheck.satWords_clayP_iff, ``Monteverde.CrossCheck.cook_levin_agree_clay,
      ``Monteverde.CrossCheck.cook_levin_agree_cslib] do
    let axs ← liftCoreM (collectAxioms n)
    let bad := axs.filter fun a => !allowedAxioms.contains a
    unless bad.isEmpty do
      throwError m!"{n} depends on axioms outside the allowlist: {bad}"
    logInfo m!"{n}: {axs}"

#check_crosscheck_axioms

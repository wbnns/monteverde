import Monteverde.Classes.Reduction
import Monteverde.Function.Bridge
import Monteverde.Headline.Bits
import Monteverde.Headline.Clay
import Monteverde.Headline.NegativeBranch

/-!
# Axiom check

`#check_axioms` fails the build if a headline theorem or class bridge depends on any axiom other
than `propext`, `Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom `sorryAx`,
so it fails too.
-/

open Lean Elab Command

/-- The only allowed axioms. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The declarations under check. -/
def checkedDecls : List Name :=
  [``Monteverde.cslibPEqNP_iff_bits, ``Monteverde.clay_iff_cslib,
    ``Monteverde.clay_negative_iff_cslib, ``Monteverde.clayP_iff_cslib,
    ``Monteverde.clayNP_iff_cslib, ``Monteverde.tm2_iff_computableInPolyTime,
    ``Monteverde.tm2_iff_computableInPolyTime_words, ``Monteverde.clayReducible_iff_cslib]

/-- Fail unless every checked declaration uses only the allowed axioms. -/
elab "#check_axioms" : command => do
  for n in checkedDecls do
    let axs ← liftCoreM (collectAxioms n)
    let bad := axs.filter fun a => !allowedAxioms.contains a
    unless bad.isEmpty do
      throwError m!"{n} depends on axioms outside the allowlist: {bad}"
    logInfo m!"{n}: {axs}"

#check_axioms

/-! The design doc asks for `#print axioms` on every headline theorem. `#check_axioms` above is
the check that fails CI; these lines print the same result for a reader. -/

#print axioms Monteverde.cslibPEqNP_iff_bits
#print axioms Monteverde.clay_iff_cslib
#print axioms Monteverde.clay_negative_iff_cslib

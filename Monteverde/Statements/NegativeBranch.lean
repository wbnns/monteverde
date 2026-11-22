import Monteverde.Statements.Clay

/-!
# L3: the negative Clay target

`Millennium.ClayPVersusNP.Formulations.NegativeBranch` is defined as `¬ ClayPVersusNP`, so this
theorem follows from `clay_iff_cslib` in one line. It is still stated, because the claim names
both official targets of LeanMillenniumPrizeProblems.
-/

namespace Monteverde

/-- **Headline theorem.** The negative Clay target is equivalent to `¬ CslibPEqNP`. -/
theorem clay_negative_iff_cslib :
    Millennium.ClayPVersusNP.Formulations.NegativeBranch ↔ ¬ CslibPEqNP :=
  not_congr clay_iff_cslib

end Monteverde

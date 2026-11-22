import Vendor.Millennium.Millennium
import Monteverde.Statements.Defs

/-!
# Statement: the negative Clay target

The statement of the headline theorem `Monteverde.clay_negative_iff_cslib`, as a definition.

Statement isolation: this file imports only the vendored Clay definitions and
`Statements/Defs.lean` (which imports only cslib-frontier's class definitions). It never imports
a proof. `Audit/Isolation.lean` checks that the theorem's type is exactly this statement.
-/

namespace Monteverde.Statements

/-- The negative Clay target is equivalent to `¬ CslibPEqNP`. -/
def ClayNegativeIffCslib : Prop :=
  Millennium.ClayPVersusNP.Formulations.NegativeBranch ↔ ¬ CslibPEqNP

end Monteverde.Statements

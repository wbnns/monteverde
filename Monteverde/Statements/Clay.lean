import Vendor.Millennium.Millennium
import Monteverde.Statements.Defs

/-!
# Statement: the Clay target

The statement of the headline theorem `Monteverde.clay_iff_cslib`, as a definition.

Statement isolation: this file imports only the vendored Clay definitions and
`Statements/Defs.lean` (which imports only cslib-frontier's class definitions). It never imports
a proof. `Audit/Isolation.lean` checks that the theorem's type is exactly this statement.
-/

namespace Monteverde.Statements

/-- The Clay P vs NP statement of LeanMillenniumPrizeProblems is equivalent to P vs NP in
cslib-frontier. -/
def ClayIffCslib : Prop :=
  Millennium.ClayPVersusNP ↔ CslibPEqNP

end Monteverde.Statements

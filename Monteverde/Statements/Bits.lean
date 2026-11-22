import Monteverde.Statements.Defs

/-!
# Statement: the binary-string form

The statement of the headline theorem `Monteverde.cslibPEqNP_iff_bits`, as a definition.

Statement isolation: this file imports only definitions (`Statements/Defs.lean`, which imports
only cslib-frontier's class definitions). It never imports a proof. `Audit/Isolation.lean`
checks that the theorem's type is exactly this statement.
-/

namespace Monteverde.Statements

open Cslib.Complexity Turing.MultiTapeTM

/-- `CslibPEqNP` is equivalent to P = NP on binary strings. -/
def CslibPEqNPIffBits : Prop :=
  CslibPEqNP ↔ P encBits = NP encBits

end Monteverde.Statements

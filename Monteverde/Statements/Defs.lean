import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Complexity.Classes.NP

/-!
# The cslib-frontier P vs NP statement

cslib-frontier has no named P = NP proposition. Its own theorems state P = NP for every instance
encoding (the form of `Cslib.Complexity.NPComplete.mem_P_iff`). `CslibPEqNP` is exactly that
form.

This file imports only cslib-frontier's class definitions, never proofs (statement isolation,
checked by `Audit/Isolation.lean`).
-/

namespace Monteverde

/-- P vs NP as cslib-frontier states it: the form of `NPComplete.mem_P_iff`. -/
def CslibPEqNP : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool), Cslib.Complexity.P enc = Cslib.Complexity.NP enc

end Monteverde

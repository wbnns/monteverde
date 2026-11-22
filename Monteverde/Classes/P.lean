import Vendor.Millennium.Millennium
import Monteverde.Function.Forward
import CslibFrontier.Computability.Complexity.Classes.P

/-!
# L2: Clay's P and cslib-frontier's P

For a finite alphabet `Γ`, a language over `Γ` is in Clay's `InPolynomialTime` exactly when it is
in cslib-frontier's `P` under the block code `blockEnc Γ`.

This file has the direction from Clay to cslib-frontier. The other direction needs the reverse
machine bridge (milestone M2).
-/

namespace Monteverde

open Turing Turing.MultiTapeTM Cslib.Complexity

/-- **Clay P to cslib-frontier P.** -/
theorem mem_P_of_inPolynomialTime {Γ : Type} [Fintype Γ] {L : Millennium.Language (List Γ)}
    (h : Millennium.InPolynomialTime (Millennium.fin_encoding_string Γ) L) :
    setOf L ∈ P (blockEnc Γ) := by
  obtain ⟨f, hf, hL⟩ := h
  refine ⟨f, ?_, hL⟩
  exact computableInPolyTime_of_tm2 (e := id) Function.injective_id
    (hf : TM2ComputableInPolyTime id (fun b : Bool => [b]) f)

end Monteverde

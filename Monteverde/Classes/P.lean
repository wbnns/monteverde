import Vendor.Millennium.Millennium
import Monteverde.Function.Bridge
import CslibFrontier.Computability.Complexity.Classes.P

/-!
# L2: Clay's P and cslib-frontier's P

For a finite alphabet `Γ`, a language over `Γ` is in Clay's `InPolynomialTime` exactly when it is
in cslib-frontier's `P` under the block code `blockEnc Γ`.

Both directions go through the L1 bridge `Monteverde.tm2_iff_computableInPolyTime` with the
encoding `id : List Γ → List Γ`, which is Clay's `fin_encoding_string Γ`.
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

/-- **cslib-frontier P to Clay P.** -/
theorem inPolynomialTime_of_mem_P {Γ : Type} [Fintype Γ] {L : Millennium.Language (List Γ)}
    (h : setOf L ∈ P (blockEnc Γ)) :
    Millennium.InPolynomialTime (Millennium.fin_encoding_string Γ) L := by
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨h'⟩ := tm2_of_computableInPolyTime (e := id) Function.injective_id hf
  exact ⟨f, h', hL⟩

variable (Γ : Type) [Fintype Γ] [Nontrivial Γ] (L : Millennium.Language (List Γ))

/-- **L2 for P.** A language over a finite alphabet with at least two symbols is in Clay's P
exactly when it is in cslib-frontier's P under the block code. -/
theorem clayP_iff_cslib :
    Millennium.InPolynomialTime (Millennium.fin_encoding_string Γ) L ↔ setOf L ∈ P (blockEnc Γ) :=
  ⟨mem_P_of_inPolynomialTime, inPolynomialTime_of_mem_P⟩

end Monteverde

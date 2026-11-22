import Vendor.Millennium.Millennium
import Monteverde.Function.Bridge
import CslibFrontier.Computability.Complexity.Reduction

/-!
# L2: Clay's reductions and cslib-frontier's reductions

For finite alphabets `Γ` and `Δ`, a Clay polynomial-time many-one reduction between languages of
words (`Millennium.PolynomialTimeReducible` with `fin_encoding_string`) is exactly a
cslib-frontier polynomial-time reduction under the block codes (`PolyTimeReducible`).

Both directions go through the L1 bridge for word outputs,
`Monteverde.tm2_iff_computableInPolyTime_words`. The target alphabet `Δ` must have a symbol for
the direction from cslib-frontier to Clay (see `Monteverde.Decoder`).
-/

namespace Monteverde

open Turing Turing.MultiTapeTM Cslib.Complexity

variable {Γ Δ : Type} [Fintype Γ] [Fintype Δ]
  {L₁ : Millennium.Language (List Γ)} {L₂ : Millennium.Language (List Δ)}

/-- **Clay reduction to cslib-frontier reduction.** -/
theorem polyTimeReducible_of_clay
    (h : Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string Γ)
      (Millennium.fin_encoding_string Δ) L₁ L₂) :
    PolyTimeReducible (blockEnc Γ) (blockEnc Δ) {w | L₁ w} {w | L₂ w} := by
  obtain ⟨f, hf, hL⟩ := h
  exact ⟨f, computableInPolyTime_of_tm2_words (e := id) (eo := id) Function.injective_id
    Function.injective_id (hf : TM2ComputableInPolyTime id id f), hL⟩

/-- **cslib-frontier reduction to Clay reduction.** -/
theorem clay_of_polyTimeReducible [Nonempty Δ]
    (h : PolyTimeReducible (blockEnc Γ) (blockEnc Δ) {w | L₁ w} {w | L₂ w}) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string Γ)
      (Millennium.fin_encoding_string Δ) L₁ L₂ := by
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨h'⟩ := tm2_of_computableInPolyTime_words (e := id) (eo := id) Function.injective_id
    Function.injective_id hf
  exact ⟨f, h', hL⟩

/-- **L2 for reductions.** -/
theorem clayReducible_iff_cslib [Nonempty Δ] :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string Γ)
        (Millennium.fin_encoding_string Δ) L₁ L₂ ↔
      PolyTimeReducible (blockEnc Γ) (blockEnc Δ) {w | L₁ w} {w | L₂ w} :=
  ⟨polyTimeReducible_of_clay, clay_of_polyTimeReducible⟩

end Monteverde

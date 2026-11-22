import Monteverde

/-!
# README examples

Every Lean example in `README.md` is checked here, so CI fails if one stops working.
-/

open Cslib.Complexity Turing.MultiTapeTM

namespace Monteverde.ReadmeExamples

/-- A cslib-frontier proof of P = NP on binary strings gives the positive Clay target. -/
example (h : P encBits = NP encBits) : Millennium.ClayPVersusNP :=
  clay_iff_cslib.mpr (cslibPEqNP_iff_bits.mpr h)

/-- A cslib-frontier problem in NP but not in P, for any encoding, gives the negative Clay
target. -/
example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hNP : A ∈ NP enc) (hP : A ∉ P enc) :
    Millennium.ClayPVersusNP.Formulations.NegativeBranch :=
  clay_negative_iff_cslib.mpr fun h => hP (by rw [h enc]; exact hNP)

/-- SAT in cslib-frontier P gives the positive Clay target. -/
example (h : encCNF '' SAT ∈ P encBits) : Millennium.ClayPVersusNP :=
  clay_iff_cslib.mpr (cslibPEqNP_of_image_SAT_mem_P h)

/-- The positive Clay target gives P = NP for every cslib-frontier encoding. -/
example (h : Millennium.ClayPVersusNP) {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  clay_iff_cslib.mp h enc

/-- Moving one language between the two definitions of P. -/
example (L : Millennium.Language (List Bool))
    (h : Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool) L) :
    {w | L w} ∈ P (blockEnc Bool) :=
  (clayP_iff_cslib Bool L).mp h

end Monteverde.ReadmeExamples

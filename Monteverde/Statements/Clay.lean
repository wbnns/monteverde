import Monteverde.Statements.Bits
import Monteverde.Classes.NP

/-!
# L3: the Clay statement

`Millennium.ClayPVersusNP` is equivalent to `CslibPEqNP`.

* Clay to cslib-frontier: apply the Clay statement at the alphabet `Bool` to the binary image of
  SAT. Its NP membership moves from `encBits` to the block code, through the L2 bridges to Clay,
  back, and to `encBits` again. Then the bits form gives `CslibPEqNP`.
* cslib-frontier to Clay: for each alphabet `Γ`, use the encoding `blockEnc Γ` and the L2
  bridges.
-/

namespace Monteverde

open Cslib.Complexity Turing.MultiTapeTM

/-- The block code of bits and the raw bits are polynomial-time equivalent. -/
theorem bits_to_blockEnc : ComputableInPolyTime (fun w : List Bool => w) encBits (blockEnc Bool) :=
  (trans_encList_polyTime encBits (encFinite Bool)).1

theorem blockEnc_to_bits : ComputableInPolyTime (fun w : List Bool => w) (blockEnc Bool) encBits :=
  (trans_encList_polyTime encBits (encFinite Bool)).2

/-- **Headline theorem.** The Clay P vs NP statement of LeanMillenniumPrizeProblems is equivalent
to P vs NP in cslib-frontier. -/
theorem clay_iff_cslib : Millennium.ClayPVersusNP ↔ CslibPEqNP := by
  constructor
  · intro h
    apply cslibPEqNP_of_image_SAT_mem_P
    let B : Set (List Bool) := encCNF '' SAT
    have hNP : B ∈ NP (blockEnc Bool) :=
      PolyTimeReducible.mem_NP ⟨fun w => w, blockEnc_to_bits, fun _ => Iff.rfl⟩ image_SAT_mem_NP
    have hClayNP := (clayNP_iff_cslib Bool (fun w => w ∈ B)).mpr hNP
    have hClayP := (h Bool (fun w => w ∈ B)).mpr hClayNP
    have hP : B ∈ P (blockEnc Bool) := (clayP_iff_cslib Bool (fun w => w ∈ B)).mp hClayP
    exact PolyTimeReducible.mem_P ⟨fun w => w, bits_to_blockEnc, fun _ => Iff.rfl⟩ hP
  · intro h Γ _ _ L
    rw [clayP_iff_cslib, clayNP_iff_cslib, h (blockEnc Γ)]
end Monteverde

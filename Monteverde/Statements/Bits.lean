import Monteverde.Statements.Defs
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Classes.NP.Image

/-!
# L3: the binary-string form

`CslibPEqNP` (P = NP for every encoding) is equivalent to P = NP on binary strings,
`P encBits = NP encBits`. So both readings of "P vs NP in cslib-frontier" are covered.

The proof uses SAT, which cslib-frontier proves NP-complete: if the image of SAT in binary
strings is in P, then SAT is in P, and `NPComplete.mem_P_iff` gives P = NP for every encoding.
-/

namespace Monteverde

open Cslib.Complexity Turing.MultiTapeTM

/-- If the binary image of SAT is in P, then P = NP in the cslib-frontier form. -/
theorem cslibPEqNP_of_image_SAT_mem_P (h : encCNF '' SAT ∈ P encBits) : CslibPEqNP := by
  have hred : PolyTimeReducible encCNF encBits SAT (encCNF '' SAT) :=
    ⟨encCNF, ComputableInPolyTime.of_eq fun _ => rfl,
      fun a => (encCNF.injective.mem_set_image).symm⟩
  intro α enc
  exact CookLevin.SAT_npComplete.mem_P_iff.mp (hred.mem_P h) enc

/-- **The binary-string form.** -/
theorem cslibPEqNP_iff_bits : CslibPEqNP ↔ P encBits = NP encBits :=
  ⟨fun h => h encBits, fun h => cslibPEqNP_of_image_SAT_mem_P (h ▸ image_SAT_mem_NP)⟩

end Monteverde

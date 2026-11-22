import Monteverde.Headline.Clay
import CslibFrontier.Computability.Complexity.Problems.Halting

/-!
# Non-vacuity tests

The bridges are true theorems, but a theorem can be true and still say nothing, for example if a
definition puts every language in NP. (The Clay file records that an earlier NP definition did
exactly that.) These tests check that the classes have real content on both sides, and that the
two sides agree on concrete languages.

1. A simple language (words that start with `true`) is in P on both sides.
2. The binary image of SAT is in NP on both sides.
3. The binary image of the halting problem is in neither NP nor P, on either side. So neither
   side's NP is the class of all languages.
-/

namespace Monteverde.Tests

open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. A simple language in P -/

/-- Words over `Bool` that start with `true`. -/
def startsTrue : Millennium.Language (List Bool) := fun w => w.headD false = true

theorem startsTrue_mem_P : {w | startsTrue w} ∈ P (blockEnc Bool) :=
  ⟨fun w => w.headD false,
    (ComputableInPolyTime.of_finite (fun b : Bool => b)).comp
      (ComputableInPolyTime.headD (encA := encFinite Bool) (encL := blockEnc Bool) false),
    fun _ => Iff.rfl⟩

theorem startsTrue_clayP :
    Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool) startsTrue :=
  (clayP_iff_cslib Bool startsTrue).mpr startsTrue_mem_P

/-! ### 2. SAT in NP -/

/-- The binary image of SAT. -/
def satWords : Set (List Bool) := encCNF '' SAT

theorem satWords_mem_NP_bits : satWords ∈ NP encBits := image_SAT_mem_NP

theorem satWords_mem_NP : satWords ∈ NP (blockEnc Bool) :=
  PolyTimeReducible.mem_NP ⟨fun w => w, blockEnc_to_bits, fun _ => Iff.rfl⟩ satWords_mem_NP_bits

theorem satWords_clayNP :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Bool)
      (fun w => w ∈ satWords) :=
  (clayNP_iff_cslib Bool (fun w => w ∈ satWords)).mpr satWords_mem_NP

/-! ### 3. A language outside NP -/

/-- The binary image of the halting problem. -/
def haltWords : Set (List Bool) := encPair encBits encBits '' haltingProblem

theorem haltWords_notMem_NP_bits : haltWords ∉ NP encBits := by
  intro h
  have hred : PolyTimeReducible (encPair encBits encBits) encBits haltingProblem haltWords :=
    ⟨encPair encBits encBits, ComputableInPolyTime.of_eq fun _ => rfl,
      fun _ => ((encPair encBits encBits).injective.mem_set_image).symm⟩
  exact haltingProblem_notMem_NP (hred.mem_NP h)

theorem haltWords_notMem_NP : haltWords ∉ NP (blockEnc Bool) := fun h =>
  haltWords_notMem_NP_bits
    (PolyTimeReducible.mem_NP ⟨fun w => w, bits_to_blockEnc, fun _ => Iff.rfl⟩ h)

/-- Clay's NP is not the class of all languages. -/
theorem haltWords_not_clayNP :
    ¬ Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Bool)
      (fun w => w ∈ haltWords) := fun h =>
  haltWords_notMem_NP ((clayNP_iff_cslib Bool (fun w => w ∈ haltWords)).mp h)

/-- Clay's P is not the class of all languages. -/
theorem haltWords_not_clayP :
    ¬ Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool)
      (fun w => w ∈ haltWords) := fun h =>
  haltWords_notMem_NP (P_subset_NP ((clayP_iff_cslib Bool (fun w => w ∈ haltWords)).mp h))

end Monteverde.Tests

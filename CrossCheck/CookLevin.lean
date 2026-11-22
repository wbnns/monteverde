import Monteverde
import Tests.NonVacuity
import Vendor.CookLevin.Pkg

/-!
# Cook-Levin cross-check

The design doc asks for this test: "After L2, the Cook-Levin proof in millennium-cook-levin
(against Clay) and the one in cslib-frontier must transfer to each other. If they disagree, a
definition is wrong." It is a test. The claim does not use it.

There are two independent Cook-Levin proofs:

* millennium-cook-levin, `PvsNP.cook_levin`: its SAT language `PvsNP.SAT` (a dense bit encoding of
  CNF formulas) is NP-complete for the Clay definitions (vendored in `Vendor/CookLevin/`).
* cslib-frontier, `Cslib.Complexity.CookLevin.SAT_npComplete`: its `SAT` is NP-complete for the
  cslib-frontier definitions. `satWords` is the binary image of this `SAT`.

The two SAT languages use different encodings, and neither library has a Lean reduction between
them. The test transfers each Cook-Levin proof through the Monteverde bridges:

1. `mcl_SAT_mem_NP`: the Clay proof that `PvsNP.SAT` is in NP gives cslib-frontier NP.
2. `mcl_SAT_mem_P_iff`: in cslib-frontier, `PvsNP.SAT` is in P exactly when P = NP.
3. `satWords_clayP_iff`: in Clay, the cslib-frontier SAT is in P exactly when the Clay statement
   holds.
4. `cook_levin_agree_clay`, `cook_levin_agree_cslib`: the two SAT languages are in P together,
   on each side.
5. `mcl_SAT_npComplete`: millennium-cook-levin's SAT is NP-complete for the cslib-frontier
   definitions. `satWords_clayNPComplete`: cslib-frontier's SAT is NP-complete for the Clay
   definitions. These move many-one reductions with the reduction bridge
   `Monteverde.clayReducible_iff_cslib`.

It also proves Clay's P ⊆ NP with no hypothesis (`clay_P_subset_NP`).
-/

namespace Monteverde.CrossCheck

open Millennium Cslib.Complexity Turing.MultiTapeTM Monteverde.Tests

/-! ### The Clay side, from millennium-cook-levin -/

/-- millennium-cook-levin discharges the composition hypothesis of the Clay file. So the Clay
file's results that assume it (for example P ⊆ NP) hold with no hypothesis. -/
theorem clay_composition : ClayPVersusNP.Support.PolynomialTimeComputableComposition :=
  PvsNP.comp

/-- With the composition hypothesis discharged, Clay's P ⊆ NP holds with no hypothesis. -/
theorem clay_P_subset_NP (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) :
    InPolynomialTime (fin_encoding_string alphabet) L →
      InNondeterministicPolynomialTime (fin_encoding_string alphabet) L :=
  PolynomialTimeContainedInNondeterministicPolynomialTime.of_turing_machine_composition
    clay_composition alphabet L

/-- The Clay Cook-Levin theorem in the form used here: `PvsNP.SAT` is in Clay P exactly when the
Clay statement holds. -/
theorem mcl_SAT_clayP_iff :
    InPolynomialTime (fin_encoding_string Bool) PvsNP.SAT ↔ ClayPVersusNP :=
  ⟨fun h => ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time
      PvsNP.comp PvsNP.cook_levin h,
    fun h => (h Bool PvsNP.SAT).2 PvsNP.sat_in_np⟩

/-! ### 1 and 2. The Clay proof, moved to cslib-frontier -/

theorem mcl_SAT_mem_NP : {w | PvsNP.SAT w} ∈ NP (blockEnc Bool) :=
  (clayNP_iff_cslib Bool PvsNP.SAT).mp PvsNP.sat_in_np

theorem mcl_SAT_mem_P_iff : {w | PvsNP.SAT w} ∈ P (blockEnc Bool) ↔ CslibPEqNP :=
  (clayP_iff_cslib Bool PvsNP.SAT).symm.trans (mcl_SAT_clayP_iff.trans clay_iff_cslib)

/-! ### 3. The cslib-frontier proof, moved to Clay -/

/-- The cslib-frontier Cook-Levin theorem in the form used here. -/
theorem satWords_mem_P_iff : satWords ∈ P encBits ↔ CslibPEqNP :=
  ⟨cslibPEqNP_of_image_SAT_mem_P, fun h => h encBits ▸ image_SAT_mem_NP⟩

theorem satWords_clayP_iff :
    InPolynomialTime (fin_encoding_string Bool) (· ∈ satWords) ↔ ClayPVersusNP := by
  refine (clayP_iff_cslib Bool (· ∈ satWords)).trans ?_
  refine Iff.trans ?_ (satWords_mem_P_iff.trans clay_iff_cslib.symm)
  exact ⟨PolyTimeReducible.mem_P ⟨fun w => w, bits_to_blockEnc, fun _ => Iff.rfl⟩,
    PolyTimeReducible.mem_P ⟨fun w => w, blockEnc_to_bits, fun _ => Iff.rfl⟩⟩

/-! ### 4. The two Cook-Levin proofs agree -/

/-- In Clay, the two SAT languages are in P together. -/
theorem cook_levin_agree_clay :
    InPolynomialTime (fin_encoding_string Bool) PvsNP.SAT ↔
      InPolynomialTime (fin_encoding_string Bool) (· ∈ satWords) :=
  mcl_SAT_clayP_iff.trans satWords_clayP_iff.symm

/-- In cslib-frontier, the two SAT languages are in P together. -/
theorem cook_levin_agree_cslib :
    {w | PvsNP.SAT w} ∈ P (blockEnc Bool) ↔ satWords ∈ P encBits :=
  mcl_SAT_mem_P_iff.trans satWords_mem_P_iff.symm

/-! ### 5. Full NP-completeness, moved both ways

With the L1 bridge for word outputs, reductions move too (`Monteverde.clayReducible_iff_cslib`).
So each library's SAT is NP-complete on the other side. Each proof uses both Cook-Levin proofs:
one for hardness, and the other to reach the other library's SAT. -/

/-- cslib-frontier's SAT reduces to millennium-cook-levin's SAT, in cslib-frontier. -/
theorem SAT_reduces_to_mcl_SAT :
    PolyTimeReducible encCNF (blockEnc Bool) SAT {w | PvsNP.SAT w} := by
  have h₁ : PolyTimeReducible encCNF encBits SAT satWords :=
    ⟨encCNF, ComputableInPolyTime.of_eq fun _ => rfl,
      fun a => (encCNF.injective.mem_set_image).symm⟩
  have h₂ : PolyTimeReducible encBits (blockEnc Bool) satWords satWords :=
    ⟨fun w => w, bits_to_blockEnc, fun _ => Iff.rfl⟩
  have h₃ : PolyTimeReducible (blockEnc Bool) (blockEnc Bool) satWords {w | PvsNP.SAT w} :=
    polyTimeReducible_of_clay (PvsNP.cook_levin.2 (fin_encoding_string Bool) _ satWords_clayNP)
  exact (h₁.trans h₂).trans h₃

/-- **millennium-cook-levin's Cook-Levin theorem, in cslib-frontier.** Its SAT is NP-complete
for the cslib-frontier definitions. -/
theorem mcl_SAT_npComplete : NPComplete (blockEnc Bool) {w | PvsNP.SAT w} :=
  ⟨mcl_SAT_mem_NP, CookLevin.SAT_npComplete.2.trans SAT_reduces_to_mcl_SAT⟩

/-- millennium-cook-levin's SAT reduces to cslib-frontier's SAT, in Clay. -/
theorem mcl_SAT_reduces_to_satWords :
    PolynomialTimeReducible (fin_encoding_string Bool) (fin_encoding_string Bool) PvsNP.SAT
      (· ∈ satWords) := by
  have h₁ : PolyTimeReducible (blockEnc Bool) encCNF {w | PvsNP.SAT w} SAT :=
    CookLevin.SAT_npComplete.2 _ _ mcl_SAT_mem_NP
  have h₂ : PolyTimeReducible encCNF encBits SAT satWords :=
    ⟨encCNF, ComputableInPolyTime.of_eq fun _ => rfl,
      fun a => (encCNF.injective.mem_set_image).symm⟩
  have h₃ : PolyTimeReducible encBits (blockEnc Bool) satWords satWords :=
    ⟨fun w => w, bits_to_blockEnc, fun _ => Iff.rfl⟩
  exact clay_of_polyTimeReducible ((h₁.trans h₂).trans h₃)

/-- **cslib-frontier's Cook-Levin theorem, in Clay.** Its SAT is NP-complete for the Clay
definitions. -/
theorem satWords_clayNPComplete :
    NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) (· ∈ satWords) :=
  NondeterministicPolynomialTimeComplete.transfer _ _ _ _ PvsNP.comp PvsNP.cook_levin
    satWords_clayNP mcl_SAT_reduces_to_satWords

end Monteverde.CrossCheck

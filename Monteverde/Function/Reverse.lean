import Monteverde.Encoding.BlockEnc
import Monteverde.Function.Recoder
import Monteverde.Function.Decoder
import Monteverde.Function.Drain
import Vendor.CookLevin.Comp
import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer

/-!
# L1 reverse: cslib-frontier to Clay machines

A cslib-frontier polynomial-time function under the block code gives a Mathlib TM2 machine over
the original alphabet. The proof composes three parts:

1. the recoder machine (`Monteverde.Recoder.recoder`), from words over `Γ` to their block code;
2. cslib-frontier's compiler from binary multi-tape machines to TM2
   (`ComputableInPolyTime.exists_tm2ComputableInPolyTime`);
3. the composition of polynomial-time TM2 machines (`PvsNP.tm2ComputableInPolyTime_comp`, from
   millennium-cook-levin, vendored in `Vendor/CookLevin/Comp.lean`).
-/

namespace Monteverde

open Turing Turing.MultiTapeTM

/-- The block code as a function of a word, through the recoder's symbol code. -/
theorem blockEnc_eq_flatMap (Γ : Type) [Fintype Γ] (w : List Γ) :
    blockEnc Γ w = w.flatMap (fun a => frame (encFinite Γ a)) := rfl

/-- **L1 reverse.** A cslib-frontier polynomial-time decision procedure under the block code is a
Mathlib TM2 polynomial-time decision procedure over the alphabet itself. -/
theorem tm2_of_computableInPolyTime {α Γ : Type} [Fintype Γ] {e : α → List Γ}
    (he : Function.Injective e) {f : α → Bool}
    (hc : ComputableInPolyTime f ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ)) encBool) :
    Nonempty (TM2ComputableInPolyTime e (fun b : Bool => [b]) f) := by
  obtain ⟨h₂, -⟩ := hc.exists_tm2ComputableInPolyTime
  have h₁ : TM2ComputableInPolyTime e ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ)) id :=
    Recoder.recoder (fun a => frame (encFinite Γ a)) e
  exact PvsNP.tm2ComputableInPolyTime_comp h₁ h₂

/-- **L1 reverse, word outputs.** A cslib-frontier polynomial-time function under the block codes
is a Mathlib TM2 polynomial-time function between the words themselves. If the output alphabet
is empty, the drain machine does the work; else the recoder, the cslib-frontier machine and the
decoder machine run in sequence. -/
theorem tm2_of_computableInPolyTime_words {α β Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    {e : α → List Γ} {eo : β → List Δ} (he : Function.Injective e) (heo : Function.Injective eo)
    {f : α → β}
    (hc : ComputableInPolyTime f ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ))
      ((⟨eo, heo⟩ : β ↪ List Δ).trans (blockEnc Δ))) :
    Nonempty (TM2ComputableInPolyTime e eo f) := by
  rcases isEmpty_or_nonempty Δ with hΔ | hΔ
  · exact ⟨Drain.drainer e eo f⟩
  obtain ⟨h₂, -⟩ := hc.exists_tm2ComputableInPolyTime
  have h₁ : TM2ComputableInPolyTime e ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ)) id :=
    Recoder.recoder (fun a => frame (encFinite Γ a)) e
  have h₃ : TM2ComputableInPolyTime ((⟨eo, heo⟩ : β ↪ List Δ).trans (blockEnc Δ)) eo id :=
    Decoder.decoder eo
  obtain ⟨h₁₂⟩ := PvsNP.tm2ComputableInPolyTime_comp h₁ h₂
  have h := PvsNP.tm2ComputableInPolyTime_comp h₁₂ h₃
  exact h

end Monteverde

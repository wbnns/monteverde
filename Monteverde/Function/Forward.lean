import Monteverde.Encoding.BlockEnc
import Monteverde.Function.Finitize
import CslibFrontier.Computability.Machines.Turing.TM2.PolyTime

/-!
# L1 forward: Clay machines to cslib-frontier

A Mathlib TM2 machine that decides `f` in polynomial time on words over a finite alphabet `Γ`
gives a cslib-frontier polynomial-time computation of `f` under the block code `blockEnc Γ`.

The proof makes all stack alphabets finite (`Monteverde.TM2ComputableInPolyTime.exists_finite`),
applies cslib-frontier's bridge `computableInPolyTime_encList`, and fixes the output encoding of
the Boolean answer with `ComputableInPolyTime.of_finite`.
-/

namespace Monteverde

open Turing Turing.MultiTapeTM

theorem singleton_injective : Function.Injective (fun b : Bool => [b]) :=
  fun _ _ h => List.head_eq_of_cons_eq h

/-- **L1 forward.** A polynomial-time TM2 decision procedure over a finite alphabet `Γ` is a
cslib-frontier polynomial-time function under the block code. The input is any injective
encoding `e : α → List Γ`. -/
theorem computableInPolyTime_of_tm2 {α Γ : Type} [Finite Γ] {e : α → List Γ}
    (he : Function.Injective e) {f : α → Bool}
    (h : TM2ComputableInPolyTime e (fun b : Bool => [b]) f) :
    ComputableInPolyTime f ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ)) encBool := by
  obtain ⟨h', hfin⟩ := TM2ComputableInPolyTime.exists_finite h
  have hc := @Turing.TM2ComputableInPolyTime.computableInPolyTime_encList _ _ _ _ _
    (encFinite Γ) (encFinite Bool) e (fun b : Bool => [b]) f h' hfin he singleton_injective
  exact (ComputableInPolyTime.of_finite (fun b : Bool => b)).comp hc

/-- **L1 forward, word outputs.** A polynomial-time TM2 function from words over `Γ` to words
over `Δ` is a cslib-frontier polynomial-time function under the block codes of both alphabets. -/
theorem computableInPolyTime_of_tm2_words {α β Γ Δ : Type} [Finite Γ] [Finite Δ]
    {e : α → List Γ} {eo : β → List Δ} (he : Function.Injective e) (heo : Function.Injective eo)
    {f : α → β} (h : TM2ComputableInPolyTime e eo f) :
    ComputableInPolyTime f ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ))
      ((⟨eo, heo⟩ : β ↪ List Δ).trans (blockEnc Δ)) := by
  obtain ⟨h', hfin⟩ := TM2ComputableInPolyTime.exists_finite h
  exact @Turing.TM2ComputableInPolyTime.computableInPolyTime_encList _ _ _ _ _
    (encFinite Γ) (encFinite Δ) e eo f h' hfin he heo

end Monteverde

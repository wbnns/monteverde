import Monteverde.Function.Forward
import Monteverde.Function.Reverse

/-!
# L1: polynomial-time decision procedures on both sides

For a finite alphabet `Γ` and an injective encoding `e : α → List Γ`, a Boolean function has a
Mathlib TM2 polynomial-time certificate on `e` exactly when it is cslib-frontier polynomial-time
under `e` followed by the block code.
-/

namespace Monteverde

open Turing Turing.MultiTapeTM

/-- **L1.** TM2 polynomial time over `Γ` is cslib-frontier polynomial time under the block code. -/
theorem tm2_iff_computableInPolyTime {α Γ : Type} [Fintype Γ] {e : α → List Γ}
    (he : Function.Injective e) (f : α → Bool) :
    Nonempty (TM2ComputableInPolyTime e (fun b : Bool => [b]) f) ↔
      ComputableInPolyTime f ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ)) encBool :=
  ⟨fun ⟨h⟩ => computableInPolyTime_of_tm2 he h, tm2_of_computableInPolyTime he⟩

/-- **L1, word outputs.** TM2 polynomial time from words over `Γ` to words over `Δ` is
cslib-frontier polynomial time under the block codes of both alphabets. -/
theorem tm2_iff_computableInPolyTime_words {α β Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    {e : α → List Γ} {eo : β → List Δ} (he : Function.Injective e) (heo : Function.Injective eo)
    (f : α → β) :
    Nonempty (TM2ComputableInPolyTime e eo f) ↔
      ComputableInPolyTime f ((⟨e, he⟩ : α ↪ List Γ).trans (blockEnc Γ))
        ((⟨eo, heo⟩ : β ↪ List Δ).trans (blockEnc Δ)) :=
  ⟨fun ⟨h⟩ => computableInPolyTime_of_tm2_words he heo h,
    tm2_of_computableInPolyTime_words he heo⟩

end Monteverde

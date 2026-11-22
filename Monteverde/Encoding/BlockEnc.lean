import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Tactic.Linarith

/-!
# L0: the block code of words over a finite alphabet

`blockEnc Γ` writes a word over a finite alphabet `Γ` as a binary word. Each symbol becomes the
framed unary code of its index (`encFinite Γ`), and the word is the concatenation of the frames
(`encList`).

This is exactly the input encoding that cslib-frontier's TM2 bridge
`Turing.TM2ComputableInPolyTime.computableInPolyTime_encList` produces for a machine over `Γ`.
So the forward direction (Clay machines to cslib-frontier) needs no recoding.
-/

namespace Monteverde

open Turing.MultiTapeTM

/-- The block code: words over a finite alphabet `Γ` as binary words. -/
noncomputable abbrev blockEnc (Γ : Type) [Finite Γ] : List Γ ↪ List Bool :=
  encList (encFinite Γ)

theorem blockEnc_apply (Γ : Type) [Finite Γ] (w : List Γ) :
    blockEnc Γ w = w.flatMap (fun a => frame (encFinite Γ a)) := rfl

theorem blockEnc_injective (Γ : Type) [Finite Γ] : Function.Injective (blockEnc Γ) :=
  (blockEnc Γ).injective

theorem length_frame (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame] at ih ⊢; omega

/-- Each symbol costs at most `2 |Γ| + 1` bits. -/
theorem length_blockEnc_le (Γ : Type) [Finite Γ] (w : List Γ) :
    (blockEnc Γ w).length ≤ (2 * Nat.card Γ + 1) * w.length := by
  induction w with
  | nil => simp [blockEnc_apply]
  | cons a w ih =>
    have ha := length_encFinite_lt a
    rw [blockEnc_apply] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, length_frame, List.length_cons] at ih ⊢
    nlinarith

/-- Each symbol costs at least one bit. -/
theorem length_le_blockEnc (Γ : Type) [Finite Γ] (w : List Γ) :
    w.length ≤ (blockEnc Γ w).length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [blockEnc_apply] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, length_frame, List.length_cons] at ih ⊢
    omega

end Monteverde

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

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
noncomputable def blockEnc (Γ : Type) [Finite Γ] : List Γ ↪ List Bool :=
  encList (encFinite Γ)

theorem blockEnc_apply (Γ : Type) [Finite Γ] (w : List Γ) :
    blockEnc Γ w = w.flatMap (fun a => frame (encFinite Γ a)) := rfl

theorem blockEnc_injective (Γ : Type) [Finite Γ] : Function.Injective (blockEnc Γ) :=
  (blockEnc Γ).injective

end Monteverde

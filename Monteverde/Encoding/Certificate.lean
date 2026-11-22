import Monteverde.Encoding.BlockEnc
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds

/-!
# L0: decoding certificates over a finite alphabet

Clay certificates are words over any finite alphabet `Δ`. cslib-frontier's witness lemma
`Cslib.Complexity.mem_NP_of_check` reads witnesses with a total `Decoder`. cslib-frontier has no
decoder for `encFinite Δ`, so this file builds one, in three steps:

1. `symDecoder Δ`: a strict partial decoder for one symbol. A symbol's code is the unary word of
   its index, so the decoder looks up the word's length in the fixed list of all symbols.
2. `wordDecoder Δ`: the strict partial decoder for words, by cslib-frontier's
   `PartialDecoder.list`.
3. `certDecoder Δ`: a total decoder for optional words (`encOption (blockEnc Δ)`). A word that
   decodes to nothing gives `none`. The type `Δ` can be empty.
-/

namespace Monteverde

open Turing.MultiTapeTM

variable (Δ : Type) [Finite Δ]

/-- All symbols, in the order of their unary codes. -/
noncomputable def symList : List Δ :=
  let _ := Fintype.ofFinite Δ
  (List.finRange (Fintype.card Δ)).map (Fintype.equivFin Δ).symm

/-- Candidate symbol for a word: the symbol whose index is the word's length. -/
noncomputable def symCandidate (w : List Bool) : Option Δ :=
  ((symList Δ).drop w.length).head?

theorem symCandidate_encFinite (a : Δ) : symCandidate Δ (encFinite Δ a) = some a := by
  let _ := Fintype.ofFinite Δ
  simp only [symCandidate, symList, List.head?_drop, List.getElem?_map, Option.map_eq_some_iff]
  refine ⟨Fintype.equivFin Δ a, ?_, by simp⟩
  change (List.finRange _)[(List.replicate ((Fintype.equivFin Δ) a).val true).length]? = _
  simp

theorem symCandidate_polyTime :
    ComputableInPolyTime (symCandidate Δ) encBits (encOption (encFinite Δ)) :=
  ComputableInPolyTime.listHead?WithInput
    (ComputableInPolyTime.listDropWithInput (ComputableInPolyTime.const _)
      ComputableInPolyTime.length_bits)

/-- Strict decoder for one symbol. -/
noncomputable def symDecoder : PartialDecoder (encFinite Δ) :=
  PartialDecoder.checked (symCandidate Δ) (symCandidate_encFinite Δ) (symCandidate_polyTime Δ)

/-- Strict decoder for words in the block code. -/
noncomputable def wordDecoder : PartialDecoder (blockEnc Δ) :=
  PartialDecoder.list (symDecoder Δ)

/-- Total decoding of optional words. -/
noncomputable def certDecode : List Bool → Option (List Δ)
  | true :: w => (wordDecoder Δ).decode w
  | _ => none

theorem certDecode_eq (w : List Bool) :
    certDecode Δ w = if w.headD false then (wordDecoder Δ).decode w.tail else none := by
  rcases w with _ | ⟨b, w⟩
  · rfl
  · cases b <;> rfl

theorem certDecode_polyTime :
    ComputableInPolyTime (certDecode Δ) encBits (encOption (blockEnc Δ)) := by
  have h : ComputableInPolyTime
      (fun w : List Bool => if w.headD false then (wordDecoder Δ).decode w.tail else none)
      encBits (encOption (blockEnc Δ)) :=
    ComputableInPolyTime.ite (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false)
      ((wordDecoder Δ).computable.comp ComputableInPolyTime.bitsTail)
      (ComputableInPolyTime.const none)
  exact h.of_enc_eq fun w => by rw [certDecode_eq]

/-- **Certificate decoder.** A total decoder for optional words over a finite alphabet. -/
noncomputable def certDecoder : Decoder (encOption (blockEnc Δ)) where
  decode := certDecode Δ
  decode_enc o := by
    rcases o with _ | y
    · rfl
    · change (wordDecoder Δ).decode (blockEnc Δ y) = some y
      exact PartialDecoder.decode_enc _ y
  computable := (certDecode_polyTime Δ).exists_degree

end Monteverde

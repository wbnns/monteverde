import Monteverde.Encoding.BlockEnc
import Vendor.Millennium.Millennium
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# L0: Clay's pair words and cslib-frontier's pairs

Clay checks a certificate `y` for an instance `w` on the word `w#y`: the symbols of `w` tagged
left, one separator, and the symbols of `y` tagged right (`Millennium.pair_encoding`).
cslib-frontier pairs encoded values with `encPair`.

This file moves between the two forms in polynomial time:

* `pairWord` builds `w#y` from `(w, y)`; it is Clay's `pair_encoding` on strings;
* `lefts` and `rights` read `w` and `y` back from `w#y`.
-/

namespace Monteverde

open Turing.MultiTapeTM

variable {Γ Δ : Type}

/-- Clay's pair word `w#y`. -/
def pairWord (p : List Γ × List Δ) : List (Γ ⊕ Option Δ) :=
  p.1.map Sum.inl ++ Sum.inr none :: p.2.map (fun b => Sum.inr (some b))

/-- `pairWord` is Clay's pair encoding of two strings. -/
theorem pair_encoding_encode_eq [Fintype Γ] [Fintype Δ] (p : List Γ × List Δ) :
    (Millennium.pair_encoding (Millennium.fin_encoding_string Γ)
      (Millennium.fin_encoding_string Δ)).encode p = pairWord p := rfl

theorem filterMap_getLeft_pairWord (p : List Γ × List Δ) :
    (pairWord p).filterMap Sum.getLeft? = p.1 := by
  simp [pairWord, List.filterMap_append, List.filterMap_map, Function.comp_def]

theorem filterMap_getRight_pairWord (p : List Γ × List Δ) :
    (pairWord p).filterMap (fun s => s.getRight?.join) = p.2 := by
  simp [pairWord, List.filterMap_append, List.filterMap_map, List.filterMap_cons, Function.comp_def]

theorem pairWord_injective : Function.Injective (pairWord : List Γ × List Δ → _) := by
  intro p q h
  have h₁ := filterMap_getLeft_pairWord p
  have h₂ := filterMap_getRight_pairWord p
  rw [h, filterMap_getLeft_pairWord] at h₁
  rw [h, filterMap_getRight_pairWord] at h₂
  exact Prod.ext h₁.symm h₂.symm

/-- The left symbols of a pair word. -/
def leftSym [Inhabited Γ] : Γ ⊕ Option Δ → Γ
  | .inl a => a
  | .inr _ => default

/-- The right symbols of a pair word. -/
def rightSym [Inhabited Δ] : Γ ⊕ Option Δ → Δ
  | .inr (some b) => b
  | _ => default

/-- A right symbol (not the separator). -/
def isRightSym : Γ ⊕ Option Δ → Bool
  | .inr (some _) => true
  | _ => false

/-- Read `w` back from `w#y`. -/
def lefts [Inhabited Γ] (s : List (Γ ⊕ Option Δ)) : List Γ :=
  (s.filter Sum.isLeft).map leftSym

/-- Read `y` back from `w#y`. -/
def rights [Inhabited Δ] (s : List (Γ ⊕ Option Δ)) : List Δ :=
  (s.filter isRightSym).map rightSym

theorem lefts_pairWord [Inhabited Γ] (p : List Γ × List Δ) : lefts (pairWord p) = p.1 := by
  obtain ⟨w, y⟩ := p
  simp only [lefts, pairWord, List.filter_append, List.filter_cons, List.filter_map,
    List.map_append, List.map_map]
  simp [Function.comp_def, leftSym]

theorem rights_pairWord [Inhabited Δ] (p : List Γ × List Δ) : rights (pairWord p) = p.2 := by
  obtain ⟨w, y⟩ := p
  simp only [rights, pairWord, List.filter_append, List.filter_cons, List.filter_map,
    List.map_append, List.map_map]
  simp [Function.comp_def, rightSym, isRightSym]

variable [Finite Γ] [Finite Δ]

/-- Building `w#y` is polynomial-time. -/
theorem pairWord_polyTime :
    ComputableInPolyTime (pairWord : List Γ × List Δ → _)
      (encPair (blockEnc Γ) (blockEnc Δ)) (blockEnc (Γ ⊕ Option Δ)) := by
  have hl : ComputableInPolyTime (fun p : List Γ × List Δ => p.1.map (Sum.inl : _ → Γ ⊕ Option Δ))
      (encPair (blockEnc Γ) (blockEnc Δ)) (blockEnc (Γ ⊕ Option Δ)) :=
    (ComputableInPolyTime.map (ComputableInPolyTime.of_finite _)).comp
      (ComputableInPolyTime.fst (blockEnc Γ) (blockEnc Δ))
  have hr : ComputableInPolyTime
      (fun p : List Γ × List Δ => p.2.map (fun b => (Sum.inr (some b) : Γ ⊕ Option Δ)))
      (encPair (blockEnc Γ) (blockEnc Δ)) (blockEnc (Γ ⊕ Option Δ)) :=
    (ComputableInPolyTime.map (ComputableInPolyTime.of_finite _)).comp
      (ComputableInPolyTime.snd (blockEnc Γ) (blockEnc Δ))
  exact ComputableInPolyTime.listAppend' hl
    (ComputableInPolyTime.cons' (ComputableInPolyTime.const _) hr)

/-- Reading `(w, y)` back from `w#y` is polynomial-time. -/
theorem unpair_polyTime [Inhabited Γ] [Inhabited Δ] :
    ComputableInPolyTime (fun s : List (Γ ⊕ Option Δ) => (lefts s, rights s))
      (blockEnc (Γ ⊕ Option Δ)) (encPair (blockEnc Γ) (blockEnc Δ)) := by
  have hl : ComputableInPolyTime (lefts : List (Γ ⊕ Option Δ) → List Γ)
      (blockEnc (Γ ⊕ Option Δ)) (blockEnc Γ) :=
    (ComputableInPolyTime.map (ComputableInPolyTime.of_finite _)).comp
      (ComputableInPolyTime.filter (ComputableInPolyTime.of_finite _))
  have hr : ComputableInPolyTime (rights : List (Γ ⊕ Option Δ) → List Δ)
      (blockEnc (Γ ⊕ Option Δ)) (blockEnc Δ) :=
    (ComputableInPolyTime.map (ComputableInPolyTime.of_finite _)).comp
      (ComputableInPolyTime.filter (ComputableInPolyTime.of_finite _))
  exact hl.prod hr

end Monteverde

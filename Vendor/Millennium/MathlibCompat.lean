/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Mathlib.Data.Fintype.Basic

/-!
# Mathlib v4.31 bundled `FinEncoding` (toolchain compatibility shim)

Copied verbatim from `Mathlib/Computability/Encoding.lean` at Mathlib commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, the Mathlib that LeanMillenniumPrizeProblems pins.
Only the namespace differs (`MathlibV431` instead of `Computability`).

Later Mathlib (2026-05-07) unbundled `Encoding` and deprecated `FinEncoding`. The vendored Clay
file is written against the bundled structures, so it uses this copy. The definitions are the
same, so the Clay statements keep their meaning. `scripts/diff_vendor.sh` checks this file
against the upstream Mathlib source.
-/

universe u v

namespace MathlibV431

-- BEGIN VERBATIM fabf563:Mathlib/Computability/Encoding.lean (Encoding, FinEncoding)
/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure Encoding (α : Type u) where
  /-- The alphabet of the encoding -/
  Γ : Type v
  /-- The encoding function -/
  encode : α → List Γ
  /-- The decoding function -/
  decode : List Γ → Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] Encoding.decode_encode

theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]

/-- An `Encoding` plus a guarantee of finiteness of the alphabet. -/
structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  /-- The alphabet of the encoding is finite -/
  ΓFin : Fintype Γ

instance Γ.fintype {α : Type u} (e : FinEncoding α) : Fintype e.toEncoding.Γ :=
  e.ΓFin
-- END VERBATIM

-- BEGIN VERBATIM fabf563:Mathlib/Computability/Encoding.lean (finEncodingBoolBool)
/-- An encoding function of `Bool` in `Bool`. -/
def encodeBool : Bool → List Bool := pure

/-- A decoding function from `List Bool` to `Bool`. -/
def decodeBool : List Bool → Bool
  | b :: _ => b
  | _ => Inhabited.default

@[simp] theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl

/-- A `FinEncoding` of `Bool` in `Bool`. -/
def finEncodingBoolBool : FinEncoding Bool where
  Γ := Bool
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)
  ΓFin := Bool.fintype
-- END VERBATIM

end MathlibV431

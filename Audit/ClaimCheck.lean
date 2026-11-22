import Monteverde.Classes.Reduction
import Monteverde.Function.Bridge
import Monteverde.Headline.Bits
import Monteverde.Headline.Clay
import Monteverde.Headline.NegativeBranch

/-!
# Claim check

Each `example` states the exact type that the claim describes. If a headline theorem is renamed
or its statement changes, this file fails to build, and CI fails.
-/

open Cslib.Complexity Turing.MultiTapeTM

/-- `CslibPEqNP` is P = NP for every instance encoding (the form of `NPComplete.mem_P_iff`). -/
example : Monteverde.CslibPEqNP =
    ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc := rfl

/-- The binary-string form. -/
example : Monteverde.CslibPEqNP ↔ P encBits = NP encBits := Monteverde.cslibPEqNP_iff_bits

/-- The positive official Clay target. -/
example : Millennium.ClayPVersusNP ↔ Monteverde.CslibPEqNP := Monteverde.clay_iff_cslib

/-- The negative official Clay target. -/
example : Millennium.ClayPVersusNP.Formulations.NegativeBranch ↔ ¬ Monteverde.CslibPEqNP :=
  Monteverde.clay_negative_iff_cslib

/-- The official targets are the vendored definitions, unchanged. -/
example : Millennium.ClayPVersusNP = Millennium.ClayPVersusNP.Formulations.ClassEquality := rfl
example : Millennium.ClayPVersusNP.Formulations.NegativeBranch = ¬ Millennium.ClayPVersusNP := rfl

/-- The class bridges (G2). -/
example (Γ : Type) [Fintype Γ] [Nontrivial Γ] (L : Millennium.Language (List Γ)) :
    Millennium.InPolynomialTime (Millennium.fin_encoding_string Γ) L ↔
      {w | L w} ∈ P (Monteverde.blockEnc Γ) :=
  Monteverde.clayP_iff_cslib Γ L

example (Γ : Type) [Fintype Γ] [Nontrivial Γ] (L : Millennium.Language (List Γ)) :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Γ) L ↔
      {w | L w} ∈ NP (Monteverde.blockEnc Γ) :=
  Monteverde.clayNP_iff_cslib Γ L

/-! ### The isolated statements (`Monteverde/Statements/`) -/

example : Monteverde.Statements.CslibPEqNPIffBits := Monteverde.cslibPEqNP_iff_bits
example : Monteverde.Statements.ClayIffCslib := Monteverde.clay_iff_cslib
example : Monteverde.Statements.ClayNegativeIffCslib := Monteverde.clay_negative_iff_cslib

/-! ### The class bridge interface, word for word as the design doc writes it

The design doc writes `setOf L`. Mathlib deprecated the name `setOf` (an alias of `Set.ofPred`)
on 2026-07-09, so the theorems write `{w | L w}`, the same set. These examples check the design
doc's exact text against the theorems. -/

set_option linter.deprecated false in
example (Γ : Type) [Fintype Γ] [Nontrivial Γ] (L : Millennium.Language (List Γ)) :
    Millennium.InPolynomialTime (Millennium.fin_encoding_string Γ) L ↔
      setOf L ∈ Cslib.Complexity.P (Monteverde.blockEnc Γ) :=
  Monteverde.clayP_iff_cslib Γ L

set_option linter.deprecated false in
example (Γ : Type) [Fintype Γ] [Nontrivial Γ] (L : Millennium.Language (List Γ)) :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Γ) L ↔
      setOf L ∈ Cslib.Complexity.NP (Monteverde.blockEnc Γ) :=
  Monteverde.clayNP_iff_cslib Γ L

/-! ### L1 for every finite alphabet (design doc, layer L1) -/

example {α β Γ Δ : Type} [Fintype Γ] [Fintype Δ] {e : α → List Γ} {eo : β → List Δ}
    (he : Function.Injective e) (heo : Function.Injective eo) (f : α → β) :
    Nonempty (Turing.TM2ComputableInPolyTime e eo f) ↔
      ComputableInPolyTime f ((⟨e, he⟩ : α ↪ List Γ).trans (Monteverde.blockEnc Γ))
        ((⟨eo, heo⟩ : β ↪ List Δ).trans (Monteverde.blockEnc Δ)) :=
  Monteverde.tm2_iff_computableInPolyTime_words he heo f

import Monteverde.Statements.Bits
import Monteverde.Statements.Clay
import Monteverde.Statements.NegativeBranch

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

# Monteverde

[![CI](https://github.com/wbnns/monteverde/actions/workflows/ci.yml/badge.svg)](https://github.com/wbnns/monteverde/actions/workflows/ci.yml)
[![Independent kernel check](https://github.com/wbnns/monteverde/actions/workflows/kernel-check.yml/badge.svg)](https://github.com/wbnns/monteverde/actions/workflows/kernel-check.yml)

**Monteverde proves in Lean 4 that the LeanMillenniumPrizeProblems formulation of the Clay
P vs NP statement is equivalent to P vs NP in
[cslib-frontier](https://github.com/cslib-community/cslib-frontier), the largest Lean complexity
library.**

The two statements are:

* the Clay statement as [LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
  formalizes it (`Millennium.ClayPVersusNP`, after Stephen Cook's official problem description),
  and
* P = NP in cslib-frontier, for every encoding of instances.

Monteverde does **not** resolve P vs NP. It connects the two statements, so that a Lean result
about one is a Lean result about the other. For example, a cslib-frontier proof that SAT is in P
gives the Clay statement, and a cslib-frontier proof that some NP problem is not in P gives the
negative Clay statement.

## Contents

1. [At a glance](#at-a-glance)
2. [The main theorems](#the-main-theorems)
3. [The two definitions of P and NP](#the-two-definitions-of-p-and-np)
4. [How to use the results](#how-to-use-the-results)
5. [How the proof works](#how-the-proof-works)
6. [Reusable results](#reusable-results)
7. [Trust and verification](#trust-and-verification)
8. [The Cook-Levin cross-check](#the-cook-levin-cross-check)
9. [Cook's text against the Lean statement](#cooks-text-against-the-lean-statement)
10. [Library size](#library-size)
11. [Build](#build)
12. [Repository map](#repository-map)
13. [Contributing](#contributing)
14. [History, open questions, citation, credits](#history)

## At a glance

| | |
|---|---|
| Result | `Millennium.ClayPVersusNP ↔ CslibPEqNP` and `NegativeBranch ↔ ¬ CslibPEqNP` |
| Also | `CslibPEqNP ↔ P encBits = NP encBits`, and bridges for P, NP, reductions and polynomial-time functions over every finite alphabet |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only. No `sorry`. |
| Independent check | nanoda (a Lean type checker written in Rust) re-checks the exported proofs: 16,507 declarations, no errors |
| Lean | `leanprover/lean4:v4.36.0-rc2` |
| Pins | cslib-frontier `9bfe667`, LeanMillenniumPrizeProblems `603053d` (vendored), millennium-cook-levin `879c483` (vendored) |
| Website | [monteverde.willbinns.org](https://monteverde.willbinns.org) |
| Release | [v1.1.0](https://github.com/wbnns/monteverde/releases/tag/v1.1.0), November 22, 2026 |
| License | Apache-2.0 |
| Development | Developed with AI assistance (Claude, by Anthropic). Every proof is checked by the Lean kernel and, independently, by nanoda. |

## The main theorems

```lean
-- Monteverde/Statements/Defs.lean
/-- P vs NP as cslib-frontier states it: the form of `NPComplete.mem_P_iff`. -/
def CslibPEqNP : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool), Cslib.Complexity.P enc = Cslib.Complexity.NP enc

-- Monteverde/Headline/
theorem cslibPEqNP_iff_bits : CslibPEqNP ↔ P encBits = NP encBits
theorem clay_iff_cslib : Millennium.ClayPVersusNP ↔ CslibPEqNP
theorem clay_negative_iff_cslib :
    Millennium.ClayPVersusNP.Formulations.NegativeBranch ↔ ¬ CslibPEqNP
```

All names are in the namespace `Monteverde`.

* `Millennium.ClayPVersusNP` and `Millennium.ClayPVersusNP.Formulations.NegativeBranch` are the
  two official targets of LeanMillenniumPrizeProblems. `NegativeBranch` is defined as
  `¬ ClayPVersusNP`.
* cslib-frontier has no named "P = NP" proposition. Its own theorems
  (`NPComplete.mem_P_iff`) state P = NP for every encoding `enc : α ↪ List Bool` of instances.
  `CslibPEqNP` is exactly that form.
* `cslibPEqNP_iff_bits` shows that this form is equivalent to the plain form on binary strings,
  `P encBits = NP encBits`. So both readings of "P = NP in cslib-frontier" are covered.

## The two definitions of P and NP

Both libraries build on Mathlib. They define P and NP in different ways.

### The Clay side (LeanMillenniumPrizeProblems)

Vendored at `Vendor/Millennium/Millennium.lean`. The machine model is Mathlib's multi-stack
Turing machine `Turing.FinTM2`, and polynomial time is Mathlib's `TM2ComputableInPolyTime`: a
machine that maps the encoded input to the encoded output in at most `p(n)` steps, for a
polynomial `p` and input length `n`.

```lean
def Language (α : Type) := α → Prop

def InPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : TM2ComputableInPolyTime ea.encode finEncodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

-- R is polynomial-time when the language { w#y | R w y } is in P (Cook's L_R).
def PolynomialTimeCheckingRelation {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (R : α → β → Prop) : Prop :=
  InPolynomialTime (pair_encoding ea eb) (fun p => R p.1 p.2)

def InNondeterministicPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    PolynomialTimeCheckingRelation ea (fin_encoding_string Γ₁) R ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y

def ClayPVersusNP : Prop :=   -- = ClayPVersusNP.Formulations.ClassEquality
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InPolynomialTime (fin_encoding_string alphabet) L ↔
      InNondeterministicPolynomialTime (fin_encoding_string alphabet) L
```

`fin_encoding_string Γ` encodes a word over `Γ` as itself. `pair_encoding` writes a pair as
Cook's `w#y`: the symbols of `w` tagged left, one separator, the symbols of `y` tagged right.

### The cslib-frontier side

The machine model is cslib-frontier's own multi-tape Turing machine over the binary alphabet.
Instances are encoded by an injective map `enc : α ↪ List Bool`.

```lean
-- f is computable in polynomial time from encIn to encOut: some binary multi-tape machine with
-- finitely many states computes it in polynomially bounded time and space.
def ComputableInPolyTime (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop

def P (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool, ComputableInPolyTime f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true}

def IsVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool) (A : Set α) :
    Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

def NP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsVerifier enc p V A}
```

### How they differ

| Aspect | Clay (LeanMillenniumPrizeProblems) | cslib-frontier |
|--------|------------------------------------|----------------|
| Machine | Mathlib `FinTM2`: finitely many stacks, finite control, any stack alphabets | Binary multi-tape machine, finitely many states |
| Inputs | Words over any finite alphabet `Γ` (`FinEncoding`) | Any type `α` with an injective binary encoding |
| Time | `p(n)` steps, `p : Polynomial ℕ` | Polynomially bounded time and space |
| Certificates | Words over any finite alphabet `Γ₁`, length `≤ n^k` | Binary words of length exactly `p(n)` |
| Checking | A `Prop` relation `R`, decided on the pair word `w#y` | A `Bool` verifier `V` on `encPair` |
| Statement | P = NP for every alphabet with at least two symbols | P = NP for every encoding |

Monteverde proves that these differences do not matter: the classes agree, so the two P = NP
statements agree.

## How to use the results

Add Monteverde as a dependency (see [Build](#build)) and `import Monteverde`. These examples are
checked in CI (`Tests/ReadmeExamples.lean`):

```lean
import Monteverde
open Cslib.Complexity Turing.MultiTapeTM Monteverde

-- A cslib-frontier proof of P = NP on binary strings gives the positive Clay target.
example (h : P encBits = NP encBits) : Millennium.ClayPVersusNP :=
  clay_iff_cslib.mpr (cslibPEqNP_iff_bits.mpr h)

-- A problem in cslib-frontier NP but not in P, for any encoding, gives the negative Clay target.
example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hNP : A ∈ NP enc) (hP : A ∉ P enc) :
    Millennium.ClayPVersusNP.Formulations.NegativeBranch :=
  clay_negative_iff_cslib.mpr fun h => hP (by rw [h enc]; exact hNP)

-- SAT in cslib-frontier P gives the positive Clay target.
example (h : encCNF '' SAT ∈ P encBits) : Millennium.ClayPVersusNP :=
  clay_iff_cslib.mpr (cslibPEqNP_of_image_SAT_mem_P h)

-- The positive Clay target gives P = NP for every cslib-frontier encoding.
example (h : Millennium.ClayPVersusNP) {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  clay_iff_cslib.mp h enc

-- One language moves between the two definitions of P.
example (L : Millennium.Language (List Bool))
    (h : Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool) L) :
    {w | L w} ∈ P (blockEnc Bool) :=
  (clayP_iff_cslib Bool L).mp h
```

What the theorems do **not** say:

* They do not resolve P vs NP.
* They do not prove that Mathlib's `FinTM2` model agrees with Cook's one-tape Turing machine.
  That is a choice of the LeanMillenniumPrizeProblems formulation, and Monteverde's result is
  about that formulation. See difference D1 in the [Cook text audit](Audit/cook_text_audit.md).

## How the proof works

The proof has four layers. Each layer uses only the layers under it. It is about 2,100 lines of
new Lean, in `Monteverde/`.

### L0: encodings (`Monteverde/Encoding/`)

* **Block code** `blockEnc Γ := encList (encFinite Γ)`. The symbol with index `i` becomes the
  bits `(1 1)^i 0`, and a word is the concatenation of its symbols. This is exactly the encoding
  that cslib-frontier's TM2 bridge (`TM2ComputableInPolyTime.computableInPolyTime_encList`)
  produces, so the forward direction needs no recoding.
* **Pair words** (`Pair.lean`): `pairWord` builds Clay's `w#y`, and `lefts`, `rights` read it
  back. Both directions are polynomial time against `encPair`.
* **Certificates** (`Certificate.lean`): `certDecoder`, a total polynomial-time decoder for
  optional words over any finite alphabet. cslib-frontier's witness lemma needs one, and
  cslib-frontier had none for finite alphabets.

### L1: polynomial-time functions (`Monteverde/Function/`)

For finite alphabets `Γ`, `Δ` and injective encodings `e : α → List Γ`, `eo : β → List Δ`:

```lean
theorem tm2_iff_computableInPolyTime_words :
    Nonempty (TM2ComputableInPolyTime e eo f) ↔
      ComputableInPolyTime f (⟨e, he⟩.trans (blockEnc Γ)) (⟨eo, heo⟩.trans (blockEnc Δ))
```

* **Forward** (Mathlib to cslib-frontier). Mathlib's `FinTM2` makes only the input alphabet
  finite, but cslib-frontier's bridge needs every stack alphabet finite. `Finitize.lean` closes
  this gap: a push writes `f σ` for a function `f` on the finite state type `σ`, so only finitely
  many symbols can ever be on a stack. Restricting each work stack to those symbols gives an
  equivalent machine with finite alphabets (`TM2ComputableInPolyTime.exists_finite`). Then
  cslib-frontier's bridge applies.
* **Reverse** (cslib-frontier to Mathlib). Three machines run in sequence, joined by the TM2
  composition theorem from millennium-cook-levin (`Vendor/CookLevin/Comp.lean`):
  1. the **recoder** (`Recoder.lean`) turns a word over `Γ` into its block code in `2n + m + 2`
     steps;
  2. cslib-frontier's compiler (`ComputableInPolyTime.exists_tm2ComputableInPolyTime`) turns the
     cslib-frontier machine into a binary TM2 machine;
  3. the **decoder** (`Decoder.lean`) turns the block code of the output back into a word over
     `Δ`, in at most `7n + 2` steps. If `Δ` is empty, the **drain** machine (`Drain.lean`)
     replaces steps 1 to 3: the only output word is `[]`.
* `tm2_iff_computableInPolyTime` is the special case of yes/no answers.

### L2: classes and reductions (`Monteverde/Classes/`)

For a finite alphabet `Γ` with at least two symbols and a language `L` over `Γ`:

```lean
theorem clayP_iff_cslib :
    InPolynomialTime (fin_encoding_string Γ) L ↔ {w | L w} ∈ P (blockEnc Γ)
theorem clayNP_iff_cslib :
    InNondeterministicPolynomialTime (fin_encoding_string Γ) L ↔ {w | L w} ∈ NP (blockEnc Γ)
theorem clayReducible_iff_cslib :   -- any finite Γ, Δ
    PolynomialTimeReducible (fin_encoding_string Γ) (fin_encoding_string Δ) L₁ L₂ ↔
      PolyTimeReducible (blockEnc Γ) (blockEnc Δ) {w | L₁ w} {w | L₂ w}
```

* **P** follows from L1 with `e = id`.
* **NP, Clay to cslib-frontier.** The cslib-frontier verifier decodes the binary certificate as
  an optional word `y` over `Γ₁` (`certDecoder`), checks `|y| ≤ |w|^k`, and runs the Clay checker
  on `w#y` (`clayCheck`). cslib-frontier's padding lemma `mem_NP_of_check` turns "some short
  certificate" into "a certificate of length exactly `p(n)`".
* **NP, cslib-frontier to Clay.** Take `Γ₁ = Bool` and let the Clay relation run the
  cslib-frontier verifier on certificates of length exactly `q(|blockEnc w|)` (`cslibCheck`).
  The Clay bound `|w|^k` must cover `q(|blockEnc w|)`. This works for `|w| ≥ 2`
  (`exists_pow_bound`). For `|w| ≤ 1` the bound `|w|^k` is at most 1, so these finitely many
  words take the empty certificate and a lookup table.

### L3: the statements (`Monteverde/Headline/`)

* **Bits form.** `CslibPEqNP` gives `P encBits = NP encBits` by taking `enc = encBits`.
  Conversely, if P = NP on binary strings, the binary image of SAT is in P, and SAT's
  NP-completeness in cslib-frontier (`CookLevin.SAT_npComplete.mem_P_iff`) gives P = NP for
  every encoding.
* **Clay to cslib-frontier.** Apply the Clay statement at `Γ = Bool` to the binary image of SAT.
  Its NP membership moves to Clay through L2, the Clay statement puts it in Clay P, and L2 brings
  it back to cslib-frontier P. Then the bits form applies.
* **cslib-frontier to Clay.** For each alphabet `Γ`, use `enc = blockEnc Γ` and L2.
* **Negative target.** `NegativeBranch` is `¬ ClayPVersusNP`, so `not_congr` gives it.

## Reusable results

All names are in the namespace `Monteverde`. "Any finite" means `[Fintype Γ]`; the type can be
empty.

| Result | What it says | File |
|--------|--------------|------|
| `blockEnc Γ` | The block code `List Γ ↪ List Bool` | `Encoding/BlockEnc.lean` |
| `wordDecoder Γ`, `certDecoder Γ` | Polynomial-time decoders for the block code and for optional words | `Encoding/Certificate.lean` |
| `pairWord_polyTime`, `unpair_polyTime` | Clay's `w#y` against `encPair`, both directions | `Encoding/Pair.lean` |
| `TM2ComputableInPolyTime.exists_finite` | Every polynomial-time `FinTM2` certificate with a finite output alphabet has one with all stack alphabets finite | `Function/Finitize.lean` |
| `Recoder.recoder`, `Decoder.decoder`, `Drain.drainer` | TM2 machines: word to block code, block code to word, and any function into an empty alphabet | `Function/Recoder.lean`, `Decoder.lean`, `Drain.lean` |
| `tm2_iff_computableInPolyTime` | L1 for yes/no answers, any finite input alphabet | `Function/Bridge.lean` |
| `tm2_iff_computableInPolyTime_words` | L1 for functions between words, any finite alphabets | `Function/Bridge.lean` |
| `clayP_iff_cslib`, `clayNP_iff_cslib` | L2 for P and NP, alphabets with at least two symbols | `Classes/P.lean`, `Classes/NP.lean` |
| `mem_NP_of_inNP`, `inNP_of_mem_NP` | The two NP directions, with weaker hypotheses (any finite `Γ`; nonempty `Γ`) | `Classes/NP.lean` |
| `clayReducible_iff_cslib` | L2 for many-one reductions, any finite alphabets | `Classes/Reduction.lean` |
| `cslibPEqNP_of_image_SAT_mem_P` | SAT in P (binary strings) gives `CslibPEqNP` | `Headline/Bits.lean` |
| `bits_to_blockEnc`, `blockEnc_to_bits` | `encBits` and `blockEnc Bool` are polynomial-time equivalent | `Headline/Clay.lean` |

## Trust and verification

### What you must trust

Lean checks every proof. The main risk is a **wrong statement**: a theorem that is true but does
not say what it appears to say. To trust the result, read these, and nothing else:

1. **The statements**, in `Monteverde/Statements/` (four short files). They import only the
   vendored Clay definitions and cslib-frontier's class definitions. They never import a proof.
2. **The Clay definitions**, in `Vendor/Millennium/Millennium.lean`. This is the upstream file
   at commit `603053d`. `scripts/diff_vendor.sh` shows that it differs from upstream only by the
   toolchain fixes listed in `Vendor/Millennium/CHANGES.md`. None of them changes a definition.
3. **The cslib-frontier definitions** of `P`, `NP` and `ComputableInPolyTime`, at commit
   `9bfe667`.
4. **A Lean kernel**: the Lean kernel, or nanoda, which re-checks the export independently.

You do not need to read the 2,100 lines of bridge proofs. If they contained an error, the kernel
would reject them.

### Automatic checks

Every check runs in CI on every pull request and on `main`.

| Check | File | It fails when |
|-------|------|---------------|
| Exact types | `Audit/ClaimCheck.lean` | A headline theorem is renamed or its type changes. It also checks the design doc's exact text for the class bridges. |
| Axiom check | `Audit/Axioms.lean` | A headline theorem or bridge uses an axiom other than `propext`, `Classical.choice`, `Quot.sound`. A `sorry` is the axiom `sorryAx`, so it fails too. |
| Statement isolation | `Audit/Isolation.lean`, `scripts/check_isolation.sh` | A statement file imports anything other than Clay and cslib-frontier class definitions; a theorem's type is not exactly its statement, term for term; or a statement mentions a theorem. |
| Vendored files | `scripts/diff_vendor.sh` | A vendored file differs from its upstream commit by an unlisted change. |
| Non-vacuity | `Tests/NonVacuity.lean` | A simple language is not in P, SAT is not in NP, or the halting problem is in NP, on either side. These tests catch a definition that puts every language in NP. |
| README examples | `Tests/ReadmeExamples.lean` | An example in this README stops working. |
| Independent kernel check | `scripts/kernel_check.sh`, `kernel-check.yml` | nanoda rejects the lean4export export of the headline theorems. |
| Cook-Levin cross-check | `CrossCheck/`, CI job "Cook-Levin cross-check" | The two Cook-Levin proofs do not transfer through the bridges (see below). |
| Size count | `Audit/size_count.py --check` | cslib-frontier is not the largest library in the table. |
| Drift | `drift.yml`, weekly | Monteverde no longer builds against cslib-frontier `main`. This does not move the pin. |
| Watch | `watch.yml`, weekly | Never fails. It opens an issue when related work appears (see [Contributing](#contributing)). |

### Check it yourself

```bash
lake build Vendor Monteverde Audit Tests     # builds the proofs and runs the Lean checks
lake env lean Audit/Axioms.lean              # prints the axioms of each theorem
lake env lean Audit/Isolation.lean           # prints the isolation result
scripts/diff_vendor.sh                       # vendored files against upstream
scripts/check_isolation.sh                   # imports of the statement files
scripts/kernel_check.sh                      # lean4export + nanoda (needs cargo)
python3 Audit/size_count.py --check          # theorem counts from full clones
```

Expected axiom output, for each headline theorem:
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

## The Cook-Levin cross-check

Two independent Lean proofs of the Cook-Levin theorem exist: millennium-cook-levin (Joshua Tan)
proves it against the Clay definitions, and cslib-frontier proves it against its own. If one of
the definitions were wrong, the two proofs would likely fail to agree through the bridges. So
`CrossCheck/CookLevin.lean` moves each proof to the other side:

| Theorem | Meaning |
|---------|---------|
| `mcl_SAT_npComplete` | millennium-cook-levin's SAT is NP-complete for the cslib-frontier definitions |
| `satWords_clayNPComplete` | cslib-frontier's SAT is NP-complete for the Clay definitions |
| `cook_levin_agree_clay`, `cook_levin_agree_cslib` | On each side, the two SAT languages are in P together |
| `clay_P_subset_NP` | Clay's P ⊆ NP, with no hypothesis (the Clay file proves it only from a composition hypothesis, which `Comp.lean` discharges) |

The cross-check is a test. The main theorems do not use it. It builds the vendored millennium-cook-levin
proof (about 12,300 lines), so it is a separate build target and CI job.

## Cook's text against the Lean statement

[`Audit/cook_text_audit.md`](Audit/cook_text_audit.md) maps each clause of Cook's official Clay
problem description to the Lean definitions, in 24 rows, and explains 8 differences. The main
ones:

* **D1, machine model.** Mathlib's multi-stack `FinTM2`, not Cook's one-tape machine. The
  models simulate each other with polynomial overhead (Cook says so himself), but no Lean file
  proves it.
* **D2, finite alphabets.** `FinTM2` requires only the input alphabet to be finite. Monteverde
  proves in Lean that this adds no power (`TM2ComputableInPolyTime.exists_finite`).
* **D3, alphabets.** The Lean target quantifies over all alphabets with at least two symbols.
  Cook fixes one alphabet and says the choice does not matter. Monteverde's proof shows this
  in Lean for the Lean model: P = NP at `Bool` gives P = NP at every alphabet.
* **D7, short inputs.** Cook's certificate bound `|y| ≤ |w|^k` allows at most one symbol when
  `|w| ≤ 1`. The Lean file keeps this literal bound. It does not change NP.
* **D8, P ⊆ NP.** The Clay file proves it only from a hypothesis. This repository discharges the
  hypothesis (`clay_P_subset_NP`).

Claude reviewed the audit on November 22, 2026: every quote against Cook's PDF and every line
reference against the files. A review by a complexity theorist adds confidence; if you write one, publish it wherever you like.

## Library size

"The largest Lean complexity library" rests on a count of `theorem` and `lemma` declarations in
each public Lean complexity library, at pinned commits, in full clones, on November 22, 2026
(`Audit/size_count.py`, full table in [`Audit/size_table.md`](Audit/size_table.md)). CI fails if
cslib-frontier is not first.

| Library | Theorems and lemmas |
|---------|--------------------:|
| cslib-frontier (`CslibFrontier/Computability`) | 49,439 |
| descriptive-complexity (PierreSenellart) | 31,938 (12,671 without its `lax/` archive copies) |
| starpos/lean-np-complete | 5,467 |
| CSLib | 3,463 |
| konard/p-vs-np | 2,444 |

## Build

You need [elan](https://github.com/leanprover/elan) and several GB of free disk for the Mathlib
cache and the cslib-frontier build.

```bash
git clone https://github.com/wbnns/monteverde && cd monteverde
lake exe cache get                        # Mathlib build cache
lake build Vendor Monteverde Audit Tests  # the proof and its checks
lake build CrossCheck                     # optional: the Cook-Levin cross-check
```

The first build compiles the needed part of cslib-frontier (about 300 modules). With a warm
cache, CI builds and checks everything in about 4 minutes.

To use Monteverde in another Lake project, add it to `lakefile.toml`. Use the same Lean toolchain
(`leanprover/lean4:v4.36.0-rc2`). cslib-frontier and Mathlib come in through Monteverde's pins.

```toml
[[require]]
name = "monteverde"
git = "https://github.com/wbnns/monteverde"
rev = "v1.1.0"
```

### Pinned versions

| Component | Commit | Toolchain |
|-----------|--------|-----------|
| cslib-frontier | `9bfe667f8c66a8a2a3e17391ce9a5cc965190544` | `leanprover/lean4:v4.36.0-rc2` |
| cslib (through cslib-frontier) | `98f9a62ac1fafa0d5091bbd78bc24091c5923aab` | same |
| Mathlib (through cslib) | `bbff2954fe5ee3b7a4b33cc26ef873a1c3277d91` | same |
| LeanMillenniumPrizeProblems (vendored) | `603053dc267cf3efe422f438eb78098c0ececd6f` | upstream v4.31.0, ported |
| millennium-cook-levin (vendored) | `879c4835640119ad009abeb62ebd7a96f87eb9e8` | upstream v4.31.0, ported |

The results refer to these commits. Moving a pin is a deliberate release step.

## Repository map

```
Monteverde/
  Statements/     The headline statements, as definitions (read these to trust the result)
    Defs.lean       CslibPEqNP
    Bits.lean, Clay.lean, NegativeBranch.lean
  Headline/       The headline theorems, one per file (L3)
  Classes/        P.lean, NP.lean, Reduction.lean (L2)
  Function/       Finitize, Forward, Recoder, Decoder, Drain, Reverse, Bridge (L1)
  Encoding/       BlockEnc, Pair, Certificate (L0)
Vendor/
  Millennium/     The Clay definitions (vendored, ported; CHANGES.md, port.patch, NOTICE)
  CookLevin/      millennium-cook-levin: Comp.lean (used by L1) and the Cook-Levin proof
                  (used only by the cross-check)
Audit/            ClaimCheck, Axioms, Isolation, cook_text_audit.md, size count
Tests/            NonVacuity, ReadmeExamples, Probe (cslib-frontier names this project uses)
CrossCheck/       The Cook-Levin cross-check and its axiom check
scripts/          diff_vendor.sh, check_isolation.sh, kernel_check.sh
.github/workflows ci.yml, kernel-check.yml, drift.yml, watch.yml
```

## Contributing

This repository is a stable reference at v1.1.0, so issues and pull requests here may not get a
reply. The best way to improve Monteverde is to fork it: it is open source under the Apache
License 2.0, and you do not need permission to change it or publish your version. Please keep
`NOTICE` and `CREDITS.md`. The notes below help you work on a fork.

**Build targets.** `lake build Vendor Monteverde Audit Tests` is the main gate.
`lake build CrossCheck` is separate and slower. A single module builds with
`lake build +Monteverde.Classes.NP` (note the `+`).

**Invariants.** Every change must keep these true. CI enforces each one.

* No `sorry` and no `axiom` declarations anywhere.
* Each theorem in `Audit/Axioms.lean` and `CrossCheck/Axioms.lean` uses only `propext`,
  `Classical.choice`, `Quot.sound`.
* `Monteverde/Statements/*.lean` imports only `Vendor.Millennium.Millennium`,
  `CslibFrontier.Computability.Complexity.Classes.P`, `...Classes.NP` and
  `Monteverde.Statements.Defs`.
* Each headline theorem's type is exactly the body of its statement definition. To change a
  statement, change both files and `Audit/Isolation.lean`.
* Every change to a vendored file must be listed in its `CHANGES.md` and in its `port.patch`.
  Regenerate the patch with `diff -u` against the upstream file at the pinned commit; see
  `scripts/diff_vendor.sh` for the exact labels and file order.

**Where to change what.**

| Task | Place |
|------|-------|
| A new bridge lemma | The matching layer in `Monteverde/`, then `Monteverde.lean`, and add it to `Audit/Axioms.lean` |
| A new README example | `Tests/ReadmeExamples.lean` first, then this file |
| Move the cslib-frontier pin | `lakefile.toml`, `lake-manifest.json`, the pins table here, a new release |
| A new library in the size table | `Audit/size_pins.json`, then run `Audit/size_count.py` |

**Known toolchain quirks** (Lean v4.36.0-rc2 with this Mathlib):

* Mathlib's `deriving Fintype` fails for enum types. Use
  `instance : Fintype T := derive_fintype% T`.
* Mathlib now has an unbundled `FinEncoding`. The Clay file needs the old bundled one, kept
  verbatim in `Vendor/Millennium/MathlibCompat.lean` (namespace `MathlibV431`). Files that use
  the Clay definitions must `open Computability hiding Encoding FinEncoding finEncodingBoolBool`
  and `open MathlibV431`.
* `M.Cfg` and `TM2.Cfg M.Γ M.Λ M.σ` are only definitionally equal. Some `simp` and `rw` steps
  need a final `rfl`, an `erw`, or a `change`.
* Do not run two `lake` commands at the same time in one checkout: they compete for the git
  config lock of the dependencies.

**Watch for related work.** `watch.yml` runs weekly. It searches cslib-frontier issues and pull
requests and konard/p-vs-np commits for Clay links, and opens an issue here when it finds one.
It searches the Lean Zulip only when the repository has the secrets `ZULIP_EMAIL` and
`ZULIP_API_KEY` (a Zulip bot on leanprover.zulipchat.com).

<a id="history"></a>
## History

Monteverde follows a design doc dated November 22, 2026. All milestones were done on that day.

| Milestone | Content |
|-----------|---------|
| M0 | Pins, vendored Clay file, diff check, CI |
| M1 | Block code, finite work alphabets, L1 forward bridge |
| M2 | Recoder machine, TM2 composition, L1 reverse bridge |
| M3 | Class bridges for P and NP, bits form |
| M4 | Headline theorems, exact-type check, axiom check, isolation, non-vacuity tests |
| M5 | Size count, independent kernel check, credits, release v1.0.0 |
| v1.1.0 | L1 for word outputs over every finite alphabet, reduction bridge, statements split from proofs, Cook-Levin cross-check, Cook text audit, weekly watch |

The design doc asked for a one-week spike on the recoder machine and new estimates after it.
The recoder took less than a day, so the milestone plan did not change.

### Open questions from the design doc

| Question | State |
|----------|-------|
| Final package name | Decided: Monteverde. |
| Offer the bridges upstream to cslib-frontier? | On hold, by the project owner's decision. |
| The optional Cook text audit, and its reviewer | Done, reviewed by Claude. Independent reviews can be published anywhere. |

### Citation

```bibtex
@software{monteverde,
  author  = {Binns, Will},
  title   = {Monteverde: two Lean statements of P vs NP, proved equivalent},
  version = {1.1.0},
  date    = {2026-11-22},
  url     = {https://github.com/wbnns/monteverde}
}
```

### Credits and license

Monteverde is by Will Binns, released under the Apache License 2.0. It builds on
LeanMillenniumPrizeProblems (Robert Joseph George), cslib-frontier (including Erik Demaine's TM2
bridge and Samuel Schlesinger's P, NP and reductions), millennium-cook-levin (Joshua Tan's TM2
composition and Cook-Levin proof), CSLib and Mathlib. `CREDITS.md` lists every reused definition
and theorem with its author and source commit. See also `NOTICE`.

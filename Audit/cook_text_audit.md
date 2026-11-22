# Cook text audit: Clay P vs NP text against the Lean statement

## Purpose

This file is the optional audit from the design doc: "A table that maps each clause of Cook's
official Clay text to the Lean definitions." The claim in `README.md` does not need this audit.
The audit helps a reader check that the vendored Lean statement says what Cook's text says.

## Sources

- Cook's text: Stephen Cook, "The P versus NP Problem", official Clay problem description.
  URL: <https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf>. Fetched on
  November 22, 2026. Page numbers below are the numbers printed on the pages.
- Lean statement: `Vendor/Millennium/Millennium.lean`, ported from
  [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
  `Problems/PVersusNP/Millennium.lean` at commit `603053d`
  (`603053dc267cf3efe422f438eb78098c0ececd6f`, see `Vendor/Millennium/UPSTREAM_COMMIT`). The port
  changes are in `Vendor/Millennium/CHANGES.md`. No port change touches a definition that this
  audit uses.
- Machine model: Mathlib at commit `bbff295` (the Mathlib that this repo pins). The file
  `Mathlib/Computability/TuringMachine/Computable.lean` holds `FinTM2` (line 46), `initList`
  (line 110), `haltList` (line 118), `TM2OutputsInTime` (line 130) and `TM2ComputableInPolyTime`
  (line 174). The file `Mathlib/Computability/TuringMachine/StackTuringMachine.lean` holds
  `Turing.TM2.Stmt` (line 125) and `Turing.TM2.step` (line 169).
- `Millennium.lean:N` in the table means line N of `Vendor/Millennium/Millennium.lean`.

Audit date: 2026-11-22.

## Review

Reviewed on November 22, 2026 by Claude (an AI model, Anthropic), the author of the Monteverde
code. The review checked:

- every quote in the table against the text of Cook's PDF, extracted from the file at the URL
  above;
- every `Millennium.lean:N` and Mathlib line reference against the files at the pinned commits;
- each "Match" value and each difference D1 to D8 against the Lean definitions.

Result: 22 of 24 rows were correct as written. Two were fixed: row 6 cited page 10 for a phrase
on page 9, and row 24 quoted `R ⊆ Σ* × Σ*` where Cook's printed text has `Σ∗ ∪ Σ∗` (a typo in
the original for `×`). The review also added the note on `#` in D6 and the Lean references in
D2 and D3. No difference changes the two target statements.

An extra review by a person with complexity-theory background can add credibility to the
release. The claim does not need it.

## Match values

- **Exact**: the Lean text says the same thing as Cook's text, symbol for symbol, up to names.
- **Equivalent**: the Lean text is different, but it defines the same class or the same
  statement. The "Differences" section gives the reason.
- **Differs**: the Lean text is weaker or stronger in a way that a proof must handle. The
  "Differences" section says if this changes the target statements.

## Table

| # | Cook's text (short quote, with page/section) | Lean definition (name, Vendor/Millennium/Millennium.lean:line) | Match | Notes |
|---|---|---|---|---|
| 1 | "a finite alphabet (that is, a finite nonempty set) with at least two elements" (p. 1, §1) | `ClayFiniteAlphabet` (`Fintype`, `Nontrivial`), Millennium.lean:448; binders `[Fintype alphabet] [Nontrivial alphabet]` in `ClayPVersusNP.Formulations.ClassEquality`, Millennium.lean:1553 | Exact | `Nontrivial` means at least two elements, so the set is also nonempty. The alphabet is any `Type` with a `Fintype` instance. See D3. |
| 2 | "the set of finite strings over Σ" (p. 1, §1) | `ClayFiniteAlphabet.Strings` = `List A.carrier`, Millennium.lean:459; `fin_encoding_string`, Millennium.lean:220 | Exact | `fin_encoding_string` is the identity encoding (`encode := id`). So the input of the machine is the string itself. |
| 3 | "a language over Σ is a subset L of Σ*" (p. 1, §1) | `Language α := α → Prop`, Millennium.lean:80; `ClayFiniteAlphabet.Language`, Millennium.lean:463 | Equivalent | A predicate on `List Σ` and a subset of Σ* carry the same data. |
| 4 | "the Turing machine" (p. 1, §1); "an infinite tape" (p. 9, Appendix) | `TM2ComputableInPolyTime` inside `InPolynomialTime`, Millennium.lean:95-97 (Mathlib `FinTM2`, a multi-stack machine) | Differs | Deterministic multi-stack machine, not one-tape. Only the input stack alphabet must be finite. See D1 and D2. |
| 5 | "a finite alphabet Γ that includes the blank symbol b"; input alphabet "not including the blank" (p. 9, Appendix) | `TM2ComputableAux.inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀` (Mathlib), used through `InPolynomialTime`, Millennium.lean:96 | Equivalent | Stacks have no blank. A `pop` on an empty stack returns `none`, so the machine can see the end of the input. See D1. |
| 6 | "a specified finite set Q of possible states" (p. 9, Appendix); "transition function" (p. 10, Appendix) | `FinTM2.Λ`, `FinTM2.σ` (both `Fintype`) and `FinTM2.m : Λ → TM2.Stmt` (Mathlib) | Equivalent | Finite control = finite labels × finite internal state. A program step runs one finite statement block, not one tape move. See D1 and D2. |
| 7 | "C₀ = q₀w" (p. 10, Appendix) | `initList` (Mathlib): input string on stack `k₀`, other stacks empty | Equivalent | The top of the input stack is the left-most symbol, as the head position in Cook's text. |
| 8 | "M accepts w ... terminates in the accepting state" (p. 1, §1; p. 10, Appendix) | `InPolynomialTime`: `f a = true`, with output encoded by `finEncodingBoolBool`, Millennium.lean:96-97 | Equivalent | The Lean machine computes a total function `f : α → Bool`. It halts with `[true]` or `[false]` on the output stack. See D4. |
| 9 | "L(M) = {w ∈ Σ* \| M accepts w}" (p. 1, §1) | `∀ a, L a ↔ f a = true`, Millennium.lean:97 | Equivalent | Same set, written as an equivalence with the decider output. |
| 10 | "t_M(w) the number of steps" (p. 1, §1); "one less than the number of configurations" (p. 10, Appendix) | `TM2OutputsInTime` and `EvalsToInTime.steps_le_m` (Mathlib), used through `TM2ComputableInPolyTime` | Equivalent | A Lean step is one `TM2.step` (one statement block). The block length is bounded by the fixed program, so the step counts differ by a constant factor at most. |
| 11 | "T_M(n) ≤ n^k + k" (p. 1, §1) | `TM2ComputableInPolyTime.time : Polynomial ℕ`, bound `time.eval (ea a).length` (Mathlib) | Equivalent | Every `Polynomial ℕ` is bounded by n^k + k for a large k, and n^k + k is a `Polynomial ℕ`. Lean bounds each input; Cook bounds the worst case per length. These are the same. |
| 12 | "P = {L \| L = L(M) for some Turing machine M that runs in polynomial time}" (p. 2, §1) | `InPolynomialTime (fin_encoding_string alphabet) L`, Millennium.lean:95 | Equivalent | Equivalent if the machine models give the same P (D1, D2) and the halt conventions match (D4). |
| 13 | "a binary relation R ⊆ Σ* × Σ₁* for some finite alphabets Σ and Σ₁" (p. 2, §1) | `R : α → List Γ₁ → Prop` with `(Γ₁ : Type) (_ : Fintype Γ₁)` in `InNondeterministicPolynomialTime`, Millennium.lean:290; field `checking_relation`, Millennium.lean:404 | Differs | Lean allows an empty Γ₁. Cook's "finite alphabet" is nonempty. This does not change NP. See D5. |
| 14 | "a language L_R over Σ ∪ Σ₁ ∪ {#}" (p. 2, §1) | `pair_symbol` = `Sum ea.Γ (Option eb.Γ)`, Millennium.lean:102 | Equivalent | Lean uses a disjoint (tagged) union. `Sum.inr none` is the symbol #. See D6. |
| 15 | "L_R = {w#y \| R(w, y)}"; "the symbol # is not in Σ" (p. 2, §1) | `pair_encoding`, Millennium.lean:161; `pair_encoding.encode_eq`, Millennium.lean:183; `pair_encoding.length_eq`, Millennium.lean:191 | Equivalent | Encoding of `(w, y)` is `map inl w ++ # :: map (inr ∘ some) y`. Length is \|w\| + 1 + \|y\|, as in Cook. # is a fresh symbol by construction. See D6. |
| 16 | "R is polynomial-time iff L_R ∈ P" (p. 2, §1) | `PolynomialTimeCheckingRelation`, Millennium.lean:272 | Equivalent | `InPolynomialTime (pair_encoding ea eb) (fun p => R p.1 p.2)`. The Lean decider must be correct only on well-formed `w#y` strings. See D6. |
| 17 | "there is k ∈ N and a polynomial-time checking relation R" (p. 2, §1) | `InNondeterministicPolynomialTime`, Millennium.lean:289-292 | Exact | Same quantifier order: ∃ Γ₁, ∃ R, ∃ k, then R polynomial-time and the membership condition. |
| 18 | "w ∈ L ⇔ ∃y (\|y\| ≤ \|w\|^k and R(w, y))" (p. 2, §1) | `∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y`, Millennium.lean:292; same as field `membership_iff_exists_bounded_certificate`, Millennium.lean:412-415 | Exact | With `fin_encoding_string`, `(ea.encode a).length` is \|w\|. Lean has `0 ^ 0 = 1`. See D7 for short inputs. |
| 19 | NP via checking relations (p. 2, §1), packaged | `ClayPolynomialTimeVerification`, Millennium.lean:398; `ClayVerifiableLanguage`, Millennium.lean:420; `ClayVerifiableLanguage.iff_in_nondeterministic_polynomial_time`, Millennium.lean:425 | Exact | A structure with the same fields as row 17 and row 18. The file proves that it is the same as `InNondeterministicPolynomialTime`. |
| 20 | "Problem Statement. Does P = NP?" (p. 2, §1), answer yes | `ClayPVersusNP`, Millennium.lean:1564 (= `ClayPVersusNP.Formulations.ClassEquality`, Millennium.lean:1552); `PositiveBranch`, Millennium.lean:1873 | Equivalent | `∀ alphabet [Fintype] [Nontrivial] L, InPolynomialTime … L ↔ InNondeterministicPolynomialTime … L`. It quantifies over all alphabets. See D3. |
| 21 | "Does P = NP?" (p. 2, §1), answer no | `ClayPVersusNP.Formulations.NegativeBranch := ¬ ClayPVersusNP`, Millennium.lean:1877 | Equivalent | ¬∀ alphabet gives P ≠ NP for one alphabet with at least two symbols. See D3. The file gives no disjunction target, on purpose (Millennium.lean:1880-1899). |
| 22 | "the answer is independent of the size of the alphabet Σ (we assume \|Σ\| ≥ 2)" (p. 2, §1) | `ClayPVersusNP.for_alphabet`, Millennium.lean:1568; `ClayFiniteAlphabet.PolynomialTimeEqualsNondeterministicPolynomialTime`, Millennium.lean:477 | Equivalent | The file does not prove this independence. It states the target for all alphabets. See D3. |
| 23 | "For \|Σ\| = 1 the problem is still open" (p. 2, §1) | `[Nontrivial alphabet]` in `ClassEquality`, Millennium.lean:1553 | Exact | The unary case is out of the target, as in Cook's statement. |
| 24 | "It is trivial to show that P ⊆ NP"; "R ⊆ Σ∗ ∪ Σ∗" (Cook's typo for Σ∗ × Σ∗) with "R(w, y) ⇐⇒ w ∈ L" (p. 2, §1) | `ClayPVersusNP.Support.DeciderAsVerifier`, Millennium.lean:1450; `PolynomialTimeContainedInNondeterministicPolynomialTime.certificate_verifier`, Millennium.lean:1520; `...of_turing_machine_composition`, Millennium.lean:1539 | Differs | Same construction (Γ₁ = Σ, k = 0). The file proves it only with the hypothesis `PolynomialTimeComputableComposition`, Millennium.lean:311. Not part of the target statements. See D8. |

Rows: 24.

## Differences

Each item lists a place where the Lean text is not literally Cook's text. Each item gives the
reason why it matters or does not matter for the two targets `ClayPVersusNP` and
`ClayPVersusNP.Formulations.NegativeBranch`.

**D1. Machine model: multi-stack `FinTM2`, not a one-tape Turing machine.** (Rows 4 to 7, 10.)
Cook defines a one-tape machine with a blank symbol and head moves of ±1. Lean uses Mathlib
`FinTM2`: a finite number of stacks, finite labels `Λ`, a finite internal state `σ`, and a
program `m : Λ → TM2.Stmt` with `push`, `pop`, `peek`, `load`, `branch`, `goto` and `halt`.
The machine is deterministic (`TM2.step` is a function). Each step runs one finite statement
block. Why it does not matter: a one-tape machine and a machine with two or more stacks
simulate each other with polynomial overhead. Cook says this himself: Turing machines simulate
"machines equipped with many tapes" by "at most squaring or cubing the computation time" (p. 1,
§1). So the class P is the same. The vendored file does not prove this simulation. It is a
standard fact. The equivalence theorems in this repo use the Lean model as it is, so they do not
need this simulation.

**D2. `FinTM2` requires only the input stack alphabet to be finite. Transition functions can be
noncomputable.** (Rows 4, 6.) Checked in Mathlib `Computable.lean:46-69`: the only alphabet
instance is `Γk₀Fin : Fintype (Γ k₀)`. Work stack alphabets `Γ k` for `k ≠ k₀` can be infinite.
The output alphabet is finite in the P definition, because `outputAlphabet` must be `≃ Bool`.
The statement functions (`σ → Γ k`, `σ → Option (Γ k) → σ`, `σ → Bool`, `σ → Λ`) are arbitrary
Lean functions, so they can be noncomputable. Why it does not matter: `σ` and `Λ` are finite, and
the program has a finite number of statements. So a `push` can write only a finite set of
symbols (the images of a finite number of functions on finite `σ`). Every function on these
finite domains is a finite table, so noncomputable functions give no extra power. A `FinTM2` is
therefore a finite machine in Cook's sense. Monteverde proves the alphabet part in Lean:
`Monteverde.TM2ComputableInPolyTime.exists_finite` gives, for every polynomial-time `FinTM2`
certificate with a finite output alphabet, one with the same function and time bound whose
stack alphabets are all finite. (Milestone M1 of this repo handles finite work
alphabets for the bridge.)

**D3. Alphabet quantifier: Lean states P = NP for every finite alphabet with at least two
symbols.** (Rows 1, 20 to 22.) Cook fixes one alphabet Σ with |Σ| ≥ 2 and says that "the answer
is independent of the size of the alphabet". `ClayPVersusNP` is
`∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] L, P ↔ NP`. `NegativeBranch` is
its negation: P ≠ NP for at least one such alphabet. Why it does not matter: by Cook's
independence remark (strings over any fixed alphabet code into binary strings with polynomial
overhead), the "for all alphabets" form, the "for one alphabet" form and the binary form are
equivalent. The vendored file does not prove this remark, but Monteverde does, for the Lean
model: `clay_iff_cslib` gets `CslibPEqNP` from the Clay statement at the one alphabet `Bool`, and
gets the Clay statement for every alphabet back from `CslibPEqNP`. So P = NP at `Bool` gives
P = NP at every alphabet with at least two symbols. Note: the alphabet is in `Type`
(universe 0). This is no restriction, because every finite alphabet has a copy in `Type`.

**D4. Accepting state against Boolean output and a strict halt configuration.** (Rows 8, 9,
12.) Cook's machine accepts by halting in `q_accept`. The Lean machine computes `f : α → Bool`
and must reach exactly `haltList tm [f a]`: label `none`, internal state equal to
`initialState`, the output stack holds the one symbol for `f a`, and every other stack (also the
input stack) is empty. Why it does not matter: a machine that accepts in polynomial time halts
on every input, so it gives a total `f`. The extra cleanup (empty the stacks, reset the state,
write one output symbol) costs at most linear time in the stack contents, which the run time
bounds. In the other direction, the Bool output maps to the accept or reject state.

**D5. Certificate alphabet Σ₁ (Lean `Γ₁`) can be empty.** (Row 13.) Cook's Σ₁ is a "finite
alphabet", and Cook defines that as a finite nonempty set. Lean asks only `Fintype Γ₁`. There is
no `Nontrivial` or `Nonempty` condition on `Γ₁`. Why it does not matter: with an empty `Γ₁`, the
only certificate is the empty string, so L = {w | R(w, [])}, and this L is in P (and in NP with a
one-symbol `Γ₁`). The extra case adds no language to NP. Cook also lets Σ₁ differ from Σ, and
Lean does the same. Lean lets `Γ₁` be any finite type, so the certificate alphabet can have one
symbol, as in Cook.

**D6. How `w#y` is encoded.** (Rows 14 to 16.) Cook writes L_R over the set union
Σ ∪ Σ₁ ∪ {#} with # ∉ Σ. (Cook does not say # ∉ Σ₁. In Lean, # is fresh for both alphabets.) Lean uses the disjoint union `Sum Σ (Option Γ₁)`: left symbols are
`Sum.inl a`, the separator is `Sum.inr none`, right symbols are `Sum.inr (some b)`. Why it does
not matter: when Σ and Σ₁ share symbols, the single # still splits the string, so the tagged and
untagged forms convert into each other in linear time. The length is |w| + 1 + |y| in both
(`pair_encoding.length_eq`). A second point: `InPolynomialTime` only asks for a correct answer
on strings that encode a pair. So the Lean decider for L_R is a promise decider. Cook's machine
must also reject strings that are not of the form w#y. Why this does not matter: a machine can
check the form in linear time and then run the promise decider.

**D7. Certificate length bound |y| ≤ |w|^k.** (Row 18.) Lean has the literal bound
`y.length ≤ w.length ^ k`. This is Cook's bound, not a general polynomial p(|w|). For |w| = 1
the bound is 1 for every k. For |w| = 0 the bound is 0 when k ≥ 1 and 1 when k = 0 (Lean
`0 ^ 0 = 1`). So for |w| ≤ 1 a certificate has at most 1 symbol. Why it does not matter: this is
also what Cook's text says. For |w| ≥ 2, every polynomial p(|w|) is at most |w|^k for a large k.
There is only a finite number of strings with |w| ≤ 1, so a checking relation can decide them
by a finite table and ignore the certificate. So the bound |w|^k and the bound p(|w|) give the
same class NP.

**D8. P ⊆ NP is conditional in the vendored file.** (Row 24.) Cook calls P ⊆ NP trivial. The
file proves it only from `ClayPVersusNP.Support.PolynomialTimeComputableComposition`
(Millennium.lean:311): closure of `TM2ComputableInPolyTime` under composition. The left
projection machine (Millennium.lean:606, linear time, Millennium.lean:1366) is proved without
this hypothesis. Why it does not matter for the targets: `ClayPVersusNP` is the literal class
equality (both directions), and `NegativeBranch` is its literal negation. Neither target uses
this hypothesis. But a reader must know that ¬`ClayPVersusNP` means "the classes differ", and the
vendored file alone does not reduce that to "NP ⊄ P". This repo closes the gap: the vendored
`Vendor/CookLevin/Comp.lean` proves the hypothesis (`PvsNP.comp`, restated as
`Monteverde.CrossCheck.clay_composition`), and `Monteverde.CrossCheck.clay_P_subset_NP` states
P ⊆ NP with no hypothesis. So in this repo
`NegativeBranch` means NP ⊄ P.

## Other observations

These items do not change the target statements.

- The module comment (Millennium.lean:36-52) says the listed examples are "from the Clay PDF".
  Some are not in Cook's text: PATH (reachability), the traveling salesman problem and vertex
  cover. Cook's text names SAT, 3-SAT, SubsetSum, Hamiltonian cycle, clique, 3-coloring, integer
  factoring and primes (AKS).
- Millennium.lean:17-20 points to `Problems/PVersusNP/references/clay/pvsnp.pdf`. That path is
  in the upstream repository. This repo does not vendor the PDF.
- `NondeterministicPolynomialTimeComplete` (Millennium.lean:334) quantifies over every
  `FinEncoding` type, also encodings with a one-symbol alphabet. Cook's Definition 4 (p. 4, §2)
  uses languages over alphabets. The targets do not use this definition.
- `TM2ComputableInPolyTime` is data (a structure in `Type`), not a `Prop`. `InPolynomialTime`
  uses it under `∃`, so only its existence counts. This is correct.

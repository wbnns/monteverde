# Monteverde

Monteverde proves in Lean 4 that the LeanMillenniumPrizeProblems formulation of the Clay
P vs NP statement is equivalent to P vs NP in
[cslib-frontier](https://github.com/cslib-community/cslib-frontier).

The project does not try to resolve P vs NP. It links two formal statements of the problem, so
that a result about one is a result about the other.

## Target claim

> I proved in Lean that the LeanMillenniumPrizeProblems formulation of the Clay P vs NP
> statement is equivalent to P vs NP in cslib-frontier, the largest Lean complexity library.

Evidence for each part of the claim:

| Part | Evidence |
|------|----------|
| "I proved in Lean" | The headline theorems compile with no `sorry` and use only `propext`, `Classical.choice`, `Quot.sound` (`Audit/Axioms.lean`). nanoda, a type checker written in Rust, checks the lean4export export of the headline theorems: 16,507 declarations, no errors (`kernel-check` workflow). Reused work is credited in `CREDITS.md`. |
| "the LeanMillenniumPrizeProblems formulation" | The theorems use `Millennium.ClayPVersusNP` and `Millennium.ClayPVersusNP.Formulations.NegativeBranch` from commit `603053d`. `scripts/diff_vendor.sh` shows that the vendored file differs from upstream only by the toolchain fixes in `Vendor/Millennium/CHANGES.md`. |
| "is equivalent to" | Two `↔` theorems, one for each official target (`Audit/ClaimCheck.lean`). |
| "P vs NP in cslib-frontier" | `CslibPEqNP` is the form of `NPComplete.mem_P_iff`, and `cslibPEqNP_iff_bits` covers `P encBits = NP encBits`. |
| "the largest Lean complexity library" | `Audit/size_table.md`, at pinned commits on November 22, 2026: cslib-frontier Computability has 49,439 theorems and lemmas; the next largest, descriptive-complexity, has 12,671 (31,938 if you also count its `lax/` archive copies, which its source archive leaves out). |

## Headline theorems

```lean
/-- P vs NP as cslib-frontier states it: the form of `NPComplete.mem_P_iff`. -/
def CslibPEqNP : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool), Cslib.Complexity.P enc = Cslib.Complexity.NP enc

theorem cslibPEqNP_iff_bits : CslibPEqNP ↔ P encBits = NP encBits
theorem clay_iff_cslib : Millennium.ClayPVersusNP ↔ CslibPEqNP
theorem clay_negative_iff_cslib :
    Millennium.ClayPVersusNP.Formulations.NegativeBranch ↔ ¬ CslibPEqNP
```

Done means: every headline theorem compiles with no `sorry`, uses only `propext`,
`Classical.choice` and `Quot.sound`, passes CI on the pinned toolchain, and passes an
independent kernel check.

## Status

| Milestone | Content | State |
|-----------|---------|-------|
| M0 | Pins, vendored Clay file, diff check, CI | Done |
| M1 | L0 block code, finite work alphabets, L1 forward bridge, Clay P to cslib P | Done |
| M2 | L1 reverse bridge (recoder machine, TM2 composition), L1 iff, Clay P ↔ cslib P | Done |
| M3 | L2 class bridges for P and NP (pair words, certificate decoder), bits form | Done |
| M4 | Headline theorems, claim check, axiom check, isolation, non-vacuity tests | Done |
| M5 | Size count, independent kernel check, credits, release | Done |
| After M5 | L1 for word outputs (decoder machine), reduction bridge | Done |
| After M5 | Cook-Levin cross-check, Cook text audit, weekly watch for related work | Done |

## Audit

| Check | File | What fails the build |
|-------|------|----------------------|
| Claim check | `Audit/ClaimCheck.lean` | A headline theorem is renamed or its type changes. |
| Axiom check | `Audit/Axioms.lean` | A checked theorem uses an axiom other than `propext`, `Classical.choice`, `Quot.sound` (a `sorry` is the axiom `sorryAx`). |
| Statement isolation | `Audit/Isolation.lean`, `scripts/check_isolation.sh` | A headline type mentions a theorem or a bridge definition, or `Statements/Defs.lean` imports more than cslib-frontier's class definitions. |
| Vendored files | `scripts/diff_vendor.sh` | A vendored file differs from its upstream commit by an unlisted change. |
| Non-vacuity | `Tests/NonVacuity.lean` | A simple language is not in P, SAT is not in NP, or the halting problem is in NP, on either side. |
| Independent kernel check | `scripts/kernel_check.sh`, `.github/workflows/kernel-check.yml` | nanoda (a Rust type checker, not the Lean kernel) rejects the lean4export export of the headline theorems. |
| Size count | `Audit/size_count.py`, `Audit/size_table.md` | (`--check`) cslib-frontier is not the largest library in the table. |
| Drift | `.github/workflows/drift.yml` | Weekly: the project no longer builds against cslib-frontier main. This does not move the pin. |
| Cook-Levin cross-check | `CrossCheck/CookLevin.lean`, `CrossCheck/Axioms.lean` (CI job "Cook-Levin cross-check") | The Cook-Levin proofs of millennium-cook-levin and cslib-frontier do not transfer to each other through the bridges. A test, not part of the claim. |
| Watch | `.github/workflows/watch.yml` | Nothing fails. Weekly, it opens an issue here if cslib-frontier issues or pull requests, or konard/p-vs-np commits, mention Clay or Millennium. The Lean Zulip stays a manual check. |

Cook text audit (optional in the design doc): `Audit/cook_text_audit.md` maps each clause of
Cook's official Clay text to the Lean definitions, in 24 rows, and explains each of the 8
differences. The reviewer is not chosen yet.

Cook-Levin cross-check: millennium-cook-levin proves Cook-Levin against the Clay definitions, and
cslib-frontier proves it against its own. `CrossCheck/CookLevin.lean` moves each proof through
the bridges. millennium-cook-levin's SAT is NP-complete for the cslib-frontier definitions
(`mcl_SAT_npComplete`), and cslib-frontier's SAT is NP-complete for the Clay definitions
(`satWords_clayNPComplete`). On each side, the two SAT languages are in P together, exactly
when P = NP. The file also proves Clay's P ⊆ NP with no hypothesis.

Statement isolation note: Lean puts a theorem's statement and proof in one declaration, so the
files in `Statements/` import the proofs. The check applies to the statements themselves: every
constant in a headline type must be a definition from the vendored Clay file, cslib-frontier,
Mathlib, or `Statements/Defs.lean`.

## Pinned versions

| Component | Commit | Toolchain |
|-----------|--------|-----------|
| cslib-frontier | `9bfe667f8c66a8a2a3e17391ce9a5cc965190544` | `leanprover/lean4:v4.36.0-rc2` |
| cslib (through cslib-frontier) | `98f9a62ac1fafa0d5091bbd78bc24091c5923aab` | same |
| Mathlib (through cslib) | `bbff2954fe5ee3b7a4b33cc26ef873a1c3277d91` | same |
| LeanMillenniumPrizeProblems (vendored) | `603053dc267cf3efe422f438eb78098c0ececd6f` | upstream v4.31.0, ported |
| millennium-cook-levin (vendored) | `879c4835640119ad009abeb62ebd7a96f87eb9e8` | upstream v4.31.0, ported |

The claim refers to these commits. Moving a pin is a deliberate release step.

## Layout

```
Vendor/Millennium/   Clay definitions, ported to this toolchain (see CHANGES.md, port.patch)
Vendor/CookLevin/    millennium-cook-levin, ported the same way: TM2 composition (used by the
                     bridge) and the Cook-Levin proof (used only by the cross-check)
Monteverde/          The bridge, in four layers:
  Encoding/          L0: block code, pairs, certificates
  Function/          L1: polynomial-time functions, both directions
  Classes/           L2: P, NP and reductions
  Statements/        L3: one headline theorem per file
Audit/               Claim check, axiom check, isolation check, size count
Tests/               Name probe and non-vacuity tests
CrossCheck/          Cook-Levin cross-check (a test, not part of the claim)
scripts/             diff_vendor.sh and other checks
```

## Build

You need [elan](https://github.com/leanprover/elan). Then:

```bash
lake exe cache get        # Mathlib build cache
lake build Vendor Monteverde Audit Tests
scripts/diff_vendor.sh    # vendored files against their upstream commits
scripts/check_isolation.sh
lake build CrossCheck     # optional: the Cook-Levin cross-check (builds millennium-cook-levin)
```

The first build compiles the needed part of cslib-frontier (about 300 modules).

## Open questions from the design doc

| Question | State |
|----------|-------|
| Final package name | Decided: Monteverde. |
| Offer the bridges upstream to cslib-frontier after release? | Open. The project owner decides. |
| Do the optional Cook text audit, and with which reviewer? | The audit is in `Audit/cook_text_audit.md`. The reviewer is open. |

## Credits and license

Monteverde is released under the Apache License 2.0. It reuses work by the authors of
LeanMillenniumPrizeProblems, cslib-frontier, CSLib and Mathlib. See `CREDITS.md` and `NOTICE`.

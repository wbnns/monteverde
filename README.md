# Monteverde

Monteverde proves in Lean 4 that the LeanMillenniumPrizeProblems formulation of the Clay
P vs NP statement is equivalent to P vs NP in
[cslib-frontier](https://github.com/cslib-community/cslib-frontier).

The project does not try to resolve P vs NP. It links two formal statements of the problem, so
that a result about one is a result about the other.

## Target claim

When milestone M5 is done, this sentence is true:

> I proved in Lean that the LeanMillenniumPrizeProblems formulation of the Clay P vs NP
> statement is equivalent to P vs NP in cslib-frontier, the largest Lean complexity library.

"The largest" stays in the claim only if the size count at release puts cslib-frontier first.
Otherwise the claim says "a major Lean complexity library".

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
| M5 | Size count, independent kernel check, credits, release | Not started |

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

The claim refers to these commits. Moving a pin is a deliberate release step.

## Layout

```
Vendor/Millennium/   Clay definitions, ported to this toolchain (see CHANGES.md, port.patch)
Vendor/CookLevin/    TM2 composition from millennium-cook-levin, ported the same way
Monteverde/          The bridge, in four layers:
  Encoding/          L0: block code, pairs, certificates
  Function/          L1: polynomial-time functions, both directions
  Classes/           L2: P and NP
  Statements/        L3: one headline theorem per file
Audit/               Claim check, axiom check, isolation check, size count
Tests/               Name probe and non-vacuity tests
scripts/             diff_vendor.sh and other checks
```

## Build

You need [elan](https://github.com/leanprover/elan). Then:

```bash
lake exe cache get        # Mathlib build cache
lake build Vendor Monteverde Audit Tests
scripts/diff_vendor.sh    # vendored files against their upstream commits
scripts/check_isolation.sh
```

The first build compiles the needed part of cslib-frontier (about 300 modules).

## Credits and license

Monteverde is released under the Apache License 2.0. It reuses work by the authors of
LeanMillenniumPrizeProblems, cslib-frontier, CSLib and Mathlib. See `CREDITS.md` and `NOTICE`.

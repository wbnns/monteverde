# Credits

Monteverde is by Will Binns. It proves the bridge between two formal statements of P vs NP, and
it stands on the work below. Every reused definition and theorem is listed with its source
commit. Authors come from file headers, `CITATION.cff` and git history at the pinned commits.

## LeanMillenniumPrizeProblems

- Source: https://github.com/lean-dojo/LeanMillenniumPrizeProblems, commit
  `603053dc267cf3efe422f438eb78098c0ececd6f`
- License: Apache-2.0
- Author: Robert Joseph George (`CITATION.cff`, `LICENSE`, and every commit to
  `Problems/PVersusNP/Millennium.lean`).
- Reused, vendored in `Vendor/Millennium/`: the whole file `Problems/PVersusNP/Millennium.lean`,
  including the two official targets `Millennium.ClayPVersusNP` and
  `Millennium.ClayPVersusNP.Formulations.NegativeBranch`, and `InPolynomialTime`,
  `InNondeterministicPolynomialTime`, `PolynomialTimeCheckingRelation`, `fin_encoding_string`,
  `pair_encoding`, `Language`.

## cslib-frontier

- Source: https://github.com/cslib-community/cslib-frontier, commit
  `9bfe667f8c66a8a2a3e17391ce9a5cc965190544`
- License: Apache-2.0
- Reused, by direct reference:

| Declaration | File (under `CslibFrontier/Computability/`) | Author |
|-------------|---------------------------------------------|--------|
| `Cslib.Complexity.P`, `NP`, `IsVerifier` | `Complexity/Classes/P.lean`, `Complexity/Classes/NP.lean` | Samuel Schlesinger |
| `PolyTimeReducible`, `NPComplete.mem_P_iff`, `P_subset_NP` | `Complexity/Reduction.lean` | Samuel Schlesinger |
| `PolyTimeReducible.mem_NP`, `mem_NP_of_check` | `Complexity/Classes/NP/Witness.lean` | Samuel Schlesinger |
| `image_SAT_mem_NP` | `Complexity/Classes/NP/Image.lean` | Samuel Schlesinger |
| `SAT`, `encCNF` | `Complexity/Problems/SAT.lean` | Samuel Schlesinger |
| `CookLevin.SAT_npComplete` | `Complexity/CookLevin/Completeness.lean` | Samuel Schlesinger |
| `haltingProblem_notMem_NP` (test only) | `Complexity/Problems/Halting.lean` | Christian Reitwiessner |
| `TM2ComputableInPolyTime.computableInPolyTime_encList` (TM2 to multi-tape) | `Machines/Turing/TM2/PolyTime.lean` | Erik Demaine |
| `ComputableInPolyTime.exists_tm2ComputableInPolyTime` (multi-tape to TM2) | `Machines/Turing/TM2/Reverse/Transfer.lean` | Erik Demaine |
| `PartialDecoder`, `PartialDecoder.list`, `PartialDecoder.checked` | `Machines/Turing/MultiTape/Encodings/Decoder/Partial.lean` | Erik Demaine |
| `encList`, `encBits` | `Machines/Turing/MultiTape/Encodings/List.lean` | Christian Reitwiessner |
| `encFinite` | `Machines/Turing/MultiTape/Encodings/Finite.lean` | Samuel Schlesinger |
| `ComputableInPolyTime` and its combinators | `Machines/Turing/MultiTape/PolyTime.lean` and `Complexity/PolyTime/` | Samuel Schlesinger, Christian Reitwiessner, Erik Demaine |

- Authors of all 498 cslib-frontier and CSLib modules in Monteverde's import closure, with the
  number of module headers that name them: Samuel Schlesinger (358), Christian Reitwiessner
  (157), Erik Demaine (38), Karn Seth (13), Bolton Bailey (10), Renfei Zhou (6), Devon Tuma (5),
  Anton Kovsharov (4), Josha Dekker (4), Kexing Ying (4), and from CSLib: Christian Reitwiessner
  (21), Samuel Schlesinger (12), Bolton Bailey (4), Aviv Bar Natan (4), Devon Tuma, Eric Wieser,
  Quang Dao, Thomas Waring (2 each), Josha Dekker, Kexing Ying, Fabrizio Montesi, John Jennings,
  Chris Henson, Jesse Alama (1 each).

## millennium-cook-levin

- Source: https://github.com/JoshuaTan42/millennium-cook-levin, commit
  `879c4835640119ad009abeb62ebd7a96f87eb9e8`
- License: Apache-2.0
- Author: Joshua Tan
- Reused, vendored in `Vendor/CookLevin/`:
  - `Comp.lean`, the composition of polynomial-time TM2 machines
    (`PvsNP.tm2ComputableInPolyTime_comp`, `PvsNP.comp`). The bridges use it.
  - The Cook-Levin proof against the Clay definitions: `Prog.lean`, `Emb.lean`,
    `CookLevin.lean` (`PvsNP.SAT`, `PvsNP.sat_in_np`), `D3Fam.lean`, `D3OneHot.lean`,
    `D3Shift.lean`, `Sit.lean`, `D3Acc.lean`, `D3Init.lean`, `Asm.lean`, `Pre.lean` and
    `Pkg.lean` (`PvsNP.cook_levin`). Only the Cook-Levin cross-check in `CrossCheck/` uses them.

## Mathlib

- Source: https://github.com/leanprover-community/mathlib4 (through cslib-frontier's pin
  `bbff2954fe5ee3b7a4b33cc26ef873a1c3277d91`)
- License: Apache-2.0
- Reused: the TM2 machine model (`Turing.FinTM2`, `TM2ComputableInPolyTime`; Pim Spelier, Daan
  van Gent), and, copied in `Vendor/Millennium/MathlibCompat.lean`, the bundled `Encoding`,
  `FinEncoding` and `finEncodingBoolBool` from `Mathlib/Computability/Encoding.lean` at commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (Pim Spelier, Daan van Gent).

## New in Monteverde

The block code wrapper, the finitization of TM2 work alphabets, the recoder and decoder
machines, the pair-word conversions, the certificate decoder, the forward and reverse bridges,
the class and reduction bridges, the statements, the audit and the Cook-Levin cross-check are new
work in this repository.

`Audit/cook_text_audit.md` quotes short phrases from Stephen Cook, "The P versus NP Problem", the
official Clay Mathematics Institute problem description.

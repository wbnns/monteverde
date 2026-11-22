# Credits

Monteverde is by Will Binns. It reuses the definitions and theorems below. Each entry names the
source commit. The final list, with every author taken from git history, is part of milestone M5.

## LeanMillenniumPrizeProblems

- Source: https://github.com/lean-dojo/LeanMillenniumPrizeProblems, commit `603053dc267cf3efe422f438eb78098c0ececd6f`
- License: Apache-2.0
- Reused: `Problems/PVersusNP/Millennium.lean` (vendored in `Vendor/Millennium/`): `Millennium.ClayPVersusNP`,
  `Millennium.ClayPVersusNP.Formulations.NegativeBranch`, `InPolynomialTime`,
  `InNondeterministicPolynomialTime`, `fin_encoding_string`, `pair_encoding` and the rest of the file.
- Authors: to be completed from git history (M5).

## cslib-frontier

- Source: https://github.com/cslib-community/cslib-frontier, commit `9bfe667f8c66a8a2a3e17391ce9a5cc965190544`
- License: Apache-2.0
- Reused: the classes `P` and `NP`, the encodings, the TM2 bridge in both directions, reductions,
  `NPComplete.mem_P_iff`, SAT and its NP-completeness, `mem_NP_of_witness`, `PolyTimeEquiv`.
- Authors: to be completed from git history (M5). This includes Erik Demaine (TM2 bridge) and
  Samuel Schlesinger (P, NP and reductions).

## Mathlib

- Source: https://github.com/leanprover-community/mathlib4
- License: Apache-2.0
- Reused: `Vendor/Millennium/MathlibCompat.lean` copies `Encoding`, `FinEncoding` and
  `finEncodingBoolBool` from `Mathlib/Computability/Encoding.lean` at commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (Pim Spelier, Daan van Gent).

## millennium-cook-levin

- Source: https://github.com/JoshuaTan42/millennium-cook-levin, commit `879c4835640119ad009abeb62ebd7a96f87eb9e8`
- License: Apache-2.0
- Reused: `Comp.lean` (vendored in `Vendor/CookLevin/`), the composition of polynomial-time TM2
  machines, `PvsNP.tm2ComputableInPolyTime_comp` (Joshua Tan).

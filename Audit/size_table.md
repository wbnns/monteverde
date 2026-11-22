# Theorem counts in public Lean complexity libraries

Counted on 2026-11-22 by `Audit/size_count.py` at the pinned commits in `Audit/size_pins.json`.
A declaration is a line that starts (after optional attributes and modifiers) with `theorem` or `lemma`.

| Rank | Library | Theorems and lemmas | .lean files | Commit |
|------|---------|--------------------:|------------:|--------|
| 1 | [cslib-frontier (Computability)](https://github.com/cslib-community/cslib-frontier) (`CslibFrontier/Computability`) | 49,439 | 4,151 | `9bfe667` |
| 2 | [descriptive-complexity (PierreSenellart)](https://github.com/PierreSenellart/descriptive-complexity) | 12,671 | 874 | `214dd41` |
| 3 | [starpos/lean-np-complete](https://github.com/starpos/lean-np-complete) | 5,467 | 495 | `10ebb66` |
| 4 | [CSLib](https://github.com/leanprover/cslib) | 3,463 | 361 | `be203ab` |
| 5 | [konard/p-vs-np](https://github.com/konard/p-vs-np) | 2,444 | 286 | `ecedd2b` |
| 6 | [millennium-cook-levin](https://github.com/JoshuaTan42/millennium-cook-levin) | 653 | 24 | `879c483` |
| 7 | [PleaNP](https://github.com/philipdallen/PleaNP) | 239 | 75 | `f8d43d2` |
| 8 | [alonamaloh/complexity-lean](https://github.com/alonamaloh/complexity-lean) | 70 | 10 | `e2030b2` |
| 9 | [descriptive-complexity (SamuelSchlesinger)](https://github.com/SamuelSchlesinger/descriptive-complexity) | 23 | 12 | `16464bc` |
| 10 | [ShantiDraconis/clay-p-vs-np-statement](https://github.com/ShantiDraconis/clay-p-vs-np-statement) | 3 | 3 | `6375290` |

Notes:

- The count reads GitHub's source archive at each commit. The archive leaves out paths that the repository marks `export-ignore` in `.gitattributes`. For descriptive-complexity (PierreSenellart) this leaves out `lax/`: 2,052 files that are archive exports of tagged versions of the library itself (its `.gitattributes` says that they restate its definitions and vendor its proofs). With `lax/`, the same pattern counts 31,938 theorems and lemmas in a full clone of that commit. cslib-frontier is first with or without these files.
- The design doc's row for descriptive-complexity (12,670, cloned on 2026-11-22) is one less than this count at the same commit (`214dd41`, dated 2026-11-18). The design doc does not record its exact line pattern. A difference of one does not change the ranking.

For reference, the whole cslib-frontier repository has 119,083 declarations in 12,288 files.

Result: cslib-frontier is first. The claim can say "the largest".

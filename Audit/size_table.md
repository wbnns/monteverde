# Theorem counts in public Lean complexity libraries

Counted on 2026-11-22 by `Audit/size_count.py` at the pinned commits in `Audit/size_pins.json`.
A declaration is a line that starts (after optional attributes and modifiers) with `theorem` or `lemma`, in any `.lean` file of a full clone.

| Rank | Library | Theorems and lemmas | .lean files | Commit |
|------|---------|--------------------:|------------:|--------|
| 1 | [cslib-frontier (Computability)](https://github.com/cslib-community/cslib-frontier) (`CslibFrontier/Computability`) | 49,439 | 4,151 | `9bfe667` |
| 2 | [descriptive-complexity (PierreSenellart)](https://github.com/PierreSenellart/descriptive-complexity) | 31,938 | 2,926 | `214dd41` |
| 3 | [starpos/lean-np-complete](https://github.com/starpos/lean-np-complete) | 5,467 | 495 | `10ebb66` |
| 4 | [CSLib](https://github.com/leanprover/cslib) | 3,463 | 361 | `be203ab` |
| 5 | [konard/p-vs-np](https://github.com/konard/p-vs-np) | 2,444 | 286 | `ecedd2b` |
| 6 | [millennium-cook-levin](https://github.com/JoshuaTan42/millennium-cook-levin) | 653 | 24 | `879c483` |
| 7 | [PleaNP](https://github.com/philipdallen/PleaNP) | 239 | 75 | `f8d43d2` |
| 8 | [alonamaloh/complexity-lean](https://github.com/alonamaloh/complexity-lean) | 70 | 10 | `e2030b2` |
| 9 | [descriptive-complexity (SamuelSchlesinger)](https://github.com/SamuelSchlesinger/descriptive-complexity) | 23 | 12 | `16464bc` |
| 10 | [ShantiDraconis/clay-p-vs-np-statement](https://github.com/ShantiDraconis/clay-p-vs-np-statement) | 3 | 3 | `6375290` |

Notes:

- Counts come from full clones, so they include every tracked file. For descriptive-complexity (PierreSenellart), 19,267 of the 31,938 are in `lax/`: archive exports of tagged versions of the library itself, which restate its definitions and vendor its proofs (see its `.gitattributes`). Without `lax/` it has 12,671. cslib-frontier is first either way.
- The design doc's row for descriptive-complexity (12,670, cloned on 2026-11-22) matches the count without `lax/` to within one. The design doc does not record its exact line pattern.

For reference, the whole cslib-frontier repository has 119,083 declarations in 12,288 files.

Result: cslib-frontier is first. The claim can say "the largest".

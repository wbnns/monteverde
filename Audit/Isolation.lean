import Monteverde.Headline.Bits
import Monteverde.Headline.Clay
import Monteverde.Headline.NegativeBranch

/-!
# Statement isolation

The main risk is a wrong statement: a theorem that is true but does not say what we claim. So
the statements must not depend on the bridge.

The statements live in `Monteverde/Statements/`, one per file, as definitions. Those files import
only the vendored Clay definitions and cslib-frontier's class definitions, never a proof
(`scripts/check_isolation.sh` checks the imports). The theorems that prove them live in
`Monteverde/Headline/`.

`#check_isolation` fails the build unless, for each headline theorem:

1. the theorem's type is exactly the body of its statement definition (the same term, not only
   definitionally equal), and
2. every constant in that statement is a definition (not a theorem) from Lean core, Mathlib and
   its dependencies, cslib, cslib-frontier, the vendored Clay file, or `Monteverde.Statements`.
-/

open Lean Elab Command

/-- Each headline theorem with its statement definition. -/
def headlinePairs : List (Name × Name) :=
  [(``Monteverde.cslibPEqNP_iff_bits, ``Monteverde.Statements.CslibPEqNPIffBits),
    (``Monteverde.clay_iff_cslib, ``Monteverde.Statements.ClayIffCslib),
    (``Monteverde.clay_negative_iff_cslib, ``Monteverde.Statements.ClayNegativeIffCslib)]

/-- Module prefixes that a statement may draw on. -/
def allowedModulePrefixes : List Name :=
  [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient, `Cslib, `CslibFrontier, `Vendor.Millennium,
    `Monteverde.Statements]

/-- Fail unless each headline theorem states exactly its isolated statement. -/
elab "#check_isolation" : command => do
  let env ← getEnv
  for (thm, stmt) in headlinePairs do
    let some (.thmInfo t) := env.find? thm | throwError m!"{thm} is not a theorem"
    let some (.defnInfo d) := env.find? stmt | throwError m!"{stmt} is not a definition"
    unless t.type == d.value do
      throwError m!"{thm}: its type is not exactly the statement {stmt}"
    let some sIdx := env.getModuleIdxFor? stmt | throwError m!"{stmt} is not imported"
    let sMod := env.header.moduleNames[sIdx.toNat]!
    unless (`Monteverde.Statements).isPrefixOf sMod do
      throwError m!"{stmt} is defined in {sMod}, not in Monteverde/Statements/"
    for c in d.value.getUsedConstants do
      let some idx := env.getModuleIdxFor? c | throwError m!"{stmt}: {c} is not imported"
      let mod := env.header.moduleNames[idx.toNat]!
      unless allowedModulePrefixes.any (·.isPrefixOf mod) do
        throwError m!"{stmt}: {c} comes from {mod}, which a statement may not use"
      if let some (.thmInfo _) := env.find? c then
        throwError m!"{stmt}: it mentions the theorem {c}"
    logInfo m!"{thm}: type is exactly {stmt}, which is isolated"

#check_isolation

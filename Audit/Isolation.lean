import Monteverde.Statements.Bits
import Monteverde.Statements.Clay
import Monteverde.Statements.NegativeBranch

/-!
# Statement isolation

The main risk is a wrong statement: a theorem that is true but does not say what we claim. So
the statements must not depend on the bridge. `#check_isolation` fails the build if the type of
a headline theorem mentions a constant that is

* a theorem (types must be built from definitions only), or
* defined in a Monteverde module other than `Monteverde.Statements.Defs`, or
* defined outside these sources: Lean core, Mathlib and its dependencies, cslib, cslib-frontier,
  and the vendored Clay file.

`scripts/check_isolation.sh` also checks that `Monteverde/Statements/Defs.lean` imports only
cslib-frontier's class definitions.
-/

open Lean Elab Command

/-- The headline theorems. -/
def headlineDecls : List Name :=
  [``Monteverde.cslibPEqNP_iff_bits, ``Monteverde.clay_iff_cslib,
    ``Monteverde.clay_negative_iff_cslib]

/-- Module prefixes that a statement may draw on. -/
def allowedModulePrefixes : List Name :=
  [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient, `Cslib, `CslibFrontier, `Vendor.Millennium,
    `Monteverde.Statements.Defs]

/-- Fail unless every constant in each headline type is a definition from an allowed module. -/
elab "#check_isolation" : command => do
  let env ← getEnv
  for n in headlineDecls do
    let some info := env.find? n | throwError m!"unknown declaration {n}"
    for c in info.type.getUsedConstants do
      let some idx := env.getModuleIdxFor? c | throwError m!"{n}: {c} is not imported"
      let mod := env.header.moduleNames[idx.toNat]!
      unless allowedModulePrefixes.any (·.isPrefixOf mod) do
        throwError m!"{n}: {c} comes from {mod}, which a statement may not use"
      if let some (.thmInfo _) := env.find? c then
        throwError m!"{n}: its type mentions the theorem {c}"
    logInfo m!"{n}: type is isolated"

#check_isolation

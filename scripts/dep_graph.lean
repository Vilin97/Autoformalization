-- Import all project modules that build successfully.
-- If new modules are added, add them here.
import Aristotle.Landau.main.Defs
import Aristotle.Landau.main.Section2
-- import Aristotle.Landau.main.Section3        -- via Section3Helpers (build issue)
import Aristotle.Landau.main.Section4
import Aristotle.Landau.main.Section5
import Aristotle.Landau.main.Section6
import Aristotle.Landau.main.Section7
import Aristotle.Landau.main.Section8
import Aristotle.Landau.main.VMLInputDerive
import Aristotle.Landau.main.Theorem42
-- import Aristotle.Landau.main.VelocityDecayInstance  -- depends on Section3Helpers
-- import Aristotle.Landau.main.SchwartzDecayDefs      -- depends on Section3Helpers

/-!
# Declaration dependency graph extractor

Discovers all non-internal `VML.*` declarations in the environment and prints
their dependencies on other `VML.*` declarations.

## Usage
```
lake env lean scripts/dep_graph.lean
```

## Output format
Each line is `DeclName: [Dep1, Dep2, ...]` showing which other VML declarations
are directly referenced in the type or proof of `DeclName`.
-/

open Lean

/-- Check if a name component signals an auto-generated declaration. -/
def hasInternalComponent (n : Name) : Bool :=
  match n with
  | .anonymous => false
  | .num parent _ => hasInternalComponent parent
  | .str parent s =>
    s.startsWith "match_" ||
    s.startsWith "proof_" ||
    s.startsWith "eq_" ||
    s.startsWith "_uniq" ||
    s.startsWith "_private" ||
    s.startsWith "_cstage" ||
    s == "rec" || s == "recOn" || s == "casesOn" || s == "brecOn" ||
    s == "below" || s == "noConfusion" || s == "noConfusionType" ||
    s == "sizeOf" || s == "sizeOf_spec" ||
    s == "injEq" || s == "mk" || s == "toCtorIdx" ||
    hasInternalComponent parent

/-- Check if a declaration is user-facing (theorem, def, axiom, inductive). -/
def isUserFacing (env : Environment) (n : Name) : Bool :=
  if hasInternalComponent n then false
  else match env.find? n with
  | some (.thmInfo _)    => true
  | some (.defnInfo _)   => true
  | some (.axiomInfo _)  => true
  | some (.opaqueInfo _) => true
  | some (.inductInfo _) => true
  | _                    => false

/-- Get all VML.* constants directly referenced in a declaration's type and value. -/
def getVMLDeps (env : Environment) (name : Name) : Array Name := Id.run do
  let some ci := env.find? name | return #[]
  let mut used : NameSet := {}
  for n in ci.type.getUsedConstants do
    used := used.insert n
  if let some v := ci.value? then
    for n in v.getUsedConstants do
      used := used.insert n
  let mut result : Array Name := #[]
  for n in used.toArray do
    if n != name && n.getRoot == `VML then
      result := result.push n
  return result

/-- Collect all user-facing VML.* declarations in the environment. -/
def collectVMLDecls (env : Environment) : Array Name := Id.run do
  let mut result : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.getRoot == `VML && isUserFacing env n then
      result := result.push n
  return result.qsort (·.toString < ·.toString)

elab "#dep_graph" : command => do
  let env ← getEnv
  let allDecls := collectVMLDecls env
  let declSet : NameSet := allDecls.foldl (fun s n => s.insert n) {}
  logInfo m!"Found {allDecls.size} VML declarations"
  for name in allDecls do
    let allDeps := getVMLDeps env name
    let deps := allDeps.filter fun n => declSet.contains n
    let depStr := deps.toList.map toString |> ", ".intercalate
    logInfo m!"{name}: [{depStr}]"

#dep_graph

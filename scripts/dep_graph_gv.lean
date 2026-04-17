-- Import all GV modules via the top-level build target.
import Aristotle.GrothendieckVanishing.main.main

/-!
# Declaration dependency graph extractor for Grothendieck Vanishing

Discovers dependencies between blueprint declarations and prints them,
including transitive dependencies through non-blueprint intermediaries.

## Usage
```
lake env lean scripts/dep_graph_gv.lean
```

## Output format
Each line is `LeanName: [Dep1, Dep2, ...]` showing which other blueprint
declarations are transitively referenced (via any intermediate declarations)
in the type or proof of `LeanName`.
-/

open Lean

/-- The set of Lean declaration names referenced in the blueprint via \lean{...}. -/
def blueprintDecls : Array Name := #[
  `IsFlasqueSheaf,
  `isFlasque_of_injective,
  `isFlasque_X₃_of_shortExact,
  `sheafH0EquivSections,
  `ext_zero_map_surjective,
  `sheafH_dimension_shift,
  `FlasqueVanishing,
  `ext_dimension_shift,
  `ext_dimension_shift_X₃,
  `closedIncl_pushforward_shortExact,
  `PushforwardHVanishing,
  `TopCat.closedIncl_counit_isIso,
  `epi_unit_of_closedImmersion,
  `closedImmersionSES,
  `opens_eq_bot_or_top_of_irreducibleSpace_dim_zero,
  `topologicalKrullDim_nonneg_of_irreducible,
  `topologicalKrullDim_lt_of_isIrreducible_of_isClosed,
  `TopCat.Presheaf.zeroOutside,
  `TopCat.Sheaf.zeroOutsideInt,
  `TopCat.Sheaf.zeroOutsideInt.sHom,
  `stalk_zeroOutsideInt_eq_zsmul_generator,
  `zsmul_generator_injective,
  `constantSheaf_flasque_of_irreducible,
  `sheaf_restriction_epi_of_irreducible_dim_zero,
  `grothendieck_vanishing_dim_zero,
  `createsFilteredColimit,
  `sheafH_preserves_filtered_colimits,
  `cohomology_vanishing_of_finitelyGenerated_vanishing,
  `zeroOutsideInt_vanishing,
  `zeroOutsideInt_cohomology_vanishing,
  `finsetGeneratedSheaf_vanishing,
  `directLimit_cohomology_vanishing,
  `exists_closed_subset_lt_dim_of_irreducible_pos,
  `exists_good_section,
  `IrreduciblePosVanishing,
  `ReducibleVanishing',
  `grothendieck_vanishing_of_irreducible,
  `GrothendieckVanishing
]

/-- Build a NameSet from the blueprint declarations array. -/
def blueprintDeclSet : NameSet :=
  blueprintDecls.foldl (fun s n => s.insert n) {}

/-- Get all constants directly referenced in a declaration's type and value. -/
def getDirectDeps (env : Environment) (name : Name) : Array Name := Id.run do
  let some ci := env.find? name | return #[]
  let mut used : NameSet := {}
  for n in ci.type.getUsedConstants do
    used := used.insert n
  if let some v := ci.value? then
    for n in v.getUsedConstants do
      used := used.insert n
  return used.toArray.filter (· != name)

/-- Check if a name belongs to our project (not Mathlib/core). -/
def isProjectDecl (n : Name) : Bool :=
  -- Include top-level declarations from our files and TopCat.* declarations we defined
  -- Exclude Lean/Mathlib namespace prefixes
  let root := n.getRoot
  root != `Lean && root != `Init && root != `Std && root != `Mathlib &&
  root != `CategoryTheory && root != `TopologicalSpace && root != `Order &&
  root != `Finset && root != `Set && root != `List && root != `Array &&
  root != `Nat && root != `Int && root != `Function && root != `Equiv &&
  root != `Bool && root != `Option && root != `Prod && root != `Sum
  -- Note: TopCat.* declarations from our files ARE in the environment
  -- but their root is `TopCat which we don't filter out

/-- Find transitive blueprint dependencies by BFS through non-blueprint intermediaries.
    Starting from `name`, follow deps through non-blueprint project declarations
    until we hit blueprint declarations (which we collect) or Mathlib declarations
    (which we stop at). -/
def getTransitiveBlueprintDeps (env : Environment) (name : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut queue : Array Name := getDirectDeps env name
  let mut result : NameSet := {}
  visited := visited.insert name
  while queue.size > 0 do
    let current := queue[0]!
    queue := queue.extract 1 queue.size
    if visited.contains current then continue
    visited := visited.insert current
    if blueprintDeclSet.contains current then
      -- This is a blueprint declaration — record it as a dependency
      result := result.insert current
    else
      -- Not a blueprint declaration — if it's a project declaration, explore its deps
      let directDeps := getDirectDeps env current
      for dep in directDeps do
        if !visited.contains dep then
          queue := queue.push dep
  return result.toArray.qsort (·.toString < ·.toString)

elab "#dep_graph_gv" : command => do
  let env ← getEnv
  -- First check which blueprint decls actually exist
  let mut missing : Array Name := #[]
  for name in blueprintDecls do
    if env.find? name |>.isNone then
      missing := missing.push name
  if missing.size > 0 then
    logWarning m!"Missing declarations: {missing.toList}"
  -- Print direct dependencies (blueprint-to-blueprint only)
  logInfo m!"=== DIRECT DEPENDENCIES ==="
  for name in blueprintDecls do
    if env.find? name |>.isSome then
      let allDeps := getDirectDeps env name
      let deps := allDeps.filter fun n => blueprintDeclSet.contains n
      let depsSorted := deps.qsort (·.toString < ·.toString)
      let depStr := depsSorted.toList.map toString |> ", ".intercalate
      logInfo m!"{name}: [{depStr}]"
  -- Print transitive dependencies
  logInfo m!"=== TRANSITIVE DEPENDENCIES (through non-blueprint intermediaries) ==="
  for name in blueprintDecls do
    if env.find? name |>.isSome then
      let deps := getTransitiveBlueprintDeps env name
      let depStr := deps.toList.map toString |> ", ".intercalate
      logInfo m!"{name}: [{depStr}]"

#dep_graph_gv

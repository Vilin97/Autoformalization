import Aristotle.GrothendieckVanishing.main.GrothendieckVanishingOverview

/-!
# Blueprint validator

Checks that every declaration referenced by the blueprint actually exists in
the Lean environment and is reachable from `GrothendieckVanishing`.

Catches hallucinated entries (names that never existed or were renamed/deleted).

## Usage
```
lake env lean scripts/validate_blueprint.lean
```
-/

open Lean

/-- Every `\lean{...}` reference from `blueprint/src/content.tex` and
    every entry in `blueprint/lean_decls`. This list must match those files.
    Discrepancies themselves indicate a problem. -/
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
  `topologicalKrullDim_nonneg,
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

/-- Check if a module belongs to our GV formalization. -/
def isGVModule (modName : Name) : Bool :=
  (`Aristotle.GrothendieckVanishing.main).isPrefixOf modName

/-- Collect all declarations from our project modules (including internal, for BFS). -/
def getAllProjectDecls (env : Environment) : NameSet := Id.run do
  let mut all_ : NameSet := {}
  for idx in [:env.header.moduleNames.size] do
    if isGVModule env.header.moduleNames[idx]! then
      for name in env.header.moduleData[idx]!.constNames do
        all_ := all_.insert name
  return all_

/-- Get constants directly referenced in a declaration's type and value. -/
def getDeps (env : Environment) (name : Name) : Array Name := Id.run do
  let some ci := env.find? name | return #[]
  let mut used : NameSet := {}
  for n in ci.type.getUsedConstants do
    if n != name then used := used.insert n
  if let some v := ci.value? then
    for n in v.getUsedConstants do
      if n != name then used := used.insert n
  return used.toArray

/-- BFS from roots through all project declarations (including private). -/
def reachable (env : Environment) (roots : Array Name)
    (expandSet : NameSet) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut queue := roots
  while queue.size > 0 do
    let current := queue[0]!
    queue := queue.extract 1 queue.size
    if visited.contains current then continue
    visited := visited.insert current
    if expandSet.contains current || roots.contains current then
      for dep in getDeps env current do
        if !visited.contains dep then
          queue := queue.push dep
  return visited

elab "#validate_blueprint" : command => do
  let env ← getEnv
  let allDeclSet := getAllProjectDecls env
  let reached := reachable env #[`GrothendieckVanishing] allDeclSet
  let mut missing : Array Name := #[]
  let mut unreachable : Array Name := #[]
  let mut ok : Nat := 0
  for name in blueprintDecls do
    if env.find? name |>.isNone then
      missing := missing.push name
    else if !reached.contains name then
      unreachable := unreachable.push name
    else
      ok := ok + 1
  -- Report
  logInfo m!"Blueprint validation: {blueprintDecls.size} entries"
  logInfo m!"  ✓ {ok} exist and are reachable from GrothendieckVanishing"
  if missing.size > 0 then
    logError m!"  ✗ {missing.size} HALLUCINATED (do not exist in the environment):"
    for name in missing do
      logError m!"      {name}"
  if unreachable.size > 0 then
    logWarning m!"  ? {unreachable.size} exist but are NOT reachable from GrothendieckVanishing:"
    for name in unreachable do
      logWarning m!"      {name}"

#validate_blueprint

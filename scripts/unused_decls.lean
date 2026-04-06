import Aristotle.GrothendieckVanishing.main.main

/-!
# Unused project declarations finder

Traces transitive dependencies from `GrothendieckVanishing` and reports
any project-defined declarations that are not reachable — i.e., dead code
that could be safely deleted without affecting the main theorem.

## Usage
```
lake env lean scripts/unused_decls.lean
```
-/

open Lean

/-- Check if a module belongs to our GV formalization. -/
def isGVModule (modName : Name) : Bool :=
  (`Aristotle.GrothendieckVanishing.main).isPrefixOf modName

/-- Collect all declarations from our project modules.
    Returns (public, all) where `public` excludes internal/private names
    and `all` includes everything (needed for BFS traversal). -/
def getProjectDecls (env : Environment) : Array Name × NameSet := Id.run do
  let mut public_ : Array Name := #[]
  let mut all_ : NameSet := {}
  for idx in [:env.header.moduleNames.size] do
    if isGVModule env.header.moduleNames[idx]! then
      for name in env.header.moduleData[idx]!.constNames do
        all_ := all_.insert name
        if !name.isInternalDetail then
          public_ := public_.push name
  return (public_, all_)

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

/-- BFS from roots through all project declarations (including private/internal).
    We expand any declaration in `expandSet` (all project module decls).
    Non-project declarations are not expanded (Mathlib can't reference us). -/
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

/-- Get the module name for a declaration (for reporting). -/
def getModule (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!.toString
  | none => "<current>"

elab "#find_unused" : command => do
  let env ← getEnv
  -- Step 1: Collect all project declarations
  let (publicDecls, allDeclSet) := getProjectDecls env
  logInfo m!"Total project declarations: {publicDecls.size} public"
  -- Step 2: BFS from GrothendieckVanishing through ALL project decls (incl. private)
  let roots := #[`GrothendieckVanishing]
  let reached := reachable env roots allDeclSet
  -- Step 3: Find unreachable public project declarations
  let mut unreached : Array (Name × String) := #[]
  for name in publicDecls do
    if !reached.contains name then
      unreached := unreached.push (name, getModule env name)
  -- Step 4: Report
  if unreached.size == 0 then
    logInfo m!"All {publicDecls.size} project declarations are reachable from GrothendieckVanishing."
  else
    logWarning m!"Found {unreached.size} unreachable declarations:"
    -- Group by module
    let unreachedSorted := unreached.qsort (fun a b => a.2 < b.2 || (a.2 == b.2 && a.1.toString < b.1.toString))
    let mut currentMod := ""
    for (name, mod) in unreachedSorted do
      if mod != currentMod then
        currentMod := mod
        logWarning m!"  [{mod}]"
      logWarning m!"    {name}"

#find_unused

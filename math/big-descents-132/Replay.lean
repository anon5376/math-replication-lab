import Lean.Replay

open Lean

/-- Recheck the compiled declarations for one module over its declared imports.
Lean 4.19 creates module-local private names during kernel replay. -/
private def replayModule (name : Name) (data : ModuleData) : IO Nat := do
  let base ← importModules data.imports {} 0
  let mut project : Std.HashMap Name ConstantInfo := {}
  let mut safe : Array Name := #[]
  for decl in data.constants do
    if !decl.isUnsafe && !decl.isPartial then
      if let .axiomInfo _ := decl then
        throw <| IO.userError s!"project axiom: {decl.name}"
      if base.contains decl.name then
        throw <| IO.userError s!"declaration already imported: {decl.name}"
      safe := safe.push decl.name
    project := project.insert decl.name decl
  let checked ← Environment.replay project base
  for decl in safe do
    unless checked.contains decl do throw <| IO.userError s!"missing declaration {decl}"
  IO.println s!"{name}: {safe.size} safe declarations"
  return safe.size

/-- Run each module in a separate process so its imported environment is
released before loading the next one. The parent fails on a reported panic. -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let root := `BigDescents132
  if let [mod] := args then
    let m := mod.toName
    unless root.isPrefixOf m do throw <| IO.userError s!"outside project: {m}"
    let (data, _region) ← readModuleData (← findOLean m)
    let _ ← replayModule m data
    return
  unless args.isEmpty do throw <| IO.userError "expected at most one module name"
  let mut pending := [root]
  let mut seen : List Name := []
  let mut total := 0
  while !pending.isEmpty do
    let m := pending.head!
    pending := pending.tail!
    if seen.contains m then continue
    seen := m :: seen
    let (data, _region) ← readModuleData (← findOLean m)
    for imp in data.imports do
      if root.isPrefixOf imp.module then pending := imp.module :: pending
    let result ← IO.Process.output { cmd := "lean", args := #["--run", "Replay.lean", m.toString] }
    unless result.exitCode == 0 && result.stderr.isEmpty do
      throw <| IO.userError s!"{m} replay failed ({result.exitCode}): {result.stderr}"
    IO.print result.stdout
    (← IO.getStdout).flush
    total := total + (data.constants.filter (fun d => !d.isUnsafe && !d.isPartial)).size
  IO.println s!"Replayed {total} safe declarations from {seen.length} project modules."

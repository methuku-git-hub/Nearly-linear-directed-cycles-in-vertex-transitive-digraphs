module

public import LeanChecker

@[expose] public section

/-!
Replay exactly the same kernel checks as the bundled `leanchecker`, one module
at a time. The bundled prefix-based CLI starts all module replays concurrently;
sequential replay avoids multiplying the memory use of imported environments.
This file is verification infrastructure and is not imported by the mathematics.
-/

unsafe def replayProjectSequentially : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let entries ← ("DirectedCycles" : System.FilePath).readDir
  let mut modules : Array String := #[]
  for entry in entries do
    if entry.path.extension == some "lean" then
      if let some stem := entry.path.fileStem then
        modules := modules.push ("DirectedCycles." ++ stem)
  modules := modules.qsort (· < ·)
  modules := modules.push "DirectedCycles"
  modules := modules.push "Mathlib.Combinatorics.Hall.Finite"
  let progress ← IO.FS.Handle.mk "verification/replay-progress.log" .write
  for moduleName in modules do
    IO.println s!"replaying {moduleName} sequentially"
    progress.putStrLn s!"replaying {moduleName} sequentially"
    progress.flush
    replayFromImports moduleName.toName
    IO.println s!"passed {moduleName}"
    progress.putStrLn s!"passed {moduleName}"
    progress.flush

#eval replayProjectSequentially

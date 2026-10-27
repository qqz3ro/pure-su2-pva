import Lake.Load.Workspace
import Lake.Build.Run
import Lake.CLI.Build

/-! Operational build helper, outside the mathematical import graph.

Use Lake's native build jobs in one workspace and one build store, waiting for
each requested target before requesting the next. This preserves Lake's normal
dependency checks, compiler invocations, artifacts, and trace files.
-/

open Lake

def main (args : List String) : IO Unit := do
  let args ← match args with
    | ["--targets-file", path] => do
        let contents ← IO.FS.readFile path
        pure ((contents.splitOn "\n").map (fun s => s.trimAscii.toString) |>.filter (· != ""))
    | _ => pure args
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | throw <| IO.userError "Cannot find the Lean installation."
  let some lake := lake? | throw <| IO.userError "Cannot find the Lake installation."
  let lakeEnv ← (Env.compute lake lean elan? (some true)).toIO IO.userError
  let some ws ← (loadWorkspace {
      lakeEnv
      wsDir := ← IO.currentDir
    }).toBaseIO
    | throw <| IO.userError "Cannot load the Lake workspace."
  let specs ← (parseTargetSpecs ws args).toIO (fun e => IO.userError (toString e))
  ws.runFetchM (cfg := {failFast := true, showSuccess := true}) do
    let mut index := 0
    for spec in specs do
      index := index + 1
      IO.println s!"[{index}/{specs.size}] Lake build {spec.info.key.toSimpleString}"
      (← IO.getStdout).flush
      discard <| (← spec.fetch).await

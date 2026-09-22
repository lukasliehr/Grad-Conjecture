import Lake
import Lake.Load.Workspace

/-! Check Lake's actual module-to-source resolution without building proofs. -/
open Lake System

def main : IO Unit := do
  let root ← IO.currentDir
  let leanInstall ← LeanInstall.get (← Lean.findSysroot)
  let lakeEnv ← (Env.compute (LakeInstall.ofLean leanInstall) leanInstall none).toIO IO.userError
  let some workspace ← (loadWorkspaceRoot { lakeEnv, wsDir := root }).toBaseIO
    | throw <| IO.userError "Could not load the repository's Lake configuration"
  let lines := (← IO.FS.readFile (root / "LeanCode/MODULES.tsv")).splitOn "\n"
  let mut checked := 0
  for line in lines.drop 1 do
    if line.isEmpty then continue
    let fields := line.splitOn "\t"
    let name := fields[0]!.toName
    let expected := root / fields[1]!
    let some mod := workspace.findModule? name
      | throw <| IO.userError s!"Lake cannot resolve {name}"
    unless (← IO.FS.realPath mod.leanFile) == (← IO.FS.realPath expected) do
      throw <| IO.userError s!"Wrong source path for {name}: {mod.leanFile}"
    checked := checked + 1
  unless checked == 5839 do
    throw <| IO.userError s!"Unexpected source count: {checked}"
  for name in ["Showcase", "Showcase_WithProofs", "LeanCode", "Showcase_DefinitionCheck"] do
    unless (workspace.findModule? name.toName).isSome do
      throw <| IO.userError s!"Missing public target: {name}"
  IO.println s!"LAKE_MODULE_RESOLUTION_CHECKED {checked}"

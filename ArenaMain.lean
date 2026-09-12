import CanonicalMin.Arena
import Export.Parse
import Lean.Environment

open Lean Meta

private def usage : String :=
  "usage: canonical-min-arena <export.ndjson>"

private inductive Result where
  | accepted
  | rejected
  | declined (reason : String)

private def addUnchecked (env : Environment) (info : ConstantInfo) : Except String Environment := do
  let declaration : Declaration ← match info with
    | .axiomInfo val => pure (.axiomDecl val)
    | .defnInfo val => pure (.defnDecl val)
    | .thmInfo val => pure (.thmDecl val)
    | .opaqueInfo val => pure (.opaqueDecl val)
    | _ => throw s!"unsupported declaration kind for {info.name}"
  match env.addDeclCore 0 declaration none false with
  | .ok env => pure env
  | .error _ => throw s!"could not add {info.name}"

private def runMeta (env : Environment) (action : MetaM α) : IO α :=
  (MetaM.run' action).toIO'
    { fileName := "<canonical-min-arena>", fileMap := FileMap.ofString "" }
    { env }

private def checkEnvironment (exported : Export.ExportedEnv)
    (initialEnv : Environment) : IO Result := do
  let mut env := initialEnv
  for name in exported.constOrder do
    let some info := exported.constMap[name]?
      | return .rejected
    if env.contains name then
      continue
    if info.isUnsafe || info.isPartial then
      return .declined s!"unsupported declaration {name}"
    match info with
    | .axiomInfo _ =>
      match addUnchecked env info with
      | .ok next => env := next
      | .error reason => return .declined reason
    | .defnInfo val | .thmInfo val | .opaqueInfo val =>
      let accepted ← try
        runMeta env (CanonicalMin.Arena.checkExpr val.value val.type)
      catch error =>
        return .declined s!"could not translate {name}: {error}"
      unless accepted do
        return .rejected
      match addUnchecked env info with
      | .ok next => env := next
      | .error reason => return .declined reason
    | _ => return .declined s!"unsupported declaration kind for {name}"
  return .accepted

private def parseExport (inputPath : String) : IO (Except String Export.ExportedEnv) :=
  try
    let handle ← IO.FS.Handle.mk inputPath .read
    return .ok (← Export.parseStream (.ofHandle handle))
  catch error =>
    return .error (toString error)

private def runArena (inputPath : String) : IO UInt32 := do
  match ← parseExport inputPath with
  | .error error =>
    IO.eprintln s!"Invalid export: {error}"
    return 1
  | .ok exported =>
    Lean.initSearchPath (← Lean.findSysroot)
    let initialEnv ← Lean.importModules #[{ module := `Canonical.TranslationUtil }] {}
    match ← checkEnvironment exported initialEnv with
    | .accepted =>
      IO.println s!"Accepted {exported.constOrder.size} declarations."
      return 0
    | .rejected =>
      IO.eprintln "Rejected."
      return 1
    | .declined reason =>
      IO.eprintln s!"Declined: {reason}"
      return 2

def main (args : List String) : IO UInt32 :=
  match args with
  | [inputPath] => runArena inputPath
  | _ => do
    IO.eprintln usage
    return 3

/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Lean

/-!
# Export the record of the build

Run this file after `lake build`:

```
lake env lean --run scripts/Export.lean <commit> <mathlib commit> <date> [module] > lean.json
```

It imports the module, `Singularity` by default, and writes one JSON object for each declaration in the namespace `Singularity`: its kind, its file, its line, its type and the axioms that it uses. The toolchain `sing index` of singularity-agent reads this record. A declaration that uses `sorryAx` gets the status `stated` and never `proved`.
-/

open Lean Meta

def kindOf : ConstantInfo → Option String
  | .defnInfo _ => some "def"
  | .thmInfo _ => some "theorem"
  | .opaqueInfo _ => some "opaque"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => some "inductive"
  | _ => none

def keep (env : Environment) (n : Name) : Bool :=
  (`Singularity).isPrefixOf n && !n.isInternalDetail && !isAuxRecursor env n && !isNoConfusion env n

def fileOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    let path := (m.toString.replace "." "/") ++ ".lean"
    if (`SingularityBase).isPrefixOf m then "base/" ++ path else path
  | none => ""

def entry (env : Environment) (n : Name) (info : ConstantInfo) (kind : String) : CoreM Json := do
  let axioms ← collectAxioms n
  let line := match ← findDeclarationRanges? n with
    | some r => r.range.pos.line
    | none => 0
  let ty ← MetaM.run' (do return toString (← ppExpr info.type))
  return Json.mkObj [
    ("kind", kind),
    ("file", fileOf env n),
    ("line", line),
    ("axioms", toJson (axioms.map Name.toString |>.qsort (· < ·))),
    ("type", ty)]

unsafe def main (args : List String) : IO UInt32 := do
  let (commit, mathlib, date, root) ← match args with
    | [c, m, d] => pure (c, m, d, `Singularity)
    | [c, m, d, r] => pure (c, m, d, r.toName)
    | _ => do
      IO.eprintln "usage: lean --run scripts/Export.lean <commit> <mathlib commit> <date> [module]"
      return 2
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  let names := env.constants.fold (init := #[]) fun acc n info =>
    if keep env n then
      match kindOf info with
      | some k => acc.push (n, info, k)
      | none => acc
    else acc
  let names := names.qsort (fun a b => a.1.toString < b.1.toString)
  let ctx : Core.Context := { fileName := "<export>", fileMap := default, maxHeartbeats := 0 }
  let (decls, _) ← (names.mapM fun (n, info, k) => do return (n.toString, ← entry env n info k)).toIO ctx { env }
  let out := Json.mkObj [
    ("repository", "https://github.com/tamnd/singularity-lean"),
    ("commit", commit),
    ("toolchain", Lean.versionString),
    ("mathlib", mathlib),
    ("built", date),
    ("decls", Json.mkObj decls.toList)]
  IO.println out.pretty
  return 0

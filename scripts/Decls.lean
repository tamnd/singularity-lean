/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Lean

/-!
# The declarations of a package

Run this file after `lake build`:

```
lake env lean --run scripts/Decls.lean [module] > decls.txt
```

It imports the module, `Singularity` by default, and writes the name of each declaration of the modules whose name starts with that module, one name on each line. Internal names are left out. The trust workflow gives the list to `leanexport`, which exports these declarations and all the declarations that they use, so that nanoda can check the export.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let root := (args.headD "Singularity").toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root }] {}
  let mods := env.header.moduleNames
  let names := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if root.isPrefixOf mods[idx.toNat]! && !n.isInternal then acc.push n.toString else acc
    | none => acc
  for n in names.qsort (· < ·) do
    IO.println n
  IO.eprintln s!"{names.size} declarations in the modules of {root}"
  return 0

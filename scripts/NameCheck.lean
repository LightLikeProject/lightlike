import Lightlike

/-!
# Name check for the API maps and the results registry

Every declaration named in an API map (`Lightlike/<Area>/API-map.md`) or in the results
registry (`docs/results.yaml`) must exist and be declared in the module of the file it is cited
with. The names are listed in `.lake/api_names.tsv`, written by `python3 scripts/api_map.py names`.
A name resolves as `Lightlike.<name>` or, failing that, as written.

Run from the repository root, after `python3 scripts/api_map.py names`:
`lake env lean scripts/NameCheck.lean`.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let src ← IO.FS.readFile ".lake/api_names.tsv"
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut n : Nat := 0
  for line in src.splitOn "\n" do
    match line.splitOn "\t" with
    | [_, file, decl] =>
      n := n + 1
      let modName := ((file.replace ".lean" "").replace "/" ".").toName
      let raw := decl.toName
      match [`Lightlike ++ raw, raw].find? env.contains with
      | none => bad := bad.push s!"{decl} ({file}): no such declaration"
      | some c =>
        match ← liftCoreM (findModuleOf? c) with
        | some m =>
          if m != modName then
            bad := bad.push s!"{decl}: declared in {m}, cited with {file}"
        | none => bad := bad.push s!"{decl}: declared in this file, not in {file}"
    | _ => pure ()
  if bad.isEmpty then
    logInfo m!"names: all {n} API-map and registry names resolve in their cited files"
  else
    logError m!"{bad.size} of {n} names do not resolve:\n{"\n".intercalate bad.toList}"

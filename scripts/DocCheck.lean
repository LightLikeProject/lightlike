import Lightlike

/-!
# Docstring coverage check

Fails (with an error) if a definition in `Lightlike` has no docstring (Batteries' `docBlame`
linter), or if a declaration named in an API map or in the results registry has none. Those
names are listed in `.lake/api_names.tsv`, written by `python3 scripts/api_map.py names`.

Run from the repository root, after `python3 scripts/api_map.py names`:
`lake env lean scripts/DocCheck.lean`.
-/

#lint- only docBlame in Lightlike

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let src ← IO.FS.readFile ".lake/api_names.tsv"
  let mut names : List Name := []
  for line in src.splitOn "\n" do
    if let [_, _, decl] := line.splitOn "\t" then
      let raw := decl.toName
      names := names ++ [if (← getEnv).contains (`Lightlike ++ raw) then `Lightlike ++ raw else raw]
  let env ← getEnv
  let missing ← names.filterM fun n => return (← findDocString? env n).isNone
  if missing.isEmpty then
    logInfo m!"docstrings: all {names.length} declarations named in the API maps and the \
      registry are documented"
  else
    logError m!"declarations named in the API maps or the registry without docstrings: {missing}"

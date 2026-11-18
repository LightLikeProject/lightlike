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
  -- each name with where it came from, so that an error names the file and the text to fix
  let mut names : List (Name × String) := []
  let mut skipped : List String := []
  for line in src.splitOn "\n" do
    if let [kind, file, decl] := line.splitOn "\t" then
      let raw := decl.toName
      let where_ := s!"{file} ({kind}): `{decl}`"
      -- a backticked path or phrase is not a declaration name: say so, do not fail on `[anonymous]`
      if raw.isAnonymous || (decl.splitOn "/").length > 1 || (decl.splitOn " ").length > 1
          || decl.endsWith ".lean" || decl.endsWith ".md" then
        skipped := skipped ++ [where_]
      else
        names := names ++ [(if (← getEnv).contains (`Lightlike ++ raw) then `Lightlike ++ raw else raw, where_)]
  unless skipped.isEmpty do
    logWarning m!"skipped, not a declaration name (a path or a phrase in backticks):\n{"\n".intercalate skipped}"
  let env ← getEnv
  let missing ← names.filterM fun p => return (← findDocString? env p.1).isNone
  if missing.isEmpty then
    logInfo m!"docstrings: all {names.length} declarations named in the API maps and the \
      registry are documented"
  else
    logError m!"declarations named in the API maps or the registry without docstrings:\n{"\n".intercalate (missing.map (·.2))}"

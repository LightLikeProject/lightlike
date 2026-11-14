import Lightlike

/-!
# Axiom audit

Fails (with an error) if a declaration of the library depends on an axiom other than Lean's
standard axioms `propext`, `Classical.choice` and `Quot.sound`. Every constant declared in a
`Lightlike` module is checked, so there is no list of theorems to keep up to date. A `sorry`
shows up here as the axiom `sorryAx`.

On a failure the audit names the declarations of the library that depend on the offending
axioms.

Run from the repository root, after `lake build`: `lake env lean scripts/AxiomAudit.lean`.
-/

open Lean Elab Command

namespace AxiomAudit

/-- The constants that a declaration refers to: those in its type and its value or proof, and
the constructors of an inductive type. -/
def deps : ConstantInfo → Array Name
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | ci => ci.type.getUsedConstants

/-- Lean's standard axioms. -/
def standard : NameSet :=
  NameSet.empty |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

/-- Every constant reachable from `roots`, and the axioms among them. -/
def reach (env : Environment) (roots : Array Name) : NameSet × NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut axs : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | some (.axiomInfo _) => axs := axs.insert c
    | some ci => stack := stack ++ deps ci
    | none => pure ()
  return (seen, axs)

/-- The constants among `seen` that depend on one of `bad`, by a search backwards along the
dependencies. -/
def tainted (env : Environment) (seen : NameSet) (bad : Array Name) : NameSet := Id.run do
  let mut users : Std.HashMap Name (Array Name) := {}
  for c in seen do
    if let some ci := env.find? c then
      for d in deps ci do
        users := users.insert d ((users.getD d #[]).push c)
  let mut out : NameSet := {}
  let mut stack := bad
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if out.contains c then continue
    out := out.insert c
    stack := stack ++ users.getD c #[]
  return out

end AxiomAudit

open AxiomAudit in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut roots : Array Name := #[]
  let mut mods : NameSet := {}
  for (c, _) in env.constants.map₁ do
    if let some m ← liftCoreM (findModuleOf? c) then
      if (`Lightlike).isPrefixOf m then
        roots := roots.push c
        mods := mods.insert m
  let (seen, axs) := reach env roots
  let bad := axs.toArray.filter (!standard.contains ·)
  if bad.isEmpty then
    logInfo m!"axioms: all {roots.size} declarations of {mods.size} modules use only \
      {axs.toArray.qsort Name.lt}"
  else
    let hit := tainted env seen bad
    let names := (roots.filter hit.contains).qsort Name.lt
    logError m!"axioms: {names.size} of {roots.size} declarations use non-standard axioms \
      {bad.qsort Name.lt}:\n{"\n".intercalate (names.toList.take 100 |>.map toString)}"

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

/-- For each constant, the constants among `seen` that refer to it (`reach` read backwards; like
`reach`, an axiom's own type is not followed). -/
def usersOf (env : Environment) (seen : NameSet) : Std.HashMap Name (Array Name) := Id.run do
  let mut users : Std.HashMap Name (Array Name) := {}
  for c in seen do
    match env.find? c with
    | some (.axiomInfo _) => pure ()
    | some ci =>
      for d in deps ci do
        users := users.insert d ((users.getD d #[]).push c)
    | none => pure ()
  return users

/-- The constants that depend on one of `bad`, by a search backwards along `users`. -/
def backwards (users : Std.HashMap Name (Array Name)) (bad : Array Name) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut stack := bad
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if out.contains c then continue
    out := out.insert c
    stack := stack ++ users.getD c #[]
  return out

/-- The constants among `seen` that depend on one of `bad`. -/
def tainted (env : Environment) (seen : NameSet) (bad : Array Name) : NameSet :=
  backwards (usersOf env seen) bad

/-- The axioms each of `qs` depends on, with one search for all of them: forwards from `qs` to
every constant and axiom they reach, then backwards from each axiom. -/
def axiomsOf (env : Environment) (qs : Array Name) : Std.HashMap Name (Array Name) := Id.run do
  let (seen, axs) := reach env qs
  let users := usersOf env seen
  let mut out : Std.HashMap Name (Array Name) := {}
  for a in axs.toArray.qsort Name.lt do
    let hit := backwards users #[a]
    for q in qs do
      if hit.contains q then out := out.insert q ((out.getD q #[]).push a)
  return out

/-- `t` without its leading `∀` binders. -/
partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | .mdata _ e => stripForall e
  | e => e

/-- Whether constant `c` is a proposition of the library: in the `Lightlike` namespace, and its
type ends in `Prop`. -/
def libraryProp (env : Environment) (c : Name) : Bool :=
  (`Lightlike).isPrefixOf c && match env.find? c with
    | some ci => match stripForall ci.type with
      | .sort u => u == .zero
      | _ => false
    | none => false

/-- The propositions of the library that a declaration of type `t` takes as hypotheses: the head
constant of each binder whose type (after its own `∀`s) is a `libraryProp`; instance arguments are
left out. Used by `scripts/consistency_check.py`: a result the catalogue calls proven must not
take a proposition that the catalogue lists as an open hypothesis. -/
partial def propHyps (env : Environment) : Expr → Array Name
  | .forallE _ ty body bi =>
    let rest := propHyps env body
    if bi.isInstImplicit then rest else
    match (stripForall ty).getAppFn with
    | .const c _ => if libraryProp env c && !rest.contains c then rest.push c else rest
    | _ => rest
  | .mdata _ e => propHyps env e
  | _ => #[]

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

/-! ## Per-declaration mode

Used by `scripts/milestone_status.py`. When `LL_DECLS` names a file with one declaration name per
line, the audit writes one JSON line per name to the file named by `LL_DECLS_OUT`: whether the
declaration exists, its module, and the axioms it depends on, with the same search as above (a
`sorry` shows up as `sorryAx`), and the propositions of the library it takes as hypotheses
(`propHyps`). For a name that does not exist, the line lists as candidates the
library's declarations with the same last component. Without `LL_DECLS` this part does nothing. -/

open AxiomAudit in
#eval show CommandElabM Unit from do
  let some inp ← (IO.getEnv "LL_DECLS" : IO (Option String)) | return
  let out := (← (IO.getEnv "LL_DECLS_OUT" : IO (Option String))).getD "decls-status.jsonl"
  let env ← getEnv
  let qs := ((← (IO.FS.readFile inp : IO String)).splitOn "\n").map
    (fun s => (s.replace " " "").replace "\r" "") |>.filter (· ≠ "")
  let last (s : String) : String := (s.splitOn ".").getLast?.getD s
  let missing := qs.filter (fun q => (env.find? q.toName).isNone) |>.map last
  -- The library's declarations whose last component is that of a missing name.
  let mut cands : Std.HashMap String (Array String) := {}
  if !missing.isEmpty then
    for (c, _) in env.constants.map₁ do
      if let .str _ s := c then
        if missing.contains s then
          if let some m ← liftCoreM (findModuleOf? c) then
            if (`Lightlike).isPrefixOf m then
              cands := cands.insert s ((cands.getD s #[]).push c.toString)
  let ax := axiomsOf env ((qs.map String.toName).filter (env.find? · |>.isSome)).toArray
  let mut lines : Array String := #[]
  for q in qs do
    let n := q.toName
    match env.find? n with
    | some ci =>
      let m ← liftCoreM (findModuleOf? n)
      let axs := (ax.getD n #[]).map (Json.str ·.toString)
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | _ => "other"
      lines := lines.push (Json.mkObj [("q", q), ("found", true), ("name", n.toString),
        ("module", (m.map Name.toString).getD ""), ("kind", kind), ("axioms", Json.arr axs),
        ("hyps", Json.arr ((propHyps env ci.type).qsort Name.lt |>.map (Json.str ·.toString)))]).compress
    | none =>
      let cs := ((cands.getD (last q) #[]).qsort (· < ·)).map Json.str
      lines := lines.push (Json.mkObj [("q", q), ("found", false), ("candidates", Json.arr cs)]).compress
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  logInfo m!"decls: {qs.length} names, {qs.length - missing.length} found, written to {out}"

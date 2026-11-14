import Lightlike
import Tasks

/-!
# Context pack (data extraction)

Writes, as JSON, everything a reader needs to work on one declaration without the repository:
its source, the source of every project-local definition and lemma its statement depends on
(transitively, nearest first; each marked `statement` when the statement itself names it), and
the statements of project lemmas about the same definitions.

Do not run this file directly; use `scripts/context-pack <declaration>`, which writes the input
file, runs `lake env lean scripts/ContextPack.lean`, applies the size limit and prints one
paste-able block.

A definition contributes the constants of its type and its body; a theorem only those of its
statement, since its proof is not needed to use it. "Project-local" means declared in a module
under `Lightlike` or `Tasks`.
-/

open Lean Elab Command Meta

namespace ContextPack

/-- Module roots whose declarations are project-local. -/
def localRoots : List Name := [`Lightlike, `Tasks]

/-- The module that declares `n`, if any. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.allImportedModuleNames[i]!

/-- Whether `n` is declared in a project-local module. -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => localRoots.contains m.getRoot
  | none => false

/-- The nearest declaration with a source range that `n` belongs to: `n` itself, or the first
prefix of `n` with one (so `Foo.mk`, `Foo.rec` and `Foo.match_1` map to `Foo`). -/
partial def sourceDecl (n : Name) : CommandElabM (Option (Name × DeclarationRange)) := do
  if n.isAnonymous then return none
  if let some r ← liftCoreM (findDeclarationRanges? n) then return some (n, r.range)
  sourceDecl n.getPrefix

/-- The file of a module, relative to the repository root. -/
def moduleFile (m : Name) : System.FilePath :=
  System.FilePath.mk (m.toString.replace "." "/") |>.addExtension "lean"

/-- The source lines of a declaration range. -/
def sourceOf (file : System.FilePath) (r : DeclarationRange) : IO String := do
  let lines := (← IO.FS.readFile file).splitOn "\n"
  let sel := (lines.drop (r.pos.line - 1)).take (r.endPos.line - r.pos.line + 1)
  return "\n".intercalate sel

/-- The constants a declaration's use depends on: its type, plus its body for a definition, plus
the constructor types for an inductive type. -/
def usedConstants (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => out := out ++ d.value.getUsedConstants
  | .opaqueInfo d => out := out ++ d.value.getUsedConstants
  | .inductInfo d =>
    for c in d.ctors do
      if let some cc := env.find? c then out := out ++ cc.type.getUsedConstants
  | _ => pure ()
  return out

/-- The kind of a constant, as shown in the pack. -/
def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .axiomInfo _ => "axiom"
  | _ => "other"

/-- Whether a name is an implementation detail rather than a user-facing lemma. -/
def isAux (n : Name) : Bool :=
  n.isInternal || match n with
    | .str _ s => s.startsWith "eq_" || s.startsWith "proof_" || s.startsWith "match_" ||
        s == "eq_def" || s == "eq_unfold" || s.endsWith "_def"
    | _ => true

/-- Whether a module's lemmas are worth suggesting: not tests or open tasks. -/
def suggestable (m : Name) : Bool :=
  !(`Lightlike.Tests).isPrefixOf m && !(`Tasks).isPrefixOf m

/-- The project lemmas that may be suggested, with the constants of their statements. -/
def candidateLemmas (env : Environment) : Array (Name × Array Name) :=
  env.constants.fold (init := #[]) fun acc n ci =>
    match ci, moduleOf? env n with
    | .thmInfo _, some m =>
      if localRoots.contains m.getRoot && suggestable m && !isAux n then
        acc.push (n, ci.type.getUsedConstants)
      else acc
    | _, _ => acc

/-- A lemma's entry: name, signature and location. -/
def lemmaJson (env : Environment) (n : Name) : CommandElabM Json := do
  let sig ← liftTermElabM do
    return (← PrettyPrinter.ppSignature n).fmt.pretty 100
  let file := match moduleOf? env n with
    | some m => (moduleFile m).toString
    | none => ""
  let line := match ← sourceDecl n with
    | some (_, r) => r.pos.line
    | none => 0
  return Json.mkObj [("name", toJson n.toString), ("signature", toJson sig),
    ("file", toJson file), ("line", toJson line)]

/-- The pack for `root`. The names in `use` (statements the task may rely on, such as other
locked task statements) are listed first among the lemmas and their dependencies are included. -/
def pack (cands : Array (Name × Array Name)) (root : Name) (use : List Name)
    (maxLemmas : Nat) : CommandElabM Json := do
  let env ← getEnv
  let some rootCi := env.find? root | throwError "context-pack: unknown declaration {root}"
  let some (_, rootRange) ← sourceDecl root | throwError "context-pack: no source for {root}"
  let some rootMod := moduleOf? env root | throwError "context-pack: {root} has no module"
  let rootFile := moduleFile rootMod
  let mut start : Array Name := rootCi.type.getUsedConstants
  for u in use do
    let some ci := env.find? u | throwError "context-pack: unknown declaration {u}"
    start := start ++ ci.type.getUsedConstants
  let mut direct : NameSet := {}
  for c in start do
    if let some (s, _) ← sourceDecl c then
      if isLocal env s then direct := direct.insert s
  -- The declarations that the statement itself names.
  let mut named : NameSet := {}
  for c in rootCi.type.getUsedConstants do
    if let some (s, _) ← sourceDecl c then
      if isLocal env s then named := named.insert s
  -- Breadth-first over the dependencies, so the nearest come first.
  let mut seen : NameSet := use.foldl NameSet.insert (({} : NameSet).insert root)
  let mut queue := start
  let mut deps : Array Json := #[]
  let mut i := 0
  while i < queue.size do
    let c := queue[i]!
    i := i + 1
    let some (s, r) ← sourceDecl c | continue
    if seen.contains s || !isLocal env s then continue
    seen := seen.insert s
    let some ci := env.find? s | continue
    let some m := moduleOf? env s | continue
    let f := moduleFile m
    deps := deps.push <| Json.mkObj [("name", toJson s.toString), ("kind", toJson (kindOf ci)),
      ("file", toJson f.toString), ("line", toJson r.pos.line),
      ("source", toJson (← sourceOf f r)), ("statement", toJson (named.contains s))]
    queue := queue ++ usedConstants env ci
  -- Lemmas whose statements mention the most direct dependencies, shortest names first.
  let scored := cands.filterMap fun (n, cs) =>
    let k := (cs.filter direct.contains).size
    if n == root || use.contains n || k == 0 then none else some (k, n)
  let ranked := scored.qsort fun a b =>
    a.1 > b.1 || (a.1 == b.1 && a.2.toString.length < b.2.toString.length)
  let mut lemmas : Array Json := #[]
  for n in use do
    lemmas := lemmas.push (← lemmaJson env n)
  for (_, n) in ranked.toList.take maxLemmas do
    lemmas := lemmas.push (← lemmaJson env n)
  return Json.mkObj [("decl", toJson root.toString), ("kind", toJson (kindOf rootCi)),
    ("file", toJson rootFile.toString), ("line", toJson rootRange.pos.line),
    ("source", toJson (← sourceOf rootFile rootRange)),
    ("use", toJson (use.map Name.toString)), ("deps", Json.arr deps), ("lemmas", Json.arr lemmas)]

end ContextPack

/-! Input: `CONTEXT_PACK_IN`, one line per pack, `<declaration> [<name it may use> ...]`.
Output: a JSON array of packs in `CONTEXT_PACK_OUT`. One run serves many task cards, since loading
the library dominates the time. -/
#eval show CommandElabM Unit from do
  let some inp ← IO.getEnv "CONTEXT_PACK_IN"
    | throwError "set CONTEXT_PACK_IN (use scripts/context-pack)"
  let some out ← IO.getEnv "CONTEXT_PACK_OUT"
    | throwError "set CONTEXT_PACK_OUT (use scripts/context-pack)"
  let maxLemmas := ((← IO.getEnv "CONTEXT_PACK_LEMMAS").bind String.toNat?).getD 25
  let cands := ContextPack.candidateLemmas (← getEnv)
  let mut packs : Array Json := #[]
  for line in (← IO.FS.readFile inp).splitOn "\n" do
    match (line.splitOn " ").filter (· ≠ "") with
    | [] => pure ()
    | d :: use => packs := packs.push (← ContextPack.pack cands d.toName (use.map String.toName) maxLemmas)
  IO.FS.writeFile out (Json.arr packs).pretty

# Lightlike: instructions for AI coding agents

This file is for every coding agent that works on this repository, whatever tool runs it, the
maintainers' agents included: they follow the same CI, review and merge rules as everyone else.
[CONTRIBUTING.md](CONTRIBUTING.md) applies to agents as to people; this file adds what an agent
needs to work well here.

Lightlike is a Lean 4 library of formalized results and open problems in fundamental physics. The
code is in `Lightlike/`; what is proven is listed in [docs/RESULTS.md](docs/RESULTS.md), the plan
in [ROADMAP.md](ROADMAP.md) and the tasks on the [task board](docs/tasks/README.md).

## Requirements

Only the CI steps marked `[hard rule]` are required ([CONTRIBUTING.md](CONTRIBUTING.md#hard-rules)):

- `lake build` passes, and `Lightlike.lean` imports every Lean file of `Lightlike/`.
- No `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by` or `extern` in `Lightlike/`.
- Every declaration depends only on Lean's standard axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- Finite compile limits: a heavy proof gets `set_option maxHeartbeats N in` for that declaration
  only, with `N` measured (about twice the need), never `maxHeartbeats 0`.
- Nothing outside an `Exploratory/` folder imports a module inside one.
- Every definition, and every declaration the catalog names, has a docstring.

A proof-task pull request changes only the proof of its declaration: the statement is locked.
Everything below is recommended practice, with the reason for it.

## Pull requests

- **One task per pull request**, with the template's line `Task: <ID>` (or `Task: none`), and
  `Closes #<issue>` when it finishes that task's issue.
- **AI assistance.** Fill in the template's field: the tool and the model.
- **Claims.** Comment `claiming` on a definition, statement or upstream task before starting it,
  so that two competing definitions of one notion do not appear, and `stopping` to release it.
  Proof tasks are non-exclusive: comment `attempting`; the first proof that passes CI is merged.
- **Branches.** Work on a branch, in a fork or, with write access, in this repository. To bring a
  pushed branch up to date, merge `main` into it (`git fetch origin` and `git merge origin/main`).
  Never force-push or rewrite pushed history.
- **Merging.** A maintainer squash-merges a pull request once every CI check is green. `main` gets
  one commit: the title with the pull request's number, and the description as its body. Write
  both for the history.

## Commits

- Messages read `type(scope): summary`, for example `feat(regge): define deficit angles`,
  `fix(curvature): …`, `docs(readme): …`, `test(sixj): …` or `ci: …`, with a body that says why.
- The author is the person, or the account, directing the agent. The trailer
  `Co-Authored-By: <agent and model name>` names the agent, without an e-mail address.

## Recommended practice

- **Weaken statements openly, never silently.** If a goal is too hard, say exactly what is
  missing and propose a smaller version; an open identity becomes an explicit hypothesis (as with
  `BiedenharnElliott`), not a hidden `sorry`. A quietly weakened statement is a wrong result that
  type-checks.
- **Document every `sorry` while exploring:** a comment saying what it stands for and how hard it
  looks. None may reach `Lightlike/`.
- **Trust checks.** Prove that a new definition gives known values on non-trivial cases, and that
  a deliberately wrong model or input gives a different answer. This catches a definition that
  type-checks but means something else.
- **Non-vacuity.** Give a concrete example that satisfies the hypotheses of each main theorem.
- **Junk values.** Check that no statement holds only because of a Lean junk value
  ([docs/CONVENTIONS.md](docs/CONVENTIONS.md#leans-junk-values)).
- **No axioms.** A physical postulate enters as the definition of a model, and a theorem says
  what follows from it ([Lightlike/Assumptions.lean](Lightlike/Assumptions.lean)). `native_decide`
  adds the axiom `Lean.ofReduceBool`; `decide +kernel` does not.
- **Reuse Mathlib and Physlib** where they fit, and explain any custom definition. Before
  building a new component, check Physlib's main branch (Physlib, PhyslibAlpha, QuantumInfo) and
  its open pull requests.
- **Numerics.** Cross-check independently with SymPy (`scripts/`, each check with a wrong-input
  control) and label the results as numerical evidence, not proof.
- **Write for outside readers.** Commit bodies, docstrings and pull requests should make sense to
  someone who has not seen the session that produced them. Session state, agent notes, local paths
  and e-mail addresses stay out of tracked files.
- **Push when there are no loose ends:** the build and the local checks pass, finished results
  have trust checks and a non-vacuity example, docstrings exist, and every limitation is fixed or
  reported. A gap that cannot be closed yet is reported, never hidden.

## Review

- A statement or definition is compared with its cited source for conventions, quantifier
  ranges, hypotheses, junk values and non-vacuity ([README.md](README.md#review)). An agent asked
  to review works in a fresh context, preferably as a different model, never on its own work, and
  posts its findings on the result's issue.
- A change of scope or of the tier definitions is proposed in an issue first.
- A surprising result in an `Exploratory/` folder is flagged on an issue; work continues meanwhile.

## Build and verify

```bash
lake exe cache get
lake build
lake build Tasks.DT.T_DT4_P1
lake env lean -DautoImplicit=false Lightlike/Tests/SixJ.lean
python3 scripts/gate.py
```

- `lake exe cache get` downloads the compiled Mathlib; `lake build Tasks.<Area>.<File>` builds a
  single proof task. `lake env lean` checks a single file but does not read the options in
  `lakefile.toml`, hence `-DautoImplicit=false`.
- `scripts/gate.py` runs the steps of `.github/workflows/ci.yml` in order. It needs Python 3.9 to
  3.12 and the packages pinned in `requirements.txt`. Commit before running it.
- `scripts/context-pack <declaration>` prints everything one declaration depends on in one block.
- CI runs on every pull request. One that changes no Lean or build file gets only the text checks.
- Lean and Mathlib `v4.35.0`. Physlib is pinned to one commit in `lakefile.toml`; its 6j symbols
  are in the lightly reviewed Alpha tier, with no maintenance promise.
- SymPy checks: `python3 -m venv .venv && .venv/bin/pip install -r requirements.txt`, then for
  example `.venv/bin/python -I scripts/be_check.py`. `scripts/sixj_support.py j1,…,j6` lists the
  admissible projection tuples for a 6j value proof. [scripts/README.md](scripts/README.md) lists
  the rest.
- **Never `lake clean` casually.** It wipes the dependency builds too, and Mathlib and Physlib then
  compile from source for hours. To rebuild only this library, delete `.lake/build`.

## Layout

| Path | Content |
|---|---|
| `Lightlike/<Area>/` | The library, one folder per area; each `API-map.md` lists its contents and what is missing |
| `Lightlike/Tests/` | Checks of definitions against known values, wrong-model tests |
| `Tasks/` | One file per proof task, with the locked statement and `sorry` |
| `ROADMAP.md` | Milestones with definitions of done and status |
| `docs/` | The catalog of results, the conventions and the task board |
| `scripts/` | CI checks, SymPy cross-checks, task and catalog tools |
| `docbuild/` | The doc-gen4 project for the API documentation |

## Conventions

The full list is [docs/CONVENTIONS.md](docs/CONVENTIONS.md). The ones met most often:

- **Spacetime:** signature (−,+,+,+), index 0 is time, coordinates `Fin n → ℝ`. Physlib uses
  (+,−,−,−) with `Fin 1 ⊕ Fin d`.
- **6j symbols:** Physlib's `sixJSym` takes **doubled** spins (`2j ∈ ℕ`) in the standard
  arrangement, with triads (j₁j₂j₃)(j₁j₅j₆)(j₄j₂j₆)(j₄j₅j₃). Normalisation and phase are the
  standard Racah–Wigner ones, so Ponzano–Regge needs no rescaling. `sixJSymEdge` indexes by pairs of
  *triads*, i.e. the dual tetrahedron. Biedenharn–Elliott in doubled units has weight `x+1` and
  sign `(-1)^((S₂+x₂)/2)`.

## Lean gotchas

- **Junk values:** Lean's `(g x)⁻¹ = 0` for singular `g`, `a/0 = 0`, and `fderiv = 0` where a
  function isn't differentiable. Every curvature predicate therefore requires `IsCoordMetric`.
- **`ring` doesn't fail cleanly:** Mathlib's `ring` falls back to `ring_nf` instead of failing,
  so inside `first | … ` use `ring1`.
- **Partial applications:** `simp only [f]` does not unfold a partially applied `f`. For example
  `jcol φ y c` stays as is; only fully applied occurrences unfold.
- **Lambda forms:** `HasFDerivAt.add`/`.mul` produce Pi forms (`f + g`). Rewrite with
  `show (fun y => f y + g y) = f + g from rfl` before using `.fderiv`.
- **Kernel `decide` over 6j projection boxes:** it works up to about 3000 tuples. Bundle the four
  admissibility conditions into one `Bool` function (`adm4`); four separate `Decidable` instances
  hit instance-synthesis limits. Set `maxRecDepth` to 100000. For larger spins use
  `sixJSym_eq_triple` (three free projections) instead of the box.
- **Exact 6j values:** evaluate factorials (`Nat.factorial`) *before* splitting square roots, then
  close surd identities with `surd_finish` (`Lightlike/Tests/SixJ.lean`).
- **`set` vs `rw`:** after `set J := …`, a `rw` can reintroduce the unfolded term, and patterns
  stated with `J` then won't match. Use the explicit term instead.
- **`set x := …` then unfolding a definition** brings back the unabstracted term. Unfold first,
  then `generalize … = x`.
- **`omega` performance traps:**
  - Never leave a hypothesis containing `min x y` of variables in context when calling `omega`,
    and never let `↑m` appear for `m : Fin (min … + 1)`. `omega` reduces `min` and blows up.
    Prove such conditions as side goals, and `generalize (m : ℕ) = mv` first.
  - `% 2` parity facts make `omega` slow. Drop parities already implied by linear relations.
  - Anonymous constructors `⟨by omega, …⟩` against Physlib's `ValidA`/`ValidB` abbreviations time
    out in `whnf`. Use `unfold ValidA; refine ⟨?_, ?_, ?_⟩ <;> omega` instead.
  - `omega` treats pair projections like `(i, k, l).2.1` as opaque atoms; state lemmas with
    explicit variables instead.
  - `maxHeartbeats` is per declaration: many `omega` calls in one lemma need
    `set_option maxHeartbeats N in` with a finite `N`.
- **`rw` vs `simp only`:** `rw` fails with "motive is not type correct" when the term also occurs
  inside a `Decidable` instance or a proof. Use `simp only [show … by omega]` there.
- **Deprecated in this toolchain:** `if_pos`/`if_neg`/`dif_pos`/`dif_neg` (use
  `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`, same arguments), `push_neg` (use
  `not_forall`/`not_imp`), `ContinuousLinearMap.mul_apply` (use `mul_apply_eq_comp`).
- **`first | exact f (by tac) | …` does not backtrack on a failing `by tac`.** Write
  `(refine f ?_ ?_ <;> first | (tac₁; done) | (tac₂; done))` instead.
- **Reusable simp sets over local hypotheses:** `set_option hygiene false in macro "ev14" … ` can
  name `hAB … hDE` from the call site (`Lightlike/PonzanoRegge/Move14.lean`). Name any
  Biedenharn–Elliott hypothesis something other than `hBE` there.
- **`rw [prod_congr rfl fun e he => by …]` can time out in `isDefEq`.** State the product equality
  as a `have` with explicit types first.
- **Matrices as a Lie algebra:** `LieRing.ofAssociativeRing` is only a *local* instance. Use
  `attribute [local instance 100] LieRing.ofAssociativeRing` in a section.
- **Matrix norms:** use `attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra`.
  The topology is definitionally the product one, but goals can show two different instance
  terms; then `rw` fails where `exact`, or a closing `rfl`, succeeds. `NormOneClass` needs
  `[NeZero d]`.
- **Imports for trigonometry:** `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv`
  does not expose `π`, `Real.sin_pos_of_pos_of_lt_pi` or `Finset.sum_div`; some files use
  `import Mathlib`.
- **Finite case checks:** reduce real-valued identities to an integer table, prove the table
  equals the real function, then use kernel `decide`. Never `native_decide`: it adds an axiom.

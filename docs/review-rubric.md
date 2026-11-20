# Review rubric

For reviewers of a pull request that changes Lean statements or definitions (it has the label
`needs-review`). A proof-task pull request does not need this: its statement is locked and CI checks
that it did not change. For a statement the question is not "does it compile" but **does it say
what its source says, and nothing vacuous or false**. Two approvals from accounts other than the
author, each with a merged pull request here, let the pull request merge (the check `review-gate`).
Approve only what you have read yourself.

Work through the five points; for each, say in the review what you checked.

## 1. Source match

- Open the source the entry or docstring cites, at the cited place (`docs/tasks/sources.yaml`,
  `scripts/sources.py`). Read the statement there.
- Does the Lean statement say the same thing? Compare the conclusion, then each hypothesis. A
  weaker or special case is fine only if the docstring and the catalogue note say so.
- Names, indices and normalisations: a factor of 2, a sign, an index shift, a convention for a
  metric signature or an inner product. These are the usual silent differences
  ([docs/CONVENTIONS.md](CONVENTIONS.md)).
- If the source is not read at the cited place, the statement is not checked: say so in the review.

## 2. Hypotheses

- Is every hypothesis in the source present, and is each hypothesis in the statement in the source?
  An extra hypothesis can make the result easy or empty; a missing one can make it false.
- Do the hypotheses together hold for at least one non-trivial example (see 5)?
- Typeclass assumptions (`[T2Space M]`, `[Fintype ι]`, a charted space over a model) are hypotheses
  too: do they match the source's setting, not just what makes the proof easy?

## 3. Conventions

- Does the statement follow [docs/CONVENTIONS.md](CONVENTIONS.md)? Where the source differs from the
  library, is the difference stated in the docstring?
- Is a new definition the same object as an existing one under another name? Search `Lightlike/`,
  Mathlib and Physlib before accepting a duplicate.
- Docstrings: does each new declaration say what it is, in words a reader of the source would use?

## 4. Quantifiers and types

- Read every `∀` and `∃`: their order, their range, and whether a bound variable is used in the
  right place. `∀ ε > 0, ∃ δ > 0` is not `∃ δ > 0, ∀ ε > 0`.
- Coercions and casts between ℕ, ℤ, ℝ and ℂ; division by zero (`x / 0 = 0` in Lean); subtraction on
  ℕ; `Real.sqrt` and `Real.log` of negative numbers; `Finset` sums over an empty set. Does the
  statement still mean what it says when one of these junk values appears?
- Does a function that should be total have the right domain, or does it return a junk value outside
  it?

## 5. Edge cases and non-vacuity

- Junk values: does the statement pass only because a definition returns `0` or `⊥` at a bad point?
- Non-vacuity: is there an example that satisfies all hypotheses, and does the conclusion say
  something there? A statement about all `x` with `x < x` is true and worthless. The pull request
  should contain such an example (a test or a `example`), or say why one exists.
- Degenerate cases: dimension 0 or 1, the empty type, the trivial group, a zero metric. Is each
  either excluded by a hypothesis or handled by the statement?
- Is a hypothesis stated as an input that the source proves? That is a weaker statement; the
  docstring and the pull request must say so.

## What to write

Approve with a short comment per point (source place read; hypotheses compared; conventions; any
quantifier or junk-value concern; the non-vacuity example). Request changes when a point fails,
and say which. If you cannot read the source, comment without approving.

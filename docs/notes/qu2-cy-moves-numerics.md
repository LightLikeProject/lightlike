# QU2: the local Pachner identities of the Crane–Yetter state sum, numerically

Status: numerical evidence, not proof (QU2 m1, labelled progress; nothing ticks before `craneYetter_isMove`).

**Question.** Does the Crane–Yetter state sum of the library (`Lightlike.TV.craneYetter`, with the braided vertex
`cyVertexLoc`, the tetrahedron weight `cyTetWeight` and the normalisation `cyN`, Lightlike/TuraevViro/CraneYetter.lean)
satisfy the local identities of all three 4D Pachner moves (3-3, 2-4, 1-5; 4-2 and 5-1 are their inverses), as its
definition stands? Before this note only the 3-3 identity had been checked.

**Answer.** Yes, at `r = 3, 4, 5`, to rounding (`≤ 5.2e-15` relative): every relative order of the six vertices for
2-4 and 1-5 at all three levels and for 3-3 at `r = 3, 4`, three orders for 3-3 at `r = 5`.
The definition needs no change for the invariance theorem.

## Method

`scripts/oscillatory/cy_moves_check.py` transcribes the definitions literally (`tlDelta`, `tlTheta`, `tlTet`,
`cyVertexLoc` with its phase `qHalf^P` and sign `(-1)^s` in integer arithmetic, `cyVertexAt` with complex conjugation on
orientation `-1`, `cyTetWeight`, `cyN`), with Lean's conventions: `x / 0 = 0`, truncated natural subtraction, `[n] = 0`
exactly when `r ∣ n`. For a move `K.IsMove σ τ` on a 5-simplex `S = σ ∪ τ` (vertices `0 < … < 5`, so the vertex order of
every 4-simplex is the order induced from `S`):

* the removed 4-simplices `S ∖ {v}`, `v ∈ τ`, carry the orientation `inc S v` (the boundary orientation of `S`), the added
  ones `S ∖ {u}`, `u ∈ σ`, carry `-inc S u` (the orientation given by `IsOrientation.move`);
* the boundary colours (triangles and tetrahedra of the star not containing `σ`, which are those of the new star not
  containing `τ`) are drawn from random colourings with a nonzero weight of the removed side;
* each side is the sum over its inner colours (`{0, …, r-2}` on the triangles and tetrahedra containing `σ`, resp. `τ`)
  of `Π Δ(inner triangles) Π cyTetWeight(inner tetrahedra) Π cyVertexAt`; the boundary weights are common to both sides;
* the identity compared is `LHS = N^k RHS` with `k = 0` (3-3), `-1` (2-4: one new edge), `-4` (1-5: one new vertex and
  five new edges), the change of `n₀ - n₁` in `craneYetter`.

## Results (MEASURED)

| r | move | patterns of σ in the order of S | boundary colourings | with a nonzero side | max relative error |
|---|---|---|---|---|---|
| 3 | 3-3 | 20 (all) | 160 | 160 | 8.9e-16 |
| 3 | 2-4 | 15 (all) | 120 | 120 | 1.0e-15 |
| 3 | 1-5 | 6 (all) | 48 | 48 | 1.5e-15 |
| 4 | 3-3 | 20 (all) | 160 | 155 | 3.1e-15 |
| 4 | 2-4 | 15 (all) | 120 | 120 | 3.6e-15 |
| 4 | 1-5 | 6 (all) | 48 | 48 | 1.1e-15 |
| 5 | 3-3 | 3 | 24 | 23 | 5.2e-15 |
| 5 | 2-4 | 15 (all) | 30 | 30 | 2.2e-15 |
| 5 | 1-5 | 6 (all) | 12 | 12 | 1.4e-15 |

Where neither side is nonzero both vanish (agreement). The values are not trivial: they include `1, ±i`, `e^{±iπ/8}`
multiples and golden-ratio values (`0.618…`, `0.809…`, `1.77…`) at `r = 5`.

**Wrong-input controls** (both detected, relative error `≈ 2`): the added 4-simplices with the orientation of the removed
ones (`+inc S u`; the identity then holds only up to complex conjugation), and positive dimensions `[n + 1]` in place of
`Δ_n = (-1)^n [n + 1]` (r = 4, 3-3).

**The bridge to `qSixJ`** (step 2 of the plan, MEASURED, every admissible tetrahedron at `r = 4, 5, 6, 7`: 36, 120, 328,
784 of them, max error `4.4e-16`): `qSixJ r A D E C B F = tlTet r A B E C D F / √|θ(A,D,E) θ(B,C,E) θ(A,B,F) θ(C,D,F)|`.
The product of the four θ takes both signs, so the absolute value is needed.

## Limitations

* Floating point (double), not exact arithmetic; `r ≤ 5`; sampled boundary colourings (all vertex orders, a few
  colourings each), not exhaustive.
* The 4-simplices of a move are compared with the vertex order induced from `S`; the global theorem also needs that this
  is what `craneYetter` sees (it is: `cyVertexAt` sorts the vertices of each simplex in the order of `V`).
* Nothing here is a proof; the Lean route is in the QU2 m1 plan (bridge, braiding layer, local identities, global step).

Run: `python3 -I scripts/oscillatory/cy_moves_check.py` (quick set, about 2 s); `--full` for every pattern at
`r = 3, 4, 5` (hours at `r = 5`).

# PL7a: what PL homeomorphism gives for the Ponzano–Regge amplitude

Question: given that the `r = 3` Turaev–Viro sum is a PL invariant (`turaevViro3_plHomeomorphic`,
`Lightlike/TuraevViro/PLInvariance.lean`), which invariance up to PL homeomorphism follows for the
regularised Ponzano–Regge amplitude (`PonzanoRegge/TriangulationIndependence/`)?

Answer (MEASURED by Lean statements on main, no numbers involved): **none as an equality.** Only
a set inclusion along forward moves, and only under a hypothesis.

## The two sides of PL7a

| | Turaev–Viro, `r = 3` | Ponzano–Regge, regularised |
|---|---|---|
| value | one real number `turaevViro 3 K` | a set `ampValues K` of gauge-fixed amplitudes over all maximal trees `T` and cut-offs `cut` |
| 2-3, 1-4 | equal (`turaevViro3_move23/14`) | `ampValues K ⊆ ampValues K'` (`ampValues_mono_forward`) |
| 3-2, 4-1 | equal (`turaevViro3_move32/41`) | `ampValues (move32 K h) ⊆ ampValues K` (the smaller complex has fewer values; `ampValues_move32_subset`, `ampValues_move41_subset`) |
| relabelling | equal (`turaevViro3_mapComplex3`) | not stated |
| PL homeomorphic | **equal** (`turaevViro3_plHomeomorphic`, unconditional) | **nothing unconditional** |

## Why nothing follows for Ponzano–Regge

1. Newman plus `moveEquiv3_lift_iff_stellarEquiv` turn PL homeomorphism into a chain of moves that
   mixes 2-3, 1-4 with 3-2, 4-1 (`MoveEquiv3`). Along a 3-2 or 4-1 step the value set shrinks, along
   2-3 or 1-4 it grows, so the ends of a mixed chain are not comparable.
2. The inverse moves need cut-off inequalities on the new edges (`Values.lean`), so the one-step
   inclusions only go in the forward direction.
3. What does follow is conditional on a forward form of Pachner's theorem
   (`PachnerForwardHyp Same`, `Main.lean`): then `Same K K'` gives a common complex `K''` with
   `ampValues K ⊆ ampValues K''` and `ampValues K' ⊆ ampValues K''`
   (`triangulation_independence_of_pachner`). That is a common upper bound, not equality.
4. The regularised amplitude depends on the maximal tree when the trees are not connected by triangle
   exchanges (ring-of-three-tetrahedra counterexample, `milestones.md` QU5); for closed manifolds this
   is open.

## What PL7a therefore claims

- **Full:** the `r = 3` Turaev–Viro state sum is a PL-homeomorphism invariant of closed
  combinatorial 3-manifolds (nonempty).
- **Not claimed:** any invariance of Ponzano–Regge up to PL homeomorphism; only the conditional
  inclusion above (QU5, `Main.lean`).

## Limitations / backlog

- The `r ≥ 4` Turaev–Viro statement needs `qBiedenharnElliott` (G3-196, parked: numeric certificate for
  Watson's transformation exists, closed form not found).
- Open question raised: is the forward form `PachnerForwardHyp` true? Pachner's theorem gives a chain
  with both directions; a forward-only chain after lifting extra vertices is plausible (one can often
  postpone the inverse moves) but not proved here.
- Comparison of `turaevViro3_plHomeomorphic` with Turaev, Chapter VII, is pending (not read at the
  location).

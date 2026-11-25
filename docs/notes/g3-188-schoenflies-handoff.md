# G3-188 (PL5, Schoenflies): handoff, parked 26 Nov 2026

Row G3-188 left the v1.0 list on 22 Nov; the work is parked here, not deleted. Branches (in the oscillatory
worktrees, all light-gated): `oscillatory/g3-188-step4`, `-cyc`, `-quad`, `-goodquad`, `-spoke`, `-insert`, `-qboundary`, `-ringcells`,
`-side` (queued #681 to #738), and `oscillatory/g3-188-nested` (cca7cbb, queued #749).

## Proven (Lean, namespace `Lightlike.PL.Schoenflies`)

* The open inside `U` of a Jordan curve is uniformly locally connected (`jordan_inner_ulc`), via Janiszewski's lemma for compact
  sets with connected intersection (`joinedIn_union_compl_of_isPreconnected`) and long arcs of the curve (`exists_arc_complement`).
* Winding numbers: `jordan_index_zero_joined`, `period_inc_eq_of_close`, `mem_inside_of_close`.
* `exists_frechet_polygon` and `exists_frechet_cyc`: for every `ρ > 0` and all large `N`, a simple polygon in `U`, traversed by a periodic loop
  within `ρ` of the curve, enclosing every point of `U` at distance `≥ 2ρ` from the curve; its `N` block chains form a trimmed cycle
  (`exists_cyc_of_raw`, `CycChains.exists_polygon`, `CycChains.exists_loop`).
* Polygon surgery: chord splits and gluing (`region_split_chain`, `region_split_homeo`), rotating and reversing vertex lists, inserting an
  edge point as a vertex (`ofList_insert`), good ring cells (`GoodQuad`, `GoodQuad.split`, `quad_split_region`, `quad_split_homeo`), the
  boundary bijection and extension of a cell (`GoodQuad.extend'`), the induction over cuts (`ring_extend`), a spoke across the ring
  (`exists_spoke`), the small-square argument (`inside_subset_sqBox`, `split_side_of_big`), the strip and keyhole cells of the ring between
  nested polygons (`NestedRing`, `split1_hyps`, `split2_hyps`).

## Remaining for the full planar Schoenflies theorem

1. The nested-ring extension theorem: hypotheses `hD` of the two chord splits (from `exists_spoke`), `split_side_of_big'` for the inside
   of the inner polygon, `region_split_homeo` twice, the strip by `GoodQuad.extend'`, the keyhole by `ring_extend`.
2. The tower: polygons `P_n` from `exists_frechet_cyc` with `N_n = 2^(n+n0)` blocks for the curve and for the circle; boundary maps by
   parameter (needs the loop injective: every block chain has two points, since `T_{j-1} ∩ T_{j+1} = ∅`); the union of the extensions.
3. Uniform continuity of the limit map and its inverse from the cell diameters, then `exists_homeo_closure_of_uniform`
   (`DenseExtension.lean`) and `jordan_schoenflies`.
Estimated 800 to 1500 more lines. Full design notes: `HANDOFF.md` in the `api-g3-188` worktree (not tracked).

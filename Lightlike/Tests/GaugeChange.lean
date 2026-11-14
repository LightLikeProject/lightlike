module

public import Lightlike.PonzanoRegge.GaugeChange
public import Lightlike.Tests.PonzanoRegge

/-!
# Tests for triangle exchanges of the gauge set

* `exchange_K1`: on the single tetrahedron `0123`, the gauge sets `{01, 12}` and `{02, 12}` (one
  exchange in the triangle `012`) give the same gauge-fixed amplitude, for every cutoff.
* `isMaxTree_K1_path`: the exchange turns the star tree `{01, 02, 03}` into the tree
  `{12, 02, 03}`, which is again maximal.
* `chain_K1`: two exchanges in a row (star at `0`, then a path, then the star at `2` minus one
  edge) are a chain in the sense of `amplitudeGF_eqvGen_exchange`.
* `weight_tri_zero`: the vanishing lemma behind the exchange applies to an explicit colouring with
  spins `0, 0, ½` on the triangle `012`.

Numerical evidence that the triangle is needed (`scripts/pr_tree_check.py`, exact arithmetic):
on a solid torus, trees connected by exchanges give equal amplitudes, while other trees give
different values (cutoff ½: `-15, -31, -63, -127`).
-/

@[expose] public section

open Finset

namespace Lightlike.PR.Test

/-- **One exchange** in the triangle `012` of `K1`: `{01, 12}` and `{02, 12}` give the same
amplitude. -/
theorem exchange_K1 (cut : Finset (Fin 5) → ℕ) :
    amplitudeGF K1 (insert {0, 2} (({{0, 1}, {1, 2}} : Finset (Finset (Fin 5))).erase {0, 1})) cut =
      amplitudeGF K1 {{0, 1}, {1, 2}} cut :=
  amplitudeGF_exchange K1 (by decide) (u := 0) (v := 1) (w := 2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) cut

/-- The exchanged gauge set is `{02, 12}`. -/
theorem exchange_K1_set :
    insert {0, 2} (({{0, 1}, {1, 2}} : Finset (Finset (Fin 5))).erase {0, 1}) = {{0, 2}, {1, 2}} := by
  decide

/-- **A maximal tree stays maximal**: exchanging `01` for `12` in the star tree of `K1` (triangle
`102`, with `02` kept) gives the maximal tree `{12, 02, 03}`. -/
theorem isMaxTree_K1_path : IsMaxTree K1 {{1, 2}, {0, 2}, {0, 3}} := by
  have h := isMaxTree_K1.exchange (u := 1) (v := 0) (w := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hset : insert ({1, 2} : Finset (Fin 5))
      (({{0, 1}, {0, 2}, {0, 3}} : Finset (Finset (Fin 5))).erase {1, 0}) =
      {{1, 2}, {0, 2}, {0, 3}} := by decide
  rwa [hset] at h

/-- **A chain of two exchanges**, from the star tree at `0` to `{12, 02, 23}`, along which the
amplitude is constant. -/
theorem chain_K1 (cut : Finset (Fin 5) → ℕ) :
    amplitudeGF K1 {{0, 1}, {0, 2}, {0, 3}} cut = amplitudeGF K1 {{1, 2}, {0, 2}, {2, 3}} cut := by
  have s1 : TreeExchange K1 {{0, 1}, {0, 2}, {0, 3}} {{1, 2}, {0, 2}, {0, 3}} := by
    have := TreeExchange.mk (K := K1) (T := {{0, 1}, {0, 2}, {0, 3}}) (by decide) (u := 1) (v := 0)
      (w := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hset : insert ({1, 2} : Finset (Fin 5))
        (({{0, 1}, {0, 2}, {0, 3}} : Finset (Finset (Fin 5))).erase {1, 0}) =
        {{1, 2}, {0, 2}, {0, 3}} := by decide
    rwa [hset] at this
  have s2 : TreeExchange K1 {{1, 2}, {0, 2}, {0, 3}} {{1, 2}, {0, 2}, {2, 3}} := by
    have := TreeExchange.mk (K := K1) (T := {{1, 2}, {0, 2}, {0, 3}}) (by decide) (u := 3) (v := 0)
      (w := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hset : insert ({3, 2} : Finset (Fin 5))
        (({{1, 2}, {0, 2}, {0, 3}} : Finset (Finset (Fin 5))).erase {3, 0}) =
        {{1, 2}, {0, 2}, {2, 3}} := by decide
    rwa [hset] at this
  exact amplitudeGF_eqvGen_exchange K1 (.trans _ _ _ (.rel _ _ s1) (.rel _ _ s2)) cut

/-- The vanishing lemma on an explicit colouring: spins `0, 0, ½` on `01, 12, 02` (doubled `0, 0,
1`) violate the triangle inequality, so the weight of `K1` is `0`. -/
theorem weight_tri_zero :
    weight K1 (fun e => if e = {0, 2} then 1 else 0) = 0 :=
  weight_eq_zero_of_tri (p := 0) (q := 2) (r := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end Lightlike.PR.Test

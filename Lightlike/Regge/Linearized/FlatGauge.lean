import Mathlib
import Lightlike.Regge.Linearized.PolarGauge

/-!
# The flat (pure displacement) part of the linearized deficit vanishes on every star

Edge data of the form "first-order change of squared edge length under a vertex displacement
field" is the linearized-Regge image of the flat part `h = L_X δ` of a metric perturbation. For a
triangle `(0, p, q)` whose vertices move by `u` (at `p`) and `v` (at `q`), the squared lengths
change to first order by `2 p·u`, `2 q·v`, `2 (p-q)·(u-v)`. The first variation of the angle at the
origin is then `sign(p × q) · (q × v / |q|² - p × u / |p|²)`, the derivative of `arg q - arg p`.

Around a closed star the outer vertex of one triangle is the inner vertex of the next, so these
terms telescope (for any cyclic relabelling) and the linearized deficit is exactly `0`, for stars of
every shape, however thin. This is item 7 of the pass-3 programme: together with
`Lightlike.Regge.Linearized.polarStarDeficit_hasDerivAt` (the curvature part) it shows that
vertex-level consistency is uniform over non-fat stars.
-/

open Real Lightlike.CMS

namespace Lightlike.Regge.Linearized

open Lightlike.Regge.Linear

/-- Dot product of two plane vectors. -/
def dot2 (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

/-- Angle at the origin of the triangle `(0, p, q)` when the squared edge lengths are changed by
the first-order effect of displacing `p` by `ε u` and `q` by `ε v`. -/
noncomputable def flatAngle (p q u v : ℝ × ℝ) (ε : ℝ) : ℝ :=
  triAngle (sqn p + ε * (2 * dot2 p u)) (sqn q + ε * (2 * dot2 q v))
    (sqn (p - q) + ε * (2 * dot2 (p - q) (u - v)))

private lemma sqn_pos {p : ℝ × ℝ} (hp : p ≠ 0) : 0 < sqn p := by
  unfold sqn
  rcases eq_or_ne p.1 0 with h1 | h1
  · have : p.2 ≠ 0 := fun h2 => hp (Prod.ext h1 h2)
    positivity
  · positivity

/-- **First variation of the angle under a vertex displacement.** For a nondegenerate triangle
`(0, p, q)` with `p × q > 0`, the derivative of the angle at the origin is
`(q × v)/|q|² - (p × u)/|p|²`. -/
theorem flatAngle_hasDerivAt (p q u v : ℝ × ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : 0 < cross2 p q) :
    HasDerivAt (flatAngle p q u v)
      (cross2 q v / sqn q - cross2 p u / sqn p) 0 := by
  have hpa := sqn_pos hp
  have hqa := sqn_pos hq
  have hD : 0 < disc (sqn p) (sqn q) (sqn (p - q)) := by
    rw [disc_sqn]; positivity
  have hder := hasDerivAt_triAngle (a := sqn p) (b := sqn q) (c := sqn (p - q))
    (a₁ := 2 * dot2 p u) (b₁ := 2 * dot2 q v) (c₁ := 2 * dot2 (p - q) (u - v)) hpa hqa hD
  have hroot : √(disc (sqn p) (sqn q) (sqn (p - q))) = 2 * cross2 p q := by
    rw [disc_sqn, show 4 * cross2 p q ^ 2 = (2 * cross2 p q) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hroot] at hder
  refine hder.congr_deriv ?_
  unfold dot2 sqn cross2 at *
  simp only [Prod.fst_sub, Prod.snd_sub] at *
  have hp' : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := hpa.ne'
  have hq' : q.1 ^ 2 + q.2 ^ 2 ≠ 0 := hqa.ne'
  have hk' : p.1 * q.2 - p.2 * q.1 ≠ 0 := hk.ne'
  rw [div_eq_iff (by positivity)]
  field_simp
  ring

/-- **Flat part of a closed star.** For a closed star of triangles `(0, pᵢ, p_{σ i})` (`σ` any
permutation, e.g. the cyclic shift; all triangles positively oriented, of any shape) and any
displacement field `u` of the outer vertices, the linearized deficit from displacement edge data
is zero: the derivative of `2π - Σ θᵢ` vanishes. -/
theorem flatStarDeficit_hasDerivAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (p u : Fin n → ℝ × ℝ)
    (hp : ∀ i, p i ≠ 0) (hk : ∀ i, 0 < cross2 (p i) (p (σ i))) :
    HasDerivAt (fun ε : ℝ => 2 * π - ∑ i, flatAngle (p i) (p (σ i)) (u i) (u (σ i)) ε)
      0 0 := by
  have hs := HasDerivAt.sum (u := Finset.univ)
    (A := fun i ε => flatAngle (p i) (p (σ i)) (u i) (u (σ i)) ε)
    (A' := fun i => cross2 (p (σ i)) (u (σ i)) / sqn (p (σ i)) - cross2 (p i) (u i) / sqn (p i))
    (x := (0 : ℝ))
    (fun i _ => flatAngle_hasDerivAt _ _ _ _ (hp i) (hp (σ i)) (hk i))
  have htel : ∑ i, (cross2 (p (σ i)) (u (σ i)) / sqn (p (σ i)) - cross2 (p i) (u i) / sqn (p i))
      = 0 := by
    rw [Finset.sum_sub_distrib,
      Equiv.sum_comp σ (fun j => cross2 (p j) (u j) / sqn (p j)), sub_self]
  have := hs.const_sub (2 * π)
  rw [htel] at this
  simpa using this

/-- A flat displacement gives zero linearized deficit on the thin kite as well: the cyclic star
with outer vertices `(±1, 0), (0, ±η)` is a special case of `flatStarDeficit_hasDerivAt`
(stated here for the cyclic shift on `Fin 4`). -/
theorem flatStar_fin_four (p u : Fin 4 → ℝ × ℝ) (hp : ∀ i, p i ≠ 0)
    (hk : ∀ i, 0 < cross2 (p i) (p (finRotate 4 i))) :
    HasDerivAt (fun ε : ℝ =>
      2 * π - ∑ i, flatAngle (p i) (p (finRotate 4 i)) (u i) (u (finRotate 4 i)) ε) 0 0 :=
  flatStarDeficit_hasDerivAt (finRotate 4) p u hp hk

end Lightlike.Regge.Linearized

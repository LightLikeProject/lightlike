import Mathlib
import Lightlike.Regge.Linearized.FlatGauge

/-!
# Flat part plus curvature part: the linearized deficit is `-t ·` area, whatever the gauge

A general first-order edge datum on a star is (gauge) + (curvature): the squared-length change of
the outer edge `p → q` is `2 (p - q)·(u - v) + t (p × q)²`, where `u, v` is a vertex displacement
field and `t` the curvature coefficient (polar gauge `t (x dy - y dx)²`). Since the first variation
of the angle is linear in the data, the angle derivative is the flat one plus `t |p × q| / 2`, and the
star deficit derivative is `- t ·` (area of the star), for every shape of star and every `u`.
This is the vertex-level statement "linearized Regge curvature = curvature · area, invariant under
the gauge `h ↦ h + L_X δ`", uniformly in fatness (pass 4, lemma 1).
-/

open Real Lightlike.CMS

namespace Lightlike.Regge.Linearized

open Lightlike.Regge.Linear

/-- Angle at the origin of `(0, p, q)` with flat displacement data `(u, v)` plus curvature data
`t (p × q)²` on the outer edge. -/
noncomputable def combAngle (p q u v : ℝ × ℝ) (t ε : ℝ) : ℝ :=
  triAngle (sqn p + ε * (2 * dot2 p u)) (sqn q + ε * (2 * dot2 q v))
    (sqn (p - q) + ε * (2 * dot2 (p - q) (u - v) + t * cross2 p q ^ 2))

private lemma sqn_pos' {p : ℝ × ℝ} (hp : p ≠ 0) : 0 < sqn p := by
  unfold sqn
  rcases eq_or_ne p.1 0 with h1 | h1
  · have : p.2 ≠ 0 := fun h2 => hp (Prod.ext h1 h2)
    positivity
  · positivity

/-- **First variation of the angle, gauge plus curvature.** For `p × q > 0`, the derivative of the
angle at the origin is the flat part `(q × v)/|q|² - (p × u)/|p|²` plus `t (p × q)/2`. -/
theorem combAngle_hasDerivAt (p q u v : ℝ × ℝ) (t : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : 0 < cross2 p q) :
    HasDerivAt (combAngle p q u v t)
      (cross2 q v / sqn q - cross2 p u / sqn p + t * (cross2 p q / 2)) 0 := by
  have hpa := sqn_pos' hp
  have hqa := sqn_pos' hq
  have hD : 0 < disc (sqn p) (sqn q) (sqn (p - q)) := by
    rw [disc_sqn]; positivity
  have hder := hasDerivAt_triAngle (a := sqn p) (b := sqn q) (c := sqn (p - q))
    (a₁ := 2 * dot2 p u) (b₁ := 2 * dot2 q v)
    (c₁ := 2 * dot2 (p - q) (u - v) + t * cross2 p q ^ 2) hpa hqa hD
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

/-- **Gauge-invariant curvature on every closed star.** For a closed star (any permutation `σ`,
positively oriented triangles of any shape) and any displacement field `u`, the derivative of the
deficit `2π - Σ θᵢ` for edge data `gauge(u) + t (pᵢ × p_{σ i})²` is `-t · Σ (pᵢ × p_{σ i}) / 2`,
that is minus `t` times the area of the star. -/
theorem combStarDeficit_hasDerivAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (p u : Fin n → ℝ × ℝ)
    (t : ℝ) (hp : ∀ i, p i ≠ 0) (hk : ∀ i, 0 < cross2 (p i) (p (σ i))) :
    HasDerivAt (fun ε : ℝ => 2 * π - ∑ i, combAngle (p i) (p (σ i)) (u i) (u (σ i)) t ε)
      (-(t * ∑ i, cross2 (p i) (p (σ i)) / 2)) 0 := by
  have hs := HasDerivAt.sum (u := Finset.univ)
    (A := fun i ε => combAngle (p i) (p (σ i)) (u i) (u (σ i)) t ε)
    (A' := fun i => (cross2 (p (σ i)) (u (σ i)) / sqn (p (σ i)) - cross2 (p i) (u i) / sqn (p i))
      + t * (cross2 (p i) (p (σ i)) / 2))
    (x := (0 : ℝ))
    (fun i _ => combAngle_hasDerivAt _ _ _ _ t (hp i) (hp (σ i)) (hk i))
  have htel : ∑ i, ((cross2 (p (σ i)) (u (σ i)) / sqn (p (σ i)) - cross2 (p i) (u i) / sqn (p i))
      + t * (cross2 (p i) (p (σ i)) / 2)) = t * ∑ i, cross2 (p i) (p (σ i)) / 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Equiv.sum_comp σ (fun j => cross2 (p j) (u j) / sqn (p j)), sub_self, zero_add,
      ← Finset.mul_sum]
  have := hs.const_sub (2 * π)
  rw [htel] at this
  simpa using this

end Lightlike.Regge.Linearized

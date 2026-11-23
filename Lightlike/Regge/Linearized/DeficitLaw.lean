import Mathlib
import Lightlike.Regge.Linearized.CombinedGauge

/-!
# The linearized deficit law: area, gauge independence, scale covariance, detection of curvature

Packaging of the first-order star deficit `-t ·` area (`combStarDeficit_hasDerivAt`):

* `starArea` is the shoelace area of a star, positive for a positively oriented star
  (`starArea_pos`) and quadratic under rescaling (`starArea_smul`);
* the derivative is independent of the gauge field `u` (`combStarDeficit_gauge_independent`);
* the angle with rescaled data and curvature `t / s²` equals the original angle
  (`combAngle_smul`), and the deficit derivative `-t ·` area is invariant under
  `p ↦ s p, u ↦ s u, t ↦ t / s²` (`combStarDeficit_scale_covariant`);
* the derivative vanishes iff the curvature coefficient vanishes (`combStarDeficit_zero_iff`),
  so the first-order deficit detects curvature on every star, however thin.
-/

open Real Lightlike.CMS

namespace Lightlike.Regge.Linearized

open Lightlike.Regge.Linear

/-- Shoelace area `Σ (pᵢ × p_{σ i}) / 2` of the star with spokes `p` and cyclic order `σ`. -/
noncomputable def starArea {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ × ℝ) : ℝ :=
  ∑ i, cross2 (p i) (p (σ i)) / 2

/-- A positively oriented nonempty star has positive area. -/
theorem starArea_pos {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ × ℝ)
    (hk : ∀ i, 0 < cross2 (p i) (p (σ i))) : 0 < starArea σ p := by
  unfold starArea
  exact Finset.sum_pos (fun i _ => by have := hk i; positivity) Finset.univ_nonempty

/-- Scaling all spokes by `s` scales the area by `s²`. -/
theorem starArea_smul {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ × ℝ) (s : ℝ) :
    starArea σ (fun i => s • p i) = s ^ 2 * starArea σ p := by
  unfold starArea
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold cross2
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **Gauge independence.** The derivative of the star deficit does not depend on the
displacement field. -/
theorem combStarDeficit_gauge_independent {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p u u' : Fin n → ℝ × ℝ) (t : ℝ) (hp : ∀ i, p i ≠ 0)
    (hk : ∀ i, 0 < cross2 (p i) (p (σ i))) :
    deriv (fun ε : ℝ => 2 * π - ∑ i, combAngle (p i) (p (σ i)) (u i) (u (σ i)) t ε) 0 =
    deriv (fun ε : ℝ => 2 * π - ∑ i, combAngle (p i) (p (σ i)) (u' i) (u' (σ i)) t ε) 0 := by
  rw [(combStarDeficit_hasDerivAt σ p u t hp hk).deriv,
    (combStarDeficit_hasDerivAt σ p u' t hp hk).deriv]

/-- The first variation of the deficit, restated with `starArea`. -/
theorem combStarDeficit_hasDerivAt_area {n : ℕ} (σ : Equiv.Perm (Fin n)) (p u : Fin n → ℝ × ℝ)
    (t : ℝ) (hp : ∀ i, p i ≠ 0) (hk : ∀ i, 0 < cross2 (p i) (p (σ i))) :
    HasDerivAt (fun ε : ℝ => 2 * π - ∑ i, combAngle (p i) (p (σ i)) (u i) (u (σ i)) t ε)
      (-(t * starArea σ p)) 0 :=
  combStarDeficit_hasDerivAt σ p u t hp hk

/-- The angle is scale invariant (local copy of `Lightlike.Regge.Linear.triAngle_smul`). -/
private lemma triAngle_smul' {k : ℝ} (hk : 0 < k) (a b c : ℝ) :
    triAngle (k * a) (k * b) (k * c) = triAngle a b c := by
  unfold triAngle
  congr 1
  rw [show k * a * (k * b) = k ^ 2 * (a * b) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hk.le]
  by_cases h : √(a * b) = 0
  · simp [h]
  · field_simp

/-- **Scale covariance of the angle.** Rescaling the spokes and displacements by `s ≠ 0` and the
curvature coefficient by `1 / s²` leaves the angle unchanged. -/
theorem combAngle_smul (p q u v : ℝ × ℝ) (t s ε : ℝ) (hs : s ≠ 0) :
    combAngle (s • p) (s • q) (s • u) (s • v) (t / s ^ 2) ε = combAngle p q u v t ε := by
  have hs2 : 0 < s ^ 2 := by positivity
  unfold combAngle
  symm
  rw [← triAngle_smul' hs2]
  congr 1
  · unfold sqn dot2
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · unfold sqn dot2
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · unfold sqn dot2 cross2
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    field_simp

/-- **Scale covariance of the first-order deficit.** The deficit derivative `-t ·` area is the same
for the star `s p` with data `s u` and curvature `t / s²`. -/
theorem combStarDeficit_scale_covariant {n : ℕ} (σ : Equiv.Perm (Fin n)) (p u : Fin n → ℝ × ℝ)
    (t s : ℝ) (hs : s ≠ 0) :
    deriv (fun ε : ℝ => 2 * π - ∑ i, combAngle (s • p i) (s • p (σ i)) (s • u i) (s • u (σ i))
      (t / s ^ 2) ε) 0 =
    deriv (fun ε : ℝ => 2 * π - ∑ i, combAngle (p i) (p (σ i)) (u i) (u (σ i)) t ε) 0 := by
  have h : (fun ε : ℝ => 2 * π - ∑ i, combAngle (s • p i) (s • p (σ i)) (s • u i)
      (s • u (σ i)) (t / s ^ 2) ε) =
      fun ε : ℝ => 2 * π - ∑ i, combAngle (p i) (p (σ i)) (u i) (u (σ i)) t ε := by
    funext ε
    simp only [combAngle_smul _ _ _ _ t s ε hs]
  rw [h]

/-- **Curvature detection.** The first-order deficit of a positively oriented star vanishes
exactly when the curvature coefficient `t` vanishes, whatever the gauge field and the shape. -/
theorem combStarDeficit_zero_iff {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n))
    (p u : Fin n → ℝ × ℝ) (t : ℝ) (hp : ∀ i, p i ≠ 0)
    (hk : ∀ i, 0 < cross2 (p i) (p (σ i))) :
    deriv (fun ε : ℝ => 2 * π - ∑ i, combAngle (p i) (p (σ i)) (u i) (u (σ i)) t ε) 0 = 0 ↔
      t = 0 := by
  rw [(combStarDeficit_hasDerivAt_area σ p u t hp hk).deriv]
  have := starArea_pos σ p hk
  constructor
  · intro h
    have h' : t * starArea σ p = 0 := by linarith
    exact (mul_eq_zero.mp h').resolve_right this.ne'
  · intro h; simp [h]

/-- Under the scaling, the star deficit derivative of the rescaled star equals `-t ·` area of the
original star (explicit form of `combStarDeficit_scale_covariant`). -/
theorem combStarDeficit_scaled_value {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ × ℝ)
    (t s : ℝ) (hs : s ≠ 0) : -(t / s ^ 2 * starArea σ (fun i => s • p i)) =
      -(t * starArea σ p) := by
  rw [starArea_smul]
  field_simp

end Lightlike.Regge.Linearized

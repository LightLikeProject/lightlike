import Lightlike.Spacetime.ConjugatePoints.JacobiVariation

/-!
# Test of the variation lemma in a flat chart (row G1-006, GE3)

For a constant symmetric invertible metric `G` and the fan of straight lines
`H (t, s) = x + t • (v + s • b)`, the variation lemma `exists_isJacobiOn_of_variation` produces a
Jacobi field along `t ↦ x + t • v`, and the variation field is `J t = t • b`, the Jacobi field of
`isJacobiOn_const_metric_line` with `a = 0`.
-/

open Set Filter Topology Matrix
open scoped ContDiff

namespace Lightlike.Geodesic

variable {n : ℕ}

/-- The fan of lines from `x` with velocities `v + s b`. -/
def fanLines (x v b : Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ := x + p.1 • (v + p.2 • b)

theorem contDiff_fanLines (x v b : Fin n → ℝ) : ContDiff ℝ 3 (fanLines x v b) := by
  unfold fanLines
  fun_prop

theorem fderiv_fanLines_fst (x v b : Fin n → ℝ) (t s : ℝ) :
    fderiv ℝ (fanLines x v b) (t, s) (1, 0) = v + s • b := by
  have hd : HasDerivAt (fun t : ℝ => ((t, s) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) t := by
    simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
  have h := ((contDiff_fanLines x v b).differentiable (by norm_num) (t, s)).hasFDerivAt.comp_hasDerivAt
    t hd
  have h2 : HasDerivAt (fun t : ℝ => fanLines x v b (t, s)) (v + s • b) t := by
    unfold fanLines
    simpa using ((hasDerivAt_id t).smul_const (v + s • b)).const_add x
  exact h.unique h2

theorem fderiv_fanLines_snd (x v b : Fin n → ℝ) (t s : ℝ) :
    fderiv ℝ (fanLines x v b) (t, s) (0, 1) = t • b := by
  have hd : HasDerivAt (fun s : ℝ => ((t, s) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) s := by
    simpa using (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
  have h := ((contDiff_fanLines x v b).differentiable (by norm_num) (t, s)).hasFDerivAt.comp_hasDerivAt
    s hd
  have h2 : HasDerivAt (fun s : ℝ => fanLines x v b (t, s)) (t • b) s := by
    unfold fanLines
    simpa [smul_add, smul_smul, mul_comm] using
      (((hasDerivAt_id s).smul_const b).const_smul t).const_add (x + t • v)
  exact h.unique h2

/-- Every line of the fan is a geodesic of a constant metric. -/
theorem isGeodesicOn_fanLines (G : Matrix (Fin n) (Fin n) ℝ) (x v b : Fin n → ℝ) (s : ℝ) :
    IsGeodesicOn (fun _ => G) (fun t => fanLines x v b (t, s))
      (fun t => fderiv ℝ (fanLines x v b) (t, s) (1, 0)) univ := by
  simp only [fderiv_fanLines_fst]
  refine ⟨fun t _ => ?_, fun t _ => ?_⟩
  · unfold fanLines
    simpa using ((hasDerivAt_id t).smul_const (v + s • b)).const_add x
  · have : accel (fun _ => G) (fanLines x v b (t, s)) (v + s • b) = 0 := by
      funext i
      simp [accel, christoffel_const]
    rw [this]
    exact hasDerivAt_const t _

/-- **Test of the variation lemma**: for a constant metric and the fan of lines, the lemma applies
and the variation field is `t • b`. -/
theorem fanLines_variation (G : Matrix (Fin n) (Fin n) ℝ) (hsym : Gᵀ = G) (hdet : IsUnit G.det)
    (x v b : Fin n → ℝ) :
    ∃ P, IsJacobiOn (fun _ => G) (fun t => fanLines x v b (t, 0)) (fun _ => v)
      (fun t => t • b) P univ := by
  obtain ⟨P, hP⟩ := exists_isJacobiOn_of_variation (g := fun _ => G) (U := univ)
    (isCoordMetric_const hsym hdet) (contDiff_fanLines x v b) (I := univ) (fun _ _ => mem_univ _)
    (Eventually.of_forall fun s => isGeodesicOn_fanLines G x v b s)
  refine ⟨P, ?_⟩
  simpa [fderiv_fanLines_fst, fderiv_fanLines_snd] using hP

end Lightlike.Geodesic

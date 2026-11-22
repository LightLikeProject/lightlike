import Lightlike.Rows.G1_069.Ensemble

/-!
# Continuity, boundedness and integrability of the reduced entropy on the sphere

`sphereEntropy m n` is continuous on the unit sphere of `ℂ^m ⊗ ℂ^n`, takes values in `[0, log m]`,
hence is integrable for the probability measure `sphereProb m n`; so `avgEntropy m n ∈ [0, log m]`.
-/

namespace Lightlike.Rows.G1_069

open MeasureTheory Metric

/-- The reduced density matrix of a unit vector is continuous in the vector (entrywise `Σ_k x(i,k) conj x(j,k)`). -/
theorem continuous_reducedState (m n : ℕ) :
    Continuous (fun x : sphere (0 : PageSpace m n) 1 => (MState.pure (ketOfSphere x)).traceRight) := by
  refine continuous_induced_rng.mpr ?_
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [MState.pure, ketOfSphere, Matrix.traceRight, Matrix.of_apply]
  refine continuous_finsetSum _ fun k _ => ?_
  have hc : ∀ p : Fin m × Fin n, Continuous fun a : sphere (0 : PageSpace m n) 1 => a.1 p :=
    fun p => (EuclideanSpace.proj p).continuous.comp continuous_subtype_val
  exact (hc (i, k)).mul (Complex.continuous_conj.comp (hc (j, k)))

/-- The reduced entropy is continuous on the sphere. -/
theorem continuous_sphereEntropy (m n : ℕ) : Continuous (sphereEntropy m n) :=
  Sᵥₙ_continuous.comp (continuous_reducedState m n)

theorem sphereEntropy_nonneg (m n : ℕ) (x : sphere (0 : PageSpace m n) 1) : 0 ≤ sphereEntropy m n x :=
  Sᵥₙ_nonneg _

theorem sphereEntropy_le_log (m n : ℕ) (x : sphere (0 : PageSpace m n) 1) :
    sphereEntropy m n x ≤ Real.log m := by
  have h := Sᵥₙ_le_log_d (MState.pure (ketOfSphere x)).traceRight
  unfold sphereEntropy
  simpa using h

/-- The reduced entropy is integrable against the Haar-random state distribution. -/
theorem integrable_sphereEntropy (m n : ℕ) [NeZero m] [NeZero n] :
    Integrable (sphereEntropy m n) (sphereProb m n) := by
  refine Integrable.of_bound (C := Real.log m) (continuous_sphereEntropy m n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereEntropy_nonneg m n x)]
  exact sphereEntropy_le_log m n x

/-- The average entanglement entropy is nonnegative. -/
theorem avgEntropy_nonneg (m n : ℕ) : 0 ≤ avgEntropy m n :=
  integral_nonneg (sphereEntropy_nonneg m n)

/-- The average entanglement entropy is at most `log m`. -/
theorem avgEntropy_le_log (m n : ℕ) [NeZero m] [NeZero n] : avgEntropy m n ≤ Real.log m := by
  have h := integral_mono (integrable_sphereEntropy m n) (integrable_const (Real.log m))
    (sphereEntropy_le_log m n) (μ := sphereProb m n)
  simpa [avgEntropy] using h

end Lightlike.Rows.G1_069

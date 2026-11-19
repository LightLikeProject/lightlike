import Lightlike.GR.EddingtonFinkelstein
import Lightlike.Spacetime.GeodesicMomentum

/-!
# Constants of motion of the geodesics in Eddington–Finkelstein coordinates

Gap row G1-020, toward the analysis of the geodesics of the Kruskal extension. The ingoing Eddington–Finkelstein
metric does not depend on `v` and on `φ`, so along every geodesic in the chart (`r > 0`, across the horizon) the
energy `-(1 - 2M/r) v' + r'` and the axial angular momentum `r² sin² θ φ'` are constant
(`ef_hasDerivAt_energy`, `ef_hasDerivAt_angular`), by `IsGeodesicOn.hasDerivAt_momentum`.
-/

open Matrix Real

noncomputable section

namespace Lightlike

/-- A function that does not depend on the coordinate `yᵏ` has vanishing partial derivative `∂_k`. -/
lemma pd_eq_zero_of_invariant {n : ℕ} (k : Fin n) {f : (Fin n → ℝ) → ℝ} (y : Fin n → ℝ)
    (hinv : ∀ (z : Fin n → ℝ) (t : ℝ), f (z + t • Pi.single k 1) = f z) : pd k f y = 0 := by
  unfold pd
  by_cases hd : DifferentiableAt ℝ f y
  · have h1 : HasDerivAt (fun t : ℝ => f (y + t • Pi.single k 1)) (fderiv ℝ f y (Pi.single k 1)) 0 := by
      have hline : HasDerivAt (fun t : ℝ => y + t • (Pi.single k 1 : Fin n → ℝ)) (Pi.single k 1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k 1 : Fin n → ℝ)).const_add y
      have h2 : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • (Pi.single k 1 : Fin n → ℝ)) := by
        simpa using hd.hasFDerivAt
      exact h2.comp_hasDerivAt 0 hline
    have h3 : HasDerivAt (fun t : ℝ => f (y + t • Pi.single k 1)) 0 0 := by
      simp only [hinv]
      exact hasDerivAt_const 0 (f y)
    exact h1.unique h3
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

variable (M : ℝ)

/-- The Eddington–Finkelstein metric does not depend on `v`. -/
lemma pd_zero_efMetric (y : Fin 4 → ℝ) (i j : Fin 4) : pd 0 (fun z => efMetric M z i j) y = 0 := by
  refine pd_eq_zero_of_invariant 0 y fun z t => ?_
  fin_cases i <;> fin_cases j <;> simp [efMetric, Pi.single_apply]

/-- The Eddington–Finkelstein metric does not depend on `φ`. -/
lemma pd_three_efMetric (y : Fin 4 → ℝ) (i j : Fin 4) : pd 3 (fun z => efMetric M z i j) y = 0 := by
  refine pd_eq_zero_of_invariant 3 y fun z t => ?_
  fin_cases i <;> fin_cases j <;> simp [efMetric, Pi.single_apply]

/-- **The energy is constant along the geodesics of the Eddington–Finkelstein chart**:
`-(1 - 2M/r) v' + r'` has derivative `0`. -/
theorem ef_hasDerivAt_energy {γ w : ℝ → Fin 4 → ℝ} {I : Set ℝ}
    (h : Lightlike.Geodesic.IsGeodesicOn (efMetric M) γ w I) {t : ℝ} (ht : t ∈ I) (hγt : γ t ∈ efU) :
    HasDerivAt (fun s => -(1 - 2 * M / γ s 1) * w s 0 + w s 1) 0 t := by
  have h1 := h.hasDerivAt_momentum (isCoordMetric_ef M) ht hγt 0 (pd_zero_efMetric M (γ t))
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp [efMetric, Fin.sum_univ_four]

/-- **The axial angular momentum is constant along the geodesics of the Eddington–Finkelstein chart**:
`r² sin² θ φ'` has derivative `0`. -/
theorem ef_hasDerivAt_angular {γ w : ℝ → Fin 4 → ℝ} {I : Set ℝ}
    (h : Lightlike.Geodesic.IsGeodesicOn (efMetric M) γ w I) {t : ℝ} (ht : t ∈ I) (hγt : γ t ∈ efU) :
    HasDerivAt (fun s => γ s 1 ^ 2 * sin (γ s 2) ^ 2 * w s 3) 0 t := by
  have h1 := h.hasDerivAt_momentum (isCoordMetric_ef M) ht hγt 3 (pd_three_efMetric M (γ t))
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp [efMetric, Fin.sum_univ_four]

end Lightlike

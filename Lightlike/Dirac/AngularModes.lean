import Mathlib
import Lightlike.Dirac.AngularFourier
import Lightlike.Dirac.EigenAngular

/-!
# Mode equations for a smooth chart spinor

For `g : ℝ² → ℂ` of class `C¹` and the polar function `G r θ = g (r cos θ, r sin θ)`:
`∂_r G + (i/r) ∂_θ G = e^{-iθ} (∂₀ g + i ∂₁ g)` and `∂_r G − (i/r) ∂_θ G = e^{iθ} (∂₀ g − i ∂₁ g)`.
-/

namespace Lightlike.Dirac

open Complex

/-- The point with polar coordinates `(r, θ)`. -/
noncomputable def polarPt (r θ : ℝ) : E 2 := (r * Real.cos θ) • e (0 : Fin 2) + (r * Real.sin θ) • e (1 : Fin 2)

/-- `g` in polar coordinates. -/
noncomputable def polarFn (g : E 2 → ℂ) (r θ : ℝ) : ℂ := g (polarPt r θ)

lemma polarPt_continuous : Continuous fun p : ℝ × ℝ => polarPt p.1 p.2 := by
  unfold polarPt; fun_prop

/-- The radial derivative of the polar function. -/
theorem hasDerivAt_polar_r {g : E 2 → ℂ} {g' : E 2 →L[ℝ] ℂ} (r θ : ℝ) (hg : HasFDerivAt g g' (polarPt r θ)) :
    HasDerivAt (fun r => polarFn g r θ) (g' (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2))) r := by
  have h1 : HasDerivAt (fun r : ℝ => polarPt r θ) (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2)) r := by
    unfold polarPt
    have a : HasDerivAt (fun r : ℝ => (r * Real.cos θ) • e (0 : Fin 2)) (Real.cos θ • e (0 : Fin 2)) r := by
      simpa using ((hasDerivAt_id r).mul_const (Real.cos θ)).smul_const (e (0 : Fin 2) : E 2)
    have b : HasDerivAt (fun r : ℝ => (r * Real.sin θ) • e (1 : Fin 2)) (Real.sin θ • e (1 : Fin 2)) r := by
      simpa using ((hasDerivAt_id r).mul_const (Real.sin θ)).smul_const (e (1 : Fin 2) : E 2)
    exact a.add b
  exact hg.comp_hasDerivAt r h1

/-- The angular derivative of the polar function. -/
theorem hasDerivAt_polar_theta {g : E 2 → ℂ} {g' : E 2 →L[ℝ] ℂ} (r θ : ℝ) (hg : HasFDerivAt g g' (polarPt r θ)) :
    HasDerivAt (fun θ => polarFn g r θ) (g' ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2))) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => polarPt r θ) ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2)) θ := by
    unfold polarPt
    have a : HasDerivAt (fun θ : ℝ => (r * Real.cos θ) • e (0 : Fin 2)) ((-(r * Real.sin θ)) • e (0 : Fin 2)) θ := by
      simpa using (((Real.hasDerivAt_cos θ).const_mul r)).smul_const (e (0 : Fin 2) : E 2)
    have b : HasDerivAt (fun θ : ℝ => (r * Real.sin θ) • e (1 : Fin 2)) ((r * Real.cos θ) • e (1 : Fin 2)) θ := by
      simpa using (((Real.hasDerivAt_sin θ).const_mul r)).smul_const (e (1 : Fin 2) : E 2)
    exact a.add b
  exact hg.comp_hasDerivAt θ h1

/-- `∂_r G + (i/r) ∂_θ G = e^{-iθ} (∂₀ g + i ∂₁ g)`. -/
theorem polar_wirtinger_bar (g' : E 2 →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    g' (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2)) +
      (Complex.I / r) * g' ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2)) =
    Complex.exp (-(θ : ℂ) * Complex.I) * (g' (e (0 : Fin 2)) + Complex.I * g' (e (1 : Fin 2))) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hexp : Complex.exp (-(θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
    rw [show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin, Complex.cos_neg, Complex.sin_neg]
    ring
  simp only [map_add, map_smul, Complex.real_smul, hexp]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- `∂_r G − (i/r) ∂_θ G = e^{iθ} (∂₀ g − i ∂₁ g)`. -/
theorem polar_wirtinger (g' : E 2 →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    g' (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2)) -
      (Complex.I / r) * g' ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2)) =
    Complex.exp ((θ : ℂ) * Complex.I) * (g' (e (0 : Fin 2)) - Complex.I * g' (e (1 : Fin 2))) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
    rw [Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  simp only [map_add, map_smul, Complex.real_smul, hexp]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

end Lightlike.Dirac

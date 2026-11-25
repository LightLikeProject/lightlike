import Lightlike.GR.SchwarzschildTrappedSpheres.Defs

/-!
# Null expansion of a normal field along a Schwarzschild coordinate sphere (row G1-011)

* `Trapped.pd_tan_eq_zero`: a function vanishing on the coordinate sphere has vanishing tangential
  partial derivatives there (no differentiability hypothesis needed: `fderiv = 0` otherwise).
* `Trapped.nullExpansion_sch`: if the normal field `k` has `k² = k³ = 0` on the sphere, its
  expansion on the sphere `(t₀, r₀)` of Schwarzschild is `2 k¹ / r₀`.
-/

open Matrix Real

noncomputable section

namespace Lightlike
namespace Trapped

/-- A function vanishing on the coordinate sphere has vanishing tangential partial derivatives
at its points. -/
lemma pd_tan_eq_zero {t₀ r₀ : ℝ} {f : (Fin 4 → ℝ) → ℝ} (hf : ∀ z ∈ sphere t₀ r₀, f z = 0)
    {y : Fin 4 → ℝ} (hy : y ∈ sphere t₀ r₀) (A : Fin 2) : pd (tan A) f y = 0 := by
  obtain ⟨h0, h1, h2, h2'⟩ := hy
  by_cases hd : DifferentiableAt ℝ f y
  · set a : Fin 4 := tan A with ha
    have hγ : HasDerivAt (fun s : ℝ => y + s • (Pi.single a (1 : ℝ) : Fin 4 → ℝ))
        (Pi.single a (1 : ℝ) : Fin 4 → ℝ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single a (1 : ℝ) : Fin 4 → ℝ)).const_add y
    have hc : HasDerivAt (fun s : ℝ => f (y + s • (Pi.single a (1 : ℝ) : Fin 4 → ℝ)))
        (fderiv ℝ f y (Pi.single a 1)) 0 := by
      have := hd.hasFDerivAt
      have h' : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • (Pi.single a (1 : ℝ) : Fin 4 → ℝ)) := by
        simpa using this
      exact h'.comp_hasDerivAt (0 : ℝ) hγ
    have hz : HasDerivAt (fun s : ℝ => f (y + s • (Pi.single a (1 : ℝ) : Fin 4 → ℝ))) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      have hev : ∀ᶠ s in nhds (0 : ℝ), 0 < y 2 + s ∧ y 2 + s < π := by
        have hc2 : Continuous fun s : ℝ => y 2 + s := by fun_prop
        exact (hc2.continuousAt.eventually (Ioo_mem_nhds (by simpa using h2) (by simpa using h2')))
      filter_upwards [hev] with s hs
      apply hf
      have hA : A = 0 ∨ A = 1 := by fin_cases A <;> simp
      rcases hA with rfl | rfl
      · simp only [ha, tan] at *
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h0, h1, hs.1, hs.2]
      · simp only [ha, tan] at *
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h0, h1, h2, h2']
    exact hc.unique hz
  · simp [pd, fderiv_zero_of_not_differentiableAt hd]

variable (M : ℝ)

/-- The induced metric of a Schwarzschild coordinate sphere is `diag(r², r² sin² θ)`. -/
lemma sphereMetric_sch (y : Fin 4 → ℝ) :
    sphereMetric (schMetric M) y = diagonal ![y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2] := by
  ext A B
  fin_cases A <;> fin_cases B <;> simp [sphereMetric, schMetric, schD, tan, diagonal_apply]

/-- The inverse induced metric of a Schwarzschild coordinate sphere, on `r ≠ 0`, `sin θ ≠ 0`. -/
lemma sphereMetric_sch_inv {y : Fin 4 → ℝ} (h1 : y 1 ≠ 0) (h2 : sin (y 2) ≠ 0) :
    (sphereMetric (schMetric M) y)⁻¹ =
      diagonal ![(y 1 ^ 2)⁻¹, (y 1 ^ 2 * sin (y 2) ^ 2)⁻¹] := by
  rw [sphereMetric_sch]
  apply Matrix.inv_eq_right_inv
  rw [diagonal_mul_diagonal]
  ext A B
  fin_cases A <;> fin_cases B <;> simp [h1] <;> field_simp

/-- **Expansion of a normal field on a Schwarzschild coordinate sphere.**  If `k² = k³ = 0` on the
sphere `(t₀, r₀)` (`r₀ > 0`, `r₀ ≠ 2M`), then `θ_k = 2 k¹ / r₀` there. -/
lemma nullExpansion_sch {t₀ r₀ : ℝ} (hr : 0 < r₀) (h2M : r₀ - 2 * M ≠ 0)
    {k : (Fin 4 → ℝ) → Fin 4 → ℝ} (hk2 : ∀ z ∈ sphere t₀ r₀, k z 2 = 0)
    (hk3 : ∀ z ∈ sphere t₀ r₀, k z 3 = 0) {y : Fin 4 → ℝ} (hy : y ∈ sphere t₀ r₀) :
    nullExpansion (schMetric M) k y = 2 * k y 1 / r₀ := by
  have hs := hy
  obtain ⟨h0, h1, h2, h2'⟩ := hs
  have hsin : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi h2 h2').ne'
  have hreg : y ∈ schRegion M := ⟨by rw [h1]; exact hr, by rw [h1]; exact h2M, hsin⟩
  have hy1 : y 1 ≠ 0 := by rw [h1]; exact hr.ne'
  have p20 := pd_tan_eq_zero hk2 hy 0
  have p21 := pd_tan_eq_zero hk2 hy 1
  have p30 := pd_tan_eq_zero hk3 hy 0
  have p31 := pd_tan_eq_zero hk3 hy 1
  simp only [tan, Matrix.cons_val_zero, Matrix.cons_val_one] at p20 p21 p30 p31
  have e2 := hk2 y hy
  have e3 := hk3 y hy
  simp only [nullExpansion, covD, sphereMetric_sch_inv M hy1 hsin, Fin.sum_univ_two,
    Fin.sum_univ_four, christoffel_sch M hreg, schΓ, schMetric, schD, tan, diagonal_apply]
  simp [p20, p21, p30, p31, e2, e3, h1]
  field_simp
  ring

end Trapped
end Lightlike

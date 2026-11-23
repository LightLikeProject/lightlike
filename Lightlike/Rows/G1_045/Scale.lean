import Mathlib
import Lightlike.Rows.G1_045.Shift

/-!
# Weinberg's no-go theorem: scale covariance forces a vanishing vacuum energy

If the potential is scale covariant, `V (φᵢ ↦ t^{dᵢ} φᵢ) = t^deg V φ` for `t > 0`, with `deg ≠ 0`
(for a classically scale-invariant theory in four dimensions, `deg = 4`), then Euler's relation
`∑ᵢ dᵢ φᵢ ∂ᵢV = deg · V` holds. At a vacuum (`∂ᵢV = 0`) this gives `V φ = 0`: a scale-invariant
theory has vanishing vacuum energy *at every vacuum*; the point of Weinberg's argument is that this
is not an adjustment but forces a flat direction (see the `Example` file).

## Main results

* `scale`: the dilatation `φᵢ ↦ t^{dᵢ} φᵢ`.
* `ScaleCovariant`: the covariance hypothesis.
* `fderiv_scale_euler`: Euler's relation.
* `weinberg_vanish`: at a vacuum of a scale-covariant potential of degree `≠ 0`, `V φ = 0`.
-/

namespace Lightlike.Rows.G1_045

variable {ι : Type*} [Fintype ι]

/-- The dilatation of the constant fields with weights `d`: `φᵢ ↦ t^{dᵢ} φᵢ`. -/
noncomputable def scale (d : ι → ℝ) (t : ℝ) (φ : ι → ℝ) : ι → ℝ :=
  fun i => t ^ (d i) * φ i

/-- **Scale covariance of degree `deg`** with weights `d`: `V (scale d t φ) = t^deg V φ` for all
`t > 0`. -/
def ScaleCovariant (V : (ι → ℝ) → ℝ) (d : ι → ℝ) (deg : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ φ : ι → ℝ, V (scale d t φ) = t ^ deg * V φ

omit [Fintype ι] in
/-- The orbit `t ↦ scale d t φ` has velocity `dᵢ φᵢ` at `t = 1`. -/
theorem hasDerivAt_scale (d : ι → ℝ) (φ : ι → ℝ) :
    HasDerivAt (fun t : ℝ => scale d t φ) (fun i => d i * φ i) 1 := by
  rw [hasDerivAt_pi]
  intro i
  have h := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := d i) (Or.inl one_ne_zero)).mul_const (φ i)
  simpa [scale] using h

omit [Fintype ι] in
@[simp] theorem scale_one (d : ι → ℝ) (φ : ι → ℝ) : scale d 1 φ = φ := by
  funext i; simp [scale]

/-- **Euler's relation** for a scale-covariant potential differentiable at `φ`:
`DV(φ) (d • φ) = deg · V φ`. -/
theorem fderiv_scale_euler {V : (ι → ℝ) → ℝ} {d : ι → ℝ} {deg : ℝ} (hV : ScaleCovariant V d deg)
    {φ : ι → ℝ} (hd : DifferentiableAt ℝ V φ) :
    fderiv ℝ V φ (fun i => d i * φ i) = deg * V φ := by
  have h1 : HasDerivAt (fun t : ℝ => V (scale d t φ)) (fderiv ℝ V φ (fun i => d i * φ i)) 1 := by
    have hd' : HasFDerivAt V (fderiv ℝ V φ) (scale d 1 φ) := by
      rw [scale_one]; exact hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (1 : ℝ) (hasDerivAt_scale d φ)
  have h2 : HasDerivAt (fun t : ℝ => t ^ deg * V φ) (deg * V φ) 1 := by
    have := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := deg) (Or.inl one_ne_zero)).mul_const
      (V φ)
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ => V (scale d t φ)) (deg * V φ) 1 := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hV t ht φ
  exact h1.unique h3

/-- **Weinberg's vanishing**: at a vacuum of a scale-covariant potential of nonzero degree the
vacuum energy is zero. -/
theorem weinberg_vanish {V : (ι → ℝ) → ℝ} {d : ι → ℝ} {deg : ℝ} (hV : ScaleCovariant V d deg)
    (hdeg : deg ≠ 0) {φ : ι → ℝ} (hφ : IsVacuum V φ) : vacuumEnergy V φ = 0 := by
  have h := fderiv_scale_euler hV hφ.1
  rw [hφ.2] at h
  simp only [zero_apply] at h
  unfold vacuumEnergy
  rcases mul_eq_zero.mp h.symm with h' | h'
  · exact absurd h' hdeg
  · exact h'

end Lightlike.Rows.G1_045

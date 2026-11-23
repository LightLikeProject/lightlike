import Mathlib

/-!
# The conformal embedding of Minkowski space including the axis, in Cartesian form (G1-016)

`MinkowskiCompactification` writes the embedding in the polar coordinates `(η, χ)`, which degenerate on the axis
`r = 0` (`χ = 0`). Here the sphere `S³` is the unit sphere `p = (p₀, p⃗)`, `p₀² + |p⃗|² = 1`, of `ℝ × ℝ³`
(`p₀ = cos χ`, `p⃗ = sin χ · n`), and the embedding is
`t = sin η / ω`, `x⃗ = p⃗ / ω`, `ω = (cos η + p₀) / 2`.
The axis is the ordinary point `p = (1, 0)`.

* `cartOmega`, `cartT`, `cartX`: the conformal factor and the Cartesian map;
* `cartOmega_eq_cos_mul_cos`: on the axis `ω = cos²(η/2)` (`cartOmega_axis`), and `cartT_axis`: `t = 2 tan (η/2)`
  there, `cartX_axis`: `x⃗ = 0`;
* `minkowski_eq_conformal_esu_cartesian`: for a tangent vector `a ∂_η + v` to `ℝ × S³` (`⟨p, v⟩ = 0`), the
  Minkowski metric `-dt² + |dx⃗|²` on its image is `ω⁻² (-a² + |v|²)`, with `|v|² = v₀² + |v⃗|²`: the metric of the
  Einstein static universe, at every point of the region `ω ≠ 0`, the axis included.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 7, eqs. (7.86)–(7.102),
  pp. 192–195; the axis `r = 0` is "well-behaved" (after (7.87)), here made explicit by the Cartesian form.
-/

noncomputable section

namespace Lightlike

open Real

/-- The conformal factor `ω = (cos η + p₀) / 2` in Cartesian form (`p₀ = cos χ`). -/
def cartOmega (η p₀ : ℝ) : ℝ := (cos η + p₀) / 2

/-- The Minkowski time `t = sin η / ω`. -/
def cartT (η p₀ : ℝ) : ℝ := sin η / cartOmega η p₀

/-- The Minkowski position `x⃗ = p⃗ / ω`, for `p⃗ ∈ ℝ³`. -/
def cartX (η p₀ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (cartOmega η p₀)⁻¹ • p

/-- On the axis `p = (1, 0)` the conformal factor is `cos² (η/2)`. -/
theorem cartOmega_axis (η : ℝ) : cartOmega η 1 = cos (η / 2) ^ 2 := by
  unfold cartOmega
  have := cos_sq (η / 2)
  rw [show 2 * (η / 2) = η by ring] at this
  linarith

/-- On the axis the Minkowski time is `t = 2 tan (η/2)` (where `cos (η/2) ≠ 0`). -/
theorem cartT_axis {η : ℝ} (h : cos (η / 2) ≠ 0) : cartT η 1 = 2 * tan (η / 2) := by
  unfold cartT
  rw [cartOmega_axis, tan_eq_sin_div_cos]
  have h2 : sin η = 2 * sin (η / 2) * cos (η / 2) := by
    rw [← sin_two_mul]; congr 1; ring
  rw [h2]
  field_simp

/-- On the axis the Minkowski position is `x⃗ = 0`: the axis is mapped to the axis `r = 0`. -/
theorem cartX_axis (η : ℝ) : cartX η 1 0 = 0 := by
  simp [cartX]

/-- **The embedding is conformal, axis included** (Carroll (7.100) in Cartesian form): for `(p₀, p⃗)` on the unit
sphere and a tangent vector `a ∂_η + (v₀, v⃗)` with `p₀ v₀ + ⟨p⃗, v⃗⟩ = 0`, and `ω ≠ 0`, the differential of
`(η, p) ↦ (t, x⃗)` carries it to `(dt, dx⃗)` with `-dt² + |dx⃗|² = ω⁻² (-a² + v₀² + |v⃗|²)`. -/
theorem minkowski_eq_conformal_esu_cartesian (η a p₀ v₀ : ℝ) (p v : EuclideanSpace ℝ (Fin 3))
    (hp : p₀ ^ 2 + ‖p‖ ^ 2 = 1) (hv : p₀ * v₀ + @inner ℝ _ _ p v = 0) (hω : cartOmega η p₀ ≠ 0) :
    let ω := cartOmega η p₀
    let dω := (v₀ - sin η * a) / 2
    let dt := cos η * a / ω - sin η * dω / ω ^ 2
    let dx : EuclideanSpace ℝ (Fin 3) := ω⁻¹ • v - (dω / ω ^ 2) • p
    (-dt ^ 2 + ‖dx‖ ^ 2) = ω⁻¹ ^ 2 * (-a ^ 2 + v₀ ^ 2 + ‖v‖ ^ 2) := by
  intro ω dω dt dx
  have hω : ω ≠ 0 := hω
  have hn : ‖dx‖ ^ 2 = (ω⁻¹) ^ 2 * ‖v‖ ^ 2 - 2 * (ω⁻¹ * (dω / ω ^ 2)) * @inner ℝ _ _ v p
      + (dω / ω ^ 2) ^ 2 * ‖p‖ ^ 2 := by
    simp only [dx, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, real_inner_comm p v]
    simp
    ring
  rw [hn]
  have hpv : @inner ℝ _ _ v p = -(p₀ * v₀) := by rw [real_inner_comm]; linarith
  rw [hpv]
  have hp' : ‖p‖ ^ 2 = 1 - p₀ ^ 2 := by linarith
  rw [hp']
  have hωdef : 2 * ω = cos η + p₀ := by simp only [ω, cartOmega]; ring
  have hc : cos η = 2 * ω - p₀ := by linarith
  have hs : sin η ^ 2 = 1 - (2 * ω - p₀) ^ 2 := by
    have := sin_sq_add_cos_sq η
    rw [hc] at this; linarith
  simp only [dt, dω]
  clear_value ω
  rw [hc]
  have hω2 : ω ≠ 0 := hω
  field_simp
  linear_combination (-(sin η ^ 2) * a ^ 2 + 2 * sin η * a * v₀ - 4 * a ^ 2 * ω ^ 2 - v₀ ^ 2) * hs

/-- Non-vacuity: the hypotheses hold on the axis `η = 0`, `p = (1, 0)`, with the tangent vector `a = 1`, `v₀ = 0`,
`v⃗ = e₀`; there `ω = 1`, and the identity reads `-1 + 1 = 1 * (-1 + 0 + 1)`. -/
example : cartOmega 0 1 ≠ 0 ∧ (1 : ℝ) ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 1 ∧
    (1 : ℝ) * 0 + @inner ℝ _ _ (0 : EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single 0 1) = 0 := by
  refine ⟨by simp [cartOmega], by simp, by simp⟩

end Lightlike

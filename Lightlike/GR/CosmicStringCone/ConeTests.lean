module

public import Lightlike.GR.CosmicStringCone.ConeHolonomy

/-!
# Trust checks for the conical metric (row G1-048, milestone CO26)

Source `hindmarsh-kibble-1995`, eq. (6.1). Three sanity checks of the statements of
`ConeFlat` and `ConeHolonomy`:

* `coneMetric_one`, `isFlatOn_cone_one`, `circleTransport_trivial_of_mu_zero`: for `μ = 0`
  (`a = 1`) the metric is Minkowski space in cylindrical coordinates and the holonomy is trivial.
* `coneMetric_zero_degenerate`, `not_isCoordMetric_cone_zero`: for `4Gμ = 1` (`a = 0`) the metric
  degenerates (`g_{θθ} = 0`), so the hypothesis `a ≠ 0` of the main statements cannot be dropped.
* `circleTransport_nontrivial`: for `0 < Gμ < 1/8` the holonomy is not trivial, i.e. the factor
  `1 − 4Gμ` is what produces the holonomy (the metric without the factor is the case `a = 1`).
-/

@[expose] public section

open Matrix
open scoped Real

noncomputable section

namespace Lightlike

namespace StringCone

/-- `μ = 0`: the conical metric is `−dt² + dz² + dr² + r² dθ²`, Minkowski in cylindrical
coordinates. -/
theorem coneMetric_one (y : Fin 4 → ℝ) :
    coneMetric 1 y = Matrix.diagonal ![-1, 1, 1, (y 2) ^ 2] := by
  simp [coneMetric]

/-- `μ = 0`: the metric is flat off the axis. -/
theorem isFlatOn_cone_one : IsFlatOn (coneMetric 1) coneRegion :=
  isFlatOn_cone one_ne_zero

/-- `μ = 0`: parallel transport around the axis has trivial holonomy. -/
theorem circleTransport_trivial_of_mu_zero {G t₀ z₀ r₀ : ℝ} (hr : r₀ ≠ 0)
    {v : ℝ → Fin 4 → ℝ} (h : IsCircleTransport (1 - 4 * G * 0) t₀ z₀ r₀ v) :
    v (2 * π) = v 0 := by
  have ha : (1 - 4 * G * 0 : ℝ) ≠ 0 := by simp
  obtain ⟨h0, h1, h2, h3⟩ := circleTransport_holonomy (G := G) (μ := 0) ha hr h
  simp only [mul_zero, sub_zero, one_mul, Real.sin_zero, Real.cos_zero, zero_mul] at h2 h3
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · simpa using h2
  · simpa [hr] using h3

/-- `4Gμ = 1` (`a = 0`): the metric component `g_{θθ}` vanishes, the metric degenerates. -/
theorem coneMetric_zero_degenerate (y : Fin 4 → ℝ) : coneMetric 0 y 3 3 = 0 := by
  simp [coneMetric]

/-- `4Gμ = 1`: the conical metric is not a coordinate metric on the region off the axis (its
determinant vanishes), so the hypothesis `a ≠ 0` is needed. -/
theorem not_isCoordMetric_cone_zero : ¬ IsCoordMetric (coneMetric 0) coneRegion := by
  intro h
  have hx : (![0, 0, 1, 0] : Fin 4 → ℝ) ∈ coneRegion := by simp [coneRegion]
  have := h.isUnit_det _ hx
  simp [coneMetric, Matrix.det_diagonal, Fin.prod_univ_four] at this

/-- **The holonomy is nontrivial** for `0 < Gμ < 1/8`: a parallel transported vector does not
return to itself after one turn around the axis. (For the metric without the factor `1 − 4Gμ`,
i.e. `μ = 0`, it does: `circleTransport_trivial_of_mu_zero`.) -/
theorem circleTransport_nontrivial {G μ : ℝ} (hpos : 0 < G * μ) (hsmall : G * μ < 1 / 8)
    {r₀ : ℝ} (hr : r₀ ≠ 0) (t₀ z₀ : ℝ) :
    ∃ v : ℝ → Fin 4 → ℝ, IsCircleTransport (1 - 4 * G * μ) t₀ z₀ r₀ v ∧ v (2 * π) ≠ v 0 := by
  have ha : (1 - 4 * G * μ : ℝ) ≠ 0 := by
    have : 4 * G * μ = 4 * (G * μ) := by ring
    intro h; linarith
  obtain ⟨hT, h0⟩ := circleTransport_exists ha hr t₀ z₀ (Pi.single 2 1)
  refine ⟨coneTransport (1 - 4 * G * μ) r₀ (Pi.single 2 1), hT, ?_⟩
  intro heq
  obtain ⟨-, -, -, h3⟩ := circleTransport_holonomy ha hr hT
  rw [h0, heq] at h3
  have hs : 0 < Real.sin (8 * π * G * μ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : 8 * π * G * μ = 8 * π * (G * μ) := by ring
      rw [this]; positivity
    · have : 8 * π * G * μ = 8 * (G * μ) * π := by ring
      rw [this]; nlinarith [Real.pi_pos]
  simp at h3
  rw [h0] at h3
  simp at h3
  linarith

end StringCone

end Lightlike

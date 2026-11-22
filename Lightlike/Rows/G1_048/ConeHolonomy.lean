module

public import Lightlike.Rows.G1_048.ConeFlat

/-!
# Holonomy of the conical metric around the axis

Row G1-048 (milestone CO26; source `hindmarsh-kibble-1995`, eq. (6.1)). Parallel transport of a
vector `v(s) ∈ ℝ⁴` (components in the coordinates `(t, z, r, θ)`) along the circle
`s ↦ (t₀, z₀, r₀, s)`, `r₀ > 0`, is the equation `v'^i = −Σ_k Γ^i_{θ k} v^k`, with the Christoffel
symbols of the library (`christoffel (coneMetric a)`).

* `IsCircleTransport a t₀ z₀ r₀ v`: `v` solves this equation for all `s`.
* `circleTransport_rotation`: for `a ≠ 0`, `r₀ ≠ 0`, the components `v^t, v^z` are constant, and
  in the orthonormal frame `(e_r, e_θ/(a r₀))` with `w = a r₀ v^θ`,
  `(v^r, w)(s) = Rot(a s) (v^r, w)(0)`, `Rot(φ) = [[cos φ, sin φ], [−sin φ, cos φ]]`.
* `circleTransport_holonomy`: around the loop `s = 2π` the rotation angle is `2π a = 2π − 8πGμ`
  for `a = 1 − 4Gμ`; as `cos (2π − 8πGμ) = cos (8πGμ)` and `sin (2π − 8πGμ) = −sin (8πGμ)`, the
  holonomy is the rotation by `8πGμ` in the `(e_r, e_θ/(a r₀))` plane.
* `circleTransport_exists`: the explicit solution with any initial value.

The identification of `μ` with the energy per unit length is not proved; `a` is a parameter.
-/

@[expose] public section

open Matrix
open scoped Real

noncomputable section

namespace Lightlike

namespace StringCone

/-- The circle `s ↦ (t₀, z₀, r₀, s)` of constant `t, z, r` around the axis. -/
def circ (t₀ z₀ r₀ : ℝ) (s : ℝ) : Fin 4 → ℝ := ![t₀, z₀, r₀, s]

/-- `v` is parallel along the circle `circ t₀ z₀ r₀`: for all `s` and `i`,
`dv^i/ds = −Σ_k Γ^i_{θ k}(γ(s)) v^k` (the tangent of the circle is `∂_θ`). -/
def IsCircleTransport (a t₀ z₀ r₀ : ℝ) (v : ℝ → Fin 4 → ℝ) : Prop :=
  ∀ (s : ℝ) (i : Fin 4), HasDerivAt (fun s => v s i)
    (-∑ k, christoffel (coneMetric a) i 3 k (circ t₀ z₀ r₀ s) * v s k) s

lemma circ_two (t₀ z₀ r₀ s : ℝ) : circ t₀ z₀ r₀ s 2 = r₀ := by simp [circ]

/-- The transport equation in components. -/
lemma circleTransport_components {a t₀ z₀ r₀ : ℝ} (ha : a ≠ 0) (hr : r₀ ≠ 0)
    {v : ℝ → Fin 4 → ℝ} (h : IsCircleTransport a t₀ z₀ r₀ v) (s : ℝ) :
    HasDerivAt (fun s => v s 0) 0 s ∧ HasDerivAt (fun s => v s 1) 0 s ∧
    HasDerivAt (fun s => v s 2) (a ^ 2 * r₀ * v s 3) s ∧
    HasDerivAt (fun s => v s 3) (-(v s 2) / r₀) s := by
  have hx : ∀ s, circ t₀ z₀ r₀ s 2 ≠ 0 := fun s => by rw [circ_two]; exact hr
  have key : ∀ i : Fin 4, -∑ k, christoffel (coneMetric a) i 3 k (circ t₀ z₀ r₀ s) * v s k =
      -∑ k, coneGamma a i 3 k (circ t₀ z₀ r₀ s) * v s k := fun i => by
    simp only [christoffel_cone ha i 3 _ (hx s)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h s 0
    rw [key] at this
    simpa [Fin.sum_univ_four, coneGamma] using this
  · have := h s 1
    rw [key] at this
    simpa [Fin.sum_univ_four, coneGamma] using this
  · have := h s 2
    rw [key] at this
    simpa [Fin.sum_univ_four, coneGamma, circ_two] using this
  · have := h s 3
    rw [key] at this
    simp [coneGamma, circ_two] at this
    convert this using 1
    ring

/-- **Parallel transport around the axis is a rotation** (for `a ≠ 0`, `r₀ ≠ 0`): `v^t, v^z` are
constant and, with `w = a r₀ v^θ` (the component in the orthonormal frame `e_θ/(a r₀)`),
`v^r(s) = cos(a s) v^r(0) + sin(a s) w(0)`, `w(s) = −sin(a s) v^r(0) + cos(a s) w(0)`. -/
theorem circleTransport_rotation {a t₀ z₀ r₀ : ℝ} (ha : a ≠ 0) (hr : r₀ ≠ 0)
    {v : ℝ → Fin 4 → ℝ} (h : IsCircleTransport a t₀ z₀ r₀ v) (s : ℝ) :
    v s 0 = v 0 0 ∧ v s 1 = v 0 1 ∧
    v s 2 = Real.cos (a * s) * v 0 2 + Real.sin (a * s) * (a * r₀ * v 0 3) ∧
    a * r₀ * v s 3 = -Real.sin (a * s) * v 0 2 + Real.cos (a * s) * (a * r₀ * v 0 3) := by
  have hc := circleTransport_components ha hr h
  have hd0 : Differentiable ℝ (fun s => v s 0) := fun s => (hc s).1.differentiableAt
  have hd1 : Differentiable ℝ (fun s => v s 1) := fun s => (hc s).2.1.differentiableAt
  refine ⟨?_, ?_, ?_⟩
  · exact is_const_of_deriv_eq_zero hd0 (fun x => (hc x).1.deriv) s 0
  · exact is_const_of_deriv_eq_zero hd1 (fun x => (hc x).2.1.deriv) s 0
  -- the two conserved quantities
  have hcos : ∀ s : ℝ, HasDerivAt (fun s => Real.cos (a * s)) (-Real.sin (a * s) * a) s := by
    intro s
    have := (Real.hasDerivAt_cos (a * s)).comp s ((hasDerivAt_id s).const_mul a)
    simpa [Function.comp_def] using this
  have hsin : ∀ s : ℝ, HasDerivAt (fun s => Real.sin (a * s)) (Real.cos (a * s) * a) s := by
    intro s
    have := (Real.hasDerivAt_sin (a * s)).comp s ((hasDerivAt_id s).const_mul a)
    simpa [Function.comp_def] using this
  have hw : ∀ s : ℝ, HasDerivAt (fun s => a * r₀ * v s 3) (-(a * v s 2)) s := by
    intro s
    have := (hc s).2.2.2.const_mul (a * r₀)
    convert this using 1
    field_simp
  have hA : ∀ s : ℝ, HasDerivAt
      (fun s => v s 2 * Real.cos (a * s) - (a * r₀ * v s 3) * Real.sin (a * s)) 0 s := by
    intro s
    have := (((hc s).2.2.1).mul (hcos s)).sub ((hw s).mul (hsin s))
    convert this using 1
    ring
  have hB : ∀ s : ℝ, HasDerivAt
      (fun s => v s 2 * Real.sin (a * s) + (a * r₀ * v s 3) * Real.cos (a * s)) 0 s := by
    intro s
    have := (((hc s).2.2.1).mul (hsin s)).add ((hw s).mul (hcos s))
    convert this using 1
    ring
  have hA' := is_const_of_deriv_eq_zero (fun s => (hA s).differentiableAt)
    (fun x => (hA x).deriv) s 0
  have hB' := is_const_of_deriv_eq_zero (fun s => (hB s).differentiableAt)
    (fun x => (hB x).deriv) s 0
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, sub_zero, zero_add] at hA' hB'
  have hsc := Real.sin_sq_add_cos_sq (a * s)
  constructor
  · calc v s 2 = (v s 2 * Real.cos (a * s) - (a * r₀ * v s 3) * Real.sin (a * s)) *
          Real.cos (a * s) + (v s 2 * Real.sin (a * s) + (a * r₀ * v s 3) * Real.cos (a * s)) *
          Real.sin (a * s) := by linear_combination (-(v s 2)) * hsc
      _ = _ := by rw [hA', hB']; ring
  · calc a * r₀ * v s 3 = (v s 2 * Real.sin (a * s) + (a * r₀ * v s 3) * Real.cos (a * s)) *
          Real.cos (a * s) - (v s 2 * Real.cos (a * s) - (a * r₀ * v s 3) * Real.sin (a * s)) *
          Real.sin (a * s) := by linear_combination (-(a * r₀ * v s 3)) * hsc
      _ = _ := by rw [hA', hB']; ring

/-- **Holonomy around the axis** (CO26): for `a = 1 − 4Gμ ≠ 0` and `r₀ ≠ 0`, parallel transport
once around the axis (`s = 2π`) leaves `v^t, v^z` unchanged and rotates `(v^r, w)`,
`w = a r₀ v^θ` the component in the orthonormal frame `e_θ/(a r₀)`, by the angle `8πGμ`:
`v^r ↦ cos(8πGμ) v^r − sin(8πGμ) w`, `w ↦ sin(8πGμ) v^r + cos(8πGμ) w`. -/
theorem circleTransport_holonomy {G μ t₀ z₀ r₀ : ℝ} (ha : 1 - 4 * G * μ ≠ 0) (hr : r₀ ≠ 0)
    {v : ℝ → Fin 4 → ℝ} (h : IsCircleTransport (1 - 4 * G * μ) t₀ z₀ r₀ v) :
    v (2 * π) 0 = v 0 0 ∧ v (2 * π) 1 = v 0 1 ∧
    v (2 * π) 2 = Real.cos (8 * π * G * μ) * v 0 2 -
      Real.sin (8 * π * G * μ) * ((1 - 4 * G * μ) * r₀ * v 0 3) ∧
    (1 - 4 * G * μ) * r₀ * v (2 * π) 3 = Real.sin (8 * π * G * μ) * v 0 2 +
      Real.cos (8 * π * G * μ) * ((1 - 4 * G * μ) * r₀ * v 0 3) := by
  obtain ⟨h0, h1, h2, h3⟩ := circleTransport_rotation ha hr h (2 * π)
  have e : (1 - 4 * G * μ) * (2 * π) = -(8 * π * G * μ) + 2 * π := by ring
  rw [e, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_neg, Real.sin_neg] at h2 h3
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [h2]; ring
  · rw [h3]; ring

/-- Converse of `circleTransport_components`: the four component equations give a transport. -/
lemma isCircleTransport_of_components {a t₀ z₀ r₀ : ℝ} (ha : a ≠ 0) (hr : r₀ ≠ 0)
    {v : ℝ → Fin 4 → ℝ}
    (h : ∀ s, HasDerivAt (fun s => v s 0) 0 s ∧ HasDerivAt (fun s => v s 1) 0 s ∧
      HasDerivAt (fun s => v s 2) (a ^ 2 * r₀ * v s 3) s ∧
      HasDerivAt (fun s => v s 3) (-(v s 2) / r₀) s) :
    IsCircleTransport a t₀ z₀ r₀ v := by
  intro s i
  have hx : circ t₀ z₀ r₀ s 2 ≠ 0 := by rw [circ_two]; exact hr
  have key : ∀ i : Fin 4, -∑ k, christoffel (coneMetric a) i 3 k (circ t₀ z₀ r₀ s) * v s k =
      -∑ k, coneGamma a i 3 k (circ t₀ z₀ r₀ s) * v s k := fun i => by
    simp only [christoffel_cone ha i 3 _ hx]
  rw [key]
  obtain ⟨h0, h1, h2, h3⟩ := h s
  fin_cases i
  · simpa [Fin.sum_univ_four, coneGamma] using h0
  · simpa [Fin.sum_univ_four, coneGamma] using h1
  · simpa [Fin.sum_univ_four, coneGamma, circ_two] using h2
  · simp [coneGamma, circ_two]
    convert h3 using 1
    ring

/-- The explicit parallel transport around the circle with initial value `u`. -/
def coneTransport (a r₀ : ℝ) (u : Fin 4 → ℝ) (s : ℝ) : Fin 4 → ℝ :=
  ![u 0, u 1, Real.cos (a * s) * u 2 + Real.sin (a * s) * (a * r₀ * u 3),
    (-Real.sin (a * s) * u 2 + Real.cos (a * s) * (a * r₀ * u 3)) / (a * r₀)]

/-- **Existence of the parallel transport** around the circle, with any initial vector. -/
theorem circleTransport_exists {a r₀ : ℝ} (ha : a ≠ 0) (hr : r₀ ≠ 0) (t₀ z₀ : ℝ)
    (u : Fin 4 → ℝ) :
    IsCircleTransport a t₀ z₀ r₀ (coneTransport a r₀ u) ∧ coneTransport a r₀ u 0 = u := by
  refine ⟨isCircleTransport_of_components ha hr (fun s => ?_), ?_⟩
  · have hcos : HasDerivAt (fun s => Real.cos (a * s)) (-Real.sin (a * s) * a) s := by
      have := (Real.hasDerivAt_cos (a * s)).comp s ((hasDerivAt_id s).const_mul a)
      simpa [Function.comp_def] using this
    have hsin : HasDerivAt (fun s => Real.sin (a * s)) (Real.cos (a * s) * a) s := by
      have := (Real.hasDerivAt_sin (a * s)).comp s ((hasDerivAt_id s).const_mul a)
      simpa [Function.comp_def] using this
    have har : a * r₀ ≠ 0 := mul_ne_zero ha hr
    refine ⟨by simpa [coneTransport] using hasDerivAt_const s (u 0),
      by simpa [coneTransport] using hasDerivAt_const s (u 1), ?_, ?_⟩
    · have := (hcos.mul_const (u 2)).add (hsin.mul_const (a * r₀ * u 3))
      simp only [coneTransport, Matrix.cons_val]
      convert this using 1
      field_simp
    · have := ((hsin.neg.mul_const (u 2)).add (hcos.mul_const (a * r₀ * u 3))).div_const (a * r₀)
      simp only [coneTransport, Matrix.cons_val]
      convert this using 1
      field_simp
      ring
  · funext i
    fin_cases i
    · simp [coneTransport]
    · simp [coneTransport]
    · simp [coneTransport]
    · simp [coneTransport]
      field_simp

end StringCone

end Lightlike

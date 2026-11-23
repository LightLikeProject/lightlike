import Mathlib

/-!
# Cosmic no-hair for the Bianchi models other than type IX (G1-041)

The cosmic no-hair theorem of Wald (1983) says that a spatially homogeneous cosmology with a positive
cosmological constant `Λ`, whose spatial slices are of Bianchi type other than IX (so that the scalar
curvature of the slices is `≤ 0`) and whose matter satisfies the strong energy condition, expands forever
and approaches de Sitter space: the Hubble rate tends to `√(Λ/3)`, and the shear, the matter density and the
spatial curvature tend to `0`, exponentially fast.

This file proves the theorem for the **scalar system of a Bianchi model**: the equations that every
spatially homogeneous cosmology in the orthonormal frame of the unit normal `u` of the slices obeys,
with `8πG = c = 1`, mean expansion rate `H = θ/3`, density `ρ`, pressure `p` (the isotropic part of the
stress), shear scalar `σ² = ½ σ_{ab}σ^{ab}` and scalar curvature `R` of the slices:

* the Raychaudhuri equation `H' = -H² - (2/3) σ² - (ρ + 3p)/6 + Λ/3` (`IsSolution.hasDerivAt`);
* the Hamiltonian constraint `3H² = ρ + Λ + σ² - R/2` (`IsSolution.constraint`).

The sign of `R` is the only place where the Bianchi type enters: it is `≤ 0` for the types I–VIII, and a
type IX slice (a deformed 3-sphere) can have `R > 0`.

**Limits.** The two equations are taken as the definition of the model (`IsSolution`); that every Bianchi
cosmology satisfies them is the classification and the field equations of the Bianchi models
(Ellis–MacCallum), not formalized here. The shear is a scalar `σ² ≥ 0` and its evolution equation is not
used (it is not needed). The dominant energy condition of Wald's statement is not needed either; only the
strong one and `ρ ≥ 0` are used. Units `8πG = c = 1`.

Source: Rendall, *Intermediate inflation and the slow-roll approximation*, Section 4 (rendall-2005).
-/

open Set Filter Topology

namespace Lightlike
namespace Cosmology
namespace Bianchi

/-- The de Sitter expansion rate `√(Λ/3)` of the cosmological constant `Λ`. -/
noncomputable def deSitterRate (Λ : ℝ) : ℝ := Real.sqrt (Λ / 3)

lemma deSitterRate_sq {Λ : ℝ} (hΛ : 0 ≤ Λ) : deSitterRate Λ ^ 2 = Λ / 3 :=
  Real.sq_sqrt (by positivity)

lemma deSitterRate_pos {Λ : ℝ} (hΛ : 0 < Λ) : 0 < deSitterRate Λ :=
  Real.sqrt_pos.2 (by positivity)

/-- **The scalar system of a spatially homogeneous cosmology** from the time `t₀` on, with cosmological
constant `Λ`: the mean expansion rate `H`, the density `ρ`, the pressure `p`, the shear scalar `σ2` and the
scalar curvature `R` of the slices obey Raychaudhuri's equation and the Hamiltonian constraint
(`8πG = c = 1`). -/
structure IsSolution (Λ t₀ : ℝ) (H ρ p σ2 R : ℝ → ℝ) : Prop where
  /-- Raychaudhuri's equation `H' = -H² - (2/3) σ² - (ρ + 3p)/6 + Λ/3`. -/
  hasDerivAt : ∀ t, t₀ ≤ t →
    HasDerivAt H (-(H t) ^ 2 - 2 / 3 * σ2 t - (ρ t + 3 * p t) / 6 + Λ / 3) t
  /-- The Hamiltonian constraint `3H² = ρ + Λ + σ² - R/2`. -/
  constraint : ∀ t, t₀ ≤ t → 3 * (H t) ^ 2 = ρ t + Λ + σ2 t - R t / 2

/-- **The hypotheses of the no-hair theorem**: nonnegative density and shear, the strong energy condition
`ρ + 3p ≥ 0`, and nonpositive spatial curvature (the Bianchi types other than IX). -/
structure IsAdmissible (t₀ : ℝ) (ρ p σ2 R : ℝ → ℝ) : Prop where
  rho_nonneg : ∀ t, t₀ ≤ t → 0 ≤ ρ t
  strong : ∀ t, t₀ ≤ t → 0 ≤ ρ t + 3 * p t
  shear_nonneg : ∀ t, t₀ ≤ t → 0 ≤ σ2 t
  curvature_nonpos : ∀ t, t₀ ≤ t → R t ≤ 0

variable {Λ t₀ : ℝ} {H ρ p σ2 R : ℝ → ℝ}

/-- The expansion rate is at least the de Sitter rate in absolute value: `Λ/3 ≤ H²`. -/
lemma sq_ge (hs : IsSolution Λ t₀ H ρ p σ2 R) (ha : IsAdmissible t₀ ρ p σ2 R) {t : ℝ} (ht : t₀ ≤ t) :
    Λ / 3 ≤ H t ^ 2 := by
  have := hs.constraint t ht
  have := ha.rho_nonneg t ht
  have := ha.shear_nonneg t ht
  have := ha.curvature_nonpos t ht
  linarith

/-- **An expanding model expands at least at the de Sitter rate**: if `Λ > 0` and `H(t₀) > 0`, then
`H(t) ≥ √(Λ/3)` for every `t ≥ t₀`. -/
theorem rate_ge (hΛ : 0 < Λ) (hs : IsSolution Λ t₀ H ρ p σ2 R) (ha : IsAdmissible t₀ ρ p σ2 R)
    (h0 : 0 < H t₀) {t : ℝ} (ht : t₀ ≤ t) : deSitterRate Λ ≤ H t := by
  have hL := deSitterRate_pos hΛ
  have hL2 := deSitterRate_sq hΛ.le
  by_contra hlt
  rw [not_le] at hlt
  have hle : H t ≤ -deSitterRate Λ := by
    by_contra h
    rw [not_le] at h
    have := sq_ge hs ha ht
    nlinarith
  have hcont : ContinuousOn H (Icc t₀ t) := fun s hs' =>
    (hs.hasDerivAt s hs'.1).continuousAt.continuousWithinAt
  obtain ⟨s, hsmem, hs0⟩ := intermediate_value_Icc' ht hcont
    (show (0 : ℝ) ∈ Icc (H t) (H t₀) from ⟨by linarith, h0.le⟩)
  have := sq_ge hs ha hsmem.1
  rw [hs0] at this
  nlinarith

/-- The Raychaudhuri inequality `H' ≤ -(H² - Λ/3)`: the shear and the strong energy condition only
decelerate. -/
lemma deriv_le (ha : IsAdmissible t₀ ρ p σ2 R) (hΛ : 0 ≤ Λ) {t : ℝ} (ht : t₀ ≤ t) :
    -(H t) ^ 2 - 2 / 3 * σ2 t - (ρ t + 3 * p t) / 6 + Λ / 3 ≤
      -((H t - deSitterRate Λ) * (H t + deSitterRate Λ)) := by
  have h1 := ha.strong t ht
  have h2 := ha.shear_nonneg t ht
  have h3 := deSitterRate_sq hΛ
  nlinarith

/-- **Exponential approach of the expansion rate to the de Sitter rate**: if `Λ > 0` and the model
expands at `t₀`, then `0 ≤ H(t) - √(Λ/3) ≤ (H(t₀) - √(Λ/3)) e^{-2√(Λ/3)(t - t₀)}` for `t ≥ t₀`. -/
theorem rate_sub_le (hΛ : 0 < Λ) (hs : IsSolution Λ t₀ H ρ p σ2 R) (ha : IsAdmissible t₀ ρ p σ2 R)
    (h0 : 0 < H t₀) {t : ℝ} (ht : t₀ ≤ t) :
    H t - deSitterRate Λ ≤
      (H t₀ - deSitterRate Λ) * Real.exp (-(2 * deSitterRate Λ * (t - t₀))) := by
  set L := deSitterRate Λ with hLdef
  have hL : 0 < L := deSitterRate_pos hΛ
  let f : ℝ → ℝ := fun s => (H s - L) * Real.exp (2 * L * (s - t₀))
  have hf : ∀ s, t₀ ≤ s → HasDerivAt f
      ((-(H s) ^ 2 - 2 / 3 * σ2 s - (ρ s + 3 * p s) / 6 + Λ / 3) * Real.exp (2 * L * (s - t₀)) +
        (H s - L) * (Real.exp (2 * L * (s - t₀)) * (2 * L))) s := by
    intro s hsn
    have h1 := (hs.hasDerivAt s hsn).sub_const L
    have h2 : HasDerivAt (fun s => Real.exp (2 * L * (s - t₀))) (Real.exp (2 * L * (s - t₀)) * (2 * L)) s := by
      have := ((hasDerivAt_id s).sub_const t₀).const_mul (2 * L)
      simpa using this.exp
    exact h1.mul h2
  have hanti : AntitoneOn f (Set.Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
    · exact fun s hsn => (hf s hsn).continuousAt.continuousWithinAt
    · intro s hsn
      rw [interior_Ici] at hsn
      exact (hf s (le_of_lt hsn)).differentiableAt.differentiableWithinAt
    · intro s hsn
      rw [interior_Ici] at hsn
      have hsn' : t₀ ≤ s := le_of_lt hsn
      rw [(hf s hsn').deriv]
      have hd := deriv_le (H := H) ha hΛ.le hsn'
      have hex := Real.exp_pos (2 * L * (s - t₀))
      have hge := rate_ge hΛ hs ha h0 hsn'
      have hmul : (-(H s) ^ 2 - 2 / 3 * σ2 s - (ρ s + 3 * p s) / 6 + Λ / 3 + 2 * L * (H s - L)) ≤ 0 := by
        nlinarith
      nlinarith
  have hft := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp only [f, sub_self, mul_zero, Real.exp_zero, mul_one] at hft
  have hneg : Real.exp (-(2 * L * (t - t₀))) * Real.exp (2 * L * (t - t₀)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(2 * L * (t - t₀)))
  calc H t - L = (H t - L) * Real.exp (2 * L * (t - t₀)) * Real.exp (-(2 * L * (t - t₀))) := by
        rw [mul_assoc, mul_comm (Real.exp _), hneg, mul_one]
    _ ≤ (H t₀ - L) * Real.exp (-(2 * L * (t - t₀))) := by
        exact mul_le_mul_of_nonneg_right hft hpos.le

/-- **Cosmic no-hair for the Bianchi models other than type IX, quantitative form** (Wald 1983; Rendall
2005, Section 4). Let `Λ > 0`, let the model be expanding at `t₀`, satisfy the strong energy condition,
`ρ ≥ 0`, and have slices of nonpositive scalar curvature. Put `L = √(Λ/3)`, `E = e^{-2L(t - t₀)}` and
`C = 3 (H(t₀)² - L²)`. Then for every `t ≥ t₀`: `L ≤ H(t) ≤ L + (H(t₀) - L) E`, and the density, the
shear and the curvature are bounded by `ρ ≤ C E`, `σ² ≤ C E`, `-R ≤ 2 C E`. -/
theorem no_hair_bounds (hΛ : 0 < Λ) (hs : IsSolution Λ t₀ H ρ p σ2 R)
    (ha : IsAdmissible t₀ ρ p σ2 R) (h0 : 0 < H t₀) {t : ℝ} (ht : t₀ ≤ t) :
    deSitterRate Λ ≤ H t ∧
    H t ≤ deSitterRate Λ + (H t₀ - deSitterRate Λ) * Real.exp (-(2 * deSitterRate Λ * (t - t₀))) ∧
    ρ t ≤ 3 * (H t₀ ^ 2 - deSitterRate Λ ^ 2) * Real.exp (-(2 * deSitterRate Λ * (t - t₀))) ∧
    σ2 t ≤ 3 * (H t₀ ^ 2 - deSitterRate Λ ^ 2) * Real.exp (-(2 * deSitterRate Λ * (t - t₀))) ∧
    -R t ≤ 2 * (3 * (H t₀ ^ 2 - deSitterRate Λ ^ 2) *
      Real.exp (-(2 * deSitterRate Λ * (t - t₀)))) := by
  set L := deSitterRate Λ with hLdef
  set E := Real.exp (-(2 * L * (t - t₀))) with hE
  have hL : 0 < L := deSitterRate_pos hΛ
  have hL2 : L ^ 2 = Λ / 3 := deSitterRate_sq hΛ.le
  have hge := rate_ge hΛ hs ha h0 ht
  have hge0 := rate_ge hΛ hs ha h0 (le_refl t₀)
  have hle := rate_sub_le hΛ hs ha h0 ht
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    have : 0 ≤ t - t₀ := by linarith
    nlinarith
  have hHle : H t ≤ H t₀ := by nlinarith
  have hc := hs.constraint t ht
  have h1 := ha.rho_nonneg t ht
  have h2 := ha.shear_nonneg t ht
  have h3 := ha.curvature_nonpos t ht
  have hprod : (H t - L) * (H t + L) ≤ (H t₀ - L) * E * (H t₀ + L) := by
    apply mul_le_mul hle (by linarith) (by linarith) (by nlinarith)
  have hsum : ρ t + σ2 t - R t / 2 = 3 * ((H t - L) * (H t + L)) := by nlinarith
  refine ⟨hge, by linarith, ?_, ?_, ?_⟩ <;> nlinarith

end Bianchi
end Cosmology
end Lightlike

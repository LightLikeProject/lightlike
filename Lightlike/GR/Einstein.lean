module

public import Lightlike.Spacetime.Curvature

/-!
# Einstein's equations in vacuum

* `einsteinTensor g = Ric − ½ R g`.
* `IsVacuumSolution Λ g U` : `g` is a coordinate metric on the open set `U` (smooth, symmetric,
  invertible - see `IsCoordMetric`) and `G_{μν} + Λ g_{μν} = 0` on `U`.
* `minkowski_isVacuumSolution` : Minkowski space solves the vacuum equations with `Λ = 0` on `ℝⁿ`.
* `minkowski_not_vacuumSolution_of_ne_zero` : …and with no other `Λ`, on any nonempty `U`.
* `vacuum_iff_ricci_eq_zero` : for `n ≠ 2`, the vacuum equations (`Λ = 0`) on `U` are equivalent to
  Ricci-flatness on `U`.
* `einstein_eq_zero_iff_ricci_eq_zero` : in spacetime dimension `n ≠ 2`, for a symmetric invertible
  metric, `G = 0 ↔ Ric = 0` (trace-reversal). This is the standard statement that the vacuum
  equations are "Ricci-flatness".

That Minkowski space solves the vacuum equations follows in one line from flatness
(`R = 0 ⇒ Ric = 0 ⇒ G = 0`); the work is in defining the curvature of a coordinate metric and
computing Minkowski's components.

**References.** R. M. Wald, *General Relativity* (University of Chicago Press, 1984), ch. 4 (Einstein's equation); S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), ch. 4 (gravitation).
-/

@[expose] public section

open Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The Einstein tensor `G_{μν} = R_{μν} − ½ R g_{μν}`. -/
def einsteinTensor (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ricci g μ ν x - (1 / 2) * scalarCurvature g x * g x μ ν

/-- **Vacuum Einstein equations with cosmological constant `Λ` on an open set `U`**: `g` is a
coordinate metric on `U` and `G_{μν} + Λ g_{μν} = 0` at every point of `U`. The `IsCoordMetric`
requirement excludes junk solutions such as `g = 0` (whose Lean "inverse" is `0`). -/
def IsVacuumSolution (Λ : ℝ) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (U : Set (Fin n → ℝ)) : Prop :=
  IsCoordMetric g U ∧ ∀ x ∈ U, ∀ μ ν, einsteinTensor g μ ν x + Λ * g x μ ν = 0

/-- If the Riemann tensor vanishes at `x`, so does the Einstein tensor. -/
lemma einsteinTensor_eq_zero_of_riemann_eq_zero {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → ℝ} (h : ∀ ρ σ μ ν, riemann g ρ σ μ ν x = 0) (μ ν : Fin n) :
    einsteinTensor g μ ν x = 0 := by
  simp [einsteinTensor, ricci_eq_zero_of_riemann_eq_zero h,
    scalarCurvature_eq_zero_of_riemann_eq_zero h]

/-- **Minkowski space solves the vacuum Einstein equations** (with `Λ = 0`) on all of `ℝⁿ`. -/
theorem minkowski_isVacuumSolution (x₀ : Fin n → ℝ) :
    IsVacuumSolution 0 ((minkowskiMetric n).coordMetric x₀) Set.univ := by
  obtain ⟨hg, hR⟩ := minkowski_flat (n := n) x₀
  exact ⟨hg, fun x hx μ ν => by simp [einsteinTensor_eq_zero_of_riemann_eq_zero (hR x hx)]⟩

/-- Minkowski space does **not** solve the vacuum equations with a nonzero cosmological constant
on any nonempty open set (in dimension `n ≥ 1`): there `G = 0` but `Λ η ≠ 0`. -/
theorem minkowski_not_vacuumSolution_of_ne_zero (hn : 0 < n) {Λ : ℝ} (hΛ : Λ ≠ 0)
    (x₀ : Fin n → ℝ) {U : Set (Fin n → ℝ)} (hU : U.Nonempty) :
    ¬ IsVacuumSolution Λ ((minkowskiMetric n).coordMetric x₀) U := by
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := hU
  have := h x hx ⟨0, hn⟩ ⟨0, hn⟩
  rw [einsteinTensor_eq_zero_of_riemann_eq_zero ((minkowski_flat x₀).2 x trivial),
    minkowski_coordMetric] at this
  simp [eta_apply, etaDiag, hΛ] at this

/-- Trace of the metric against its inverse: `g^{μν} g_{μν} = n` for a symmetric invertible `g`. -/
lemma trace_inv_mul_self {G : Matrix (Fin n) (Fin n) ℝ} (hsym : Gᵀ = G) (hdet : IsUnit G.det) :
    ∑ μ, ∑ ν, G⁻¹ μ ν * G μ ν = n := by
  have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have htr : Matrix.trace (G⁻¹ * G) = n := by simp [h1]
  rw [← htr, Matrix.trace]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← hsym, Matrix.transpose_apply, hsym]

/-- **Trace-reversal**: in dimension `n ≠ 2`, at a point where the metric is symmetric and
invertible, the Einstein tensor vanishes iff the Ricci tensor does. Hence the vacuum equations
(`Λ = 0`) say exactly that spacetime is Ricci-flat. -/
theorem einstein_eq_zero_iff_ricci_eq_zero (hn : n ≠ 2)
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hsym : (g x)ᵀ = g x) (hdet : IsUnit (g x).det) :
    (∀ μ ν, einsteinTensor g μ ν x = 0) ↔ (∀ μ ν, ricci g μ ν x = 0) := by
  constructor
  · intro hG
    -- Take the trace: g^{μν} G_{μν} = R − (n/2) R = (1 − n/2) R.
    have htr : ∑ μ, ∑ ν, (g x)⁻¹ μ ν * einsteinTensor g μ ν x =
        (1 - (n : ℝ) / 2) * scalarCurvature g x := by
      simp only [einsteinTensor, mul_sub, Finset.sum_sub_distrib]
      have : ∑ μ, ∑ ν, (g x)⁻¹ μ ν * (1 / 2 * scalarCurvature g x * g x μ ν) =
          (1 / 2 * scalarCurvature g x) * ∑ μ, ∑ ν, (g x)⁻¹ μ ν * g x μ ν := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => by ring
      rw [this, trace_inv_mul_self hsym hdet, scalarCurvature]
      ring
    have hR : scalarCurvature g x = 0 := by
      have h0 : (1 - (n : ℝ) / 2) * scalarCurvature g x = 0 := by
        rw [← htr]; simp [hG]
      have hne : (1 - (n : ℝ) / 2) ≠ 0 := by
        intro h
        apply hn
        have : (n : ℝ) = 2 := by linarith
        exact_mod_cast this
      exact (mul_eq_zero.mp h0).resolve_left hne
    intro μ ν
    have := hG μ ν
    simp only [einsteinTensor, hR] at this
    linarith
  · intro hRic μ ν
    have hR : scalarCurvature g x = 0 := by simp [scalarCurvature, hRic]
    simp [einsteinTensor, hRic, hR]

/-- For `n ≠ 2` and a coordinate metric on `U`, the vacuum equations with `Λ = 0` on `U` are
equivalent to Ricci-flatness on `U`. -/
theorem vacuum_iff_ricci_eq_zero (hn : n ≠ 2) {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {U : Set (Fin n → ℝ)} (hg : IsCoordMetric g U) :
    IsVacuumSolution 0 g U ↔ ∀ x ∈ U, ∀ μ ν, ricci g μ ν x = 0 := by
  constructor
  · rintro ⟨-, h⟩ x hx
    exact (einstein_eq_zero_iff_ricci_eq_zero hn g x (hg.symm x hx) (hg.isUnit_det x hx)).mp
      fun μ ν => by simpa using h x hx μ ν
  · intro h
    refine ⟨hg, fun x hx μ ν => ?_⟩
    have := (einstein_eq_zero_iff_ricci_eq_zero hn g x (hg.symm x hx) (hg.isUnit_det x hx)).mpr
      (h x hx)
    simp [this μ ν]

end Lightlike

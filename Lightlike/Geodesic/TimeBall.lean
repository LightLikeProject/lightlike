import Lightlike.Geodesic.Gauss
import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.CausalLadder.ConeAlgebra
import Lightlike.Spacetime.Causal.ConeConvex

/-!
# Normal balls with a time function

For a Lorentzian coordinate metric `g` on `U`, a normal chart `φ` at `p` and a timelike vector `e`
at `p`, the function `x⁰ = -g_p (e, φ⁻¹ ·)` is the time coordinate of the normal coordinates
whose time axis is `e`. `IsTimeBall g U p ρ φ e r N` says that on the normal ball `φ (B(0, r))`
the gradient of `x⁰` is timelike: `N v` is the vector at `φ v` with `g (N v, ·) = -dx⁰`, and
`g (N v, N v) < 0`. This is the hypothesis "`∇x⁰` is timelike on `O`" of the local causality
theorem.

Also two facts on Lorentzian forms used there.

## References

* P. T. Chruściel, *Elements of causality theory*, arXiv:1110.6706v1: Definition 2.2.7 (page 13)
  and Proposition 2.4.5 (pages 20–21), where the hypothesis is "any normal-coordinate ball such
  that `∇x⁰` is timelike on `O`".
-/

open Set Metric Filter Topology Matrix
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike

section ConeAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A future-directed causal vector and a future-directed timelike vector have negative
product. -/
theorem IsLorentzianForm.neg_of_causal_timelike (h : IsLorentzianForm n B) {u w X : V}
    (hX : B X X < 0) (hu : B u u ≤ 0) (hw : B w w < 0) (hu' : B u X < 0) (hw' : B w X < 0) :
    B u w < 0 := by
  have hle := h.nonpos_of_futureCausal hX hu hw.le hu' hw'
  refine lt_of_le_of_ne hle fun h0 => ?_
  have hu0 := h.eq_zero_of_orthogonal_timelike hw h0 hu
  rw [hu0] at hu'
  simp at hu'

/-- **The cone inequality for a spacelike vector**: for a timelike `N`, a causal `w` and a vector
`P` with `B P P ≥ 0`, all three on the same side of `N`,
`2 (-B (P, N)) B (P, w) ≤ B (P, P) (-B (w, N))`. -/
theorem IsLorentzianForm.two_mul_le_of_spacelike (h : IsLorentzianForm n B) {P w N : V}
    (hN : B N N < 0) (hw : B w w ≤ 0) (hwN : B w N < 0) (hPN : B P N < 0) (hP : 0 ≤ B P P) :
    2 * (-(B P N)) * B P w ≤ B P P * (-(B w N)) := by
  have hα : 0 < -(B P N) := by linarith
  set lam : ℝ := B P P / (2 * (-(B P N))) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hP (by linarith)
  have hlamα : lam * (2 * (-(B P N))) = B P P := by
    rw [hlam]; exact div_mul_cancel₀ _ (by linarith)
  have hsymm := h.symm
  have h1 : B (P + lam • N) (P + lam • N) = B P P + 2 * lam * B P N + lam ^ 2 * B N N := by
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsymm N P]; ring
  have hcausal : B (P + lam • N) (P + lam • N) ≤ 0 := by
    rw [h1]; nlinarith [sq_nonneg lam]
  have h2 : B (P + lam • N) N = B P N + lam * B N N := by
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hfut : B (P + lam • N) N < 0 := by
    rw [h2]; nlinarith
  have h3 := h.nonpos_of_futureCausal hN hcausal hw hfut hwN
  have h4 : B (P + lam • N) w = B P w + lam * B w N := by
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsymm N w]
  rw [h4] at h3
  nlinarith

end ConeAlgebra

namespace Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The pairing is the bilinear form of the matrix `g y`. -/
lemma pairing_eq_matForm (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a b : Fin n → ℝ) :
    pairing g y a b = matForm (g y) a b := by
  rw [matForm_apply]
  simp only [pairing, mul_assoc]

/-- The bilinear form of a Lorentzian coordinate metric is Lorentzian at every point. -/
lemma isLorentzianForm_matForm (hL : IsLorentzianCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U) :
    IsLorentzianForm n (matForm (g y)) := by
  obtain ⟨P, hP, h⟩ := hL.2 y hy
  rw [h]
  exact matForm_isLorentzian P hP

/-- **A normal ball with a time function.** `φ` is a normal chart at `p` of radius `ρ`, `e` is a
timelike vector at `p`, `0 < r ≤ ρ`, and for every `v` in the ball of radius `r` the vector `N v`
at `φ v` represents the differential of `-x⁰`, where `x⁰ = -g_p (e, φ⁻¹ ·)`:
`g (N v, Dφ (v) w) = g_p (e, w)` for all `w`; it is timelike, and continuous in `v`. So
`N = -∇x⁰`, and "`∇x⁰` is timelike on the ball". -/
structure IsTimeBall (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (p : Fin n → ℝ) (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ))
    (e : Fin n → ℝ) (r : ℝ) (N : (Fin n → ℝ) → Fin n → ℝ) : Prop where
  /-- `φ` is a normal chart at `p`. -/
  chart : IsNormalChart g U p ρ φ
  /-- The radius is positive. -/
  pos : 0 < r
  /-- The ball lies in the domain of the chart. -/
  le : r ≤ ρ
  /-- `e` is timelike at `p`. -/
  timelike_zero : pairing g p e e < 0
  /-- `N v` represents the differential of `-x⁰` at `φ v`. -/
  dual : ∀ v ∈ ball (0 : Fin n → ℝ) r, ∀ w : Fin n → ℝ,
    pairing g (φ v) (N v) (fderiv ℝ φ v w) = pairing g p e w
  /-- The gradient of `x⁰` is timelike on the ball. -/
  timelike : ∀ v ∈ ball (0 : Fin n → ℝ) r, pairing g (φ v) (N v) (N v) < 0
  /-- The gradient is continuous. -/
  continuousOn : ContinuousOn N (ball 0 r)

namespace IsTimeBall

variable {p e : Fin n → ℝ} {ρ r : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}
  {N : (Fin n → ℝ) → Fin n → ℝ}

lemma mem_ball (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) : v ∈ ball (0 : Fin n → ℝ) ρ :=
  ball_subset_ball h.le hv

lemma mem_source (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) : v ∈ φ.source := by
  rw [h.chart.source_eq]; exact h.mem_ball hv

lemma map_mem (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) : φ v ∈ U :=
  h.chart.target_subset (φ.map_source (h.mem_source hv))

lemma hasFDerivAt (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) : HasFDerivAt φ (fderiv ℝ φ v) v :=
  (((h.chart.contDiffOn.contDiffAt (φ.open_source.mem_nhds (h.mem_source hv))).differentiableAt
    (by simp))).hasFDerivAt

/-- The derivative of the inverse chart at `φ v` is the inverse of the derivative of the chart
at `v`. -/
lemma exists_fderiv_symm (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) :
    ∃ D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ), HasFDerivAt φ.symm D (φ v) ∧
      (∀ w, fderiv ℝ φ v (D w) = w) ∧ ∀ w, D (fderiv ℝ φ v w) = w := by
  have hsrc := h.mem_source hv
  have hφ := h.hasFDerivAt hv
  have hψ : HasFDerivAt φ.symm (fderiv ℝ φ.symm (φ v)) (φ v) :=
    ((h.chart.contDiffOn_symm.contDiffAt (φ.open_target.mem_nhds
      (φ.map_source hsrc))).differentiableAt (by simp)).hasFDerivAt
  refine ⟨fderiv ℝ φ.symm (φ v), hψ, fun w => ?_, fun w => ?_⟩
  · have c2 : HasFDerivAt (φ ∘ φ.symm) ((fderiv ℝ φ v).comp (fderiv ℝ φ.symm (φ v))) (φ v) :=
      HasFDerivAt.comp (φ v) (by rw [φ.left_inv hsrc]; exact hφ) hψ
    have hev : (φ ∘ φ.symm) =ᶠ[𝓝 (φ v)] id :=
      φ.eventually_right_inverse (φ.map_source hsrc)
    have h3 := (hasFDerivAt_id (𝕜 := ℝ) (φ v)).unique (c2.congr_of_eventuallyEq hev.symm)
    have h4 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L w) h3
    simpa using h4.symm
  · have c1 : HasFDerivAt (φ.symm ∘ φ) ((fderiv ℝ φ.symm (φ v)).comp (fderiv ℝ φ v)) v :=
      hψ.comp v hφ
    have hev : (φ.symm ∘ φ) =ᶠ[𝓝 v] id := φ.eventually_left_inverse hsrc
    have h3 := (hasFDerivAt_id (𝕜 := ℝ) v).unique (c1.congr_of_eventuallyEq hev.symm)
    have h4 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L w) h3
    simpa using h4.symm

end IsTimeBall

end Geodesic

end Lightlike

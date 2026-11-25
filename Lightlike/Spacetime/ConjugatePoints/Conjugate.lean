import Lightlike.Spacetime.ConjugatePoints.Jacobi

/-!
# Conjugate points along a geodesic, in a chart (row G1-006, GE3)

Two parameters `t₀ ≠ t₁` of a geodesic `γ` (velocity `w`) are **conjugate** along `γ` on `I` when
some Jacobi field (`Lightlike.Geodesic.IsJacobiOn`) that does not vanish identically on `I` vanishes
at both. This is the analytic notion used by the singularity theorems (Hawking–Ellis 1973).

## Main definitions

* `Lightlike.Geodesic.IsConjugateOn g γ w I t₀ t₁`.

## Trust check

In a flat chart (constant metric) every Jacobi field is affine in `t`
(`isJacobiOn_const_metric_affine`), hence there are no conjugate points
(`not_isConjugateOn_const_metric`).
-/

open Set Filter Topology Matrix

namespace Lightlike.Geodesic

variable {n : ℕ}

/-- `t₀` and `t₁` are **conjugate** along the geodesic `γ` (velocity `w`) on `I`: `t₀ ≠ t₁` are in
`I` and a Jacobi field, not identically zero on `I`, vanishes at both. -/
def IsConjugateOn (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ w : ℝ → Fin n → ℝ) (I : Set ℝ)
    (t₀ t₁ : ℝ) : Prop :=
  t₀ ∈ I ∧ t₁ ∈ I ∧ t₀ ≠ t₁ ∧
    ∃ J P : ℝ → Fin n → ℝ, IsJacobiOn g γ w J P I ∧ J t₀ = 0 ∧ J t₁ = 0 ∧ ∃ t ∈ I, J t ≠ 0

/-- Conjugacy is symmetric. -/
theorem IsConjugateOn.symm {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {γ w : ℝ → Fin n → ℝ}
    {I : Set ℝ} {t₀ t₁ : ℝ} (h : IsConjugateOn g γ w I t₀ t₁) : IsConjugateOn g γ w I t₁ t₀ := by
  obtain ⟨h0, h1, hne, J, P, hJ, e0, e1, hn⟩ := h
  exact ⟨h1, h0, hne.symm, J, P, hJ, e1, e0, hn⟩

/-- **Flat chart**: for a constant metric, on an open interval, a Jacobi field is affine:
`J t = J t₀ + (t - t₀) P t₀`, and `P` is constant. -/
theorem isJacobiOn_const_metric_affine (G : Matrix (Fin n) (Fin n) ℝ) {γ w J P : ℝ → Fin n → ℝ}
    {I : Set ℝ} (hI : IsOpen I) (hI' : IsPreconnected I)
    (h : IsJacobiOn (fun _ => G) γ w J P I) {t₀ : ℝ} (h0 : t₀ ∈ I) :
    ∀ t ∈ I, P t = P t₀ ∧ J t = J t₀ + (t - t₀) • P t₀ := by
  have g1 : ∀ (x v u : Fin n → ℝ), gammaApply (fun _ => G) x v u = 0 := by
    intro x v u; funext i
    simp [gammaApply, christoffel_const]
  have g2 : ∀ (x w u : Fin n → ℝ), riemannApply (fun _ => G) x w u = 0 := by
    intro x w u; funext i
    simp [riemannApply, riemann_const]
  have hP : ∀ t ∈ I, HasDerivAt P 0 t := by
    intro t ht
    have := h.deriv_cov t ht
    rwa [g1, g2, neg_zero, sub_zero] at this
  have hPc : ∀ t ∈ I, P t = P t₀ := by
    intro t ht
    exact hI.is_const_of_deriv_eq_zero hI'
      (fun s hs => (hP s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => by simpa using (hP s hs).deriv) ht h0
  have hK : ∀ t ∈ I, HasDerivAt (fun s => J s - (s - t₀) • P t₀) 0 t := by
    intro t ht
    have h1 := h.deriv_field t ht
    rw [g1, sub_zero] at h1
    have h2 : HasDerivAt (fun s : ℝ => (s - t₀) • P t₀) (P t₀) t := by
      simpa using ((hasDerivAt_id t).sub_const t₀).smul_const (P t₀)
    have h3 := h1.sub h2
    rw [hPc t ht, sub_self] at h3
    exact h3
  have hKc : ∀ t ∈ I, J t - (t - t₀) • P t₀ = J t₀ - (t₀ - t₀) • P t₀ := by
    intro t ht
    exact hI.is_const_of_deriv_eq_zero hI'
      (f := fun s => J s - (s - t₀) • P t₀)
      (fun s hs => (hK s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => by simpa using (hK s hs).deriv) ht h0
  intro t ht
  refine ⟨hPc t ht, ?_⟩
  have := hKc t ht
  simp only [sub_self, zero_smul, sub_zero] at this
  rw [← this]; abel

/-- **Trust check, flat chart**: a constant metric has no conjugate points, on any open interval. -/
theorem not_isConjugateOn_const_metric (G : Matrix (Fin n) (Fin n) ℝ) (γ w : ℝ → Fin n → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (hI' : IsPreconnected I) (t₀ t₁ : ℝ) :
    ¬ IsConjugateOn (fun _ => G) γ w I t₀ t₁ := by
  rintro ⟨h0, h1, hne, J, P, hJ, e0, e1, t, ht, hJt⟩
  have A := isJacobiOn_const_metric_affine G hI hI' hJ h0
  have hP : P t₀ = 0 := by
    have := (A t₁ h1).2
    rw [e1, e0, zero_add] at this
    have hs : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr hne.symm
    exact (smul_eq_zero.mp this.symm).resolve_left hs
  apply hJt
  have := (A t ht).2
  rw [e0, hP, smul_zero, zero_add] at this
  exact this

end Lightlike.Geodesic

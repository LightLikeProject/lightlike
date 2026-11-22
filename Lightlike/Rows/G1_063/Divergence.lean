import Lightlike.Rows.G1_063.Curvature2D

/-!
# Trace and divergence of a symmetric tensor on `(ℝ², e^{2ψ} η)` (row G1-063, milestone SC7)

For a symmetric `(0,2)`-tensor field `T` (components `T a b : ℝ² → ℝ`) on the metric `g = e^{2ψ} η`
this file defines the trace `T^μ_μ = g^{ab} T_{ab}` (`trT`) and the divergence
`(div T)_ν = g^{μa} ∇_a T_{μν}` (`divT`), the latter with the library's Christoffel symbols
(`Lightlike.christoffel`). It then computes both explicitly in conformal gauge:

* `christoffel_confEta2`: `Γ^a_{bc} = δ^a_c ∂_b ψ + δ^a_b ∂_c ψ - η_{bc} η^{aa} ∂_a ψ`;
* `trT_confEta2`: `T^μ_μ = e^{-2ψ} (-T_tt + T_xx)`;
* `divT_confEta2`: `(div T)_ν = e^{-2ψ} (-∂_t T_{tν} + ∂_x T_{xν} - ∂_ν ψ · (-T_tt + T_xx))`.
-/

noncomputable section

namespace Lightlike.Rows.G1_063

open Lightlike
open scoped ContDiff

/-- Trace `T^μ_μ = g^{ab} T_{ab}` of a `(0,2)`-tensor field `T` for the metric `g`. -/
def trT (g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (T : Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ)
    (x : Fin 2 → ℝ) : ℝ :=
  ∑ a, ∑ b, (g x)⁻¹ a b * T a b x

/-- Divergence `(div T)_ν = g^{μa} (∂_a T_{μν} - Γ^λ_{aμ} T_{λν} - Γ^λ_{aν} T_{μλ})`
(`= ∇^μ T_{μν}`) of a `(0,2)`-tensor field `T` for the metric `g`, using the library Christoffel
symbols of `g`. -/
def divT (g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (T : Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ)
    (ν : Fin 2) (x : Fin 2 → ℝ) : ℝ :=
  ∑ μ, ∑ a, (g x)⁻¹ μ a *
    (pd a (T μ ν) x - ∑ l, christoffel g l a μ x * T l ν x - ∑ l, christoffel g l a ν x * T μ l x)

lemma isSymm_eta2 (a b : Fin 2) : (eta 2) a b = (eta 2) b a := by
  exact congrFun (congrFun (eta_transpose 2) b) a

/-- The inverse of `e^{2ψ} η` is `e^{-2ψ} η`. -/
lemma confEta2_inv (ψ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    (confEta2 ψ x)⁻¹ = Real.exp (-(2 * ψ x)) • eta 2 := by
  have he : Real.exp (2 * ψ x) ≠ 0 := (Real.exp_pos _).ne'
  have := Matrix.inv_smul' (Units.mk0 _ he) (A := eta 2) (eta_isUnit_det 2)
  simp only [confEta2, conformalMetric]
  simpa [Units.smul_def, eta_inv, Real.exp_neg] using this

/-- **Christoffel symbols of `e^{2ψ} η` on `ℝ²`**:
`Γ^a_{bc} = δ^a_c ∂_b ψ + δ^a_b ∂_c ψ - η_{bc} η^{aa} ∂_a ψ`. -/
theorem christoffel_confEta2 {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (a b c : Fin 2)
    (x : Fin 2 → ℝ) :
    christoffel (confEta2 ψ) a b c x =
      pd b ψ x * (1 : Matrix (Fin 2) (Fin 2) ℝ) a c + pd c ψ x * (1 : Matrix (Fin 2) (Fin 2) ℝ) a b -
        eta 2 b c * (etaDiag a * pd a ψ x) := by
  have h := christoffel_conformal (g := fun _ : Fin 2 → ℝ => eta 2) (ψ := ψ) (x := x)
    (fun a b => differentiableAt_const _) (hψ.differentiable (by simp)).differentiableAt
    (by simpa using (eta_isUnit_det 2).ne_zero) (fun a b => isSymm_eta2 a b) a b c
  unfold confEta2
  rw [h, christoffel_const]
  simp only [eta_inv, eta_apply]
  simp [Finset.sum_ite_eq]

/-- The trace in conformal gauge: `T^μ_μ = e^{-2ψ} (-T_tt + T_xx)`. -/
theorem trT_confEta2 (ψ : (Fin 2 → ℝ) → ℝ) (T : Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    trT (confEta2 ψ) T x = Real.exp (-(2 * ψ x)) * (-T 0 0 x + T 1 1 x) := by
  simp [trT, confEta2_inv, eta_apply, etaDiag, Fin.sum_univ_two]
  ring

/-- The divergence in conformal gauge, for a symmetric tensor `T` at `x`:
`(div T)_ν = e^{-2ψ} (-∂_t T_{tν} + ∂_x T_{xν} - ∂_ν ψ · (-T_tt + T_xx))`. -/
theorem divT_confEta2 {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (T : Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) (hT : T 0 1 x = T 1 0 x) (ν : Fin 2) :
    divT (confEta2 ψ) T ν x = Real.exp (-(2 * ψ x)) *
      (-pd 0 (T 0 ν) x + pd 1 (T 1 ν) x - pd ν ψ x * (-T 0 0 x + T 1 1 x)) := by
  fin_cases ν <;>
  · simp [divT, confEta2_inv, christoffel_confEta2 hψ, eta_apply, etaDiag, Fin.sum_univ_two, hT]
    ring

end Lightlike.Rows.G1_063

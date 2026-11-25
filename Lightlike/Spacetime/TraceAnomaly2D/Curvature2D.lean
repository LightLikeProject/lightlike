import Lightlike.Spacetime.ConformalRicci

/-!
# Scalar curvature of a two-dimensional conformally flat metric (row G1-063, milestone SC7)

The semiclassical stress-tensor milestone SC7 asks for `⟨T^μ_μ⟩ = c R / (24 π)` in two dimensions.
The anomaly is stated against the scalar curvature `R` of the metric `g = e^{2ψ} η` on `ℝ²`
(coordinates `(t, x)`, `η = diag(-1, 1)`), the form in which Birrell–Davies and Fabbri–Navarro-Salas
derive it. This file computes that `R` from the library's coordinate curvature
(`Lightlike.scalarCurvature`), via `scalarCurvature_conformal`:

`R = 2 e^{-2ψ} (∂_t² ψ - ∂_x² ψ)`   (`scalarCurvature_conformalEta2`).
-/

noncomputable section

namespace Lightlike.Rows.G1_063

open Lightlike
open scoped ContDiff

/-- The two-dimensional conformally flat metric `e^{2ψ} η` in coordinates `(t, x)`. -/
def confEta2 (ψ : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ :=
  conformalMetric (fun _ => eta 2) ψ

/-- The Minkowski chart matrix is a coordinate metric on all of `ℝ²` (constant `η`). -/
lemma isCoordMetric_eta2 : IsCoordMetric (fun _ : Fin 2 → ℝ => eta 2) Set.univ :=
  isCoordMetric_const (eta_transpose 2) (eta_isUnit_det 2)

/-- The scalar curvature of the constant metric `η` vanishes. -/
lemma scalarCurvature_eta2 (x : Fin 2 → ℝ) : scalarCurvature (fun _ : Fin 2 → ℝ => eta 2) x = 0 := by
  simp [scalarCurvature, ricci, riemann_const]

/-- The wave operator of the flat metric `η = diag(-1, 1)` is `□ψ = -∂_t² ψ + ∂_x² ψ`. -/
lemma boxC_eta2 (ψ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    boxC (fun _ : Fin 2 → ℝ => eta 2) ψ x =
      -pd 0 (fun y => pd 0 ψ y) x + pd 1 (fun y => pd 1 ψ y) x := by
  simp [boxC, hessC, christoffel_const, eta_inv, eta_apply, etaDiag, Fin.sum_univ_two]

/-- **Scalar curvature of the conformally flat metric `e^{2ψ} η` on `ℝ²`**:
`R = 2 e^{-2ψ} (∂_t² ψ - ∂_x² ψ)`. This is the curvature against which the 2D trace anomaly
`⟨T^μ_μ⟩ = c R / (24 π)` is stated. -/
theorem scalarCurvature_conformalEta2 {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : Fin 2 → ℝ) :
    scalarCurvature (confEta2 ψ) x =
      2 * Real.exp (-(2 * ψ x)) * (pd 0 (fun y => pd 0 ψ y) x - pd 1 (fun y => pd 1 ψ y) x) := by
  have h := scalarCurvature_conformal (g := fun _ : Fin 2 → ℝ => eta 2) (U := Set.univ) (ψ := ψ) (x := x)
    isCoordMetric_eta2 (fun y a b => by
      rw [eta_apply, eta_apply]
      by_cases hab : a = b
      · subst hab; rfl
      · simp [hab, Ne.symm hab])
    hψ.contDiffOn (Set.mem_univ x)
  unfold confEta2
  rw [h, scalarCurvature_eta2, boxC_eta2]
  norm_num
  ring

end Lightlike.Rows.G1_063

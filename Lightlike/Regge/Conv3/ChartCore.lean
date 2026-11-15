import Lightlike.Regge.Conv3.ChartCases0
import Lightlike.Regge.Conv3.ChartCases1
import Lightlike.Regge.Conv3.ChartCases2
import Lightlike.Regge.Conv3.ChartCases3
import Lightlike.Regge.Conv3.ChartCases4
import Lightlike.Regge.Conv3.ChartCases5

open Real
namespace Lightlike.Regge.Conv3

/-- `ℓ dθ` at every (tetrahedron, hinge) pair of the diagonal chart is the closed form `cf`. -/
theorem ldth_eq_cf (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) (σ h : Fin 6) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] σ h 0) (dsq ![α, β, γ] σ h 1) (dsq ![α, β, γ] σ h 2)
      (dsq ![α, β, γ] σ h 3) (dsq ![α, β, γ] σ h 4) (dsq ![α, β, γ] σ h 5)
      (dkds ric ![α, β, γ] σ h 0) (dkds ric ![α, β, γ] σ h 1) (dkds ric ![α, β, γ] σ h 2)
      (dkds ric ![α, β, γ] σ h 3) (dkds ric ![α, β, γ] σ h 4) (dkds ric ![α, β, γ] σ h 5) =
      cf α β γ ric σ h := by
  fin_cases σ <;> fin_cases h
  · exact ldth_cf00 α β γ hα hβ hγ ric hs
  · exact ldth_cf01 α β γ hα hβ hγ ric hs
  · exact ldth_cf02 α β γ hα hβ hγ ric hs
  · exact ldth_cf03 α β γ hα hβ hγ ric hs
  · exact ldth_cf04 α β γ hα hβ hγ ric hs
  · exact ldth_cf05 α β γ hα hβ hγ ric hs
  · exact ldth_cf10 α β γ hα hβ hγ ric hs
  · exact ldth_cf11 α β γ hα hβ hγ ric hs
  · exact ldth_cf12 α β γ hα hβ hγ ric hs
  · exact ldth_cf13 α β γ hα hβ hγ ric hs
  · exact ldth_cf14 α β γ hα hβ hγ ric hs
  · exact ldth_cf15 α β γ hα hβ hγ ric hs
  · exact ldth_cf20 α β γ hα hβ hγ ric hs
  · exact ldth_cf21 α β γ hα hβ hγ ric hs
  · exact ldth_cf22 α β γ hα hβ hγ ric hs
  · exact ldth_cf23 α β γ hα hβ hγ ric hs
  · exact ldth_cf24 α β γ hα hβ hγ ric hs
  · exact ldth_cf25 α β γ hα hβ hγ ric hs
  · exact ldth_cf30 α β γ hα hβ hγ ric hs
  · exact ldth_cf31 α β γ hα hβ hγ ric hs
  · exact ldth_cf32 α β γ hα hβ hγ ric hs
  · exact ldth_cf33 α β γ hα hβ hγ ric hs
  · exact ldth_cf34 α β γ hα hβ hγ ric hs
  · exact ldth_cf35 α β γ hα hβ hγ ric hs
  · exact ldth_cf40 α β γ hα hβ hγ ric hs
  · exact ldth_cf41 α β γ hα hβ hγ ric hs
  · exact ldth_cf42 α β γ hα hβ hγ ric hs
  · exact ldth_cf43 α β γ hα hβ hγ ric hs
  · exact ldth_cf44 α β γ hα hβ hγ ric hs
  · exact ldth_cf45 α β γ hα hβ hγ ric hs
  · exact ldth_cf50 α β γ hα hβ hγ ric hs
  · exact ldth_cf51 α β γ hα hβ hγ ric hs
  · exact ldth_cf52 α β γ hα hβ hγ ric hs
  · exact ldth_cf53 α β γ hα hβ hγ ric hs
  · exact ldth_cf54 α β γ hα hβ hγ ric hs
  · exact ldth_cf55 α β γ hα hβ hγ ric hs

/-- The 36 closed forms sum to `-R αβγ / 2`. -/
theorem cf_sum (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) :
    ∑ σ : Fin 6, ∑ h : Fin 6, cf α β γ ric σ h = -(scal ric) * (α * β * γ) / 2 := by
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  simp only [Fin.sum_univ_six, cf, cf00, cf01, cf02, cf03, cf04, cf05, cf10, cf11, cf12, cf13, cf14, cf15, cf20, cf21, cf22, cf23, cf24, cf25, cf30, cf31, cf32, cf33, cf34, cf35, cf40, cf41, cf42, cf43, cf44, cf45, cf50, cf51, cf52, cf53, cf54, cf55, scal, Fin.sum_univ_three]
  simp
  field_simp
  ring

/-- **Algebraic core of the 3D convergence in a diagonal chart.** In a chart whose metric at the
vertex is `diag(α², β², γ²)`, the six Kuhn tetrahedra are the images of the orthonormal-frame ones
under `diag(α, β, γ)`. Summed over all 36 (tetrahedron, hinge) incidences, the hinge length times
the first variation of the dihedral angle under the curvature perturbation of the squared edge
lengths is `-R αβγ / 2`, where `R` is the scalar curvature of `ric` and `αβγ` is the volume of the
chart cell. For `α = β = γ = 1` this is the orthonormal-frame core. -/
theorem diag_core (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ∑ σ : Fin 6, ∑ h : Fin 6, √(dsq ![α, β, γ] σ h 0) *
      dihSq' (dsq ![α, β, γ] σ h 0) (dsq ![α, β, γ] σ h 1) (dsq ![α, β, γ] σ h 2)
        (dsq ![α, β, γ] σ h 3) (dsq ![α, β, γ] σ h 4) (dsq ![α, β, γ] σ h 5)
        (dkds ric ![α, β, γ] σ h 0) (dkds ric ![α, β, γ] σ h 1) (dkds ric ![α, β, γ] σ h 2)
        (dkds ric ![α, β, γ] σ h 3) (dkds ric ![α, β, γ] σ h 4) (dkds ric ![α, β, γ] σ h 5) =
      -(scal ric) * (α * β * γ) / 2 := by
  rw [← cf_sum α β γ hα hβ hγ ric]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
  have g := inc_geom α β γ hα hβ hγ σ h
  rw [← ldth_eq_cf α β γ hα hβ hγ ric hs σ h]
  refine sqrt_mul_dihSq' g.1 g.2.1 g.2.2.1 (by positivity) ?_
  rw [g.2.2.2]; ring

/-- Non-vacuity and a wrong-model control for `diag_core`: for the chart `diag(1, 2, 1)` and the
Ricci tensor `ric = δ` (scalar curvature `3`) the value is `-3`, not the orthonormal-frame value
`-3/2`, so the volume factor `αβγ = 2` is genuinely present. -/
theorem diag_core_example :
    ∑ σ : Fin 6, ∑ h : Fin 6, √(dsq ![1, 2, 1] σ h 0) *
      dihSq' (dsq ![1, 2, 1] σ h 0) (dsq ![1, 2, 1] σ h 1) (dsq ![1, 2, 1] σ h 2)
        (dsq ![1, 2, 1] σ h 3) (dsq ![1, 2, 1] σ h 4) (dsq ![1, 2, 1] σ h 5)
        (dkds (fun i j => if i = j then 1 else 0) ![1, 2, 1] σ h 0)
        (dkds (fun i j => if i = j then 1 else 0) ![1, 2, 1] σ h 1)
        (dkds (fun i j => if i = j then 1 else 0) ![1, 2, 1] σ h 2)
        (dkds (fun i j => if i = j then 1 else 0) ![1, 2, 1] σ h 3)
        (dkds (fun i j => if i = j then 1 else 0) ![1, 2, 1] σ h 4)
        (dkds (fun i j => if i = j then 1 else 0) ![1, 2, 1] σ h 5) = -3 := by
  have := diag_core 1 2 1 one_pos two_pos one_pos (fun i j => if i = j then 1 else 0)
    (fun i j => by by_cases h : i = j <;> simp [h, eq_comm])
  rw [this]
  simp [scal, Fin.sum_univ_three]
  norm_num

/-- The wrong-model control: the diagonal-chart value differs from the orthonormal one. -/
theorem diag_core_ne_orthonormal : (-3 : ℝ) ≠ -3 / 2 := by norm_num

end Lightlike.Regge.Conv3

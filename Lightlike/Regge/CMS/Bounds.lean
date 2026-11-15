import Mathlib
import Lightlike.Regge.CMS.EdgeNormal

/-!
# Uniform bounds on a compact set (RC6b, step 7)

On a compact subset of the domain of a Riemannian metric, the scalar curvature is bounded, and the
metric is comparable to the Euclidean one in the chart.

## Main results

* `abs_jetScalar_le`: a bound of the scalar curvature of a jet by bounds of its ingredients.
* `IsRiemMetric.exists_abs_scalarCurvature_le`: `|R| ≤ Rm` on a compact set.
-/

open Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

variable {n : ℕ}

/-- **The scalar curvature of a jet is bounded by its ingredients.** -/
theorem abs_jetScalar_le {g : Matrix (Fin n) (Fin n) ℝ} {A : Fin n → Fin n → Fin n → ℝ}
    {B : Fin n → Fin n → Fin n → Fin n → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hinv : ∀ i j, |g⁻¹ i j| ≤ M)
    (hgam : ∀ i j k, |gam g A i j k| ≤ M) (hdgam : ∀ l i j k, |dGam g A B l i j k| ≤ M) :
    |jetScalar g A B| ≤ n ^ 2 * M * (n * (2 * M + 2 * n * M ^ 2)) := by
  have hR : ∀ ρ σ μ ν, |jetRiem g A B ρ σ μ ν| ≤ 2 * M + 2 * n * M ^ 2 := by
    intro ρ σ μ ν
    unfold jetRiem
    have h3 : |∑ l, (gam g A ρ μ l * gam g A l ν σ - gam g A ρ ν l * gam g A l μ σ)| ≤
        ∑ _l : Fin n, (M * M + M * M) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul (hgam _ _ _) (hgam _ _ _) (abs_nonneg _) hM0
      · rw [abs_mul]; exact mul_le_mul (hgam _ _ _) (hgam _ _ _) (abs_nonneg _) hM0
    have h4 : ∑ _l : Fin n, (M * M + M * M) = 2 * n * M ^ 2 := by
      simp; ring
    have h5 := abs_sub (dGam g A B μ ρ ν σ) (dGam g A B ν ρ μ σ)
    have h6 := abs_add_le (dGam g A B μ ρ ν σ - dGam g A B ν ρ μ σ)
      (∑ l, (gam g A ρ μ l * gam g A l ν σ - gam g A ρ ν l * gam g A l μ σ))
    linarith [hdgam μ ρ ν σ, hdgam ν ρ μ σ]
  unfold jetScalar
  have hs : ∀ σ ν, |g⁻¹ σ ν * ∑ ρ, jetRiem g A B ρ σ ρ ν| ≤ M * (n * (2 * M + 2 * n * M ^ 2)) := by
    intro σ ν
    rw [abs_mul]
    refine mul_le_mul (hinv _ _) ?_ (abs_nonneg _) hM0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _ρ : Fin n, (2 * M + 2 * n * M ^ 2) := Finset.sum_le_sum fun ρ _ => hR _ _ _ _
      _ = _ := by simp; ring
  calc _ ≤ ∑ σ, |∑ ν, g⁻¹ σ ν * ∑ ρ, jetRiem g A B ρ σ ρ ν| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Fin n, ∑ ν : Fin n, M * (n * (2 * M + 2 * n * M ^ 2)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => hs σ ν)
    _ = _ := by simp; ring

/-- **The scalar curvature is bounded on a compact set.** -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.exists_abs_scalarCurvature_le
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : Lightlike.Geodesic.IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ Rm : ℝ, 0 ≤ Rm ∧ ∀ v ∈ K, |scalarCurvature g v| ≤ Rm := by
  obtain ⟨M, hM0, hM⟩ := hg.coord.exists_jet_bound hK hKU
  refine ⟨((2 : ℕ) : ℝ) ^ 2 * M * (((2 : ℕ) : ℝ) * (2 * M + 2 * ((2 : ℕ) : ℝ) * M ^ 2)), by positivity,
    fun v hv => ?_⟩
  have hvU : v ∈ U := hKU hv
  rw [← Lightlike.Geodesic.jetScalar_eq_scalarCurvature hg.coord hvU]
  refine abs_jetScalar_le hM0 (fun i j => (hM v hv i j i i i).2.1) (fun i j k => ?_)
    (fun l i j k => ?_)
  · rw [gam_eq_christoffel]; exact (hM v hv i j k i i).2.2.2.2.2.1
  · have e : dGam (g v) (jetA g v) (jetB g v) l i j k = pd l (christoffel g i j k) v :=
      (pd_christoffel hg.coord hvU l i j k).symm
    rw [e]; exact (hM v hv i j k l l).2.2.2.2.2.2

end Lightlike.CMS

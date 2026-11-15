import Mathlib
import Lightlike.Regge.CMS.PerTriangle

/-!
# Uniform constants of a Riemannian metric on a compact set (RC6b, step 8)

Everything the per-triangle estimate needs, bundled: on a compact subset `K` of the domain the
chart form `ip (g v)` is symmetric, comparable to the squared sup norm, has determinant bounded
below, and the scalar curvature of its jet is bounded.

## Main results

* `IsRiemMetric.exists_uniform_G`: the constants `l, Lm, δ, Rm`.
-/

open Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- The sup norm squared is at most the Euclidean squared norm. -/
theorem norm_sq_le_dot (x : Fin 2 → ℝ) : ‖x‖ ^ 2 ≤ x ⬝ᵥ x := by
  have h : ‖x‖ ≤ √(x ⬝ᵥ x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    simp only [dotProduct, Fin.sum_univ_two]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have h0 := norm_nonneg x
  calc ‖x‖ ^ 2 ≤ √(x ⬝ᵥ x) ^ 2 := by gcongr
    _ = x ⬝ᵥ x := Real.sq_sqrt (by simp only [dotProduct, Fin.sum_univ_two]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)])

/-- The Euclidean squared norm is at most twice the squared sup norm. -/
theorem dot_le_two_norm_sq (x : Fin 2 → ℝ) : x ⬝ᵥ x ≤ 2 * ‖x‖ ^ 2 := by
  have h0 : x 0 ^ 2 ≤ ‖x‖ ^ 2 := by
    have := norm_le_pi_norm x 0
    rw [Real.norm_eq_abs] at this
    calc x 0 ^ 2 = |x 0| ^ 2 := (sq_abs _).symm
      _ ≤ _ := by gcongr
  have h1 : x 1 ^ 2 ≤ ‖x‖ ^ 2 := by
    have := norm_le_pi_norm x 1
    rw [Real.norm_eq_abs] at this
    calc x 1 ^ 2 = |x 1| ^ 2 := (sq_abs _).symm
      _ ≤ _ := by gcongr
  simp only [dotProduct, Fin.sum_univ_two]
  nlinarith

/-- **Uniform constants.** On a compact `K ⊆ U`, the chart form `ip (g v)` is symmetric, and
comparable to the squared sup norm with constants `l, Lm`, `det (g v) ≥ δ > 0`, and the scalar
curvature of the jet is at most `Rm` in absolute value. -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.exists_uniform_G
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ l Lm δ Rm : ℝ, 0 < l ∧ 0 < Lm ∧ 0 < δ ∧ 0 ≤ Rm ∧ ∀ v ∈ K, g v 0 1 = g v 1 0 ∧
      (∀ x, l * ‖x‖ ^ 2 ≤ ip (g v) x x) ∧ (∀ x, ip (g v) x x ≤ Lm * ‖x‖ ^ 2) ∧
      δ ≤ (g v).det ∧ |jetScalar (g v) (jetA g v) (jetB g v)| ≤ Rm := by
  obtain ⟨l, L, hl, hL, hlL⟩ := hg.exists_bounds_of_isCompact hK hKU
  obtain ⟨Rm, hRm0, hRm⟩ := hg.exists_abs_scalarCurvature_le hK hKU
  have hdetpos : ∀ v ∈ K, 0 < (g v).det := fun v hv => (hg.posDef v (hKU hv)).det_pos
  have hcont : ContinuousOn (fun v => (g v).det) K := by
    have : (fun v => (g v).det) = fun v => g v 0 0 * g v 1 1 - g v 0 1 * g v 1 0 := by
      funext v; exact Matrix.det_fin_two (g v)
    rw [this]
    have c : ∀ i j, ContinuousOn (fun y => g y i j) K := fun i j =>
      (hg.coord.smooth i j).continuousOn.mono hKU
    exact ((c 0 0).mul (c 1 1)).sub ((c 0 1).mul (c 1 0))
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ K, δ ≤ (g v).det := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, fun v hv => absurd hv (Set.notMem_empty v)⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := hK.exists_isMinOn hne hcont
      exact ⟨_, hdetpos v₀ hv₀, fun v hv => hmin hv⟩
  refine ⟨l, 2 * L, δ, Rm, hl, by positivity, hδ, hRm0, fun v hv => ?_⟩
  have hvU := hKU hv
  refine ⟨(jet_symm hg.coord hvU).1 0 1, fun x => ?_, fun x => ?_, hδK v hv, ?_⟩
  · have h1 := (hlL v hv x).1
    have h2 : normSq g v x = ip (g v) x x := by
      unfold normSq; exact dot_mulVec_eq_ip _ _ _
    rw [← h2]
    calc l * ‖x‖ ^ 2 ≤ l * eNormSq x := by
          gcongr; exact norm_sq_le_dot x
      _ ≤ _ := h1
  · have h1 := (hlL v hv x).2
    have h2 : normSq g v x = ip (g v) x x := by
      unfold normSq; exact dot_mulVec_eq_ip _ _ _
    rw [← h2]
    calc normSq g v x ≤ L * eNormSq x := h1
      _ ≤ L * (2 * ‖x‖ ^ 2) := by gcongr; exact dot_le_two_norm_sq x
      _ = _ := by ring
  · rw [jetScalar_eq_scalarCurvature hg.coord hvU]; exact hRm v hv

end Lightlike.CMS

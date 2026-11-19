import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.EHManifold.Perturbation

/-!
# Symmetric tensor fields from chart data

`SymBilinField.ofChart x₁ ρ hρ hρs S hS`: for a smooth function `ρ` on `M` supported in the domain of the
chart at `x₁` and a symmetric matrix `S`, the smooth symmetric tensor field whose components in that chart
are `ρ S` (`SymBilinField.coordComp_ofChart`) and which vanishes where `ρ` does.

It is defined with the inverse of the trivialization of the bundle of bilinear forms, which makes its
smoothness immediate.

Supporting definitions for "stationary implies Einstein's equation" on a manifold; no catalogue entry.
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Matrix Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The trivialization, in the chart at `x₁`, of the bundle of bilinear forms on the tangent spaces. -/
abbrev formTriv (n : ℕ) {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] (x₁ : M) :=
  trivializationAt ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x₁

lemma mem_formTriv_baseSet (x₁ : M) {y : M} (hy : y ∈ (chartTriv n x₁).baseSet) :
    y ∈ (formTriv n x₁).baseSet := by
  simp only [hom_trivializationAt_baseSet, mem_inter_iff]
  exact ⟨hy, hy, mem_univ _⟩

/-- **The trivialization of a bilinear form** is the form in the components of the chart. -/
lemma formTriv_apply (x₁ : M) {y : M} (hy : y ∈ (chartTriv n x₁).baseSet)
    (B : TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] ℝ)
    (a b : Fin n → ℝ) :
    ((formTriv n x₁) ⟨y, B⟩).2 a b =
      B ((chartTriv n x₁).symmL ℝ y a) ((chartTriv n x₁).symmL ℝ y b) := by
  have hb : y ∈ (trivializationAt ((Fin n → ℝ) →L[ℝ] ℝ)
      (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x₁).baseSet := by
    simp only [hom_trivializationAt_baseSet, mem_inter_iff]
    exact ⟨hy, mem_univ _⟩
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem _ hb, hom_trivializationAt_apply]
  simp

/-- **A symmetric tensor field with components `ρ S` in the chart at `x₁`.** -/
def SymBilinField.ofChart (x₁ : M) (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = S j i) : SymBilinField 𝓘(ℝ, Fin n → ℝ) M where
  h y := (formTriv n x₁).symm y (ρ y • matForm S)
  symm y v w := by
    by_cases hy : y ∈ (chartTriv n x₁).baseSet
    · have hy' := mem_formTriv_baseSet x₁ hy
      have key : ∀ u u' : TangentSpace 𝓘(ℝ, Fin n → ℝ) y,
          (formTriv n x₁).symm y (ρ y • matForm S) u u' =
            ρ y * matForm S ((chartTriv n x₁).continuousLinearMapAt ℝ y u)
              ((chartTriv n x₁).continuousLinearMapAt ℝ y u') := by
        intro u u'
        have h1 := formTriv_apply x₁ hy ((formTriv n x₁).symm y (ρ y • matForm S))
          ((chartTriv n x₁).continuousLinearMapAt ℝ y u)
          ((chartTriv n x₁).continuousLinearMapAt ℝ y u')
        rw [(formTriv n x₁).apply_mk_symm hy', (chartTriv n x₁).symmL_continuousLinearMapAt hy,
          (chartTriv n x₁).symmL_continuousLinearMapAt hy] at h1
        exact h1.symm
      rw [key v w, key w v, matForm_apply, matForm_apply]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hS j i]
      ring
    · have hy' : y ∉ (formTriv n x₁).baseSet := fun h => hy h.1
      rw [(formTriv n x₁).symm_apply_of_notMem hy']
      rfl
  contMDiff := by
    intro x₀
    by_cases hx : x₀ ∈ (chartTriv n x₁).baseSet
    · rw [(formTriv n x₁).contMDiffAt_section_iff (mem_formTriv_baseSet x₁ hx)]
      have hev : (fun y => ((formTriv n x₁) ⟨y, (formTriv n x₁).symm y (ρ y • matForm S)⟩).2) =ᶠ[𝓝 x₀]
          fun y => ρ y • matForm S := by
        filter_upwards [(chartTriv n x₁).open_baseSet.mem_nhds hx] with y hy
        rw [(formTriv n x₁).apply_mk_symm (mem_formTriv_baseSet x₁ hy)]
      exact ((hρ x₀).smul contMDiffAt_const).congr_of_eventuallyEq hev
    · have hx' : x₀ ∉ tsupport ρ := fun h => hx (hρs h)
      have hz : ∀ᶠ y in 𝓝 x₀, (formTriv n x₁).symm y (ρ y • matForm S) = 0 := by
        filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hx'] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
        by_cases hyb : y ∈ (formTriv n x₁).baseSet
        · rw [← (formTriv n x₁).symmL_apply (R := ℝ) hyb, map_zero]
        · exact (formTriv n x₁).symm_apply_of_notMem hyb _
      refine (contMDiff_zeroSection ℝ
        (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ)
        x₀).congr_of_eventuallyEq ?_
      filter_upwards [hz] with y hy
      show TotalSpace.mk' _ y ((formTriv n x₁).symm y (ρ y • matForm S)) = _
      rw [hy]
      rfl

/-- The field `ofChart` on two tangent vectors at a point of the chart domain. -/
lemma SymBilinField.ofChart_apply (x₁ : M) (ρ : M → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ) (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ i j, S i j = S j i) {y : M}
    (hy : y ∈ (chartTriv n x₁).baseSet) (a b : Fin n → ℝ) :
    (SymBilinField.ofChart x₁ ρ hρ hρs S hS).h y ((chartTriv n x₁).symmL ℝ y a)
      ((chartTriv n x₁).symmL ℝ y b) = ρ y * matForm S a b := by
  have h1 := formTriv_apply x₁ hy ((formTriv n x₁).symm y (ρ y • matForm S)) a b
  rw [(formTriv n x₁).apply_mk_symm (mem_formTriv_baseSet x₁ hy)] at h1
  exact h1.symm

/-- **The components of `ofChart` in its chart are `ρ S`.** -/
theorem SymBilinField.coordComp_ofChart (x₁ : M) (ρ : M → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ) (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ i j, S i j = S j i) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) (i j : Fin n) :
    (SymBilinField.ofChart x₁ ρ hρ hρs S hS).coordComp x₁ y i j =
      ρ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) * S i j := by
  rw [SymBilinField.coordComp_eq _ x₁ hy, coordBasis_apply, coordBasis_apply,
    SymBilinField.ofChart_apply x₁ ρ hρ hρs S hS (symm_mem_chartTriv_baseSet x₁ hy), matForm_single]

/-- `ofChart` vanishes where `ρ` does. -/
lemma SymBilinField.ofChart_eq_zero (x₁ : M) (ρ : M → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ) (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ i j, S i j = S j i) {y : M} (hy : ρ y = 0) :
    (SymBilinField.ofChart x₁ ρ hρ hρs S hS).h y = 0 := by
  show (formTriv n x₁).symm y (ρ y • matForm S) = 0
  rw [hy, zero_smul]
  by_cases hyb : y ∈ (formTriv n x₁).baseSet
  · rw [← (formTriv n x₁).symmL_apply (R := ℝ) hyb, map_zero]
  · exact (formTriv n x₁).symm_apply_of_notMem hyb _

end Lightlike

import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.EHManifold.Perturbation

/-!
# Symmetric tensor fields from chart data

`SymBilinField.ofChart x₁ ρ hρ hρs S hS`: for a smooth function `ρ` on `M` supported in the domain of the
chart at `x₁` and a symmetric matrix `S`, the smooth symmetric tensor field whose components in that chart
are `ρ S` (`SymBilinField.coordComp_ofChart`) and which vanishes where `ρ` does.

It is defined with the inverse (`symmL`) of the trivialization of the bundle of bilinear forms, which makes
its smoothness immediate.

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
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  have h2 := Trivialization.coe_linearMapAt_of_mem (R := ℝ)
    (trivializationAt ((Fin n → ℝ) →L[ℝ] ℝ)
      (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x₁) hb
  rw [h2]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  simp

/-- The bilinear form at `y` with components `ρ(y) S` in the chart at `x₁` (zero outside the chart domain). -/
def ofChartFun (x₁ : M) (ρ : M → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (y : M) :
    TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] ℝ :=
  (formTriv n x₁).symmL ℝ y (ρ y • matForm S)

/-- In the trivialization, `ofChartFun` is `ρ S`. -/
lemma formTriv_ofChartFun (x₁ : M) (ρ : M → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) {y : M}
    (hy : y ∈ (chartTriv n x₁).baseSet) :
    ((formTriv n x₁) ⟨y, ofChartFun x₁ ρ S y⟩).2 = ρ y • matForm S := by
  have hy' := mem_formTriv_baseSet x₁ hy
  have h := (formTriv n x₁).continuousLinearMapAt_symmL (R := ℝ) hy' (ρ y • matForm S)
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (e := formTriv n x₁) (hb := hy')] at h
  exact h

/-- `ofChartFun` on two tangent vectors given by their components. -/
lemma ofChartFun_apply (x₁ : M) (ρ : M → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) {y : M}
    (hy : y ∈ (chartTriv n x₁).baseSet) (a b : Fin n → ℝ) :
    ofChartFun x₁ ρ S y ((chartTriv n x₁).symmL ℝ y a) ((chartTriv n x₁).symmL ℝ y b) =
      ρ y * matForm S a b := by
  have h1 := formTriv_apply x₁ hy (ofChartFun x₁ ρ S y) a b
  rw [formTriv_ofChartFun x₁ ρ S hy] at h1
  exact h1.symm

/-- `ofChartFun` vanishes where `ρ` does. -/
lemma ofChartFun_eq_zero (x₁ : M) (ρ : M → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) {y : M}
    (hy : ρ y = 0) : ofChartFun x₁ ρ S y = 0 := by
  have h0 : ρ y • matForm S = 0 := by
    rw [hy]
    ext a b
    simp
  unfold ofChartFun
  rw [h0]
  exact map_zero _

set_option maxHeartbeats 1600000 in
/-- `ofChartFun` is symmetric when `S` is. -/
lemma ofChartFun_symm (x₁ : M) (ρ : M → ℝ) (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ i j, S i j = S j i) (y : M)
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
    ofChartFun x₁ ρ S y v w = ofChartFun x₁ ρ S y w v := by
  by_cases hy : y ∈ (chartTriv n x₁).baseSet
  · have key : ∀ u u' : TangentSpace 𝓘(ℝ, Fin n → ℝ) y,
        ofChartFun x₁ ρ S y u u' =
          ρ y * matForm S ((chartTriv n x₁).continuousLinearMapAt ℝ y u)
            ((chartTriv n x₁).continuousLinearMapAt ℝ y u') := by
      intro u u'
      have h1 := ofChartFun_apply x₁ ρ S hy ((chartTriv n x₁).continuousLinearMapAt ℝ y u)
        ((chartTriv n x₁).continuousLinearMapAt ℝ y u')
      rw [(chartTriv n x₁).symmL_continuousLinearMapAt hy,
        (chartTriv n x₁).symmL_continuousLinearMapAt hy] at h1
      exact h1
    rw [key v w, key w v, matForm_apply, matForm_apply]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hS j i]
    ring
  · have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hρs h)
    rw [ofChartFun_eq_zero x₁ ρ S hρ0]
    rfl

set_option maxHeartbeats 1600000 in
/-- `ofChartFun` is a smooth section of the bundle of bilinear forms. -/
lemma contMDiff_ofChartFun (x₁ : M) (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet) (S : Matrix (Fin n) (Fin n) ℝ) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ)
      (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ)
        x (ofChartFun x₁ ρ S x)) := by
  intro x₀
  by_cases hx : x₀ ∈ (chartTriv n x₁).baseSet
  · rw [(formTriv n x₁).contMDiffAt_section_iff (mem_formTriv_baseSet x₁ hx)]
    have hev : (fun y => ((formTriv n x₁) ⟨y, ofChartFun x₁ ρ S y⟩).2) =ᶠ[𝓝 x₀]
        fun y => ρ y • matForm S := by
      filter_upwards [(chartTriv n x₁).open_baseSet.mem_nhds hx] with y hy
      exact formTriv_ofChartFun x₁ ρ S hy
    exact ((hρ x₀).smul contMDiffAt_const).congr_of_eventuallyEq hev
  · have hx' : x₀ ∉ tsupport ρ := fun h => hx (hρs h)
    have hzs : ContMDiffAt 𝓘(ℝ, Fin n → ℝ)
        (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)) ∞
        (fun x ↦ TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ)
          x 0) x₀ :=
      contMDiff_zeroSection ℝ
        (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x₀
    refine hzs.congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hx'] with y hy
    have h0 := ofChartFun_eq_zero x₁ ρ S (image_eq_zero_of_notMem_tsupport hy)
    simp only [h0]

/-- **A symmetric tensor field with components `ρ S` in the chart at `x₁`.** -/
def SymBilinField.ofChart (x₁ : M) (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = S j i) : SymBilinField 𝓘(ℝ, Fin n → ℝ) M where
  h := ofChartFun x₁ ρ S
  symm := ofChartFun_symm x₁ ρ hρs S hS
  contMDiff := contMDiff_ofChartFun x₁ ρ hρ hρs S

/-- **The components of `ofChart` in its chart are `ρ S`.** -/
theorem SymBilinField.coordComp_ofChart (x₁ : M) (ρ : M → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ) (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ i j, S i j = S j i) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) (i j : Fin n) :
    (SymBilinField.ofChart x₁ ρ hρ hρs S hS).coordComp x₁ y i j =
      ρ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) * S i j := by
  rw [SymBilinField.coordComp_eq _ x₁ hy, coordBasis_apply, coordBasis_apply]
  show ofChartFun x₁ ρ S _ _ _ = _
  rw [ofChartFun_apply x₁ ρ S (symm_mem_chartTriv_baseSet x₁ hy), matForm_single]

/-- `ofChart` vanishes where `ρ` does. -/
lemma SymBilinField.ofChart_eq_zero (x₁ : M) (ρ : M → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ) (hρs : tsupport ρ ⊆ (chartTriv n x₁).baseSet)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : ∀ i j, S i j = S j i) {y : M} (hy : ρ y = 0) :
    (SymBilinField.ofChart x₁ ρ hρ hρs S hS).h y = 0 :=
  ofChartFun_eq_zero x₁ ρ S hy

end Lightlike

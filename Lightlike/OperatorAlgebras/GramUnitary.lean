import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Equal Gram matrices give a unitary

Two linear maps `Φ₁ : (X →₀ ℂ) → K₁` and `Φ₂ : (X →₀ ℂ) → K₂` into Hilbert spaces whose generators have the
same Gram matrix (`⟪Φ₁ eₓ, Φ₁ e_y⟫ = ⟪Φ₂ eₓ, Φ₂ e_y⟫`) have the same norm on every vector
(`norm_eq_of_gram_eq`). If their ranges are dense, there is a unitary `U : K₁ ≃ₗᵢ K₂` with
`U (Φ₁ c) = Φ₂ c` (`exists_unitary_of_gram_eq`), the extension by density of the isometry
`Φ₁ c ↦ Φ₂ c` (Mathlib: `LinearEquiv.extendOfIsometry`). This is the step that built the unitary in the
uniqueness of the Fock representation (`FockUnique.lean`) and builds the Weyl unitaries in its existence.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {X : Type*} {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂]

lemma inner_expand {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Φ : (X →₀ ℂ) →ₗ[ℂ] K) (c d : X →₀ ℂ) :
    ⟪Φ c, Φ d⟫_ℂ = c.sum fun x a => d.sum fun y b =>
      (starRingEnd ℂ) a * b * ⟪Φ (Finsupp.single x 1), Φ (Finsupp.single y 1)⟫_ℂ := by
  have hc : ∀ c : X →₀ ℂ, Φ c = c.sum fun x a => a • Φ (Finsupp.single x 1) := by
    intro c
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [map_finsuppSum]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [← Finsupp.smul_single_one, map_smul]
  rw [hc c, hc d]
  unfold Finsupp.sum
  rw [sum_inner]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

lemma inner_eq_of_gram_eq {Φ₁ : (X →₀ ℂ) →ₗ[ℂ] K₁} {Φ₂ : (X →₀ ℂ) →ₗ[ℂ] K₂}
    (h : ∀ x y, ⟪Φ₁ (Finsupp.single x 1), Φ₁ (Finsupp.single y 1)⟫_ℂ =
      ⟪Φ₂ (Finsupp.single x 1), Φ₂ (Finsupp.single y 1)⟫_ℂ) (c d : X →₀ ℂ) :
    ⟪Φ₁ c, Φ₁ d⟫_ℂ = ⟪Φ₂ c, Φ₂ d⟫_ℂ := by
  rw [inner_expand Φ₁, inner_expand Φ₂]
  simp only [h]

lemma norm_eq_of_gram_eq {Φ₁ : (X →₀ ℂ) →ₗ[ℂ] K₁} {Φ₂ : (X →₀ ℂ) →ₗ[ℂ] K₂}
    (h : ∀ x y, ⟪Φ₁ (Finsupp.single x 1), Φ₁ (Finsupp.single y 1)⟫_ℂ =
      ⟪Φ₂ (Finsupp.single x 1), Φ₂ (Finsupp.single y 1)⟫_ℂ) (c : X →₀ ℂ) :
    ‖Φ₁ c‖ = ‖Φ₂ c‖ := by
  have h2 : ‖Φ₁ c‖ ^ 2 = ‖Φ₂ c‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_eq_of_gram_eq h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

lemma denseRange_subtype_of_dense {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : Submodule ℂ K) (hp : Dense (p : Set K)) : DenseRange p.subtype := by
  rw [DenseRange, Submodule.coe_subtype, Subtype.range_coe]; exact hp

/-- **Equal Gram matrices give a unitary**: if the ranges are dense and complete spaces, there is a unitary
`U` with `U (Φ₁ c) = Φ₂ c`. -/
theorem exists_unitary_of_gram_eq [CompleteSpace K₁] [CompleteSpace K₂]
    {Φ₁ : (X →₀ ℂ) →ₗ[ℂ] K₁} {Φ₂ : (X →₀ ℂ) →ₗ[ℂ] K₂}
    (h : ∀ x y, ⟪Φ₁ (Finsupp.single x 1), Φ₁ (Finsupp.single y 1)⟫_ℂ =
      ⟪Φ₂ (Finsupp.single x 1), Φ₂ (Finsupp.single y 1)⟫_ℂ)
    (hd₁ : Dense ((LinearMap.range Φ₁ : Submodule ℂ K₁) : Set K₁))
    (hd₂ : Dense ((LinearMap.range Φ₂ : Submodule ℂ K₂) : Set K₂)) :
    ∃ U : K₁ ≃ₗᵢ[ℂ] K₂, ∀ c, U (Φ₁ c) = Φ₂ c := by
  have hker : LinearMap.ker Φ₁ = LinearMap.ker Φ₂ := by
    ext c
    simp only [LinearMap.mem_ker, ← norm_eq_zero (E := K₁), ← norm_eq_zero (E := K₂),
      norm_eq_of_gram_eq h c]
  let e : LinearMap.range Φ₁ ≃ₗ[ℂ] LinearMap.range Φ₂ :=
    ((LinearMap.quotKerEquivRange Φ₁).symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      (LinearMap.quotKerEquivRange Φ₂)
  have he : ∀ c, ((e ⟨Φ₁ c, LinearMap.mem_range_self _ c⟩ : _) : K₂) = Φ₂ c := by
    intro c
    have h1 : (LinearMap.quotKerEquivRange Φ₁).symm ⟨Φ₁ c, LinearMap.mem_range_self _ c⟩ =
        Submodule.Quotient.mk c := LinearMap.quotKerEquivRange_symm_apply_image _ c _
    simp [e, h1, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk]
  have hnorm : ∀ x : LinearMap.range Φ₁,
      ‖(LinearMap.range Φ₂).subtype (e x)‖ = ‖(LinearMap.range Φ₁).subtype x‖ := by
    rintro ⟨_, c, rfl⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply]
    have := he c
    simp only at this ⊢
    rw [this, norm_eq_of_gram_eq h c]
  refine ⟨e.extendOfIsometry (LinearMap.range Φ₁).subtype (LinearMap.range Φ₂).subtype
    (denseRange_subtype_of_dense _ hd₁) (denseRange_subtype_of_dense _ hd₂) hnorm, fun c => ?_⟩
  have := LinearEquiv.extendOfIsometry_eq e (LinearMap.range Φ₁).subtype (LinearMap.range Φ₂).subtype
    (denseRange_subtype_of_dense _ hd₁) (denseRange_subtype_of_dense _ hd₂) hnorm
    ⟨Φ₁ c, LinearMap.mem_range_self _ c⟩
  simpa [he c] using this

end Lightlike.OperatorAlgebras

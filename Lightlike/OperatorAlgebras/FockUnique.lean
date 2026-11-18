import Lightlike.OperatorAlgebras.Weyl
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Uniqueness of the Fock representation

Helper lemmas for `T-OP2-P2` (`Tasks/OP/T_OP2_P2.lean`). The Gram matrix `⟪W f Ω, W g Ω⟫` of the vectors
`W f Ω` of a Fock representation is a function of `f` and `g` alone (`fockGram`), by the Weyl relations and
the vacuum expectation. So the map `Σ cᵢ W fᵢ Ω ↦ Σ cᵢ W' fᵢ Ω'` between two Fock representations is
well defined and norm preserving on the (dense) span of these vectors, and extends to a unitary
(Mathlib: `LinearEquiv.extendOfIsometry`).
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The Gram function of the Fock vectors: `⟪W f Ω, W g Ω⟫ = fockGram f g`. -/
noncomputable def fockGram (f g : h) : ℂ :=
  Complex.exp (-(Complex.I * (symp h (-f) g / 2 : ℝ))) * Complex.exp (-(‖-f + g‖ ^ 2 / 4 : ℝ))

lemma symp_neg_self (f : h) : symp h (-f) f = 0 := by
  simp [symp, inner_neg_left, ← Complex.ofReal_pow]

lemma symp_self_neg (f : h) : symp h f (-f) = 0 := by
  simp [symp, inner_neg_right, ← Complex.ofReal_pow]

variable (R : CCRRep h K)

lemma CCRRep.W_zero_apply (ψ : K) : R.W 0 ψ = ψ := by
  rw [R.W_zero]; rfl

lemma CCRRep.W_neg_W (f : h) (ψ : K) : R.W (-f) (R.W f ψ) = ψ := by
  rw [R.weyl, symp_neg_self, neg_add_cancel, R.W_zero_apply]; simp

lemma CCRRep.W_W_neg (f : h) (ψ : K) : R.W f (R.W (-f) ψ) = ψ := by
  rw [R.weyl, symp_self_neg, add_neg_cancel, R.W_zero_apply]; simp

/-- **The Gram matrix of the Fock vectors** `W f Ω` is `fockGram`, whatever the representation. -/
lemma FockRep.inner_W_Ω (R : FockRep h K) (f g : h) :
    ⟪R.W f R.Ω, R.W g R.Ω⟫_ℂ = fockGram f g := by
  have h1 : R.W g R.Ω = R.W f (R.W (-f) (R.W g R.Ω)) := (R.toCCRRep.W_W_neg f _).symm
  conv_lhs => rw [h1]
  rw [LinearIsometryEquiv.inner_map_map, R.weyl, inner_smul_right, R.vacuum_expectation]
  rfl

/-- The linear map `c ↦ ∑ c f • W f Ω` from finitely supported coefficients to the Hilbert space. -/
noncomputable def fockMap (R : FockRep h K) : (h →₀ ℂ) →ₗ[ℂ] K :=
  Finsupp.linearCombination ℂ fun f => R.W f R.Ω

lemma fockMap_inner (R : FockRep h K) (c d : h →₀ ℂ) :
    ⟪fockMap R c, fockMap R d⟫_ℂ =
      c.sum fun f a => d.sum fun g b => (starRingEnd ℂ) a * b * fockGram f g := by
  unfold fockMap
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  rw [sum_inner]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [inner_smul_left, inner_smul_right, R.inner_W_Ω]
  ring

lemma fockMap_norm_eq {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] (R : FockRep h K₁) (S : FockRep h K₂)
    (c : h →₀ ℂ) : ‖fockMap S c‖ = ‖fockMap R c‖ := by
  have h1 : ⟪fockMap R c, fockMap R c⟫_ℂ = ⟪fockMap S c, fockMap S c⟫_ℂ := by
    rw [fockMap_inner, fockMap_inner]
  have h2 : ‖fockMap R c‖ ^ 2 = ‖fockMap S c‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2).symm

lemma fockMap_ker_eq {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] (R : FockRep h K₁) (S : FockRep h K₂) :
    LinearMap.ker (fockMap R) = LinearMap.ker (fockMap S) := by
  ext c
  simp only [LinearMap.mem_ker, ← norm_eq_zero (E := K₁), ← norm_eq_zero (E := K₂),
    fockMap_norm_eq R S c]

lemma range_fockMap (R : FockRep h K) :
    LinearMap.range (fockMap R) = Submodule.span ℂ (Set.range fun f => R.W f R.Ω) :=
  Finsupp.range_linearCombination _

lemma dense_range_fockMap (R : FockRep h K) : Dense ((LinearMap.range (fockMap R) : Submodule ℂ K) : Set K) := by
  rw [range_fockMap, Submodule.dense_iff_topologicalClosure_eq_top]
  exact R.cyclic

lemma denseRange_subtype_fockMap (R : FockRep h K) : DenseRange (LinearMap.range (fockMap R)).subtype := by
  rw [DenseRange, Submodule.coe_subtype, Subtype.range_coe]; exact dense_range_fockMap R

/-- The linear equivalence between the ranges of `fockMap R` and `fockMap S`, `Φ_R c ↦ Φ_S c`. -/
noncomputable def fockEquiv {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] (R : FockRep h K₁) (S : FockRep h K₂) :
    LinearMap.range (fockMap R) ≃ₗ[ℂ] LinearMap.range (fockMap S) :=
  ((LinearMap.quotKerEquivRange (fockMap R)).symm.trans
    (Submodule.quotEquivOfEq _ _ (fockMap_ker_eq R S))).trans (LinearMap.quotKerEquivRange (fockMap S))

lemma fockEquiv_apply {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] (R : FockRep h K₁) (S : FockRep h K₂)
    (c : h →₀ ℂ) : ((fockEquiv R S ⟨fockMap R c, LinearMap.mem_range_self _ c⟩ : _) : K₂) = fockMap S c := by
  unfold fockEquiv
  have h1 : (LinearMap.quotKerEquivRange (fockMap R)).symm ⟨fockMap R c, LinearMap.mem_range_self _ c⟩ =
      Submodule.Quotient.mk c := LinearMap.quotKerEquivRange_symm_apply_image _ c _
  simp [h1, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk]

section Unitary

variable {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- The unitary between two Fock representations, the extension of `Φ_R c ↦ Φ_S c` by density. -/
noncomputable def fockUnitary (R : FockRep h K₁) (S : FockRep h K₂) : K₁ ≃ₗᵢ[ℂ] K₂ :=
  (fockEquiv R S).extendOfIsometry (LinearMap.range (fockMap R)).subtype
    (LinearMap.range (fockMap S)).subtype
    (denseRange_subtype_fockMap R)
    (denseRange_subtype_fockMap S)
    (by
      rintro ⟨_, c, rfl⟩
      rw [Submodule.subtype_apply, Submodule.subtype_apply]
      have := fockEquiv_apply R S c
      simp only at this ⊢
      rw [this, fockMap_norm_eq R S c])

lemma fockUnitary_fockMap (R : FockRep h K₁) (S : FockRep h K₂) (c : h →₀ ℂ) :
    fockUnitary R S (fockMap R c) = fockMap S c := by
  have := LinearEquiv.extendOfIsometry_eq (fockEquiv R S) (LinearMap.range (fockMap R)).subtype
    (LinearMap.range (fockMap S)).subtype
    (denseRange_subtype_fockMap R)
    (denseRange_subtype_fockMap S)
    (by
      rintro ⟨_, c, rfl⟩
      rw [Submodule.subtype_apply, Submodule.subtype_apply]
      have := fockEquiv_apply R S c
      simp only at this ⊢
      rw [this, fockMap_norm_eq R S c]) ⟨fockMap R c, LinearMap.mem_range_self _ c⟩
  simpa [fockUnitary, fockEquiv_apply] using this

lemma fockUnitary_W_Ω (R : FockRep h K₁) (S : FockRep h K₂) (g : h) :
    fockUnitary R S (R.W g R.Ω) = S.W g S.Ω := by
  have := fockUnitary_fockMap R S (Finsupp.single g 1)
  simpa [fockMap] using this

/-- **Uniqueness of the Fock representation**: the unitary `fockUnitary R S` maps the vacuum to the vacuum
and intertwines the Weyl unitaries. -/
theorem fockUnitary_spec (R : FockRep h K₁) (S : FockRep h K₂) :
    fockUnitary R S R.Ω = S.Ω ∧ ∀ f ψ, fockUnitary R S (R.W f ψ) = S.W f (fockUnitary R S ψ) := by
  refine ⟨?_, fun f => ?_⟩
  · have := fockUnitary_W_Ω R S 0
    rwa [R.toCCRRep.W_zero_apply, S.toCCRRep.W_zero_apply] at this
  · have hd : Dense ((Submodule.span ℂ (Set.range fun g => R.W g R.Ω) : Submodule ℂ K₁) : Set K₁) := by
      rw [← range_fockMap]; exact dense_range_fockMap R
    have hc1 : Continuous fun ψ => fockUnitary R S (R.W f ψ) :=
      (fockUnitary R S).continuous.comp (R.W f).continuous
    have hc2 : Continuous fun ψ => S.W f (fockUnitary R S ψ) :=
      (S.W f).continuous.comp (fockUnitary R S).continuous
    have := Continuous.ext_on hd hc1 hc2 (fun ψ hψ => by
      induction hψ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        show fockUnitary R S (R.W f (R.W g R.Ω)) = S.W f (fockUnitary R S (R.W g R.Ω))
        rw [fockUnitary_W_Ω, R.weyl, map_smul, fockUnitary_W_Ω, S.weyl]
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | smul a x _ hx => simp only [map_smul] at hx ⊢; rw [hx])
    exact fun ψ => congrFun this ψ

end Unitary

end Lightlike.OperatorAlgebras

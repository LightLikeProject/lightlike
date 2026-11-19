import Lightlike.OperatorAlgebras.FiniteRankApprox
import Lightlike.OperatorAlgebras.TraceClass.BoundedSesquilinearForm
import Lightlike.OperatorAlgebras.TraceClass.TracePairingSurjectivity
import Lightlike.OperatorAlgebras.TraceClass.Polar

/-!
# The dual of the compact operators: the representing operator

Second brick toward `T-OP6-P1` (`K* ≅ S¹`). A continuous functional `f` on the compact operators `𝒦(H)` of a complex Hilbert
space gives, on rank-one operators, the bounded sesquilinear form `(x, y) ↦ conj (f |x⟩⟨y|)` (`‖|x⟩⟨y|‖ = ‖x‖ ‖y‖`), hence a bounded operator
`T` with `⟪y, T x⟫ = f |x⟩⟨y|` (`compactFunctionalOperator_inner`). The next brick shows `T` is trace class.
-/

open scoped InnerProductSpace ComplexOrder

namespace Lightlike.OperatorAlgebras

open TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compact operators as a normed space (a submodule of the bounded operators). -/
abbrev CompactOps (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  compactOperator (RingHom.id ℂ) H H

/-- The rank-one operator `|x⟩⟨y|` as a compact operator. -/
noncomputable def rankOneCompact (x y : H) : CompactOps H :=
  ⟨InnerProductSpace.rankOne ℂ x y, isCompactOperator_rankOne x y⟩

lemma norm_rankOneCompact (x y : H) : ‖rankOneCompact x y‖ = ‖x‖ * ‖y‖ :=
  InnerProductSpace.norm_rankOne x y

lemma rankOneCompact_add_right (x y z : H) :
    rankOneCompact x (y + z) = rankOneCompact x y + rankOneCompact x z := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ x (y + z) = InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ x z
  ext v
  simp [InnerProductSpace.rankOne_apply]

lemma rankOneCompact_smul_right (c : ℂ) (x y : H) :
    rankOneCompact x (c • y) = (starRingEnd ℂ c) • rankOneCompact x y := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ x (c • y) = (starRingEnd ℂ c) • InnerProductSpace.rankOne ℂ x y
  ext v
  simp [InnerProductSpace.rankOne_apply]

lemma rankOneCompact_add_left (x z y : H) :
    rankOneCompact (x + z) y = rankOneCompact x y + rankOneCompact z y := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ (x + z) y = InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ z y
  ext v
  simp [InnerProductSpace.rankOne_apply]

lemma rankOneCompact_smul_left (c : ℂ) (x y : H) :
    rankOneCompact (c • x) y = c • rankOneCompact x y := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ (c • x) y = c • InnerProductSpace.rankOne ℂ x y
  ext v
  simp

/-- The bounded sesquilinear form `(x, y) ↦ conj (f |x⟩⟨y|)` of a continuous functional `f` on the compact operators. -/
noncomputable def sesquilinearFormOfCompactFunctional (f : CompactOps H →L[ℂ] ℂ) : BoundedSesquilinearForm H :=
  { form :=
      { toFun := fun x =>
          { toFun := fun y => starRingEnd ℂ (f (rankOneCompact x y))
            map_add' := fun y z => by rw [rankOneCompact_add_right, map_add]; simp
            map_smul' := fun c y => by rw [rankOneCompact_smul_right, map_smul]; simp }
        map_add' := fun x z => by
          apply LinearMap.ext; intro y
          change starRingEnd ℂ (f (rankOneCompact (x + z) y)) = _
          rw [rankOneCompact_add_left, map_add]; simp
        map_smul' := fun c x => by
          apply LinearMap.ext; intro y
          change starRingEnd ℂ (f (rankOneCompact (c • x) y)) = _
          rw [rankOneCompact_smul_left, map_smul]; simp }
    bound := by
      refine ⟨‖f‖, fun x y => ?_⟩
      change ‖starRingEnd ℂ (f (rankOneCompact x y))‖ ≤ ‖f‖ * ‖x‖ * ‖y‖
      rw [← RCLike.star_def, norm_star]
      calc ‖f (rankOneCompact x y)‖ ≤ ‖f‖ * ‖rankOneCompact x y‖ := f.le_opNorm _
        _ = ‖f‖ * ‖x‖ * ‖y‖ := by rw [norm_rankOneCompact, mul_assoc] }

/-- The bounded operator `T` of a continuous functional `f` on the compact operators. -/
noncomputable def compactFunctionalOperator (f : CompactOps H →L[ℂ] ℂ) : H →L[ℂ] H :=
  (sesquilinearFormOfCompactFunctional f).operator

/-- **`⟪y, T x⟫ = f |x⟩⟨y|`**. -/
theorem compactFunctionalOperator_inner (f : CompactOps H →L[ℂ] ℂ) (x y : H) :
    ⟪y, compactFunctionalOperator f x⟫_ℂ = f (rankOneCompact x y) := by
  rw [compactFunctionalOperator, BoundedSesquilinearForm.operator_inner]
  change starRingEnd ℂ (starRingEnd ℂ (f (rankOneCompact x y))) = _
  simp

section PartialSums

variable {ι : Type*}

/-- **The operator `∑_{i ∈ F} |bᵢ⟩⟨ψᵢ|` for an orthonormal family `b` and vectors `ψᵢ = W bᵢ` with `W` a contraction has norm `≤ 1`**:
`‖A z‖² = ∑ |⟪W bᵢ, z⟫|² = ∑ |⟪bᵢ, W† z⟫|² ≤ ‖W† z‖² ≤ ‖z‖²` (Bessel). -/
theorem norm_sum_rankOne_le {b : ι → H} (hb : Orthonormal ℂ b) (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1) (F : Finset ι) :
    ‖∑ i ∈ F, InnerProductSpace.rankOne ℂ (b i) (W (b i))‖ ≤ 1 := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  set c : ι → ℂ := fun i => ⟪W (b i), z⟫_ℂ with hc
  have hAz : (∑ i ∈ F, InnerProductSpace.rankOne ℂ (b i) (W (b i))) z = ∑ i ∈ F, c i • b i := by
    simp [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply, hc]
  have hinner : ∀ j ∈ F, ⟪b j, ∑ i ∈ F, c i • b i⟫_ℂ = c j := fun j hj => hb.inner_right_sum c hj
  have hsq : ‖∑ i ∈ F, c i • b i‖ ^ 2 = ∑ i ∈ F, ‖c i‖ ^ 2 := by
    have h1 : ⟪∑ i ∈ F, c i • b i, ∑ i ∈ F, c i • b i⟫_ℂ = ((∑ i ∈ F, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [sum_inner]
      push_cast
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [inner_smul_left, hinner i hi, Complex.conj_mul']
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ i ∈ F, c i • b i)
    rw [h1] at h2
    have h4 : ((‖∑ i ∈ F, c i • b i‖ ^ 2 : ℝ) : ℂ) = ((∑ i ∈ F, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, Complex.ofReal_pow]
      push_cast at h2 ⊢
      exact h2.symm
    exact Complex.ofReal_injective h4
  have hbes : ∑ i ∈ F, ‖c i‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    have hcc : ∀ i, c i = ⟪b i, (ContinuousLinearMap.adjoint W) z⟫_ℂ := fun i => by
      simp [hc, ContinuousLinearMap.adjoint_inner_right]
    calc ∑ i ∈ F, ‖c i‖ ^ 2 = ∑ i ∈ F, ‖⟪b i, (ContinuousLinearMap.adjoint W) z⟫_ℂ‖ ^ 2 := by simp_rw [hcc]
      _ ≤ ‖(ContinuousLinearMap.adjoint W) z‖ ^ 2 := hb.sum_inner_products_le _
      _ ≤ ‖z‖ ^ 2 := by
        have h1 : ‖ContinuousLinearMap.adjoint W‖ ≤ 1 := by
          rw [ContinuousLinearMap.adjoint.norm_map]; exact hW
        have h3 : ‖(ContinuousLinearMap.adjoint W) z‖ ≤ ‖z‖ :=
          ((ContinuousLinearMap.adjoint W).le_opNorm z).trans (by nlinarith [norm_nonneg z])
        exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  rw [hAz, one_mul]
  have : ‖∑ i ∈ F, c i • b i‖ ^ 2 ≤ ‖z‖ ^ 2 := hsq ▸ hbes
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

/-- **The diagonal sums of `|T|` are bounded by `‖f‖`**: for the operator `T` of a continuous functional `f` on the compact operators and
an orthonormal family `b`, `∑_{i ∈ F} ⟪bᵢ, |T| bᵢ⟫ ≤ ‖f‖`. Indeed `⟪bᵢ, |T| bᵢ⟫ = ⟪W bᵢ, T bᵢ⟫ = f |bᵢ⟩⟨W bᵢ|` with `W` the polar factor, so the
sum is `f (∑ |bᵢ⟩⟨W bᵢ|)` and the operator has norm `≤ 1`. -/
theorem sum_abs_inner_le (f : CompactOps H →L[ℂ] ℂ) {b : ι → H} (hb : Orthonormal ℂ b) (F : Finset ι) :
    ∑ i ∈ F, (⟪b i, CFC.abs (compactFunctionalOperator f) (b i)⟫_ℂ).re ≤ ‖f‖ := by
  classical
  set T := compactFunctionalOperator f with hT
  set W := Polar.polarFactor T with hW
  have hterm : ∀ i, ⟪b i, CFC.abs T (b i)⟫_ℂ = f (rankOneCompact (b i) (W (b i))) := by
    intro i
    have habs : CFC.abs T = ContinuousLinearMap.adjoint W * T := by
      rw [← Polar.absOperator, ← Polar.star_polarFactor_mul_self T, ContinuousLinearMap.star_eq_adjoint]
    rw [habs, ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right,
      compactFunctionalOperator_inner]
  have hsum : (∑ i ∈ F, rankOneCompact (b i) (W (b i))) =
      ⟨∑ i ∈ F, InnerProductSpace.rankOne ℂ (b i) (W (b i)),
        Submodule.sum_mem _ fun i _ => isCompactOperator_rankOne _ _⟩ := by
    apply Subtype.ext
    simp [rankOneCompact]
  have hnorm : ‖∑ i ∈ F, rankOneCompact (b i) (W (b i))‖ ≤ 1 := by
    rw [hsum]
    exact norm_sum_rankOne_le hb W (Polar.polarFactor_opNorm_le T) F
  calc ∑ i ∈ F, (⟪b i, CFC.abs T (b i)⟫_ℂ).re
      = (f (∑ i ∈ F, rankOneCompact (b i) (W (b i)))).re := by
        rw [map_sum, Complex.re_sum]; simp_rw [hterm]
    _ ≤ ‖f (∑ i ∈ F, rankOneCompact (b i) (W (b i)))‖ := Complex.re_le_norm _
    _ ≤ ‖f‖ * ‖∑ i ∈ F, rankOneCompact (b i) (W (b i))‖ := f.le_opNorm _
    _ ≤ ‖f‖ * 1 := by gcongr
    _ = ‖f‖ := mul_one _

end PartialSums

/-- **The operator of a continuous functional on the compact operators is trace class**. -/
theorem isTraceClass_compactFunctionalOperator (f : CompactOps H →L[ℂ] ℂ) :
    IsTraceClass (compactFunctionalOperator f) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  refine summable_of_sum_le (c := ‖f‖) (fun i => ?_) fun F => sum_abs_inner_le f b.orthonormal F
  exact real_inner_nonneg_of_nonneg (CFC.abs_nonneg (compactFunctionalOperator f)) (b i)

/-- **The trace norm of the operator of `f` is at most `‖f‖`**. -/
theorem traceNorm_compactFunctionalOperator_le (f : CompactOps H →L[ℂ] ℂ) :
    traceNorm (compactFunctionalOperator f) (isTraceClass_compactFunctionalOperator f) ≤ ‖f‖ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis (isTraceClass_compactFunctionalOperator f) b]
  exact Real.tsum_le_of_sum_le (fun i => real_inner_nonneg_of_nonneg (CFC.abs_nonneg (compactFunctionalOperator f)) (b i))
    fun F => sum_abs_inner_le f b.orthonormal F

end Lightlike.OperatorAlgebras

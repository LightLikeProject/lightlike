import Lightlike.Poincare.SnagJoint

/-!
# Covariance of the joint spectral measure

Conjugating a projection-valued measure by a unitary `W` gives a projection-valued measure (`conjPVM`), whose scalar
measures and integrals are those of the original one transported by `W` (`assoc_conjPVM`, `integral_conjPVM`). If
`W T(a) W⁻¹ = T(L a)` for the unitary representation `T(a) = ∫ e^{i⟨a, p⟩} dP(p)` of `ℝⁿ`, with `⟨L a, p⟩ = ⟨a, L' p⟩`,
then `W P(S) W⁻¹ = P(L'⁻¹ S)` for every Borel set `S` (`covariant_jointSpectralMeasure`, from the uniqueness of `P`),
and a Borel set invariant under all such `L'` has a projection commuting with every `W` and every `T(a)`
(`commute_of_invariant`).

## References

* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §7, Lemma 7.1 (the projection-valued measure of an irreducible representation is ergodic), page 150.
-/

open scoped InnerProductSpace
open Filter Topology MeasureTheory Lightlike.OperatorAlgebras.Spectral Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Poincare

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {X : Type*} [MeasurableSpace X]

lemma inner_symm_apply (W : H ≃ₗᵢ[ℂ] H) (u y : H) : ⟪W.symm u, y⟫_ℂ = ⟪u, W y⟫_ℂ := by
  rw [← W.inner_map_map, LinearIsometryEquiv.apply_symm_apply]

/-- The operator `W⁻¹ B W`. -/
def conjOp (W : H ≃ₗᵢ[ℂ] H) (B : H →L[ℂ] H) : H →L[ℂ] H :=
  (W.symm.toContinuousLinearEquiv : H →L[ℂ] H) ∘L B ∘L (W.toContinuousLinearEquiv : H →L[ℂ] H)

@[simp] lemma conjOp_apply (W : H ≃ₗᵢ[ℂ] H) (B : H →L[ℂ] H) (ψ : H) : conjOp W B ψ = W.symm (B (W ψ)) := rfl

lemma conjOp_mul (W : H ≃ₗᵢ[ℂ] H) (B B' : H →L[ℂ] H) : conjOp W (B * B') = conjOp W B * conjOp W B' := by
  ext ψ; simp

lemma isStarProjection_conjOp (W : H ≃ₗᵢ[ℂ] H) {B : H →L[ℂ] H} (hB : IsStarProjection B) :
    IsStarProjection (conjOp W B) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, ← conjOp_mul, hB.isIdempotentElem.eq]
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hB.isSelfAdjoint) (W x) (W y)
    simp only [ContinuousLinearMap.coe_coe, conjOp_apply] at hs ⊢
    rw [inner_symm_apply, hs, ← inner_symm_apply W.symm, LinearIsometryEquiv.symm_symm]

/-- **A projection-valued measure conjugated by a unitary**: `E ↦ W⁻¹ μ(E) W`. -/
def conjPVM (W : H ≃ₗᵢ[ℂ] H) (μ : ProjectionValuedMeasure X H) : ProjectionValuedMeasure X H where
  toFun E := conjOp W (μ E)
  isStarProjection' E := isStarProjection_conjOp W (μ.isStarProjection_apply E)
  notMeasurable' E hE := by
    ext ψ; simp [μ.apply_of_not_measurableSet hE]
  univ' := by
    ext ψ; simp [μ.apply_univ]
  hasSum' E hE hdisj v := by
    have h := (μ.hasSum_apply E hE hdisj (W v)).map (W.symm.toLinearIsometry.toLinearMap)
      W.symm.continuous
    exact h
  inter' E F hE hF := by
    rw [μ.apply_inter hE hF, conjOp_mul]

@[simp] lemma conjPVM_apply (W : H ≃ₗᵢ[ℂ] H) (μ : ProjectionValuedMeasure X H) (E : Set X) (ψ : H) :
    conjPVM W μ E ψ = W.symm (μ E (W ψ)) := rfl

lemma assoc_conjPVM (W : H ≃ₗᵢ[ℂ] H) (μ : ProjectionValuedMeasure X H) (ψ : H) :
    (conjPVM W μ).assoc ψ = μ.assoc (W ψ) := by
  refine (ProjectionValuedMeasure.existsUnique_assoc (conjPVM W μ) ψ).unique
    ⟨inferInstance, fun E hE => ProjectionValuedMeasure.assoc_apply _ ψ hE⟩
    ⟨inferInstance, fun E hE => ?_⟩
  rw [ProjectionValuedMeasure.assoc_apply _ _ hE, conjPVM_apply, ← inner_symm_apply W.symm,
    LinearIsometryEquiv.symm_symm]

lemma integral_conjPVM (W : H ≃ₗᵢ[ℂ] H) (μ : ProjectionValuedMeasure X H) {f : X → ℂ}
    (hf : f ∈ BddMeasurable X) : (conjPVM W μ).integral f = conjOp W (μ.integral f) := by
  have hq : ∀ ψ : H, ⟪((conjPVM W μ).integral f - conjOp W (μ.integral f)) ψ, ψ⟫_ℂ = 0 := by
    intro ψ
    rw [_root_.sub_apply, inner_sub_left, ← inner_conj_symm, ← inner_conj_symm (conjOp W _ ψ),
      ProjectionValuedMeasure.inner_integral _ hf, assoc_conjPVM, conjOp_apply, ← inner_symm_apply W.symm,
      LinearIsometryEquiv.symm_symm, ProjectionValuedMeasure.inner_integral _ hf, sub_self]
  have h0 := (inner_map_self_eq_zero (((conjPVM W μ).integral f - conjOp W (μ.integral f) : H →L[ℂ] H) :
    H →ₗ[ℂ] H)).1 hq
  exact sub_eq_zero.1 (ContinuousLinearMap.coe_injective h0)

/-! ## Covariance -/

variable {n : ℕ}

/-- **Covariance of the joint spectral measure**: if `W T(a) = T(L a) W` and `⟨L a, p⟩ = ⟨a, L' p⟩`, then
`W P(S) = P(L'⁻¹ S) W`. -/
theorem covariant_jointSpectralMeasure {T : (Fin n → ℝ) → (H ≃ₗᵢ[ℂ] H)}
    {P : ProjectionValuedMeasure (Fin n → ℝ) H}
    (hP : ∀ a ψ, T a ψ = P.integral (fun p => Complex.exp (Complex.I * ((∑ k, a k * p k : ℝ) : ℂ))) ψ)
    (W : H ≃ₗᵢ[ℂ] H) (L : (Fin n → ℝ) → (Fin n → ℝ)) (L' : (Fin n → ℝ) → (Fin n → ℝ)) (hL' : Measurable L')
    (hdual : ∀ a p, ∑ k, L a k * p k = ∑ k, a k * L' p k)
    (hW : ∀ a ψ, W (T a ψ) = T (L a) (W ψ)) {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (ψ : H) :
    W (P S ψ) = P (L' ⁻¹' S) (W ψ) := by
  have heq : conjPVM W (pushforwardPVM P L' hL') = P := by
    refine jointSpectralMeasure_unique fun a => ?_
    rw [integral_conjPVM _ _ (expCoord_mem_bddMeasurable a Finset.univ),
      integral_pushforwardPVM _ hL' (expCoord_mem_bddMeasurable a Finset.univ)]
    ext ψ
    have e : ((fun p : Fin n → ℝ => Complex.exp (Complex.I * ((∑ k, a k * p k : ℝ) : ℂ))) ∘ L') =
        fun p => Complex.exp (Complex.I * ((∑ k, L a k * p k : ℝ) : ℂ)) := by
      funext p
      simp only [Function.comp_apply, hdual]
    rw [conjOp_apply, e, ← hP, ← hW, LinearIsometryEquiv.symm_apply_apply, hP]
  have h := congrArg (fun μ : ProjectionValuedMeasure (Fin n → ℝ) H => μ S ψ) heq
  simp only [conjPVM_apply, pushforwardPVM_apply _ hL' hS] at h
  rw [← h, LinearIsometryEquiv.apply_symm_apply]

/-- The projections of a projection-valued measure commute with its integrals. -/
lemma apply_commute_integral (P : ProjectionValuedMeasure X H) {S : Set X} (hS : MeasurableSet S)
    {f : X → ℂ} (hf : f ∈ BddMeasurable X) (ψ : H) : P S (P.integral f ψ) = P.integral f (P S ψ) := by
  have hb := (indicator_one_mem_bddMeasurable_iff (X := X)).2 hS
  rw [← ProjectionValuedMeasure.integral_indicator _ hS, ← ContinuousLinearMap.mul_apply,
    ← ContinuousLinearMap.mul_apply, ← ProjectionValuedMeasure.integral_mul _ hb hf,
    ← ProjectionValuedMeasure.integral_mul _ hf hb, mul_comm]

/-- **Invariant Borel sets give commuting projections** (Freitag, Lemma V.7.1): if `L'⁻¹ S = S` for the dual
action of every symmetry `W`, then `P(S)` commutes with every `W` and every translation. -/
theorem commute_of_invariant {T : (Fin n → ℝ) → (H ≃ₗᵢ[ℂ] H)} {P : ProjectionValuedMeasure (Fin n → ℝ) H}
    (hP : ∀ a ψ, T a ψ = P.integral (fun p => Complex.exp (Complex.I * ((∑ k, a k * p k : ℝ) : ℂ))) ψ)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    (∀ a ψ, P S (T a ψ) = T a (P S ψ)) ∧
    ∀ (W : H ≃ₗᵢ[ℂ] H) (L L' : (Fin n → ℝ) → (Fin n → ℝ)) (hL' : Measurable L'),
      (∀ a p, ∑ k, L a k * p k = ∑ k, a k * L' p k) → (∀ a ψ, W (T a ψ) = T (L a) (W ψ)) → L' ⁻¹' S = S →
        ∀ ψ, W (P S ψ) = P S (W ψ) := by
  refine ⟨fun a ψ => ?_, fun W L L' hL' hdual hW hinv ψ => ?_⟩
  · rw [hP, hP, apply_commute_integral P hS (expCoord_mem_bddMeasurable a Finset.univ)]
  · rw [covariant_jointSpectralMeasure hP W L L' hL' hdual hW hS, hinv]

end

end Lightlike.Poincare

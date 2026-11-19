import Lightlike.Poincare.SnagGelfand
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The joint spectral measure of a unitary representation of `ℝⁿ` (SNAG)

For a strongly continuous unitary representation `T` of the additive group `ℝⁿ` there is a projection-valued measure
`P` on `ℝⁿ` with `T(a) = ∫ e^{i⟨a, p⟩} dP(p)` (`exists_jointSpectralMeasure`). Proof: the one-parameter groups
`t ↦ T(t e_k)` commute; by Stone's theorem they have self-adjoint generators `A_k`, whose Cayley transforms `C_k`
commute (`cayley_commute_of_commute`); the joint projection-valued measure of the `C_k` on their joint spectrum
(`jointPVM`), pushed forward by the inverse Cayley map coordinatewise, is `P`. Its `k`-th marginal is the spectral
measure of `A_k` (by the uniqueness in the spectral theorem, `eq_cayleyPVM_of_pmapIntegral_eq`), so
`T(t e_k) = e^{itA_k} = ∫ e^{itp_k} dP(p)`, and the product over `k` gives the formula. The measure is unique
(`jointSpectralMeasure_unique`: the scalar measures `⟨ψ, P(·)ψ⟩` are determined by their characteristic functions).

## References

* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §5, Theorem 5.1 (Stone's theorem for `ℝⁿ`, as a unitary equivalence with a multiplication
  representation), page 146; Remark 5.3 (the operators `S(φ)` depend only on the representation), Remark 5.4 and
  Definition 5.5 (projection-valued measures), page 147.

Difference from the source (representation): Theorem 5.1 is stated in the projection-valued-measure form of Remarks
5.3, 5.4 and Definition 5.5, not as a unitary equivalence with a multiplication representation. Uniqueness, the
content of Remark 5.3, is `jointSpectralMeasure_unique`.
-/

open scoped InnerProductSpace IsMulCommutative
open Filter Topology MeasureTheory Lightlike.OperatorAlgebras.Spectral Lightlike.OperatorAlgebras.Spectral.Stone
  Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Poincare

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}

/-! ## The marginals of the joint measure -/

section Marginal

variable {C : Fin n → H →L[ℂ] H} (hC : CommutingUnitaries C)

lemma coord_mem_spectrum (z : jointSpectrum hC) (k : Fin n) : (z : Fin n → ℂ) k ∈ spectrum ℂ (C k) := by
  letI := jointCommAlg hC
  obtain ⟨χ, hχ⟩ := z.2
  have h1 := WeakDual.CharacterSpace.apply_mem_spectrum χ (jointGen (C := C) k)
  haveI : IsClosed ((jointAlg C : Set (H →L[ℂ] H))) := (StarAlgebra.adjoin ℂ _).isClosed_topologicalClosure
  have h2 := (StarSubalgebra.mem_spectrum_iff (jointAlg C)).1 h1
  rw [← hχ]
  exact h2

/-- The `k`-th coordinate, into the spectrum of `C_k`. -/
def coordK (k : Fin n) (z : jointSpectrum hC) : spectrum ℂ (C k) := ⟨(z : Fin n → ℂ) k, coord_mem_spectrum hC z k⟩

lemma measurable_coordK (k : Fin n) : Measurable (coordK hC k) :=
  (Continuous.subtype_mk ((continuous_apply k).comp continuous_subtype_val) _).measurable

/-- The `k`-th marginal of the joint measure, on the spectrum of `C_k`. -/
def marginalSpec (k : Fin n) : ProjectionValuedMeasure (spectrum ℂ (C k)) H :=
  pushforwardPVM (jointPVM hC) (coordK hC k) (measurable_coordK hC k)

lemma marginalSpec_integral (k : Fin n) : (marginalSpec hC k).integral (fun u => (u : ℂ)) = C k := by
  have hb : (fun u : spectrum ℂ (C k) => (u : ℂ)) ∈ BddMeasurable (spectrum ℂ (C k)) :=
    ⟨continuous_subtype_val.measurable, 1, fun u => by
      have h := spectrum.subset_circle_of_unitary (𝕜 := ℂ) (hC.mem_unitary k) u.2
      rw [mem_sphere_zero_iff_norm] at h
      exact h.le⟩
  rw [marginalSpec, integral_pushforwardPVM _ _ hb]
  exact jointPVM_integral_coord hC k

end Marginal

/-! ## Unitary representations of `ℝⁿ` -/

/-- A strongly continuous unitary representation of the additive group `ℝⁿ`. -/
structure IsUnitaryRepRn (T : (Fin n → ℝ) → (H ≃ₗᵢ[ℂ] H)) : Prop where
  map_zero : ∀ ψ, T 0 ψ = ψ
  map_add : ∀ a b ψ, T (a + b) ψ = T a (T b ψ)
  continuous : ∀ ψ, Continuous fun a => T a ψ

lemma norm_exp_I_mul_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

lemma expCoord_mem_bddMeasurable (b : Fin n → ℝ) (s : Finset (Fin n)) :
    (fun p : Fin n → ℝ => Complex.exp (Complex.I * ((∑ k ∈ s, b k * p k : ℝ) : ℂ))) ∈ BddMeasurable (Fin n → ℝ) :=
  ⟨(Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k))))).measurable,
    1, fun p => (norm_exp_I_mul_ofReal _).le⟩

/-- **SNAG for `ℝⁿ`**: a strongly continuous unitary representation of `ℝⁿ` is `T(a) = ∫ e^{i⟨a, p⟩} dP(p)` for a
projection-valued measure `P` on `ℝⁿ`. -/
theorem exists_jointSpectralMeasure {T : (Fin n → ℝ) → (H ≃ₗᵢ[ℂ] H)} (hT : IsUnitaryRepRn T) :
    ∃ P : ProjectionValuedMeasure (Fin n → ℝ) H, ∀ a ψ,
      T a ψ = P.integral (fun p => Complex.exp (Complex.I * ((∑ k, a k * p k : ℝ) : ℂ))) ψ := by
  -- the one-parameter groups along the axes
  set U : Fin n → ℝ → (H ≃ₗᵢ[ℂ] H) := fun k t => T (Pi.single k t) with hUdef
  have hU : ∀ k, IsOneParameterUnitaryGroup (U k) := fun k =>
    ⟨fun ψ => by simp only [hUdef, Pi.single_zero, hT.map_zero],
     fun s t ψ => by simp only [hUdef, Pi.single_add, hT.map_add]⟩
  have hc : ∀ k, IsStronglyContinuous (U k) := fun k ψ => by
    have h : Continuous fun t : ℝ => (Pi.single k t : Fin n → ℝ) := continuous_single (A := fun _ : Fin n => ℝ) k
    exact (hT.continuous ψ).comp h
  have hcomm : ∀ j k (s t : ℝ) (ψ : H), U j s (U k t ψ) = U k t (U j s ψ) := by
    intro j k s t ψ
    simp only [hUdef]
    rw [← hT.map_add, ← hT.map_add, add_comm]
  -- Stone's theorem and the Cayley transforms
  choose hA _ hexp _ using fun k => stone (hU k) (hc k)
  choose B C hCay hCu _ _ _ hC1 using fun k => exists_isCayleyTransform (hA k)
  have hC : CommutingUnitaries C := ⟨hCu, fun j k => ContinuousLinearMap.ext fun φ =>
    cayley_commute_of_commute (hcomm j k) (hCay j) (hCay k) φ⟩
  -- the joint measure on `ℝⁿ`
  have hF : Measurable fun z : jointSpectrum hC => fun k => cayleyInv ((z : Fin n → ℂ) k) :=
    measurable_pi_iff.2 fun k => measurable_cayleyInv.comp ((measurable_pi_apply k).comp measurable_subtype_coe)
  set P := pushforwardPVM (jointPVM hC) _ hF
  -- the marginals are the spectral measures of the generators
  have hmarg : ∀ k (t : ℝ) (ψ : H), U k t ψ = P.integral (fun p => Complex.exp (Complex.I * ((t * p k : ℝ) : ℂ))) ψ := by
    intro k t ψ
    have h1 := eq_cayleyPVM_of_pmapIntegral_eq (hCay k) (hCu k) (hC1 k) (marginalSpec_integral hC k)
      (pmapIntegral_spectralMeasure (hA k))
    have hFk : Measurable fun z : jointSpectrum hC => cayleyInv ((z : Fin n → ℂ) k) :=
      measurable_cayleyInv.comp ((measurable_pi_apply k).comp measurable_subtype_coe)
    have h2 : cayleyPVM (marginalSpec hC k) = pushforwardPVM (jointPVM hC) _ hFk := by
      refine ProjectionValuedMeasure.ext fun E => ?_
      by_cases hE : MeasurableSet E
      · have hE' : MeasurableSet {u : spectrum ℂ (C k) | cayleyInv (u : ℂ) ∈ E} :=
          (measurable_cayleyInv.comp measurable_subtype_coe) hE
        rw [cayleyPVM_apply _ hE, pushforwardPVM_apply _ hFk hE, marginalSpec,
          pushforwardPVM_apply _ (measurable_coordK hC k) hE']
        rfl
      · rw [ProjectionValuedMeasure.apply_of_not_measurableSet _ hE,
          ProjectionValuedMeasure.apply_of_not_measurableSet _ hE]
    have hb : expFun t ∈ BddMeasurable ℝ := expFun_mem_bddMeasurable t
    have hbP : (fun p : Fin n → ℝ => Complex.exp (Complex.I * ((t * p k : ℝ) : ℂ))) ∈ BddMeasurable (Fin n → ℝ) :=
      ⟨(Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_apply k))))).measurable, 1, fun p => (norm_exp_I_mul_ofReal _).le⟩
    rw [hexp k t, expUnitary_apply, h1, h2, integral_pushforwardPVM _ hFk hb, integral_pushforwardPVM _ hF hbP]
    rfl
  -- the product over the coordinates
  refine ⟨P, fun a => ?_⟩
  have hs : ∀ s : Finset (Fin n), ∀ ψ, T (∑ k ∈ s, Pi.single k (a k)) ψ =
      P.integral (fun p => Complex.exp (Complex.I * ((∑ k ∈ s, a k * p k : ℝ) : ℂ))) ψ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro ψ
      have e : (fun p : Fin n → ℝ => Complex.exp (Complex.I * ((∑ k ∈ (∅ : Finset (Fin n)), a k * p k : ℝ) : ℂ))) =
          1 := funext fun p => by simp
      rw [Finset.sum_empty, hT.map_zero, e, ProjectionValuedMeasure.integral_one]
      rfl
    | insert j s hj ih =>
      intro ψ
      rw [Finset.sum_insert hj, hT.map_add, ih]
      have h := hmarg j (a j) (P.integral (fun p => Complex.exp (Complex.I * ((∑ k ∈ s, a k * p k : ℝ) : ℂ))) ψ)
      change U j (a j) _ = _
      have hbj : (fun p : Fin n → ℝ => Complex.exp (Complex.I * ((a j * p j : ℝ) : ℂ))) ∈
          BddMeasurable (Fin n → ℝ) :=
        ⟨(Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.mul (continuous_apply j))))).measurable, 1, fun p => (norm_exp_I_mul_ofReal _).le⟩
      rw [h, ← ContinuousLinearMap.mul_apply, ← ProjectionValuedMeasure.integral_mul _ hbj
        (expCoord_mem_bddMeasurable a s)]
      congr 2
      funext p
      simp only [Pi.mul_apply, Finset.sum_insert hj]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  intro ψ
  have h := hs Finset.univ ψ
  rwa [Finset.univ_sum_single] at h

/-! ## Uniqueness -/

/-- **Uniqueness of the joint spectral measure**: two projection-valued measures on `ℝⁿ` with the same integrals
of the characters `p ↦ e^{i⟨a, p⟩}` are equal (their scalar measures have the same characteristic functions). -/
theorem jointSpectralMeasure_unique {P P' : ProjectionValuedMeasure (Fin n → ℝ) H}
    (h : ∀ a : Fin n → ℝ, P.integral (fun p => Complex.exp (Complex.I * ((∑ k, a k * p k : ℝ) : ℂ))) =
      P'.integral (fun p => Complex.exp (Complex.I * ((∑ k, a k * p k : ℝ) : ℂ)))) : P = P' := by
  -- the scalar measures agree
  have hassoc : ∀ ψ : H, P.assoc ψ = P'.assoc ψ := by
    intro ψ
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    set a : Fin n → ℝ := fun k => L (Pi.single k 1)
    have hL : ∀ v : Fin n → ℝ, Complex.exp ((L v : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((∑ k, a k * v k : ℝ) : ℂ)) := by
      intro v
      have hv : L v = ∑ k, a k * v k := by
        conv_lhs => rw [← Finset.univ_sum_single v]
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (Pi.single k (v k) : Fin n → ℝ) = v k • Pi.single k 1 by
          rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
      rw [hv, mul_comm]
    rw [charFunDual_apply, charFunDual_apply]
    simp_rw [hL]
    rw [← ProjectionValuedMeasure.inner_integral _ (expCoord_mem_bddMeasurable a Finset.univ),
      ← ProjectionValuedMeasure.inner_integral _ (expCoord_mem_bddMeasurable a Finset.univ), h a]
  refine ProjectionValuedMeasure.ext fun S => ?_
  by_cases hS : MeasurableSet S
  · have hb := (indicator_one_mem_bddMeasurable_iff (X := Fin n → ℝ)).2 hS
    have hq : ∀ ψ : H, ⟪(P S - P' S) ψ, ψ⟫_ℂ = 0 := by
      intro ψ
      rw [_root_.sub_apply, inner_sub_left, ← inner_conj_symm, ← inner_conj_symm (P' S ψ),
        ← ProjectionValuedMeasure.integral_indicator _ hS, ← ProjectionValuedMeasure.integral_indicator _ hS,
        ProjectionValuedMeasure.inner_integral _ hb, ProjectionValuedMeasure.inner_integral _ hb, hassoc, sub_self]
    have h0 := (inner_map_self_eq_zero ((P S - P' S : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 hq
    exact sub_eq_zero.1 (ContinuousLinearMap.coe_injective h0)
  · rw [ProjectionValuedMeasure.apply_of_not_measurableSet _ hS,
      ProjectionValuedMeasure.apply_of_not_measurableSet _ hS]

end

end Lightlike.Poincare

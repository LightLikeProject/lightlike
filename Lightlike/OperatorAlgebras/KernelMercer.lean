import Mathlib
import Lightlike.OperatorAlgebras.KernelSpectral

/-!
# Mercer's theorem for integral operators with continuous kernels

Let `X` be a compact space with a finite Borel measure `μ` that is positive on non-empty open sets,
`K` a continuous Hermitian kernel whose integral operator `T_K` is positive, and `(b_i, λ_i)` an
eigenbasis of `T_K`. This file builds the continuous eigenfunctions and the pointwise expansion of
`T_K` used for Mercer's theorem:

* the eigenvalues are non-negative (`eigen_nonneg`);
* `φ_i = λ_i⁻¹ (x ↦ ⟪k_x, b_i⟫)` is continuous and `x ↦ ⟪k_x, b_i⟫ = λ_i φ_i` (`kernelToC_eigen`),
  also when `λ_i = 0`, because a continuous function vanishing almost everywhere vanishes;
* `(T_K f)(x) = Σ_i λ_i φ_i(x) ⟪b_i, f⟫` for every `x` (`hasSum_kernelToC`), by Parseval's identity
  for `⟪k_x, f⟫`.
* the diagonal is non-negative (`re_diag_nonneg`); applied to the truncated kernel
  `K - Σ_{i ∈ S} λ_i φ_i ⊗ conj φ_i`, which is again positive (`isPositiveKernel_truncKer`), this gives
  `Σ_{i ∈ S} λ_i |φ_i(x)|² ≤ K(x, x)` (`sum_le_diag`);
* by Cauchy–Schwarz the row series `Σ_i λ_i φ_i(x) conj φ_i` converges uniformly
  (`summable_rowTerm`), and pairing it with every `f ∈ L²` identifies its sum with `conj K(x, ·)`, so
  `K(x, x) = Σ_i λ_i |φ_i(x)|²` (`hasSum_diag`);
* **Mercer's trace formula** `Σ_i λ_i = ∫ K(x, x) dμ(x)` (`hasSum_eigenvalues`): by Dini's theorem
  the diagonal partial sums converge uniformly, and `∫ |φ_i|² = ‖b_i‖² = 1` when `λ_i ≠ 0`.

## Main results

* `re_diag_nonneg`, `sum_le_diag`, `hasSum_diag`, `hasSum_eigenvalues`

## References

* A. Gheondea, *Mercer's theorem* (arXiv:2512.06475), Theorem 4.16, p. 36, and Corollary 4.17,
  p. 37 (there for `supp ν ⊇ supp K`; here `μ` is positive on open sets, which holds for the
  Riemannian volume).
* J. Mercer, *Functions of positive and negative type, and their connection with the theory of
  integral equations*, Phil. Trans. R. Soc. Lond. A 209 (1909), 415–446 (the interval case).
-/

open MeasureTheory Filter Topology

namespace Lightlike.OperatorAlgebras

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The operator `T_K` is positive: `0 ≤ re ⟪T_K f, f⟫` for all `f`. -/
def IsPositiveKernel (K : C(X × X, ℂ)) : Prop :=
  ∀ f : Lp ℂ 2 μ, 0 ≤ RCLike.re (inner ℂ (kernelOp μ K f) f)

/-- **The eigenvalues of a positive operator are non-negative.** -/
lemma eigen_nonneg {K : C(X × X, ℂ)} (hpos : IsPositiveKernel μ K) {b : Lp ℂ 2 μ} {lam : ℝ}
    (hb : kernelOp μ K b = (lam : ℂ) • b) (hb1 : ‖b‖ = 1) : 0 ≤ lam := by
  have h := hpos b
  rw [hb, inner_smul_left, inner_self_eq_norm_sq_to_K, hb1] at h
  simpa using h

omit [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
/-- A continuous function vanishing almost everywhere for a measure positive on open sets vanishes. -/
lemma eq_zero_of_ae_eq_zero [μ.IsOpenPosMeasure] {g : C(X, ℂ)} (hg : (g : X → ℂ) =ᵐ[μ] 0) :
    g = 0 := by
  ext x
  exact congrFun ((g.continuous.ae_eq_iff_eq μ continuous_const).1 hg) x

/-- The continuous eigenfunction `φ = λ⁻¹ (x ↦ ⟪k_x, b⟫)`. -/
def eigenFun (K : C(X × X, ℂ)) (b : Lp ℂ 2 μ) (lam : ℝ) : C(X, ℂ) :=
  ((lam : ℂ))⁻¹ • kernelToC μ K b

/-- **`x ↦ ⟪k_x, b⟫ = λ φ`** for an eigenvector `T_K b = λ b`, including `λ = 0`. -/
lemma kernelToC_eigen [μ.IsOpenPosMeasure] (K : C(X × X, ℂ)) {b : Lp ℂ 2 μ} {lam : ℝ}
    (hb : kernelOp μ K b = (lam : ℂ) • b) :
    kernelToC μ K b = (lam : ℂ) • eigenFun μ K b lam := by
  by_cases hl : lam = 0
  · subst hl
    have hz : kernelOp μ K b = 0 := by rw [hb]; simp
    have hae : (kernelToC μ K b : X → ℂ) =ᵐ[μ] 0 := by
      have h1 := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (kernelToC μ K b)
      have e : ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kernelToC μ K b) = 0 := hz
      rw [e] at h1
      filter_upwards [h1, Lp.coeFn_zero ℂ 2 μ] with x hx1 hx2
      rw [← hx1, hx2]
    rw [eq_zero_of_ae_eq_zero μ hae]
    simp
  · have hl' : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
    rw [eigenFun, smul_smul, mul_inv_cancel₀ hl', one_smul]

/-- `φ` represents `b` when `λ ≠ 0`. -/
lemma ae_eq_eigenFun (K : C(X × X, ℂ)) {b : Lp ℂ 2 μ} {lam : ℝ} (hl : lam ≠ 0)
    (hb : kernelOp μ K b = (lam : ℂ) • b) :
    (b : X → ℂ) =ᵐ[μ] eigenFun μ K b lam := by
  have h := ae_eq_continuous_of_eigen μ K (lam := (lam : ℂ)) (by exact_mod_cast hl) hb
  filter_upwards [h] with x hx
  rw [hx, eigenFun]
  simp

/-- **The pointwise expansion**: `⟪k_x, f⟫ = Σ_i λ_i φ_i(x) ⟪b_i, f⟫` for every `x`. -/
theorem hasSum_kernelToC [μ.IsOpenPosMeasure] (K : C(X × X, ℂ)) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
    (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (f : Lp ℂ 2 μ) (x : X) :
    HasSum (fun i => (lam i : ℂ) * eigenFun μ K (b i) (lam i) x * inner ℂ (b i) f)
      (kernelToC μ K f x) := by
  have h := b.hasSum_inner_mul_inner (kernelVecOf μ K x) f
  rw [← kernelToC_apply] at h
  refine h.congr_fun fun i => ?_
  rw [← kernelToC_apply, kernelToC_eigen μ K (hb i)]
  simp [mul_assoc]

/-- **A positive continuous kernel has a non-negative diagonal**: `0 ≤ re K(x, x)`, for a measure
positive on open sets (test `T_K` on the indicator of a small neighbourhood). -/
theorem re_diag_nonneg [μ.IsOpenPosMeasure] {K : C(X × X, ℂ)} (hpos : IsPositiveKernel μ K)
    (x₀ : X) : 0 ≤ (K (x₀, x₀)).re := by
  by_contra hneg
  push Not at hneg
  set c := -(K (x₀, x₀)).re / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  -- a neighbourhood `U × U` of `(x₀, x₀)` where `re K < -c`
  have hopen : IsOpen {p : X × X | (K p).re < -c} :=
    isOpen_lt (Complex.continuous_re.comp K.continuous) continuous_const
  have hmem : {p : X × X | (K p).re < -c} ∈ 𝓝 (x₀, x₀) :=
    hopen.mem_nhds (by show (K (x₀, x₀)).re < -c; rw [hc]; linarith)
  obtain ⟨u, v, hu, hxu, hv, hxv, hsub⟩ := mem_nhds_prod_iff'.1 hmem
  set U := u ∩ v with hUdef
  have hUo : IsOpen U := hu.inter hv
  have hxU : x₀ ∈ U := ⟨hxu, hxv⟩
  have hUU : ∀ x ∈ U, ∀ y ∈ U, (K (x, y)).re < -c := fun x hx y hy => hsub ⟨hx.1, hy.2⟩
  have hUm : MeasurableSet U := hUo.measurableSet
  have hμU : 0 < μ.real U :=
    ENNReal.toReal_pos (hUo.measure_pos μ ⟨x₀, hxU⟩).ne' (measure_ne_top μ U)
  set f : Lp ℂ 2 μ := indicatorConstLp 2 hUm (measure_ne_top μ U) (1 : ℂ) with hfdef
  have hf : (f : X → ℂ) =ᵐ[μ] U.indicator fun _ => (1 : ℂ) := indicatorConstLp_coeFn
  -- `(T f)(x) = ∫_U K(x, y)`
  have hTf : ∀ x, kernelToC μ K f x = ∫ y in U, K (x, y) ∂μ := fun x => by
    rw [kernelToC_apply, inner_kernelVecOf, ← integral_indicator hUm]
    refine integral_congr_ae ?_
    filter_upwards [hf] with y hy
    rw [hy]
    by_cases hyU : y ∈ U <;> simp [hyU]
  have hcont : Continuous fun x => kernelToC μ K f x := (kernelToC μ K f).continuous
  have hinner : inner ℂ (kernelOp μ K f) f =
      ∫ x in U, (starRingEnd ℂ) (∫ y in U, K (x, y) ∂μ) ∂μ := by
    rw [MeasureTheory.L2.inner_def, ← integral_indicator hUm]
    refine integral_congr_ae ?_
    have h1 := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (kernelToC μ K f)
    filter_upwards [h1, hf] with x hx1 hx2
    change inner ℂ ((ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kernelToC μ K f)) x) (f x) = _
    rw [hx1, hx2, RCLike.inner_apply, hTf]
    by_cases hxU : x ∈ U <;> simp [hxU]
  have hbound : ∀ x ∈ U, ((starRingEnd ℂ) (∫ y in U, K (x, y) ∂μ)).re ≤ -c * μ.real U := by
    intro x hx
    have hKx : Continuous fun y => K (x, y) := K.continuous.comp (Continuous.prodMk_right x)
    rw [Complex.conj_re, ← RCLike.re_to_complex, ← integral_re (hKx.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn]
    simp only [RCLike.re_to_complex]
    calc ∫ y in U, (K (x, y)).re ∂μ ≤ ∫ y in U, -c ∂μ :=
          setIntegral_mono_on (Complex.continuous_re.comp hKx |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).integrableOn (integrableOn_const
              (measure_ne_top μ U)) hUm fun y hy => (hUU x hx y hy).le
      _ = -c * μ.real U := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hre : (inner ℂ (kernelOp μ K f) f).re ≤ -c * μ.real U * μ.real U := by
    have hg : Continuous fun x => (starRingEnd ℂ) (∫ y in U, K (x, y) ∂μ) := by
      have : (fun x => (starRingEnd ℂ) (∫ y in U, K (x, y) ∂μ)) =
          fun x => (starRingEnd ℂ) (kernelToC μ K f x) := funext fun x => by rw [hTf]
      rw [this]; exact Complex.continuous_conj.comp hcont
    rw [hinner, ← RCLike.re_to_complex, ← integral_re (hg.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn]
    simp only [RCLike.re_to_complex]
    calc ∫ x in U, ((starRingEnd ℂ) (∫ y in U, K (x, y) ∂μ)).re ∂μ
        ≤ ∫ x in U, -c * μ.real U ∂μ :=
          setIntegral_mono_on (Complex.continuous_re.comp hg |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).integrableOn
            (integrableOn_const (measure_ne_top μ U)) hUm hbound
      _ = -c * μ.real U * μ.real U := by rw [setIntegral_const, smul_eq_mul]; ring
  have h0 := hpos f
  have : -c * μ.real U * μ.real U < 0 := by
    have := mul_pos hc0 (mul_pos hμU hμU)
    nlinarith
  exact absurd (h0.trans hre) (not_le.2 this)

/-- The rank-one kernel `g(x) conj g(y)`. -/
def tensorKer (g : C(X, ℂ)) : C(X × X, ℂ) :=
  ⟨fun p => g p.1 * starRingEnd ℂ (g p.2), by fun_prop⟩

lemma kernelToC_sub (K L : C(X × X, ℂ)) (f : Lp ℂ 2 μ) :
    kernelToC μ (K - L) f = kernelToC μ K f - kernelToC μ L f := by
  ext x
  simp only [ContinuousMap.sub_apply, kernelToC_apply, kernelVecOf]
  have : kernelCurry (K - L) x = kernelCurry K x - kernelCurry L x := by
    ext y; simp [kernelCurry_apply]
  rw [this, map_sub, inner_sub_left]

lemma kernelToC_smul (c : ℂ) (L : C(X × X, ℂ)) (f : Lp ℂ 2 μ) :
    kernelToC μ (c • L) f = c • kernelToC μ L f := by
  ext x
  simp only [ContinuousMap.smul_apply, kernelToC_apply, kernelVecOf, smul_eq_mul]
  have : kernelCurry (c • L) x = (starRingEnd ℂ c) • kernelCurry L x := by
    ext y; simp [kernelCurry_apply]
  rw [this, map_smul, inner_smul_left, Complex.conj_conj]

lemma kernelToC_sum {ι : Type*} (S : Finset ι) (L : ι → C(X × X, ℂ)) (f : Lp ℂ 2 μ) :
    kernelToC μ (∑ i ∈ S, L i) f = ∑ i ∈ S, kernelToC μ (L i) f := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    ext x
    simp only [Finset.sum_empty, kernelToC_apply, kernelVecOf, ContinuousMap.zero_apply]
    have : kernelCurry (0 : C(X × X, ℂ)) x = 0 := by ext y; simp [kernelCurry_apply]
    rw [this, map_zero, inner_zero_left]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have h := kernelToC_sub μ (L a + ∑ i ∈ S, L i) (∑ i ∈ S, L i) f
    rw [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]

lemma kernelToC_tensorKer (g : C(X, ℂ)) (f : Lp ℂ 2 μ) :
    kernelToC μ (tensorKer g) f = inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ g) f • g := by
  ext x
  simp only [kernelToC_apply, kernelVecOf, ContinuousMap.smul_apply, smul_eq_mul]
  have : kernelCurry (tensorKer g) x = (starRingEnd ℂ (g x)) • g := by
    ext y; simp [kernelCurry_apply, tensorKer, mul_comm]
  rw [this, map_smul, inner_smul_left, Complex.conj_conj, mul_comm]

lemma kernelOp_eq_toLp (K : C(X × X, ℂ)) (f : Lp ℂ 2 μ) :
    kernelOp μ K f = ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kernelToC μ K f) := rfl

/-- `⟪T_K f, f⟫ = Σ_i λ_i |⟪b_i, f⟫|²` for a symmetric `T_K` and an eigenbasis. -/
lemma hasSum_inner_kernelOp [SecondCountableTopology X] (K : C(X × X, ℂ))
    (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
    (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (f : Lp ℂ 2 μ) :
    HasSum (fun i => ((lam i * ‖inner ℂ (b i) f‖ ^ 2 : ℝ) : ℂ)) (inner ℂ (kernelOp μ K f) f) := by
  have h := b.hasSum_inner_mul_inner (kernelOp μ K f) f
  refine h.congr_fun fun i => ?_
  have hS := isSymmetric_kernelOp μ K hK
  have e : inner ℂ (kernelOp μ K f) (b i) = (lam i : ℂ) * inner ℂ f (b i) := by
    have := hS f (b i)
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, hb i, inner_smul_right]
  rw [e, mul_assoc, ← inner_conj_symm f (b i), Complex.conj_mul']
  push_cast
  ring

/-- The truncated kernel `K - Σ_{i ∈ S} λ_i φ_i(x) conj φ_i(y)`. -/
def truncKer (K : C(X × X, ℂ)) {ι : Type*} (S : Finset ι) (lam : ι → ℝ) (φ : ι → C(X, ℂ)) :
    C(X × X, ℂ) :=
  K - ∑ i ∈ S, ((lam i : ℝ) : ℂ) • tensorKer (φ i)

/-- `toLp φ = b` for an eigenvector with `λ ≠ 0`. -/
lemma toLp_eigenFun (K : C(X × X, ℂ)) {b : Lp ℂ 2 μ} {lam : ℝ} (hl : lam ≠ 0)
    (hb : kernelOp μ K b = (lam : ℂ) • b) :
    ContinuousMap.toLp (E := ℂ) 2 μ ℂ (eigenFun μ K b lam) = b := by
  refine Lp.ext ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ)
    (eigenFun μ K b lam), ae_eq_eigenFun μ K hl hb] with x hx1 hx2
  rw [hx1, hx2]

/-- **The truncated kernel is positive.** -/
theorem isPositiveKernel_truncKer [μ.IsOpenPosMeasure] [SecondCountableTopology X]
    (K : C(X × X, ℂ)) (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
    (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (hpos : IsPositiveKernel μ K)
    (S : Finset ι) :
    IsPositiveKernel μ (truncKer K S lam fun i => eigenFun μ K (b i) (lam i)) := by
  intro f
  set φ := fun i => eigenFun μ K (b i) (lam i) with hφ
  have hlam : ∀ i, 0 ≤ lam i := fun i => eigen_nonneg μ hpos (hb i) (b.orthonormal.1 i)
  -- the operator of the truncated kernel
  have hop : kernelOp μ (truncKer K S lam φ) f = kernelOp μ K f -
      ∑ i ∈ S, ((lam i : ℂ) * inner ℂ (b i) f) • b i := by
    rw [kernelOp_eq_toLp, truncKer, kernelToC_sub, kernelToC_sum, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kernelToC_smul, kernelToC_tensorKer, map_smul, map_smul, smul_smul]
    by_cases hl : lam i = 0
    · simp [hl]
    · rw [toLp_eigenFun μ K hl (hb i)]
  have htot := hasSum_inner_kernelOp μ K hK b lam hb f
  have hre : HasSum (fun i => lam i * ‖inner ℂ (b i) f‖ ^ 2)
      (RCLike.re (inner ℂ (kernelOp μ K f) f)) := by
    have := Complex.reCLM.hasSum htot
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at this
    exact this
  have hpart : ∑ i ∈ S, lam i * ‖inner ℂ (b i) f‖ ^ 2 ≤ RCLike.re (inner ℂ (kernelOp μ K f) f) :=
    sum_le_hasSum S (fun i _ => mul_nonneg (hlam i) (sq_nonneg _)) hre
  rw [hop, inner_sub_left, sum_inner, map_sub, map_sum]
  have hterm : ∀ i ∈ S, RCLike.re (inner ℂ (((lam i : ℂ) * inner ℂ (b i) f) • b i) f) =
      lam i * ‖inner ℂ (b i) f‖ ^ 2 := by
    intro i _
    rw [inner_smul_left, map_mul (starRingEnd ℂ), Complex.conj_ofReal, mul_assoc,
      Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, RCLike.re_to_complex,
      Complex.ofReal_re]
  rw [Finset.sum_congr rfl hterm]
  linarith

/-- **The diagonal bound**: `Σ_{i ∈ S} λ_i |φ_i(x)|² ≤ re K(x, x)` for every finite `S`. -/
theorem sum_le_diag [μ.IsOpenPosMeasure] [SecondCountableTopology X]
    (K : C(X × X, ℂ)) (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
    (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (hpos : IsPositiveKernel μ K)
    (S : Finset ι) (x : X) :
    ∑ i ∈ S, lam i * ‖eigenFun μ K (b i) (lam i) x‖ ^ 2 ≤ (K (x, x)).re := by
  have h := re_diag_nonneg μ (isPositiveKernel_truncKer μ K hK b lam hb hpos S) x
  simp only [truncKer, ContinuousMap.sub_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.smul_apply, tensorKer, ContinuousMap.coe_mk, Complex.sub_re, Complex.re_sum,
    smul_eq_mul, Complex.re_ofReal_mul, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re] at h
  linarith

section Expansion

variable [μ.IsOpenPosMeasure] [SecondCountableTopology X] (K : C(X × X, ℂ))
  (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) {ι : Type*}
  (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
  (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (hpos : IsPositiveKernel μ K)
include hK hb hpos

/-- The terms `λ_i φ_i(x) conj φ_i` of the row series of the kernel at `x`. -/
def rowTerm (x : X) (i : ι) : C(X, ℂ) :=
  (((lam i : ℂ) * eigenFun μ K (b i) (lam i) x)) • star (eigenFun μ K (b i) (lam i))

/-- The tail bound `‖Σ_{i ∈ t} λ_i φ_i(x) conj φ_i‖ ≤ √(Σ_t λ_i |φ_i(x)|²) √M`. -/
lemma norm_sum_rowTerm_le (x : X) {M : ℝ} (hM : ∀ y, (K (y, y)).re ≤ M) (t : Finset ι) :
    ‖∑ i ∈ t, rowTerm μ K b lam x i‖ ≤
      Real.sqrt (∑ i ∈ t, lam i * ‖eigenFun μ K (b i) (lam i) x‖ ^ 2) * Real.sqrt M := by
  have hlam : ∀ i, 0 ≤ lam i := fun i => eigen_nonneg μ hpos (hb i) (b.orthonormal.1 i)
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun y => ?_
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, rowTerm, ContinuousMap.smul_apply,
    ContinuousMap.star_apply, smul_eq_mul]
  set φ := fun i => eigenFun μ K (b i) (lam i) with hφ
  calc ‖∑ i ∈ t, (lam i : ℂ) * φ i x * star (φ i y)‖
      ≤ ∑ i ∈ t, ‖(lam i : ℂ) * φ i x * star (φ i y)‖ := norm_sum_le _ _
    _ = ∑ i ∈ t, Real.sqrt (lam i * ‖φ i x‖ ^ 2) * Real.sqrt (lam i * ‖φ i y‖ ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hlam i), ← Real.sqrt_mul (mul_nonneg (hlam i) (sq_nonneg _)),
          show lam i * ‖φ i x‖ ^ 2 * (lam i * ‖φ i y‖ ^ 2) = (lam i * ‖φ i x‖ * ‖φ i y‖) ^ 2 by ring,
          Real.sqrt_sq (by have := hlam i; positivity)]
    _ ≤ Real.sqrt (∑ i ∈ t, lam i * ‖φ i x‖ ^ 2) * Real.sqrt (∑ i ∈ t, lam i * ‖φ i y‖ ^ 2) :=
        Real.sum_sqrt_mul_sqrt_le t (fun i => by have := hlam i; positivity)
          (fun i => by have := hlam i; positivity)
    _ ≤ Real.sqrt (∑ i ∈ t, lam i * ‖φ i x‖ ^ 2) * Real.sqrt M := by
        gcongr
        exact (sum_le_diag μ K hK b lam hb hpos t y).trans (hM y)

/-- The diagonal series converges: `Σ_i λ_i |φ_i(x)|²` is summable. -/
lemma summable_diag (x : X) :
    Summable fun i => lam i * ‖eigenFun μ K (b i) (lam i) x‖ ^ 2 := by
  have hlam : ∀ i, 0 ≤ lam i := fun i => eigen_nonneg μ hpos (hb i) (b.orthonormal.1 i)
  exact summable_of_sum_le (fun i => mul_nonneg (hlam i) (sq_nonneg _))
    (sum_le_diag μ K hK b lam hb hpos · x)

/-- The row series converges in `C(X, ℂ)`. -/
lemma summable_rowTerm (x : X) : Summable (rowTerm μ K b lam x) := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := X)).exists_bound_of_continuousOn
    (Complex.continuous_re.comp (K.continuous.comp (continuous_id.prodMk continuous_id))).continuousOn
  have hM' : ∀ y, (K (y, y)).re ≤ M := fun y =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM y (Set.mem_univ y))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (by simpa [Real.norm_eq_abs] using hM x (Set.mem_univ x))
  rw [summable_iff_vanishing_norm]
  intro ε hε
  set δ := (ε / (Real.sqrt M + 1)) ^ 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 (summable_diag μ K hK b lam hb hpos x) δ hδ0
  refine ⟨s, fun t ht => ?_⟩
  have h1 := norm_sum_rowTerm_le μ K hK b lam hb hpos x hM' t
  have h2 := hs t ht
  have hlam : ∀ i, 0 ≤ lam i := fun i => eigen_nonneg μ hpos (hb i) (b.orthonormal.1 i)
  have hnn : 0 ≤ ∑ i ∈ t, lam i * ‖eigenFun μ K (b i) (lam i) x‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)
  rw [Real.norm_of_nonneg hnn] at h2
  have h3 : Real.sqrt (∑ i ∈ t, lam i * ‖eigenFun μ K (b i) (lam i) x‖ ^ 2) <
      ε / (Real.sqrt M + 1) := by
    rw [← Real.sqrt_sq (show 0 ≤ ε / (Real.sqrt M + 1) by positivity)]
    exact Real.sqrt_lt_sqrt hnn h2
  calc ‖∑ i ∈ t, rowTerm μ K b lam x i‖ ≤ _ := h1
    _ ≤ ε / (Real.sqrt M + 1) * Real.sqrt M :=
        mul_le_mul_of_nonneg_right h3.le (Real.sqrt_nonneg _)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [Real.sqrt_nonneg M]

end Expansion

section Diagonal

variable [μ.IsOpenPosMeasure] [SecondCountableTopology X] (K : C(X × X, ℂ))
  (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) {ι : Type*}
  (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
  (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (hpos : IsPositiveKernel μ K)
include hK hb hpos

/-- **Mercer's expansion on the diagonal**: `K(x, x) = Σ_i λ_i |φ_i(x)|²`. -/
theorem hasSum_diag (x : X) :
    HasSum (fun i => ((lam i * ‖eigenFun μ K (b i) (lam i) x‖ ^ 2 : ℝ) : ℂ)) (K (x, x)) := by
  set G := ∑' i, rowTerm μ K b lam x i with hGdef
  have hG : HasSum (rowTerm μ K b lam x) G :=
    (summable_rowTerm μ K hK b lam hb hpos x).hasSum
  -- pairing with every `f` identifies `conj G` with `conj K(x, ·)`
  have hΛ : ∀ f : Lp ℂ 2 μ, inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (star G)) f =
      kernelToC μ K f x := by
    intro f
    let A : C(X, ℂ) →+ ℂ :=
      { toFun := fun g => inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (star g)) f
        map_zero' := by simp
        map_add' := fun g h => by simp [star_add, inner_add_left] }
    have hAc : Continuous A :=
      ((ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp continuous_star).inner continuous_const
    have h1 := hG.map A hAc
    have h2 := hasSum_kernelToC μ K b lam hb f x
    refine h1.unique (h2.congr_fun fun i => ?_)
    show inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (star (rowTerm μ K b lam x i))) f = _
    simp only [rowTerm, star_smul, star_star, map_smul, inner_smul_left]
    by_cases hl : lam i = 0
    · simp [hl]
    · rw [toLp_eigenFun μ K hl (hb i)]
      simp only [RCLike.star_def, Complex.conj_conj]
  have hstar : ContinuousMap.toLp (E := ℂ) 2 μ ℂ (star G) = kernelVecOf μ K x :=
    ext_inner_right ℂ fun f => by rw [hΛ, kernelToC_apply]
  have hGK : star G = kernelCurry K x := ContinuousMap.toLp_injective μ hstar
  have hval : G x = K (x, x) := by
    have h := congrArg (fun g : C(X, ℂ) => g x) hGK
    simp only [ContinuousMap.star_apply, kernelCurry_apply] at h
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have hev := hG.map (ContinuousMap.evalCLM ℂ x) (ContinuousMap.evalCLM ℂ x).continuous
  rw [← hval]
  refine hev.congr_fun fun i => ?_
  simp only [Function.comp_apply, ContinuousMap.evalCLM_apply, rowTerm, ContinuousMap.smul_apply,
    ContinuousMap.star_apply, smul_eq_mul]
  rw [mul_assoc, RCLike.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul]

end Diagonal

/-- Integrals of a uniformly convergent net of continuous functions on a finite measure space. -/
lemma tendsto_integral_of_tendstoUniformly {ι : Type*} {F : Finset ι → X → ℝ} {f : X → ℝ}
    (hF : ∀ s, Continuous (F s)) (hf : Continuous f) (hU : TendstoUniformly F f atTop) :
    Tendsto (fun s => ∫ x, F s x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set c := μ.real Set.univ + 1 with hc
  have hc0 : 0 < c := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.1 hU (ε / c) (by positivity)] with s hs
  rw [dist_eq_norm, ← integral_sub (integrable_of_continuous μ (hF s)) (integrable_of_continuous μ hf)]
  calc ‖∫ x, (F s x - f x) ∂μ‖ ≤ ε / c * μ.real Set.univ := by
        refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => ?_)
        have := hs x
        rw [dist_comm, dist_eq_norm] at this
        exact this.le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc0]
        nlinarith [measureReal_nonneg (μ := μ) (s := Set.univ)]

section Trace

/-- **Mercer's trace formula**: for a positive integral operator with a continuous Hermitian kernel
and any eigenbasis, `Σ_i λ_i = ∫ K(x, x) dμ(x)`. -/
theorem hasSum_eigenvalues [μ.IsOpenPosMeasure] [SecondCountableTopology X] (K : C(X × X, ℂ))
    (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
    (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (hpos : IsPositiveKernel μ K) :
    HasSum (fun i => (lam i : ℂ)) (∫ x, K (x, x) ∂μ) := by
  have hlam : ∀ i, 0 ≤ lam i := fun i => eigen_nonneg μ hpos (hb i) (b.orthonormal.1 i)
  set φ := fun i => eigenFun μ K (b i) (lam i) with hφ
  set F : Finset ι → X → ℝ := fun S x => ∑ i ∈ S, lam i * ‖φ i x‖ ^ 2 with hFdef
  set f : X → ℝ := fun x => (K (x, x)).re with hfdef
  have hF : ∀ S, Continuous (F S) := fun S =>
    continuous_finsetSum _ fun i _ => continuous_const.mul (((φ i).continuous.norm).pow 2)
  have hf : Continuous f :=
    Complex.continuous_re.comp (K.continuous.comp (continuous_id.prodMk continuous_id))
  have hmono : Monotone F := fun S T hST x =>
    Finset.sum_le_sum_of_subset_of_nonneg hST fun i _ _ => mul_nonneg (hlam i) (sq_nonneg _)
  have hpt : ∀ x, Tendsto (F · x) atTop (𝓝 (f x)) := fun x => by
    have h := Complex.reCLM.hasSum (hasSum_diag μ K hK b lam hb hpos x)
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h
    exact h
  have hU := Monotone.tendstoUniformly_of_forall_tendsto hF hmono hf hpt
  have hI := tendsto_integral_of_tendstoUniformly μ hF hf hU
  have hterm : ∀ i, lam i * ∫ x, ‖φ i x‖ ^ 2 ∂μ = lam i := by
    intro i
    by_cases hl : lam i = 0
    · simp [hl]
    · rw [← norm_sq_toLp_eq, toLp_eigenFun μ K hl (hb i), b.orthonormal.1 i, one_pow, mul_one]
  have hsum : ∀ S, ∫ x, F S x ∂μ = ∑ i ∈ S, lam i := by
    intro S
    show ∫ x, ∑ i ∈ S, lam i * ‖φ i x‖ ^ 2 ∂μ = _
    rw [integral_finsetSum S fun i _ => integrable_of_continuous μ
      (show Continuous fun x => lam i * ‖φ i x‖ ^ 2 from
        continuous_const.mul (((φ i).continuous.norm).pow 2))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hterm]
  have hreal : HasSum lam (∫ x, f x ∂μ) := hI.congr hsum
  have hdiag : ∀ x, K (x, x) = ((K (x, x)).re : ℂ) := fun x => by
    have := hK x x
    exact (Complex.conj_eq_iff_re.1 this.symm).symm
  have hint : ∫ x, K (x, x) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun x => hdiag x)
  rw [hint]
  exact Complex.ofRealCLM.hasSum hreal

/-- **The trace of a positive integral operator is `∫ K(x, x)`, in every Hilbert basis**:
`Σ_i ⟪T_K e_i, e_i⟫ = ∫ K(x, x) dμ(x)` for any Hilbert basis `(e_i)` of `L²(X, μ)`. Proof: with an
eigenbasis `(b_j, λ_j)`, `⟪T_K e_i, e_i⟫ = Σ_j λ_j |⟪b_j, e_i⟫|²` and `Σ_i |⟪b_j, e_i⟫|² = 1`; the
double series has non-negative terms, so it may be summed in either order. -/
theorem hasSum_inner_basis_eq_integral_diag [μ.IsOpenPosMeasure] [SecondCountableTopology X]
    (K : C(X × X, ℂ)) (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y)))
    (hpos : IsPositiveKernel μ K) {κ : Type*} (e : HilbertBasis κ ℂ (Lp ℂ 2 μ)) :
    HasSum (fun i => inner ℂ (kernelOp μ K (e i)) (e i)) (∫ x, K (x, x) ∂μ) := by
  obtain ⟨ι, b, lam, hb⟩ := exists_hilbertBasis_eigenvectors_kernelOp μ K hK
  have hlam : ∀ j, 0 ≤ lam j := fun j => eigen_nonneg μ hpos (hb j) (b.orthonormal.1 j)
  set f : ι × κ → ℝ := fun p => lam p.1 * ‖inner ℂ (b p.1) (e p.2)‖ ^ 2 with hfdef
  have hf0 : 0 ≤ f := fun p => mul_nonneg (hlam p.1) (sq_nonneg _)
  have hrow : ∀ j, HasSum (fun i => f (j, i)) (lam j) := by
    intro j
    have h := (hasSum_norm_sq_inner_basis e (b j)).mul_left (lam j)
    rw [b.orthonormal.1 j, one_pow, mul_one] at h
    refine h.congr_fun fun i => ?_
    simp only [hfdef, norm_inner_symm]
  have htrC := hasSum_eigenvalues μ K hK b lam hb hpos
  have htr : HasSum lam (∫ x, K (x, x) ∂μ).re := by
    have := Complex.reCLM.hasSum htrC
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at this
    exact this
  have hsum : Summable f := by
    refine (summable_prod_of_nonneg hf0).2 ⟨fun j => (hrow j).summable, ?_⟩
    convert htr.summable using 1
    funext j
    exact (hrow j).tsum_eq
  have ha : HasSum f (∫ x, K (x, x) ∂μ).re := by
    have h := hsum.hasSum
    rwa [(h.prod_fiberwise hrow).unique htr] at h
  have hswap : HasSum (f ∘ Equiv.prodComm κ ι) (∫ x, K (x, x) ∂μ).re :=
    (Equiv.prodComm κ ι).hasSum_iff.2 ha
  have hcolC : ∀ i, HasSum (fun j => ((f (j, i) : ℝ) : ℂ)) (inner ℂ (kernelOp μ K (e i)) (e i)) :=
    fun i => hasSum_inner_kernelOp μ K hK b lam hb (e i)
  have hcol : ∀ i, HasSum (fun j => f (j, i)) (inner ℂ (kernelOp μ K (e i)) (e i)).re := by
    intro i
    have := Complex.reCLM.hasSum (hcolC i)
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at this
    exact this
  have hreal : HasSum (fun i => (inner ℂ (kernelOp μ K (e i)) (e i)).re) (∫ x, K (x, x) ∂μ).re :=
    hswap.prod_fiberwise fun i => hcol i
  have hI : (((∫ x, K (x, x) ∂μ).re : ℝ) : ℂ) = ∫ x, K (x, x) ∂μ :=
    (Complex.ofRealCLM.hasSum htr).unique htrC
  have hT : ∀ i, (((inner ℂ (kernelOp μ K (e i)) (e i)).re : ℝ) : ℂ) =
      inner ℂ (kernelOp μ K (e i)) (e i) := fun i =>
    (Complex.ofRealCLM.hasSum (hcol i)).unique (hcolC i)
  have := Complex.ofRealCLM.hasSum hreal
  simp only [Complex.ofRealCLM_apply, hT, hI] at this
  exact this

end Trace

end

end Lightlike.OperatorAlgebras

import Lightlike.OperatorAlgebras.FockIrreducible
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian average of the Weyl unitaries over finitely many modes

Helper for the necessity part of Shale's criterion (`T-OP2-P6`, `Tasks/OP/T_OP2_P6.lean`). For an orthonormal
family `e : m → h` and real coordinates `x : m ⊕ m → ℝ` put `f_x = ∑ₖ (x (inl k) + i x (inr k)) • eₖ`
(`modeVec`). In a Fock representation, for every vector `Φ`,

`(√(2π))^(2n) |⟪Ω, Φ⟫|² ≤ Re ∫ exp (-‖f_x‖²/4) ⟪Φ, W f_x Φ⟫ dx` (`gaussZ_mul_norm_inner_sq_le`).

The right side is `(2π)ⁿ ⟪Φ, P Φ⟫` for the projection `P` onto the vectors in which the modes `eₖ` are in the vacuum;
the operator `P` is not built. For `Φ = ∑ⱼ cⱼ W gⱼ Ω` the integral is a Gaussian integral, equal to
`(2π)ⁿ ‖Φ'‖²` with `Φ' = ∑ⱼ cⱼ λⱼ W gⱼ' Ω`, `gⱼ'` the part of `gⱼ` orthogonal to the modes and
`λⱼ = exp (-(‖gⱼ‖² - ‖gⱼ'‖²)/4)`, and `⟪Ω, Φ'⟫ = ⟪Ω, Φ⟫`; these vectors are dense and both sides are continuous.
-/

open scoped InnerProductSpace
open MeasureTheory Complex Filter Topology

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {m : Type*} [Fintype m]

lemma half_re_pos : 0 < (1 / 2 : ℂ).re := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]; norm_num

lemma quarter_re_pos : 0 < (1 / 4 : ℂ).re := by
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]; norm_num

/-- The vector `∑ₖ (x (inl k) + i x (inr k)) • eₖ` of the modes `e` with real coordinates `x`. -/
noncomputable def modeVec (e : m → h) (x : m ⊕ m → ℝ) : h :=
  ∑ k, ((x (Sum.inl k) : ℂ) + I * (x (Sum.inr k) : ℂ)) • e k

lemma inner_modeVec_right (e : m → h) (x : m ⊕ m → ℝ) (g : h) :
    ⟪g, modeVec e x⟫_ℂ = ∑ k, ((x (Sum.inl k) : ℂ) + I * (x (Sum.inr k) : ℂ)) * ⟪g, e k⟫_ℂ := by
  unfold modeVec
  rw [inner_sum]
  exact Finset.sum_congr rfl fun k _ => inner_smul_right _ _ _

lemma inner_modeVec_left (e : m → h) (x : m ⊕ m → ℝ) (g : h) :
    ⟪modeVec e x, g⟫_ℂ = ∑ k, ((x (Sum.inl k) : ℂ) - I * (x (Sum.inr k) : ℂ)) * ⟪e k, g⟫_ℂ := by
  unfold modeVec
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_left]
  simp [sub_eq_add_neg]

lemma norm_modeVec_sq {e : m → h} (he : Orthonormal ℂ e) (x : m ⊕ m → ℝ) :
    ‖modeVec e x‖ ^ 2 = ∑ i, x i ^ 2 := by
  have h1 : ⟪modeVec e x, modeVec e x⟫_ℂ = ((∑ i, x i ^ 2 : ℝ) : ℂ) := by
    unfold modeVec
    rw [he.inner_sum, Fintype.sum_sum_type]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_add, map_mul, conj_ofReal, conj_I]
    linear_combination (-((x (Sum.inr k) : ℂ)) ^ 2) * Complex.I_sq
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (modeVec e x)
  rw [h1] at h2
  rw [← h2]
  exact Complex.ofReal_re _

/-- `exp (-‖f_x‖²/4)` as a complex exponential of the coordinates. -/
lemma gaussE_modeVec {e : m → h} (he : Orthonormal ℂ e) (x : m ⊕ m → ℝ) :
    (gaussE (modeVec e x) : ℂ) = cexp (-(1 / 4 : ℂ) * ∑ i, (x i : ℂ) ^ 2) := by
  unfold gaussE
  rw [norm_modeVec_sq he]
  push_cast
  congr 1
  ring

lemma integrable_gaussE_modeVec {e : m → h} (he : Orthonormal ℂ e) :
    Integrable fun x : m ⊕ m → ℝ => gaussE (modeVec e x) := by
  have h1 := (GaussianFourier.integrable_cexp_neg_mul_sum_add (ι := m ⊕ m) (b := (1 / 4 : ℂ))
    quarter_re_pos 0).norm
  refine h1.congr (Eventually.of_forall fun x => ?_)
  have h2 := gaussE_modeVec he x
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← h2, Complex.norm_real, Real.norm_of_nonneg (gaussE_pos _).le]

/-- The matrix element of a Weyl unitary between two coherent vectors. -/
lemma inner_W_Ω_W_Ω (R : FockRep h K) (g f g' : h) :
    ⟪R.W g R.Ω, R.W f (R.W g' R.Ω)⟫_ℂ =
      (gaussE g : ℂ) * gaussE g' * gaussE f * cexp (⟪g, g'⟫_ℂ / 2 + ⟪g, f⟫_ℂ / 2 - ⟪f, g'⟫_ℂ / 2) := by
  rw [R.weyl, inner_smul_right, R.inner_W_Ω, fockGram_eq]
  have hn : gaussE (f + g') = gaussE f * gaussE g' * Real.exp (-(⟪f, g'⟫_ℂ).re / 2) := by
    unfold gaussE
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have h1 := norm_add_sq (𝕜 := ℂ) f g'
    have h2 : RCLike.re ⟪f, g'⟫_ℂ = (⟪f, g'⟫_ℂ).re := rfl
    rw [h1, h2]
    ring
  have key : cexp (-(I * ((⟪f, g'⟫_ℂ).im / 2 : ℂ))) * cexp (-((⟪f, g'⟫_ℂ).re : ℂ) / 2) *
      cexp ((⟪g, f⟫_ℂ + ⟪g, g'⟫_ℂ) / 2) = cexp (⟪g, g'⟫_ℂ / 2 + ⟪g, f⟫_ℂ / 2 - ⟪f, g'⟫_ℂ / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (-1 / 2 : ℂ) * Complex.re_add_im ⟪f, g'⟫_ℂ
  rw [hn, inner_add_right]
  simp only [symp]
  push_cast
  linear_combination ((gaussE g : ℂ) * gaussE g' * gaussE f) * key

/-- The coefficients of the linear term of the Gaussian integrand. -/
noncomputable def modeCoef (e : m → h) (g g' : h) : m ⊕ m → ℂ :=
  Sum.elim (fun k => (⟪g, e k⟫_ℂ - ⟪e k, g'⟫_ℂ) / 2) (fun k => I * (⟪g, e k⟫_ℂ + ⟪e k, g'⟫_ℂ) / 2)

/-- The integrand of the Gaussian average between two coherent vectors, as a Gaussian in the coordinates. -/
lemma vacuumIntegrand_eq (R : FockRep h K) {e : m → h} (he : Orthonormal ℂ e) (g g' : h) (x : m ⊕ m → ℝ) :
    (gaussE (modeVec e x) : ℂ) * ⟪R.W g R.Ω, R.W (modeVec e x) (R.W g' R.Ω)⟫_ℂ =
      ((gaussE g : ℂ) * gaussE g' * cexp (⟪g, g'⟫_ℂ / 2)) *
        cexp (-(1 / 2 : ℂ) * ∑ i, (x i : ℂ) ^ 2 + ∑ i, modeCoef e g g' i * x i) := by
  rw [inner_W_Ω_W_Ω, gaussE_modeVec he, inner_modeVec_right, inner_modeVec_left]
  have hc : ∑ i, modeCoef e g g' i * (x i : ℂ) =
      (∑ k, ((x (Sum.inl k) : ℂ) + I * (x (Sum.inr k) : ℂ)) * ⟪g, e k⟫_ℂ) / 2 -
        (∑ k, ((x (Sum.inl k) : ℂ) - I * (x (Sum.inr k) : ℂ)) * ⟪e k, g'⟫_ℂ) / 2 := by
    rw [Fintype.sum_sum_type, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [modeCoef, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [hc]
  set S := ∑ i, (x i : ℂ) ^ 2
  set S1 := ∑ k, ((x (Sum.inl k) : ℂ) + I * (x (Sum.inr k) : ℂ)) * ⟪g, e k⟫_ℂ
  set S2 := ∑ k, ((x (Sum.inl k) : ℂ) - I * (x (Sum.inr k) : ℂ)) * ⟪e k, g'⟫_ℂ
  rw [show ⟪g, g'⟫_ℂ / 2 + S1 / 2 - S2 / 2 = ⟪g, g'⟫_ℂ / 2 + (S1 / 2 - S2 / 2) by ring,
    show -(1 / 2 : ℂ) * S + (S1 / 2 - S2 / 2) = -(1 / 4 : ℂ) * S + (-(1 / 4 : ℂ) * S + (S1 / 2 - S2 / 2)) by
      ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_add]
  ring

lemma integrable_vacuumIntegrand (R : FockRep h K) {e : m → h} (he : Orthonormal ℂ e) (g g' : h) :
    Integrable fun x : m ⊕ m → ℝ =>
      (gaussE (modeVec e x) : ℂ) * ⟪R.W g R.Ω, R.W (modeVec e x) (R.W g' R.Ω)⟫_ℂ := by
  simp_rw [vacuumIntegrand_eq R he]
  exact (GaussianFourier.integrable_cexp_neg_mul_sum_add half_re_pos _).const_mul _

/-- The normalisation `(√(2π))^(2n)` of the Gaussian average over `n` modes. -/
noncomputable def gaussZ (m : Type*) [Fintype m] : ℝ := Real.sqrt (2 * Real.pi) ^ Fintype.card (m ⊕ m)

lemma gaussZ_pos : 0 < gaussZ m := by
  unfold gaussZ; positivity

lemma gaussZ_eq_cpow :
    (gaussZ m : ℂ) = ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ ((Fintype.card (m ⊕ m) : ℂ) / 2) := by
  have h0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h1 : gaussZ m = (2 * Real.pi) ^ ((Fintype.card (m ⊕ m) : ℝ) / 2) := by
    unfold gaussZ
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
    congr 1
    ring
  rw [h1, Complex.ofReal_cpow h0]
  push_cast
  congr 1
  ring

/-- **The Gaussian average between two coherent vectors.** -/
lemma integral_vacuumIntegrand (R : FockRep h K) {e : m → h} (he : Orthonormal ℂ e) (g g' : h) :
    ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * ⟪R.W g R.Ω, R.W (modeVec e x) (R.W g' R.Ω)⟫_ℂ =
      (gaussZ m : ℂ) * ((gaussE g : ℂ) * gaussE g' *
        cexp (⟪g, g'⟫_ℂ / 2 - (∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ) / 2)) := by
  simp_rw [vacuumIntegrand_eq R he]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sum_add half_re_pos _, ← gaussZ_eq_cpow]
  have hs : (∑ i, modeCoef e g g' i ^ 2) / (4 * (1 / 2 : ℂ)) = -(∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ) / 2 := by
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    have : ∑ k, (modeCoef e g g' (Sum.inl k) ^ 2 + modeCoef e g g' (Sum.inr k) ^ 2) =
        -∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [modeCoef, Sum.elim_inl, Sum.elim_inr]
      linear_combination ((⟪g, e k⟫_ℂ + ⟪e k, g'⟫_ℂ) ^ 2 / 4) * Complex.I_sq
    rw [this]
    ring
  rw [hs, sub_eq_add_neg, Complex.exp_add, neg_div]
  ring

/-- The linear term of the Gaussian integrand, in inner products. -/
lemma sum_modeCoef_mul (e : m → h) (g g' : h) (x : m ⊕ m → ℝ) :
    ∑ i, modeCoef e g g' i * (x i : ℂ) = ⟪g, modeVec e x⟫_ℂ / 2 - ⟪modeVec e x, g'⟫_ℂ / 2 := by
  rw [inner_modeVec_right, inner_modeVec_left, Fintype.sum_sum_type, Finset.sum_div, Finset.sum_div,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [modeCoef, Sum.elim_inl, Sum.elim_inr]
  ring

/-- The Gaussian integral with the linear term `modeCoef`. -/
lemma integral_cexp_modeCoef (e : m → h) (g g' : h) :
    ∫ x : m ⊕ m → ℝ, cexp (-(1 / 2 : ℂ) * ∑ i, (x i : ℂ) ^ 2 + ∑ i, modeCoef e g g' i * x i) =
      (gaussZ m : ℂ) * cexp (-(∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ) / 2) := by
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add half_re_pos _, ← gaussZ_eq_cpow]
  congr 2
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  have : ∑ k, (modeCoef e g g' (Sum.inl k) ^ 2 + modeCoef e g g' (Sum.inr k) ^ 2) =
      -∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [modeCoef, Sum.elim_inl, Sum.elim_inr]
    linear_combination ((⟪g, e k⟫_ℂ + ⟪e k, g'⟫_ℂ) ^ 2 / 4) * Complex.I_sq
  rw [this]
  ring

/-- `∫ exp (-‖f_x‖²/2) dx = (√(2π))^(2n)`. -/
lemma integral_gaussE_sq {e : m → h} (he : Orthonormal ℂ e) :
    ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * gaussE (modeVec e x) = (gaussZ m : ℂ) := by
  have h1 := GaussianFourier.integral_cexp_neg_mul_sum_add (ι := m ⊕ m) (b := (1 / 2 : ℂ)) half_re_pos 0
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, Complex.exp_zero, mul_one] at h1
  rw [← gaussZ_eq_cpow] at h1
  rw [← h1]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [gaussE_modeVec he, ← Complex.exp_add]
  congr 1
  ring

/-- The part of `g` orthogonal to the modes `e`. -/
noncomputable def modePerp (e : m → h) (g : h) : h := g - ∑ k, ⟪e k, g⟫_ℂ • e k

lemma inner_modePerp {e : m → h} (he : Orthonormal ℂ e) (g g' : h) :
    ⟪modePerp e g, modePerp e g'⟫_ℂ = ⟪g, g'⟫_ℂ - ∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ := by
  unfold modePerp
  have h1 : ⟪g, ∑ k, ⟪e k, g'⟫_ℂ • e k⟫_ℂ = ∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [inner_smul_right, mul_comm]
  have h2 : ⟪∑ k, ⟪e k, g⟫_ℂ • e k, g'⟫_ℂ = ∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun k _ => by rw [inner_smul_left, inner_conj_symm]
  have h3 : ⟪∑ k, ⟪e k, g⟫_ℂ • e k, ∑ k, ⟪e k, g'⟫_ℂ • e k⟫_ℂ = ∑ k, ⟪g, e k⟫_ℂ * ⟪e k, g'⟫_ℂ := by
    rw [he.inner_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [inner_conj_symm]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, h1, h2, h3]
  ring

/-- The weight `λ = e(g) / e(g')` of a coherent vector whose mode components are removed. -/
noncomputable def modeWeight (e : m → h) (g : h) : ℝ := gaussE g / gaussE (modePerp e g)

lemma modeWeight_mul (e : m → h) (g : h) : modeWeight e g * gaussE (modePerp e g) = gaussE g :=
  div_mul_cancel₀ _ (gaussE_pos _).ne'

/-- The Gaussian average between two coherent vectors is `(2π)ⁿ` times the inner product of the weighted
coherent vectors with the mode components removed. -/
lemma integral_vacuumIntegrand' (R : FockRep h K) {e : m → h} (he : Orthonormal ℂ e) (g g' : h) :
    ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * ⟪R.W g R.Ω, R.W (modeVec e x) (R.W g' R.Ω)⟫_ℂ =
      (gaussZ m : ℂ) * ((modeWeight e g : ℂ) * modeWeight e g' *
        ⟪R.W (modePerp e g) R.Ω, R.W (modePerp e g') R.Ω⟫_ℂ) := by
  rw [integral_vacuumIntegrand R he, R.inner_W_Ω, fockGram_eq, inner_modePerp he, ← modeWeight_mul e g,
    ← modeWeight_mul e g']
  push_cast
  rw [sub_div]
  ring

lemma inner_Ω_W_Ω (R : FockRep h K) (f : h) : ⟪R.Ω, R.W f R.Ω⟫_ℂ = (gaussE f : ℂ) := by
  rw [R.vacuum_expectation, gaussE, Complex.ofReal_exp, Complex.ofReal_neg]

/-- The bound on the dense set of finite combinations of coherent vectors. -/
lemma gaussZ_mul_norm_inner_sq_le_of_span (R : FockRep h K) {e : m → h} (he : Orthonormal ℂ e)
    {J : Type*} (s : Finset J) (c : J → ℂ) (g : J → h) :
    gaussZ m * ‖⟪R.Ω, ∑ j ∈ s, c j • R.W (g j) R.Ω⟫_ℂ‖ ^ 2 ≤
      (∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
        ⟪∑ j ∈ s, c j • R.W (g j) R.Ω, R.W (modeVec e x) (∑ j ∈ s, c j • R.W (g j) R.Ω)⟫_ℂ).re := by
  set φ' : K := ∑ j ∈ s, (c j * modeWeight e (g j)) • R.W (modePerp e (g j)) R.Ω with hφ'
  -- the integrand as a double sum
  have hint : ∀ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
      ⟪∑ j ∈ s, c j • R.W (g j) R.Ω, R.W (modeVec e x) (∑ j ∈ s, c j • R.W (g j) R.Ω)⟫_ℂ =
      ∑ j ∈ s, ∑ k ∈ s, (starRingEnd ℂ (c j) * c k) * ((gaussE (modeVec e x) : ℂ) *
        ⟪R.W (g j) R.Ω, R.W (modeVec e x) (R.W (g k) R.Ω)⟫_ℂ) := by
    intro x
    rw [map_sum, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right]
    ring
  have hval : ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
      ⟪∑ j ∈ s, c j • R.W (g j) R.Ω, R.W (modeVec e x) (∑ j ∈ s, c j • R.W (g j) R.Ω)⟫_ℂ =
      (gaussZ m : ℂ) * ⟪φ', φ'⟫_ℂ := by
    simp_rw [hint]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (integrable_vacuumIntegrand R he (g j) (g k)).const_mul _]
    rw [hφ', sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => (integrable_vacuumIntegrand R he (g j) (g k)).const_mul _,
      inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_vacuumIntegrand' R he, inner_smul_left, inner_smul_right]
    simp only [map_mul, conj_ofReal]
    ring
  have hΩ : ⟪R.Ω, φ'⟫_ℂ = ⟪R.Ω, ∑ j ∈ s, c j • R.W (g j) R.Ω⟫_ℂ := by
    rw [hφ', inner_sum, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, inner_smul_right, inner_Ω_W_Ω, inner_Ω_W_Ω, ← modeWeight_mul e (g j)]
    push_cast
    ring
  have hin : (⟪φ', φ'⟫_ℂ).re = ‖φ'‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) φ'
  rw [hval, ← hΩ, Complex.re_ofReal_mul, hin]
  refine mul_le_mul_of_nonneg_left ?_ gaussZ_pos.le
  have hcs : ‖⟪R.Ω, φ'⟫_ℂ‖ ≤ ‖φ'‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) R.Ω φ'
    rwa [R.norm_Ω, one_mul] at this
  exact pow_le_pow_left₀ (norm_nonneg _) hcs 2

/-- **The Gaussian average of the Weyl unitaries bounds the vacuum overlap.** For an orthonormal family `e`
and every vector `Φ` of a Fock representation,
`(√(2π))^(2n) |⟪Ω, Φ⟫|² ≤ Re ∫ exp (-‖f_x‖²/4) ⟪Φ, W f_x Φ⟫ dx`. -/
theorem gaussZ_mul_norm_inner_sq_le (R : FockRep h K) {e : m → h} (he : Orthonormal ℂ e) (Φ : K) :
    gaussZ m * ‖⟪R.Ω, Φ⟫_ℂ‖ ^ 2 ≤
      (∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * ⟪Φ, R.W (modeVec e x) Φ⟫_ℂ).re := by
  have hmem : Φ ∈ closure ((LinearMap.range (fockMap R) : Submodule ℂ K) : Set K) :=
    (dense_range_fockMap R) Φ
  obtain ⟨φ, hφmem, hφlim⟩ := mem_closure_iff_seq_limit.1 hmem
  have hφmem' : ∀ n, ∃ c, fockMap R c = φ n := fun n => LinearMap.mem_range.1 (hφmem n)
  choose c hc using hφmem'
  have hφ : ∀ n, φ n = ∑ f ∈ (c n).support, (c n) f • R.W f R.Ω := fun n => by
    rw [← hc n]; unfold fockMap; rw [Finsupp.linearCombination_apply]; rfl
  obtain ⟨M, hM⟩ := hφlim.norm.bddAbove_range
  have hMn : ∀ n, ‖φ n‖ ≤ M := fun n => hM (Set.mem_range_self n)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMn 0)
  -- dominated convergence
  have hlim : Tendsto (fun n => ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
      ⟪φ n, R.W (modeVec e x) (φ n)⟫_ℂ) atTop
      (𝓝 (∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * ⟪Φ, R.W (modeVec e x) Φ⟫_ℂ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => gaussE (modeVec e x) * M ^ 2) ?_
      ((integrable_gaussE_modeVec he).mul_const _) ?_ ?_
    · intro n
      have hi : Integrable fun x : m ⊕ m → ℝ => (gaussE (modeVec e x) : ℂ) *
          ⟪φ n, R.W (modeVec e x) (φ n)⟫_ℂ := by
        rw [hφ n]
        have hint : ∀ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
            ⟪∑ f ∈ (c n).support, (c n) f • R.W f R.Ω,
              R.W (modeVec e x) (∑ f ∈ (c n).support, (c n) f • R.W f R.Ω)⟫_ℂ =
            ∑ j ∈ (c n).support, ∑ k ∈ (c n).support, (starRingEnd ℂ ((c n) j) * (c n) k) *
              ((gaussE (modeVec e x) : ℂ) * ⟪R.W j R.Ω, R.W (modeVec e x) (R.W k R.Ω)⟫_ℂ) := by
          intro x
          rw [map_sum, sum_inner, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [inner_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul, inner_smul_left, inner_smul_right]
          ring
        simp_rw [hint]
        exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
          (integrable_vacuumIntegrand R he j k).const_mul _
      exact hi.aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussE_pos _).le]
      refine mul_le_mul_of_nonneg_left ?_ (gaussE_pos _).le
      calc ‖⟪φ n, R.W (modeVec e x) (φ n)⟫_ℂ‖ ≤ ‖φ n‖ * ‖R.W (modeVec e x) (φ n)‖ := norm_inner_le_norm _ _
        _ = ‖φ n‖ * ‖φ n‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ M * M := mul_le_mul (hMn n) (hMn n) (norm_nonneg _) hM0
        _ = M ^ 2 := (sq M).symm
    · refine Eventually.of_forall fun x => ?_
      exact (hφlim.inner (((R.W (modeVec e x)).continuous.tendsto Φ).comp hφlim)).const_mul _
  have hl : Tendsto (fun n => gaussZ m * ‖⟪R.Ω, φ n⟫_ℂ‖ ^ 2) atTop (𝓝 (gaussZ m * ‖⟪R.Ω, Φ⟫_ℂ‖ ^ 2)) :=
    (((tendsto_const_nhds (x := R.Ω)).inner hφlim).norm.pow 2).const_mul _
  have hr := (Complex.continuous_re.tendsto _).comp hlim
  refine le_of_tendsto_of_tendsto' hl hr fun n => ?_
  have := gaussZ_mul_norm_inner_sq_le_of_span R he (c n).support (c n) fun f => f
  rw [← hφ n] at this
  exact this

end Lightlike.OperatorAlgebras

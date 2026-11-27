module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteBasisComplete
public import Lightlike.Lorentz.SL2RPlancherel.DiscreteSchur
public import Lightlike.Lorentz.SL2RPlancherel.NonnegSeriesUnique

/-!
# The coherent vectors `D_n(a) e₀` of the holomorphic discrete series

For the diagonal element `g_A = diag(A, A⁻¹)` the vector `D_n(g_A) e₀` is the function `z ↦ (A z + i/A)^{-n}`
(`discreteAction_diag_lowest`). Its pairing with the `K`-weight vector `e_k` is
`γ_A β_k (-t_A)^k ‖e_k‖²` with `γ_A = (2/(A + A⁻¹))^n`, `t_A = (A - A⁻¹)/(A + A⁻¹)` and
`β_k = C(n-1+k, n-1)` the coefficients of `(1 - x)^{-n}` (`inner_kClass_diag_lowest`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The coherent function `z ↦ (A z + i A⁻¹)^{-n}` on `ℍ`. -/
def cohFun (n : ℕ) (A : ℝ) (z : ℍ) : ℂ :=
  ((A : ℂ) * (z : ℂ) + Complex.I * ((A⁻¹ : ℝ) : ℂ)) ^ (-(n : ℤ))

lemma cohArg_ne_zero {A : ℝ} (hA : 0 < A) (z : ℍ) :
    (A : ℂ) * (z : ℂ) + Complex.I * ((A⁻¹ : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_im,
    UpperHalfPlane.coe_re, Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_zero, Complex.zero_im] at this
  have h1 : 0 < A * z.im := mul_pos hA z.im_pos
  have h2 : 0 < A⁻¹ := inv_pos.2 hA
  linarith

lemma continuous_cohFun {A : ℝ} (hA : 0 < A) (n : ℕ) : Continuous (cohFun n A) := by
  unfold cohFun
  exact Continuous.zpow₀ (by fun_prop) _ fun z => Or.inl (cohArg_ne_zero hA z)

lemma mdifferentiable_cohFun {A : ℝ} (hA : 0 < A) (n : ℕ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cohFun n A) := by
  intro z
  have h : DifferentiableAt ℂ (fun w : ℂ => ((A : ℂ) * w + Complex.I * ((A⁻¹ : ℝ) : ℂ)) ^ (-(n : ℤ))) z :=
    ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)).zpow
      (Or.inl (cohArg_ne_zero hA z))
  exact (h.mdifferentiableAt).comp z (UpperHalfPlane.mdifferentiable_coe z)

/-- **`D_n(diag(A, A⁻¹)) e₀` is the coherent function.** -/
theorem discreteAction_diag_lowest {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 < A) :
    discreteAction n (diagSL A hA.ne') (lowestClass hn) =ᵐ[μn n] cohFun n A := by
  have h := coeFn_discreteAction_holo n (diagSL A hA.ne') (f := lowestClass hn) (φ := lowestVec n)
    (MemLp.coeFn_toLp _)
  filter_upwards [h] with z hz
  rw [hz]
  have hj : jac (diagSL A hA.ne') (z : ℂ) = ((A⁻¹ : ℝ) : ℂ) := by simp [jac, diagSL]
  have ht : ((tsmul (diagSL A hA.ne') z : ℍ) : ℂ) = (A : ℂ) ^ 2 * (z : ℂ) := by
    rw [coe_tsmul, hj]
    have : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    simp [diagSL]
    field_simp
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  unfold lowestVec cohFun
  rw [hj, ht]
  have : (A : ℂ) * (z : ℂ) + Complex.I * ((A⁻¹ : ℝ) : ℂ) = ((A⁻¹ : ℝ) : ℂ) * ((A : ℂ) ^ 2 * (z : ℂ) + Complex.I) := by
    push_cast; field_simp
  rw [this, mul_zpow]

/-- The parameter `t_A = (A - A⁻¹)/(A + A⁻¹) ∈ (-1, 1)`. -/
def tpar (A : ℝ) : ℝ := (A - A⁻¹) / (A + A⁻¹)

lemma abs_tpar_lt_one {A : ℝ} (hA : 0 < A) : |tpar A| < 1 := by
  have h1 : 0 < A + A⁻¹ := by positivity
  have h2 : 0 < A⁻¹ := inv_pos.2 hA
  unfold tpar
  rw [abs_div, abs_of_pos h1, div_lt_one h1, abs_lt]
  constructor <;> linarith

/-- The constant `κ_A = 4 (-2i)^{-n} (i (A + A⁻¹))^{-n}`. -/
def kappa (n : ℕ) (A : ℝ) : ℂ :=
  4 * ((-2 * Complex.I) ^ n)⁻¹ * ((Complex.I * ((A + A⁻¹ : ℝ) : ℂ)) ^ n)⁻¹

/-- **The disc function of the coherent vector**: `κ_A (1 + t_A w)^{-n}` on the unit disc. -/
lemma bergmanDisc_cohFun {n : ℕ} {A : ℝ} (hA : 0 < A) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    bergmanDisc n (fun w => cohFun n A (UpperHalfPlane.ofComplex w)) w =
      kappa n A * ((1 + (tpar A : ℂ) * w) ^ n)⁻¹ := by
  have hu := one_sub_ne_zero hw
  have hz : ((UpperHalfPlane.ofComplex (cayleyInv w) : ℍ) : ℂ) = cayleyInv w := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (cayleyInv_mem hw)]
  have hs : (A + A⁻¹ : ℝ) ≠ 0 := by positivity
  have hs' : ((A + A⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have key : (A : ℂ) * cayleyInv w + Complex.I * ((A⁻¹ : ℝ) : ℂ) =
      Complex.I * ((A + A⁻¹ : ℝ) : ℂ) * (1 + (tpar A : ℂ) * w) / (1 - w) := by
    unfold cayleyInv tpar
    have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast
    have hs2 : (A : ℂ) + (A : ℂ)⁻¹ ≠ 0 := by push_cast at hs'; exact hs'
    have h1A : (1 : ℂ) + (A : ℂ) ^ 2 ≠ 0 := by
      have : (0 : ℝ) < 1 + A ^ 2 := by positivity
      exact_mod_cast this.ne'
    have h1A' : (A : ℂ) ^ 2 + 1 ≠ 0 := by rw [add_comm]; exact h1A
    field_simp
    ring
  unfold bergmanDisc kappa cohFun
  simp only [hz, zpow_neg, zpow_natCast]
  rw [key]
  have h1 : (1 - w) ^ n ≠ 0 := pow_ne_zero _ hu
  have h2 : (Complex.I * ((A + A⁻¹ : ℝ) : ℂ)) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero hs')
  have h3 : ((-2 * Complex.I) ^ n) ≠ 0 := pow_ne_zero _ (by simp [Complex.I_ne_zero])
  simp only [div_pow, mul_pow]
  field_simp

/-- **The Taylor coefficients of `κ (1 + t w)^{-n}`**: `κ C(n-1+k, n-1) (-t)^k`. -/
lemma discCoeff_inv_pow {n : ℕ} (hn : 2 ≤ n) (κ : ℂ) {t : ℝ} (ht : |t| < 1) (k : ℕ) :
    discCoeff (fun w => κ * ((1 + (t : ℂ) * w) ^ n)⁻¹) k =
      κ * ((Nat.choose (n - 1 + k) (n - 1) : ℂ) * (-(t : ℂ)) ^ k) := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  set u : ℂ →L[ℂ] ℂ := (-(t : ℂ)) • ContinuousLinearMap.id ℂ ℂ with hudef
  have hu : ∀ w, u w = -(t : ℂ) * w := fun w => by simp [hudef]
  have H := one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a
  have H0 : HasFPowerSeriesOnBall (fun x : ℂ => 1 / (1 - x) ^ (a + 1))
      (FormalMultilinearSeries.ofScalars ℂ (𝕜 := ℂ) fun n => (Nat.choose (a + n) a : ℂ)) (u 0) 1 := by
    rw [map_zero]; exact H
  have H1 := H0.compContinuousLinearMap (u := u) (x := 0)
  have hu1 : ‖u‖ ≤ 1 := by
    calc ‖u‖ ≤ ‖(-(t : ℂ))‖ * ‖ContinuousLinearMap.id ℂ ℂ‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ |t| * 1 := by
          gcongr
          · simp
          · exact ContinuousLinearMap.norm_id_le
      _ ≤ 1 := by linarith [ht.le]
  have hne : ‖u‖ₑ ≤ 1 := by rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 hu1
  have hrad : (1 : ENNReal) ≤ 1 / ‖u‖ₑ :=
    (ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top)).2 (by simpa using hne)
  have H2 := (H1.mono one_pos hrad).const_smul (c := κ)
  have hfun : (fun w : ℂ => κ * ((1 + (t : ℂ) * w) ^ (a + 1))⁻¹) =
      κ • ((fun x : ℂ => 1 / (1 - x) ^ (a + 1)) ∘ u) := by
    funext w
    simp only [Function.comp_apply, hu, Pi.smul_apply, smul_eq_mul, one_div]
    congr 3; ring
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => κ * ((1 + (t : ℂ) * w) ^ (a + 1))⁻¹) (ball (0 : ℂ) 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hne1 : 1 + (t : ℂ) * w ≠ 0 := by
      intro h0
      have h1 : (t : ℂ) * w = -1 := by linear_combination h0
      have h2 : ‖(t : ℂ) * w‖ = 1 := by rw [h1]; simp
      have h3 : ‖(t : ℂ) * w‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |t| * ‖w‖ ≤ |t| * 1 := by gcongr
          _ < 1 := by linarith
      linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).mul ?_
    exact (((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)).pow _).inv
      (pow_ne_zero _ hne1)
  rw [hfun] at hdiff ⊢
  rw [discCoeff_eq_of_hasFPowerSeriesOnBall hdiff H2 k]
  show κ * ((FormalMultilinearSeries.ofScalars ℂ (𝕜 := ℂ) fun n => (Nat.choose (a + n) a : ℂ)).compContinuousLinearMap
    u k (fun _ : Fin k => (1 : ℂ))) = _
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
  have : (u ∘ fun _ : Fin k => (1 : ℂ)) = fun _ => -(t : ℂ) := by funext i; simp [hu]
  rw [this, FormalMultilinearSeries.ofScalars_apply_eq]
  simp only [Nat.add_sub_cancel, smul_eq_mul]

/-- The constant `γ_A = (2/(A + A⁻¹))^n`. -/
def gam (n : ℕ) (A : ℝ) : ℝ := (2 / (A + A⁻¹)) ^ n

lemma kappa_mul (n : ℕ) {A : ℝ} (hA : 0 < A) :
    kappa n A * ((4 : ℂ) ^ n / 4) = (gam n A : ℂ) := by
  have hs : (A + A⁻¹ : ℝ) ≠ 0 := by positivity
  have hs' : ((A + A⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have h1 : (-2 * Complex.I) * (Complex.I * ((A + A⁻¹ : ℝ) : ℂ)) = 2 * ((A + A⁻¹ : ℝ) : ℂ) := by
    linear_combination (-2 * ((A + A⁻¹ : ℝ) : ℂ)) * Complex.I_sq
  have e : (4 : ℂ) * ((-2 * Complex.I) ^ n)⁻¹ * ((Complex.I * ((A + A⁻¹ : ℝ) : ℂ)) ^ n)⁻¹ =
      4 * ((2 * ((A + A⁻¹ : ℝ) : ℂ)) ^ n)⁻¹ := by
    rw [mul_assoc, ← mul_inv, ← mul_pow, h1]
  unfold kappa gam
  rw [e]
  have h3 : (((A + A⁻¹ : ℝ) : ℂ)) ≠ 0 := hs'
  push_cast
  have h3' : ((A : ℂ) + (A : ℂ)⁻¹) ≠ 0 := by push_cast at h3; exact h3
  have h44 : (4 : ℂ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [h44]
  simp only [div_pow, mul_pow]
  have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5 : ((A : ℂ) + (A : ℂ)⁻¹) ^ n ≠ 0 := pow_ne_zero _ h3'
  field_simp

/-- **The pairing of `e_k` with the coherent vector**:
`⟨e_k, D_n(diag(A, A⁻¹)) e₀⟩ = γ_A C(n-1+k, n-1) (-t_A)^k ‖e_k‖²`. -/
theorem inner_kClass_diag_lowest {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 < A) (k : ℕ) :
    ⟪kClass hn k, discreteAction n (diagSL A hA.ne') (lowestClass hn)⟫_ℂ =
      (gam n A : ℂ) * ((Nat.choose (n - 1 + k) (n - 1) : ℂ) * (-(tpar A : ℂ)) ^ k) *
        ((‖kClass hn k‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_kClass_holo hn k (mdifferentiable_cohFun hA n) (discreteAction_diag_lowest hn hA)]
  rw [discCoeff_congr (h' := fun w => kappa n A * ((1 + (tpar A : ℂ) * w) ^ n)⁻¹)
    (fun w hw => bergmanDisc_cohFun hA hw) k, discCoeff_inv_pow hn (kappa n A) (abs_tpar_lt_one hA) k]
  rw [norm_sq_kClass hn k, ← kappa_mul n hA]
  push_cast
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- `γ_A² = (1 - t_A²)^n`. -/
lemma gam_sq (n : ℕ) {A : ℝ} (hA : 0 < A) : gam n A ^ 2 = (1 - tpar A ^ 2) ^ n := by
  have hs : (0 : ℝ) < A + A⁻¹ := by positivity
  have h1 : (2 / (A + A⁻¹)) ^ 2 = 1 - tpar A ^ 2 := by
    unfold tpar
    have hA0 : A ≠ 0 := hA.ne'
    field_simp
    ring_nf
  unfold gam
  rw [← pow_mul, mul_comm, pow_mul, h1]

/-- Every `t ∈ (-1, 1)` is `t_A` for some `A > 0`. -/
lemma exists_tpar_eq {t : ℝ} (ht : |t| < 1) : ∃ A : ℝ, 0 < A ∧ tpar A = t := by
  have h1 : 0 < 1 - t := by linarith [(abs_lt.1 ht).2]
  have h2 : 0 < 1 + t := by linarith [(abs_lt.1 ht).1]
  refine ⟨Real.sqrt ((1 + t) / (1 - t)), Real.sqrt_pos.2 (by positivity), ?_⟩
  set A := Real.sqrt ((1 + t) / (1 - t)) with hAdef
  have hA2 : A ^ 2 = (1 + t) / (1 - t) := Real.sq_sqrt (by positivity)
  have hA0 : 0 < A := Real.sqrt_pos.2 (by positivity)
  unfold tpar
  have : A + A⁻¹ ≠ 0 := by positivity
  have hA2' : A ^ 2 * (1 - t) = 1 + t := by rw [hA2]; field_simp
  rw [div_eq_iff this]
  field_simp
  nlinarith [hA2']

lemma choose_pos {n : ℕ} (_hn : 2 ≤ n) (k : ℕ) : 0 < (Nat.choose (n - 1 + k) (n - 1) : ℝ) :=
  Nat.cast_pos.2 (Nat.choose_pos (by omega))

/-- The squared modulus of the pairing of `e_i` with the coherent vector. -/
lemma norm_sq_inner_diag_lowest {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 < A) (i : ℕ) :
    ‖⟪kClass hn i, discreteAction n (diagSL A hA.ne') (lowestClass hn)⟫_ℂ‖ ^ 2 =
      gam n A ^ 2 * (Nat.choose (n - 1 + i) (n - 1) : ℝ) ^ 2 * (tpar A ^ 2) ^ i * (‖kClass hn i‖ ^ 2) ^ 2 := by
  rw [inner_kClass_diag_lowest hn hA i]
  have h1 : (gam n A : ℂ) * ((Nat.choose (n - 1 + i) (n - 1) : ℂ) * (-(tpar A : ℂ)) ^ i) *
      ((‖kClass hn i‖ ^ 2 : ℝ) : ℂ) =
      ((gam n A * ((Nat.choose (n - 1 + i) (n - 1) : ℝ) * (-tpar A) ^ i) * ‖kClass hn i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h3 : ((-tpar A) ^ i) ^ 2 = (tpar A ^ 2) ^ i := by rw [← pow_mul, mul_comm, pow_mul, neg_sq]
  calc (gam n A * ((Nat.choose (n - 1 + i) (n - 1) : ℝ) * (-tpar A) ^ i) * ‖kClass hn i‖ ^ 2) ^ 2
      = gam n A ^ 2 * (Nat.choose (n - 1 + i) (n - 1) : ℝ) ^ 2 * ((-tpar A) ^ i) ^ 2 *
          (‖kClass hn i‖ ^ 2) ^ 2 := by ring
    _ = _ := by rw [h3]

/-- **Parseval for the coherent vector**: `Σ_i γ_A² C_i² t_A^{2i} ‖e_i‖² = ‖e₀‖²`, `C_i = C(n-1+i, n-1)`. -/
lemma hasSum_coh_parseval {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 < A) :
    HasSum (fun i : ℕ => gam n A ^ 2 * (Nat.choose (n - 1 + i) (n - 1) : ℝ) ^ 2 * (tpar A ^ 2) ^ i *
      ‖kClass hn i‖ ^ 2) (‖kClass hn 0‖ ^ 2) := by
  set xv : holoSubmodule n := ⟨discreteAction n (diagSL A hA.ne') (lowestClass hn),
    discreteAction_mem_holoSubmodule n _ (lowestClass_mem hn)⟩ with hxv
  have hP := (kBasis hn).hasSum_inner_mul_inner xv xv
  have hb : ∀ i, (kBasis hn) i = kUnit hn i := fun i =>
    congrFun (HilbertBasis.coe_mk (kUnit_orthonormal hn) (kUnit_span_top hn)) i
  have hterm : ∀ i : ℕ, ⟪xv, (kBasis hn) i⟫_ℂ * ⟪(kBasis hn) i, xv⟫_ℂ =
      ((gam n A ^ 2 * (Nat.choose (n - 1 + i) (n - 1) : ℝ) ^ 2 * (tpar A ^ 2) ^ i * ‖kClass hn i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [hb i]
    have hu : ⟪kUnit hn i, xv⟫_ℂ = ((‖kClass hn i‖⁻¹ : ℝ) : ℂ) *
        ⟪kClass hn i, discreteAction n (diagSL A hA.ne') (lowestClass hn)⟫_ℂ := by
      simp only [kUnit, Submodule.coe_inner, inner_smul_left, Complex.conj_ofReal, hxv]
    have h2 : ⟪xv, kUnit hn i⟫_ℂ = (starRingEnd ℂ) ⟪kUnit hn i, xv⟫_ℂ := by
      simp only [Submodule.coe_inner]; exact (inner_conj_symm _ _).symm
    rw [h2, Complex.conj_mul', hu, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hne : ‖kClass hn i‖ ≠ 0 := (norm_kClass_pos hn i).ne'
    have hreal : (|‖kClass hn i‖⁻¹| *
        ‖⟪kClass hn i, discreteAction n (diagSL A hA.ne') (lowestClass hn)⟫_ℂ‖) ^ 2 =
        gam n A ^ 2 * (Nat.choose (n - 1 + i) (n - 1) : ℝ) ^ 2 * (tpar A ^ 2) ^ i * ‖kClass hn i‖ ^ 2 := by
      rw [mul_pow, sq_abs, norm_sq_inner_diag_lowest hn hA i]
      field_simp
    rw [← Complex.ofReal_pow, hreal]
  have hnorm : ⟪xv, xv⟫_ℂ = ((‖kClass hn 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Submodule.coe_inner, inner_self_eq_norm_sq_to_K]
    have : ‖(xv : Hn n)‖ = ‖kClass hn 0‖ := by
      rw [kClass_zero hn]
      show ‖discreteAction n (diagSL A hA.ne') (lowestClass hn)‖ = ‖lowestClass hn‖
      exact discreteAction_norm n _ _
    rw [this]
    norm_cast
  simp only [hterm, hnorm] at hP
  exact_mod_cast hP

/-- **The series `Σ C(a+i, a) x^i = (1 - x)^{-(a+1)}`** on `[0, 1)`, from Mathlib's binomial series. -/
lemma hasSum_choose_series (a : ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    HasSum (fun i : ℕ => (Nat.choose (a + i) a : ℝ) * x ^ i) (1 / (1 - x) ^ (a + 1)) := by
  have H := one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a
  have hy : (x : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by
    simp only [Metric.eball, edist_zero_right, Set.mem_ofPred_eq]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact ENNReal.ofReal_lt_one.2 hx.2
  have h1 := H.hasSum hy
  rw [zero_add] at h1
  have h2 : HasSum (fun i : ℕ => (((Nat.choose (a + i) a : ℝ) * x ^ i : ℝ) : ℂ))
      (((1 / (1 - x) ^ (a + 1) : ℝ) : ℂ)) := by
    simp only [FormalMultilinearSeries.ofScalars_apply_eq] at h1
    push_cast
    simpa [smul_eq_mul] using h1
  exact Complex.hasSum_ofReal.1 h2

lemma hasSum_choose_series' {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    HasSum (fun i : ℕ => (Nat.choose (n - 1 + i) (n - 1) : ℝ) * x ^ i) (1 / (1 - x) ^ n) := by
  have := hasSum_choose_series (n - 1) hx
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this

/-- **The coefficients of the norms of the `K`-weight vectors**: `C(n-1+k, n-1) ‖e_k‖² = ‖e₀‖²`. -/
theorem choose_mul_norm_sq_kClass {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (Nat.choose (n - 1 + k) (n - 1) : ℝ) * ‖kClass hn k‖ ^ 2 = ‖kClass hn 0‖ ^ 2 := by
  set β : ℕ → ℝ := fun i => (Nat.choose (n - 1 + i) (n - 1) : ℝ) with hβ
  set N : ℕ → ℝ := fun i => ‖kClass hn i‖ ^ 2 with hN
  have hβpos : ∀ i, 0 < β i := fun i => choose_pos hn i
  have hA : ∀ x ∈ Ico (0 : ℝ) 1, HasSum (fun i => (β i ^ 2 * N i) * x ^ i) (N 0 / (1 - x) ^ n) := by
    intro x hx
    have ht : |Real.sqrt x| < 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_lt' one_pos).2 (by simpa using hx.2)
    obtain ⟨A, hA0, hAt⟩ := exists_tpar_eq ht
    have hP := hasSum_coh_parseval hn hA0
    rw [hAt, Real.sq_sqrt hx.1] at hP
    have hg : gam n A ^ 2 = (1 - x) ^ n := by
      rw [gam_sq n hA0, hAt, Real.sq_sqrt hx.1]
    have hgpos : 0 < (1 - x) ^ n := pow_pos (by linarith [hx.2]) _
    have := hP.div_const (gam n A ^ 2)
    rw [hg] at this
    convert this using 1
    · funext i; simp only [hβ, hN]; field_simp
  have hB : ∀ x ∈ Ico (0 : ℝ) 1, HasSum (fun i => (N 0 * β i) * x ^ i) (N 0 / (1 - x) ^ n) := by
    intro x hx
    have := (hasSum_choose_series' hn hx).mul_left (N 0)
    have e1 : (fun i => (N 0 * β i) * x ^ i) = fun i => N 0 * ((β i) * x ^ i) := by funext i; ring
    have e2 : N 0 / (1 - x) ^ n = N 0 * (1 / (1 - x) ^ n) := (mul_one_div _ _).symm
    rw [e1, e2]; exact this
  have hcoef := coeff_eq_of_hasSum (a := fun i => β i ^ 2 * N i) (b := fun i => N 0 * β i)
    (fun i => by simp only [hN]; positivity) (fun i => by have := hβpos i; simp only [hN]; positivity)
    (S := fun x => N 0 / (1 - x) ^ n) hA hB
  have hk := congrFun hcoef k
  have : β k * N k = N 0 := by
    have hbk := hβpos k
    have : β k * (β k * N k) = β k * N 0 := by linarith [hk]
    exact mul_left_cancel₀ hbk.ne' this
  simpa [hβ, hN] using this

end Lightlike.Lorentz.SL2RPlancherel

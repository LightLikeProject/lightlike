module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteBasis
public import Lightlike.Lorentz.SL2RPlancherel.BergmanReproducing
public import Lightlike.Lorentz.SL2RPlancherel.DiscMode

/-!
# Completeness of the `K`-weight vectors of the holomorphic discrete series

The pairing of `e_k(z) = (z - i)^k (z + i)^{-(n+k)}` with a vector `ψ` of the weighted Bergman space `A²_n` is, after the
Cayley transform, the `k`-th Taylor coefficient at `0` of the holomorphic function `w ↦ φ(i(1+w)/(1-w)) (1-w)^{-n}`
times a positive constant (`inner_kClass_holo`). So a vector orthogonal to every `e_k` vanishes (`kClass_complete`):
together with the orthogonality of `DiscreteBasis.lean`, the family `(e_k)` is an orthogonal Hilbert basis of `A²_n`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real UpperHalfPlane Lightlike.Lorentz.SL2R
open scoped InnerProductSpace Manifold

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The holomorphic function on the unit disc attached to `φ` by the Cayley transform:
`w ↦ 4 (-2i)^{-n} φ(i(1+w)/(1-w)) (1-w)^{-n}`. -/
def bergmanDisc (n : ℕ) (φ : ℂ → ℂ) (w : ℂ) : ℂ :=
  4 * ((-2 * Complex.I) ^ n)⁻¹ * (φ (cayleyInv w) * ((1 - w) ^ n)⁻¹)

lemma differentiableOn_bergmanDisc (n : ℕ) {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ (bergmanDisc n φ) (ball (0 : ℂ) 1) := by
  intro w hw
  have h1 := one_sub_ne_zero hw
  have hz : cayleyInv w ∈ {z : ℂ | 0 < z.im} := cayleyInv_mem hw
  have hφd : DifferentiableAt ℂ φ (cayleyInv w) :=
    (hφ (cayleyInv w) hz).differentiableAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)
  have hc : DifferentiableAt ℂ cayleyInv w := (hasDerivAt_cayleyInv hw).differentiableAt
  have : DifferentiableAt ℂ (bergmanDisc n φ) w := by
    show DifferentiableAt ℂ (fun w => 4 * ((-2 * Complex.I) ^ n)⁻¹ * (φ (cayleyInv w) * ((1 - w) ^ n)⁻¹)) w
    refine (differentiableAt_const _).mul ((hφd.comp w hc).mul ?_)
    exact ((differentiableAt_const _).sub differentiableAt_id |>.pow n).inv (pow_ne_zero _ h1)
  exact this.differentiableWithinAt

/-- The Cayley transform of the pairing with `e_k`: the integrand is `h(w) conj(w)^k ρ(|w|)`. -/
lemma pairing_cayley_mode {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (m : ℕ) (φ : ℂ → ℂ) :
    (4 / ‖1 - w‖ ^ 4 : ℝ) • (φ (cayleyInv w) *
        (starRingEnd ℂ) ((cayleyInv w - Complex.I) ^ m * ((cayleyInv w + Complex.I) ^ (n + m))⁻¹) *
        (((cayleyInv w).im ^ (n - 2) : ℝ) : ℂ)) =
      (4 * ((-2 * Complex.I) ^ n)⁻¹ * (φ (cayleyInv w) * ((1 - w) ^ n)⁻¹)) * (starRingEnd ℂ w) ^ m *
        (((1 - ‖w‖ ^ 2) ^ (n - 2) : ℝ) : ℂ) := by
  have hu := one_sub_ne_zero hw
  have hzI : cayleyInv w + Complex.I = 2 * Complex.I / (1 - w) := by
    unfold cayleyInv; field_simp; ring
  have hz0 : cayleyInv w + Complex.I ≠ 0 := by
    rw [hzI]; exact div_ne_zero (by simp [Complex.I_ne_zero]) hu
  have hzm : cayleyInv w - Complex.I = w * (cayleyInv w + Complex.I) := by
    unfold cayleyInv; field_simp; ring
  have hk : (cayleyInv w - Complex.I) ^ m * ((cayleyInv w + Complex.I) ^ (n + m))⁻¹ =
      w ^ m * ((cayleyInv w + Complex.I) ^ n)⁻¹ := by
    rw [hzm, mul_pow, pow_add, mul_inv]
    field_simp
  have hpc := pairing_cayley hn hw φ
  rw [hk, map_mul, map_pow]
  have e : (4 / ‖1 - w‖ ^ 4 : ℝ) • (φ (cayleyInv w) *
      ((starRingEnd ℂ w) ^ m * (starRingEnd ℂ) (((cayleyInv w + Complex.I) ^ n)⁻¹)) *
        (((cayleyInv w).im ^ (n - 2) : ℝ) : ℂ)) =
      (starRingEnd ℂ w) ^ m * ((4 / ‖1 - w‖ ^ 4 : ℝ) • (φ (cayleyInv w) *
        (starRingEnd ℂ) (((cayleyInv w + Complex.I) ^ n)⁻¹) * (((cayleyInv w).im ^ (n - 2) : ℝ) : ℂ))) := by
    simp only [Complex.real_smul]; ring
  rw [e, hpc]; ring

/-- **The Cayley form of the pairing with `e_m`**: the integral over the upper half-plane is `2π` times the `m`-th Taylor
coefficient of `bergmanDisc n φ` times `∫_0^1 s^{2m+1} (1 - s²)^{n-2} ds`. -/
theorem bergman_mode {n : ℕ} (hn : 2 ≤ n) (m : ℕ) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ {z : ℂ | 0 < z.im})
    (hint : IntegrableOn (fun z : ℂ => φ z * (starRingEnd ℂ) ((z - Complex.I) ^ m * ((z + Complex.I) ^ (n + m))⁻¹) *
      (((z.im ^ (n - 2) : ℝ)) : ℂ)) {z : ℂ | 0 < z.im}) :
    ∫ z in {z : ℂ | 0 < z.im}, φ z * (starRingEnd ℂ) ((z - Complex.I) ^ m * ((z + Complex.I) ^ (n + m))⁻¹) *
        (((z.im ^ (n - 2) : ℝ)) : ℂ) =
      (2 * π : ℂ) * discCoeff (bergmanDisc n φ) m *
        ((∫ s in Ioo (0 : ℝ) 1, s ^ (2 * m + 1) * (1 - s ^ 2) ^ (n - 2) : ℝ) : ℂ) := by
  set g : ℂ → ℂ := fun z => φ z * (starRingEnd ℂ) ((z - Complex.I) ^ m * ((z + Complex.I) ^ (n + m))⁻¹) * (((z.im ^ (n - 2) : ℝ)) : ℂ)
    with hg
  set k : ℂ → ℂ := bergmanDisc n φ with hk
  set ρ : ℝ → ℝ := fun s => (1 - s ^ 2) ^ (n - 2) with hρ
  have hρc : Continuous ρ := by simp only [hρ]; fun_prop
  have hkd : DifferentiableOn ℂ k (ball (0 : ℂ) 1) := differentiableOn_bergmanDisc n hφ
  -- integrability on the disc
  have hf' : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt cayleyInv
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ))
      (ball (0 : ℂ) 1) w :=
    fun w hw => ((hasDerivAt_cayleyInv hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hintD : IntegrableOn (fun w => (4 / ‖1 - w‖ ^ 4 : ℝ) • g (cayleyInv w)) (ball (0 : ℂ) 1) := by
    have := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_ball hf'
      cayleyInv_injOn g).1 (by rw [image_cayleyInv]; exact hint)
    refine this.congr_fun (fun w hw => ?_) measurableSet_ball
    simp only [abs_det_cayleyInv hw]
  have hint2 : IntegrableOn (fun w => k w * (starRingEnd ℂ w) ^ m * (ρ ‖w‖ : ℂ)) (ball (0 : ℂ) 1) := by
    refine hintD.congr_fun (fun w hw => ?_) measurableSet_ball
    simp only [hg, hk, hρ, bergmanDisc]
    exact pairing_cayley_mode hn hw m φ
  rw [integral_upperHalf_eq_disc g]
  rw [setIntegral_congr_fun measurableSet_ball (fun w hw => pairing_cayley_mode hn hw m φ)]
  exact integral_ball_mode hkd m hρc hint2

open Lightlike.Lorentz in
/-- **The pairing with `e_k` is a Taylor coefficient**: for `ψ ∈ A²_n` with holomorphic representative `φ`,
`⟨e_k, ψ⟩ = 2π a_k ∫_0^1 s^{2k+1} (1 - s²)^{n-2} ds` with `a_k` the `k`-th Taylor coefficient at `0` of
`w ↦ 4 (-2i)^{-n} φ(i(1+w)/(1-w)) (1-w)^{-n}`. -/
theorem inner_kClass_holo {n : ℕ} (hn : 2 ≤ n) (k : ℕ) {ψ : Hn n} {φ : ℍ → ℂ}
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hψ : ψ =ᵐ[μn n] φ) :
    ⟪kClass hn k, ψ⟫_ℂ = (2 * π : ℂ) * discCoeff (bergmanDisc n (fun w => φ (UpperHalfPlane.ofComplex w))) k *
      ((∫ s in Ioo (0 : ℝ) 1, s ^ (2 * k + 1) * (1 - s ^ 2) ^ (n - 2) : ℝ) : ℂ) := by
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (kClass hn k) ψ
  have h1 : kClass hn k =ᵐ[μn n] kVec n k := coeFn_kClass hn k
  have hae : ∀ᵐ z ∂(μn n), ⟪(kClass hn k : ℍ → ℂ) z, (ψ : ℍ → ℂ) z⟫_ℂ =
      (starRingEnd ℂ) (kVec n k z) * φ z := by
    filter_upwards [h1, hψ] with z hz1 hz2
    rw [hz1, hz2]
    simp [RCLike.inner_apply, mul_comm]
  rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
  set F : ℍ → ℂ := fun z => (starRingEnd ℂ) (kVec n k z) * φ z with hF
  have hFc : Measurable F := by
    have hc : Continuous F := by
      simp only [hF]
      exact (Complex.continuous_conj.comp (continuous_kVec n k)).mul hφ.continuous
    exact hc.measurable
  rw [integral_μn_eq_halfplane hn F]
  have hφd : DifferentiableOn ℂ (fun w => φ (UpperHalfPlane.ofComplex w)) {z : ℂ | 0 < z.im} := by
    have := (UpperHalfPlane.mdifferentiable_iff.1 hφ)
    simpa [Function.comp_def] using this
  have hcongr : ∀ w ∈ {z : ℂ | 0 < z.im},
      (((w.im ^ (n - 2) : ℝ)) : ℂ) * F (UpperHalfPlane.ofComplex w) =
        φ (UpperHalfPlane.ofComplex w) * (starRingEnd ℂ) ((w - Complex.I) ^ k * ((w + Complex.I) ^ (n + k))⁻¹) *
          (((w.im ^ (n - 2) : ℝ)) : ℂ) := by
    intro w hw
    have hw' : (0 : ℝ) < w.im := hw
    have hz : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    simp only [hF, kVec, hz, zpow_neg, zpow_natCast]
    ring
  have hint : IntegrableOn (fun w : ℂ => φ (UpperHalfPlane.ofComplex w) *
      (starRingEnd ℂ) ((w - Complex.I) ^ k * ((w + Complex.I) ^ (n + k))⁻¹) * (((w.im ^ (n - 2) : ℝ)) : ℂ))
      {z : ℂ | 0 < z.im} := by
    have hintF : Integrable F (μn n) := hi.congr hae
    have := (integrable_μn_iff_halfplane hn F hFc).1 hintF
    exact this.congr_fun (fun w hw => hcongr w hw) (measurableSet_lt measurable_const Complex.measurable_im)
  rw [setIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im) hcongr]
  exact bergman_mode hn k hφd hint

lemma integral_mode_weight_pos {n : ℕ} (_hn : 2 ≤ n) (k : ℕ) :
    0 < ∫ s in Ioo (0 : ℝ) 1, s ^ (2 * k + 1) * (1 - s ^ 2) ^ (n - 2) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) one_pos
  · exact (by fun_prop : Continuous fun s : ℝ => s ^ (2 * k + 1) * (1 - s ^ 2) ^ (n - 2)).intervalIntegrable _ _
  · have h1 : 0 < x := hx.1
    have h2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    positivity

open Lightlike.Lorentz in
/-- **Completeness of the `K`-weight vectors**: a vector of `A²_n` orthogonal to every `e_k` is zero. -/
theorem kClass_complete {n : ℕ} (hn : 2 ≤ n) {v : Hn n} (hv : v ∈ holoSubmodule n)
    (h0 : ∀ k, ⟪kClass hn k, v⟫_ℂ = 0) : v = 0 := by
  obtain ⟨φ, hφ, hvφ⟩ := hv
  have hφd : DifferentiableOn ℂ (fun w => φ (UpperHalfPlane.ofComplex w)) {z : ℂ | 0 < z.im} := by
    have := (UpperHalfPlane.mdifferentiable_iff.1 hφ)
    simpa [Function.comp_def] using this
  have hcoef : ∀ k, discCoeff (bergmanDisc n (fun w => φ (UpperHalfPlane.ofComplex w))) k = 0 := by
    intro k
    have h := inner_kClass_holo hn k hφ hvφ
    rw [h0 k] at h
    have hJ : ((∫ s in Ioo (0 : ℝ) 1, s ^ (2 * k + 1) * (1 - s ^ 2) ^ (n - 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (integral_mode_weight_pos hn k).ne'
    have h2pi : (2 * π : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this]
    rcases mul_eq_zero.1 h.symm with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' h2pi
      · exact h''
    · exact absurd h' hJ
  have hzero := eq_zero_of_discCoeff_eq_zero (differentiableOn_bergmanDisc n hφd) hcoef
  have hc : (4 * ((-2 * Complex.I) ^ n)⁻¹ : ℂ) ≠ 0 := by
    have : (-2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
    simp
  have hφ0 : ∀ z : ℂ, 0 < z.im → φ (UpperHalfPlane.ofComplex z) = 0 := by
    intro z hz
    have hz' : z ∈ cayleyInv '' ball (0 : ℂ) 1 := by rw [image_cayleyInv]; exact hz
    obtain ⟨w, hw, rfl⟩ := hz'
    have h := hzero w hw
    simp only [bergmanDisc] at h
    have h1 := one_sub_ne_zero hw
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hc
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' (inv_ne_zero (pow_ne_zero _ h1))
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hvφ] with z hz
  rw [hz]
  have := hφ0 (z : ℂ) z.im_pos
  rwa [UpperHalfPlane.ofComplex_apply] at this

lemma kFun_cayley (n k : ℕ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (cayleyInv w - Complex.I) ^ k * ((cayleyInv w + Complex.I) ^ (n + k))⁻¹ =
      w ^ k * (((2 * Complex.I) ^ n)⁻¹ * (1 - w) ^ n) := by
  have hu := one_sub_ne_zero hw
  have hzI : cayleyInv w + Complex.I = 2 * Complex.I / (1 - w) := by
    unfold cayleyInv; field_simp; ring
  have hz0 : cayleyInv w + Complex.I ≠ 0 := by
    rw [hzI]; exact div_ne_zero (by simp [Complex.I_ne_zero]) hu
  have hzm : cayleyInv w - Complex.I = w * (cayleyInv w + Complex.I) := by
    unfold cayleyInv; field_simp; ring
  rw [hzm, mul_pow, pow_add, mul_inv, hzI]
  have h2I : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  simp only [div_pow]
  have h1n : (1 - w) ^ n ≠ 0 := pow_ne_zero _ hu
  have h1k : (1 - w) ^ k ≠ 0 := pow_ne_zero _ hu
  have h2n : (2 * Complex.I) ^ n ≠ 0 := pow_ne_zero _ h2I
  have h2k : (2 * Complex.I) ^ k ≠ 0 := pow_ne_zero _ h2I
  field_simp

/-- The constant `4 (-2i)^{-n} (2i)^{-n} = 4 / 4^n`. -/
lemma const_bergman (n : ℕ) :
    (4 * ((-2 * Complex.I) ^ n)⁻¹ * ((2 * Complex.I) ^ n)⁻¹ : ℂ) = ((4 / 4 ^ n : ℝ) : ℂ) := by
  have h : (-2 * Complex.I) * (2 * Complex.I) = (4 : ℂ) := by linear_combination (-4) * Complex.I_sq
  rw [mul_assoc, ← mul_inv, ← mul_pow, h]
  push_cast
  ring

open Lightlike.Lorentz in
/-- The disc function of `e_k` is a monomial. -/
lemma bergmanDisc_kVec {n : ℕ} (k : ℕ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    bergmanDisc n (fun w => kVec n k (UpperHalfPlane.ofComplex w)) w =
      (4 * ((-2 * Complex.I) ^ n)⁻¹ * ((2 * Complex.I) ^ n)⁻¹) * w ^ k := by
  have hu := one_sub_ne_zero hw
  have hz : ((UpperHalfPlane.ofComplex (cayleyInv w) : ℍ) : ℂ) = cayleyInv w := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (cayleyInv_mem hw)]
  unfold bergmanDisc
  simp only [kVec, hz, zpow_neg, zpow_natCast]
  rw [kFun_cayley n k hw]
  have h1 : (1 - w) ^ n ≠ 0 := pow_ne_zero _ hu
  field_simp

open Lightlike.Lorentz in
/-- **The norm of `e_k`**: `‖e_k‖² = 2π (4/4ⁿ) ∫_0^1 s^{2k+1} (1-s²)^{n-2} ds`. -/
theorem norm_sq_kClass {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ‖kClass hn k‖ ^ 2 = 2 * π * (4 / 4 ^ n) * ∫ s in Ioo (0 : ℝ) 1, s ^ (2 * k + 1) * (1 - s ^ 2) ^ (n - 2) := by
  have h := inner_kClass_holo hn k (mdifferentiable_kVec n k) (coeFn_kClass hn k)
  have hc : discCoeff (bergmanDisc n (fun w => kVec n k (UpperHalfPlane.ofComplex w))) k =
      4 * ((-2 * Complex.I) ^ n)⁻¹ * ((2 * Complex.I) ^ n)⁻¹ := by
    rw [discCoeff_congr (h' := fun w => (4 * ((-2 * Complex.I) ^ n)⁻¹ * ((2 * Complex.I) ^ n)⁻¹) * w ^ k)
      (fun w hw => bergmanDisc_kVec k hw) k]
    exact discCoeff_monomial _ k
  rw [hc, const_bergman, inner_self_eq_norm_sq_to_K] at h
  have : ((‖kClass hn k‖ ^ 2 : ℝ) : ℂ) = ((2 * π * (4 / 4 ^ n) *
      ∫ s in Ioo (0 : ℝ) 1, s ^ (2 * k + 1) * (1 - s ^ 2) ^ (n - 2) : ℝ) : ℂ) := by
    push_cast at h ⊢
    linear_combination h
  exact_mod_cast this

open Lightlike.Lorentz in
theorem norm_kClass_pos {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : 0 < ‖kClass hn k‖ := by
  have h1 := norm_sq_kClass hn k
  have h2 := integral_mode_weight_pos hn k
  have h3 : 0 < ‖kClass hn k‖ ^ 2 := by rw [h1]; positivity
  exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at h3; simp at h3)

open Lightlike.Lorentz in
/-- **The unit vector `e_k / ‖e_k‖`** as an element of the Bergman space `A²_n`. -/
def kUnit {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : holoSubmodule n :=
  ⟨((‖kClass hn k‖⁻¹ : ℝ) : ℂ) • kClass hn k, Submodule.smul_mem _ _ (kClass_mem hn k)⟩

open Lightlike.Lorentz in
theorem kUnit_orthonormal {n : ℕ} (hn : 2 ≤ n) : Orthonormal ℂ (kUnit hn) := by
  rw [orthonormal_iff_ite]
  intro j k
  have hj : (‖kClass hn j‖ : ℝ) ≠ 0 := (norm_kClass_pos hn j).ne'
  have hk : (‖kClass hn k‖ : ℝ) ≠ 0 := (norm_kClass_pos hn k).ne'
  simp only [kUnit, Submodule.coe_inner, inner_smul_left, inner_smul_right]
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal]
    have : ((‖kClass hn j‖⁻¹ : ℝ) : ℂ) * ((‖kClass hn j‖⁻¹ : ℝ) : ℂ) * ((‖kClass hn j‖ : ℝ) : ℂ) ^ 2 = 1 := by
      have h : ((‖kClass hn j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hj
      push_cast
      field_simp
    linear_combination this
  · simp only [hjk, ↓reduceIte, kClass_orthogonal hn hjk, mul_zero]

open Lightlike.Lorentz in
theorem kUnit_span_top {n : ℕ} (hn : 2 ≤ n) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (kUnit hn))).topologicalClosure := by
  have h : (Submodule.span ℂ (Set.range (kUnit hn))).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    have h0 : ∀ k, ⟪kClass hn k, (x : Hn n)⟫_ℂ = 0 := by
      intro k
      have hk := hx (kUnit hn k) (Submodule.subset_span ⟨k, rfl⟩)
      have hne : (‖kClass hn k‖ : ℝ) ≠ 0 := (norm_kClass_pos hn k).ne'
      simp only [kUnit, Submodule.coe_inner, inner_smul_left, Complex.conj_ofReal] at hk
      rcases mul_eq_zero.1 hk with h | h
      · exfalso; exact hne (by simpa using h)
      · exact h
    exact Subtype.ext (kClass_complete hn x.2 h0)
  exact h.ge

open Lightlike.Lorentz in
/-- **The orthonormal Hilbert basis `e_k/‖e_k‖` of the weighted Bergman space `A²_n`.** -/
def kBasis {n : ℕ} (hn : 2 ≤ n) : HilbertBasis ℕ ℂ (holoSubmodule n) :=
  HilbertBasis.mk (kUnit_orthonormal hn) (kUnit_span_top hn)

end Lightlike.Lorentz.SL2RPlancherel

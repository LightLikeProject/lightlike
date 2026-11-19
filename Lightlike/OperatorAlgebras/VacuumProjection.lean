import Lightlike.OperatorAlgebras.ShaleNecessity
import Lightlike.OperatorAlgebras.FockContinuity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The vacuum projection of finitely many modes

Helper for the sufficiency part of Shale's criterion (`T-OP2-P7`, `Tasks/OP/T_OP2_P7.lean`). For a strongly
continuous representation `W` of the Weyl relations and a finite orthonormal family `e` of `n` modes,

`P ψ = (2π)⁻ⁿ ∫ exp (-‖f_x‖²/4) W f_x ψ dx`, `f_x = ∑ₖ (x (inl k) + i x (inr k)) • eₖ` (`vacAvg`),

is the orthogonal projection onto the vectors in which the modes `e` are in the vacuum:

* `⟪P φ, ψ⟫ = ⟪φ, P ψ⟫` (`vacAvg_symm`);
* `P (W f (P ψ)) = exp (-‖f‖²/4) P ψ` for `f` in the span of the modes (`vacAvg_W_vacAvg`), by the Weyl
  relation, a change of variables and one Gaussian integral; in particular `P (P ψ) = P ψ`;
* `P ψ = ψ` iff `⟪ψ, W f ψ⟫ = exp (-‖f‖²/4) ‖ψ‖²` for all `f` in the span of the modes
  (`inner_W_of_vacAvg_eq`, `vacAvg_eq_of_inner_W`), so the range decreases when modes are added.

`exists_fixed_of_decreasing_projections`: a decreasing net of such projections applied to a vector whose images
have norms bounded below converges to a nonzero vector fixed by all of them.
-/

open scoped InnerProductSpace
open MeasureTheory Complex Filter Topology

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {m : Type*} [Fintype m]

/-! ### The mode vector is linear and continuous in the coordinates -/

lemma modeVec_add (e : m → h) (x y : m ⊕ m → ℝ) : modeVec e (x + y) = modeVec e x + modeVec e y := by
  simp only [modeVec_eq_sum, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma modeVec_neg (e : m → h) (x : m ⊕ m → ℝ) : modeVec e (-x) = -modeVec e x := by
  simp only [modeVec_eq_sum, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

lemma modeVec_sub (e : m → h) (x y : m ⊕ m → ℝ) : modeVec e (x - y) = modeVec e x - modeVec e y := by
  rw [sub_eq_add_neg, modeVec_add, modeVec_neg, sub_eq_add_neg]

lemma modeVec_zero (e : m → h) : modeVec e 0 = 0 := by
  simp only [modeVec_eq_sum, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

@[fun_prop]
lemma continuous_modeVec (e : m → h) : Continuous (modeVec e) := by
  show Continuous fun x : m ⊕ m → ℝ => ∑ k, ((x (Sum.inl k) : ℂ) + I * (x (Sum.inr k) : ℂ)) • e k
  exact continuous_finset_sum _ fun k _ =>
    ((Complex.continuous_ofReal.comp (continuous_apply (Sum.inl k))).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply (Sum.inr k))))).smul
      continuous_const

@[fun_prop]
lemma continuous_gaussE : Continuous (gaussE : h → ℝ) := by
  show Continuous fun f : h => Real.exp (-(‖f‖ ^ 2 / 4))
  exact Real.continuous_exp.comp ((continuous_norm.pow 2).div_const 4).neg

lemma gaussE_zero : gaussE (0 : h) = 1 := by simp [gaussE]

lemma inner_modeVec_self {e : m → h} (he : Orthonormal ℂ e) (a : m ⊕ m → ℝ) (r : h) :
    ∑ k, ⟪r, e k⟫_ℂ * ⟪e k, modeVec e a⟫_ℂ = ⟪r, modeVec e a⟫_ℂ := by
  rw [inner_modeVec_right e a r]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_modeVec_right e a (e k), mul_comm]
  congr 1
  rw [Finset.sum_eq_single k]
  · have h1 : ⟪e k, e k⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he.1 k]; simp
    rw [h1, mul_one]
  · intro j _ hj
    rw [he.2 (Ne.symm hj), mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

/-! ### Two identities between Gaussian weights and Weyl phases -/

lemma gauss_shift_pointwise (p q r : h) :
    (gaussE p : ℂ) * ((gaussE (r - p - q) : ℂ) *
      (cexp (-(I * ((symp h q (r - p - q) / 2 : ℝ) : ℂ))) *
        cexp (-(I * ((symp h p (r - p) / 2 : ℝ) : ℂ))))) =
      ((gaussE (r - q) : ℂ) * cexp (-(I * ((symp h q r / 2 : ℝ) : ℂ)))) *
        cexp (-(1 / 2 : ℂ) * ((‖p‖ ^ 2 : ℝ) : ℂ) + (⟪r, p⟫_ℂ / 2 - ⟪p, q⟫_ℂ / 2)) := by
  have hn : ‖r - p - q‖ ^ 2 = ‖r - q‖ ^ 2 - 2 * ((⟪r, p⟫_ℂ).re - (⟪p, q⟫_ℂ).re) + ‖p‖ ^ 2 := by
    have h1 := norm_sub_sq (𝕜 := ℂ) (r - q) p
    have h2 : r - q - p = r - p - q := by abel
    have h3 : RCLike.re ⟪r - q, p⟫_ℂ = (⟪r, p⟫_ℂ).re - (⟪p, q⟫_ℂ).re := by
      rw [inner_sub_left, map_sub]
      have : RCLike.re ⟪q, p⟫_ℂ = RCLike.re ⟪p, q⟫_ℂ := inner_re_symm (𝕜 := ℂ) q p
      rw [this]; rfl
    rw [h2, h3] at h1
    exact h1
  have hs1 : symp h q (r - p - q) = (⟪q, r⟫_ℂ).im + (⟪p, q⟫_ℂ).im := by
    unfold symp
    rw [inner_sub_right, inner_sub_right, Complex.sub_im, Complex.sub_im]
    have h1 : (⟪q, p⟫_ℂ).im = -(⟪p, q⟫_ℂ).im := inner_im_symm (𝕜 := ℂ) q p
    have h2 : (⟪q, q⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) q
    rw [h1, h2]; ring
  have hs2 : symp h p (r - p) = -(⟪r, p⟫_ℂ).im := by
    unfold symp
    rw [inner_sub_right, Complex.sub_im]
    have h1 : (⟪p, r⟫_ℂ).im = -(⟪r, p⟫_ℂ).im := inner_im_symm (𝕜 := ℂ) p r
    have h2 : (⟪p, p⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) p
    rw [h1, h2]; ring
  have hs3 : symp h q r = (⟪q, r⟫_ℂ).im := rfl
  unfold gaussE
  rw [hn, hs1, hs2, hs3]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (1 / 2 : ℂ) * Complex.re_add_im ⟪r, p⟫_ℂ - (1 / 2 : ℂ) * Complex.re_add_im ⟪p, q⟫_ℂ

lemma gauss_shift_const (q r : h) :
    ((gaussE (r - q) : ℂ) * cexp (-(I * ((symp h q r / 2 : ℝ) : ℂ)))) * cexp (-⟪r, q⟫_ℂ / 2) =
      (gaussE q : ℂ) * gaussE r := by
  have hn : ‖r - q‖ ^ 2 = ‖r‖ ^ 2 - 2 * (⟪r, q⟫_ℂ).re + ‖q‖ ^ 2 := norm_sub_sq (𝕜 := ℂ) r q
  have hs : symp h q r = -(⟪r, q⟫_ℂ).im := inner_im_symm (𝕜 := ℂ) q r
  unfold gaussE
  rw [hn, hs]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (1 / 2 : ℂ) * Complex.re_add_im ⟪r, q⟫_ℂ

/-- The kernel that appears when two Gaussian averages are composed around `W f_a`. -/
noncomputable def shiftKernel (e : m → h) (a x u : m ⊕ m → ℝ) : ℂ :=
  (gaussE (modeVec e u - modeVec e x - modeVec e a) : ℂ) *
    (cexp (-(I * ((symp h (modeVec e a) (modeVec e u - modeVec e x - modeVec e a) / 2 : ℝ) : ℂ))) *
      cexp (-(I * ((symp h (modeVec e x) (modeVec e u - modeVec e x) / 2 : ℝ) : ℂ))))

lemma norm_cexp_neg_I_mul (r : ℝ) : ‖cexp (-(I * (r : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma norm_shiftKernel (e : m → h) (a x u : m ⊕ m → ℝ) :
    ‖shiftKernel e a x u‖ = gaussE (modeVec e (u - x - a)) := by
  unfold shiftKernel
  rw [norm_mul, norm_mul, norm_cexp_neg_I_mul, norm_cexp_neg_I_mul, mul_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (gaussE_pos _).le, modeVec_sub, modeVec_sub]

lemma continuous_symp : Continuous fun p : h × h => symp h p.1 p.2 := by
  unfold symp
  exact Complex.continuous_im.comp (continuous_fst.inner continuous_snd)

lemma continuous_shiftKernel (e : m → h) (a : m ⊕ m → ℝ) :
    Continuous fun p : (m ⊕ m → ℝ) × (m ⊕ m → ℝ) => shiftKernel e a p.1 p.2 := by
  have hu : Continuous fun p : (m ⊕ m → ℝ) × (m ⊕ m → ℝ) => modeVec e p.2 :=
    (continuous_modeVec e).comp continuous_snd
  have hx : Continuous fun p : (m ⊕ m → ℝ) × (m ⊕ m → ℝ) => modeVec e p.1 :=
    (continuous_modeVec e).comp continuous_fst
  have hph : ∀ {F G : (m ⊕ m → ℝ) × (m ⊕ m → ℝ) → h}, Continuous F → Continuous G →
      Continuous fun p => cexp (-(I * ((symp h (F p) (G p) / 2 : ℝ) : ℂ))) := fun hF hG =>
    Complex.continuous_exp.comp ((continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_symp.comp (hF.prodMk hG)).div_const 2))).neg)
  unfold shiftKernel
  exact (Complex.continuous_ofReal.comp (continuous_gaussE.comp ((hu.sub hx).sub continuous_const))).mul
    ((hph continuous_const ((hu.sub hx).sub continuous_const)).mul (hph hx (hu.sub hx)))

/-- **The Gaussian integral of the composition kernel**: `∫ e(f_x) k_a(x, u) dx = (2π)ⁿ e(f_a) e(f_u)`. -/
lemma integral_shiftKernel {e : m → h} (he : Orthonormal ℂ e) (a u : m ⊕ m → ℝ) :
    ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * shiftKernel e a x u =
      (gaussZ m : ℂ) * ((gaussE (modeVec e a) : ℂ) * gaussE (modeVec e u)) := by
  have hpt : ∀ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * shiftKernel e a x u =
      ((gaussE (modeVec e u - modeVec e a) : ℂ) *
        cexp (-(I * ((symp h (modeVec e a) (modeVec e u) / 2 : ℝ) : ℂ)))) *
        cexp (-(1 / 2 : ℂ) * ∑ i, (x i : ℂ) ^ 2 +
          ∑ i, modeCoef e (modeVec e u) (modeVec e a) i * x i) := by
    intro x
    unfold shiftKernel
    rw [gauss_shift_pointwise, norm_modeVec_sq he, sum_modeCoef_mul]
    push_cast
    rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_cexp_modeCoef, inner_modeVec_self he]
  rw [← gauss_shift_const (modeVec e a) (modeVec e u)]
  ring

/-! ### The Gaussian average as an operator -/

omit [CompleteSpace K] in
lemma CCRRep.inner_W_neg_left (R : CCRRep h K) (f : h) (φ ψ : K) :
    ⟪R.W (-f) φ, ψ⟫_ℂ = ⟪φ, R.W f ψ⟫_ℂ := by
  rw [← (R.W f).inner_map_map (R.W (-f) φ) ψ, R.W_W_neg]

/-- **The vacuum projection of the modes `e`**: the normalised Gaussian average of the Weyl unitaries over the
real span of the modes. -/
noncomputable def vacAvg (R : CCRRep h K) (e : m → h) (ψ : K) : K :=
  ((gaussZ m : ℂ))⁻¹ • ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) • R.W (modeVec e x) ψ

variable (R : CCRRep h K) (hc : ∀ ψ, Continuous fun f : h => R.W f ψ) {e : m → h} (he : Orthonormal ℂ e)

include hc he in
lemma integrable_vacAvg (ψ : K) :
    Integrable fun x : m ⊕ m → ℝ => (gaussE (modeVec e x) : ℂ) • R.W (modeVec e x) ψ := by
  refine Integrable.mono' ((integrable_gaussE_modeVec he).mul_const ‖ψ‖) ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((Complex.continuous_ofReal.comp (continuous_gaussE.comp (continuous_modeVec e))).smul
      ((hc ψ).comp (continuous_modeVec e))).aestronglyMeasurable
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (gaussE_pos _).le, LinearIsometryEquiv.norm_map]

include hc he in
lemma inner_vacAvg (φ ψ : K) :
    ⟪φ, vacAvg R e ψ⟫_ℂ =
      ((gaussZ m : ℂ))⁻¹ * ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * ⟪φ, R.W (modeVec e x) ψ⟫_ℂ := by
  unfold vacAvg
  rw [inner_smul_right, ← integral_inner (integrable_vacAvg R hc he ψ)]
  simp only [inner_smul_right]

include hc he in
/-- The vacuum projection is symmetric. -/
lemma vacAvg_symm (φ ψ : K) : ⟪vacAvg R e φ, ψ⟫_ℂ = ⟪φ, vacAvg R e ψ⟫_ℂ := by
  rw [← inner_conj_symm, inner_vacAvg R hc he, inner_vacAvg R hc he, map_mul, map_inv₀, conj_ofReal,
    ← integral_conj]
  congr 1
  rw [← integral_neg_eq_self
    (fun x : m ⊕ m → ℝ => (gaussE (modeVec e x) : ℂ) * ⟪φ, R.W (modeVec e x) ψ⟫_ℂ)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul, conj_ofReal, inner_conj_symm, modeVec_neg, gaussE_neg']
  rw [← R.inner_W_neg_left (-(modeVec e x)), neg_neg]

include hc he in
lemma vacAvg_add (a b : K) : vacAvg R e (a + b) = vacAvg R e a + vacAvg R e b := by
  unfold vacAvg
  simp only [map_add, smul_add]
  rw [integral_add (integrable_vacAvg R hc he a) (integrable_vacAvg R hc he b), smul_add]

lemma vacAvg_smul (c : ℂ) (a : K) : vacAvg R e (c • a) = c • vacAvg R e a := by
  unfold vacAvg
  simp only [map_smul]
  simp_rw [smul_comm _ c]
  rw [integral_smul, smul_comm]

include hc he in
lemma vacAvg_sub (a b : K) : vacAvg R e (a - b) = vacAvg R e a - vacAvg R e b := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ b, vacAvg_add R hc he, vacAvg_smul, neg_one_smul, ← sub_eq_add_neg]

include hc he in
/-- **`P W f P = exp (-‖f‖²/4) P`** for `f` in the span of the modes. -/
theorem vacAvg_W_vacAvg (a : m ⊕ m → ℝ) (ψ : K) :
    vacAvg R e (R.W (modeVec e a) (vacAvg R e ψ)) = (gaussE (modeVec e a) : ℂ) • vacAvg R e ψ := by
  refine ext_inner_left ℂ fun φ => ?_
  rw [inner_smul_right, inner_vacAvg R hc he φ ψ, inner_vacAvg R hc he]
  -- the inner Gaussian average, moved to the variable `u = x + a + y`
  have hinner : ∀ x : m ⊕ m → ℝ, ⟪φ, R.W (modeVec e x) (R.W (modeVec e a) (vacAvg R e ψ))⟫_ℂ =
      ((gaussZ m : ℂ))⁻¹ * ∫ u : m ⊕ m → ℝ, shiftKernel e a x u * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ := by
    intro x
    rw [← R.inner_W_neg_left (modeVec e x), ← R.inner_W_neg_left (modeVec e a), inner_vacAvg R hc he]
    congr 1
    have h1 := integral_sub_right_eq_self (μ := (volume : Measure (m ⊕ m → ℝ)))
      (fun y : m ⊕ m → ℝ => (gaussE (modeVec e y) : ℂ) *
      ⟪R.W (-(modeVec e a)) (R.W (-(modeVec e x)) φ), R.W (modeVec e y) ψ⟫_ℂ) (x + a)
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hy : modeVec e (u - (x + a)) = modeVec e u - modeVec e x - modeVec e a := by
      rw [modeVec_sub, modeVec_add, sub_add_eq_sub_sub]
    have e1 : modeVec e a + (modeVec e u - modeVec e x - modeVec e a) = modeVec e u - modeVec e x := by
      abel
    have e2 : modeVec e x + (modeVec e u - modeVec e x) = modeVec e u := by abel
    simp only [hy]
    rw [R.inner_W_neg_left, R.inner_W_neg_left, R.weyl (modeVec e a), e1, map_smul,
      R.weyl (modeVec e x), e2, inner_smul_right, inner_smul_right]
    unfold shiftKernel
    ring
  simp_rw [hinner]
  have hL : ∀ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * (((gaussZ m : ℂ))⁻¹ *
      ∫ u : m ⊕ m → ℝ, shiftKernel e a x u * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ) =
      ((gaussZ m : ℂ))⁻¹ * ∫ u : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
        (shiftKernel e a x u * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ) := by
    intro x
    rw [integral_const_mul]
    ring
  simp_rw [hL]
  rw [integral_const_mul]
  -- Fubini
  have hInt : Integrable (Function.uncurry fun (x u : m ⊕ m → ℝ) => (gaussE (modeVec e x) : ℂ) *
      (shiftKernel e a x u * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ)) (volume.prod volume) := by
    have hb0 : Integrable (fun z : (m ⊕ m → ℝ) × (m ⊕ m → ℝ) =>
        (gaussE (modeVec e z.1) * (‖φ‖ * ‖ψ‖)) * gaussE (modeVec e (z.2 - a))) (volume.prod volume) :=
      ((integrable_gaussE_modeVec he).mul_const _).mul_prod
        ((integrable_gaussE_modeVec he).comp_sub_right a)
    have hb := (measurePreserving_prod_sub (volume : Measure (m ⊕ m → ℝ))
      (volume : Measure (m ⊕ m → ℝ))).integrable_comp_of_integrable hb0
    refine Integrable.mono' hb ?_ (Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact (Complex.continuous_ofReal.comp (continuous_gaussE.comp
        ((continuous_modeVec e).comp continuous_fst))).mul
        ((continuous_shiftKernel e a).mul
          (continuous_const.inner ((hc ψ).comp ((continuous_modeVec e).comp continuous_snd))))
    · obtain ⟨x, u⟩ := z
      simp only [Function.uncurry_apply_pair, Function.comp_apply]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussE_pos _).le, norm_shiftKernel]
      have hin : ‖⟪φ, R.W (modeVec e u) ψ⟫_ℂ‖ ≤ ‖φ‖ * ‖ψ‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) φ (R.W (modeVec e u) ψ)
        rwa [LinearIsometryEquiv.norm_map] at this
      have h1 := mul_le_mul_of_nonneg_left hin (gaussE_pos (modeVec e (u - x - a))).le
      have h2 := mul_le_mul_of_nonneg_left h1 (gaussE_pos (modeVec e x)).le
      calc gaussE (modeVec e x) * (gaussE (modeVec e (u - x - a)) * ‖⟪φ, R.W (modeVec e u) ψ⟫_ℂ‖)
          ≤ gaussE (modeVec e x) * (gaussE (modeVec e (u - x - a)) * (‖φ‖ * ‖ψ‖)) := h2
        _ = gaussE (modeVec e x) * (‖φ‖ * ‖ψ‖) * gaussE (modeVec e (u - x - a)) := by ring
  rw [integral_integral_swap hInt]
  have hx : ∀ u : m ⊕ m → ℝ, ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
      (shiftKernel e a x u * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ) =
      ((gaussZ m : ℂ) * (gaussE (modeVec e a) : ℂ)) *
        ((gaussE (modeVec e u) : ℂ) * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ) := by
    intro u
    have h1 : ∀ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
        (shiftKernel e a x u * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ) =
        ((gaussE (modeVec e x) : ℂ) * shiftKernel e a x u) * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ := fun x => by
      ring
    simp_rw [h1]
    rw [integral_mul_const, integral_shiftKernel he]
    ring
  simp_rw [hx]
  rw [integral_const_mul]
  have hZ : (gaussZ m : ℂ) ≠ 0 := by exact_mod_cast (gaussZ_pos (m := m)).ne'
  generalize (∫ u : m ⊕ m → ℝ, (gaussE (modeVec e u) : ℂ) * ⟪φ, R.W (modeVec e u) ψ⟫_ℂ) = J
  have hZZ : ((gaussZ m : ℂ))⁻¹ * (gaussZ m : ℂ) = 1 := inv_mul_cancel₀ hZ
  linear_combination (((gaussZ m : ℂ))⁻¹ * (gaussE (modeVec e a) : ℂ) * J) * hZZ

include hc he in
/-- The vacuum projection is idempotent. -/
lemma vacAvg_idem (ψ : K) : vacAvg R e (vacAvg R e ψ) = vacAvg R e ψ := by
  have h1 := vacAvg_W_vacAvg R hc he 0 ψ
  rwa [modeVec_zero, R.W_zero_apply, gaussE_zero, Complex.ofReal_one, one_smul] at h1

include hc he in
lemma inner_vacAvg_vacAvg (φ ψ : K) : ⟪vacAvg R e φ, vacAvg R e ψ⟫_ℂ = ⟪φ, vacAvg R e ψ⟫_ℂ := by
  rw [vacAvg_symm R hc he, vacAvg_idem R hc he]

include hc he in
/-- The vacuum projection is a contraction. -/
lemma norm_vacAvg_le (ψ : K) : ‖vacAvg R e ψ‖ ≤ ‖ψ‖ := by
  have h1 : ‖vacAvg R e ψ‖ ^ 2 ≤ ‖ψ‖ * ‖vacAvg R e ψ‖ := by
    have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (vacAvg R e ψ)
    rw [inner_vacAvg_vacAvg R hc he] at h2
    rw [← h2]
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  by_cases h0 : ‖vacAvg R e ψ‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖vacAvg R e ψ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [sq] at h1
    exact le_of_mul_le_mul_right h1 hpos

include hc he in
/-- A vector in the range of the vacuum projection has the vacuum expectation on the modes. -/
lemma inner_W_of_vacAvg_eq {ψ : K} (hψ : vacAvg R e ψ = ψ) (a : m ⊕ m → ℝ) :
    ⟪ψ, R.W (modeVec e a) ψ⟫_ℂ = (gaussE (modeVec e a) : ℂ) * ⟪ψ, ψ⟫_ℂ := by
  calc ⟪ψ, R.W (modeVec e a) ψ⟫_ℂ
      = ⟪vacAvg R e ψ, R.W (modeVec e a) (vacAvg R e ψ)⟫_ℂ := by rw [hψ]
    _ = ⟪ψ, vacAvg R e (R.W (modeVec e a) (vacAvg R e ψ))⟫_ℂ := vacAvg_symm R hc he _ _
    _ = (gaussE (modeVec e a) : ℂ) * ⟪ψ, ψ⟫_ℂ := by
        rw [vacAvg_W_vacAvg R hc he, inner_smul_right, hψ]

include hc he in
/-- A vector with the vacuum expectation on the modes is fixed by the vacuum projection. -/
lemma vacAvg_eq_of_inner_W {ψ : K}
    (hψ : ∀ a : m ⊕ m → ℝ, ⟪ψ, R.W (modeVec e a) ψ⟫_ℂ = (gaussE (modeVec e a) : ℂ) * ⟪ψ, ψ⟫_ℂ) :
    vacAvg R e ψ = ψ := by
  have hZ : (gaussZ m : ℂ) ≠ 0 := by exact_mod_cast (gaussZ_pos (m := m)).ne'
  have h1 : ⟪ψ, vacAvg R e ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
    rw [inner_vacAvg R hc he]
    have h2 : ∀ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) * ⟪ψ, R.W (modeVec e x) ψ⟫_ℂ =
        ((gaussE (modeVec e x) : ℂ) * gaussE (modeVec e x)) * ⟪ψ, ψ⟫_ℂ := fun x => by
      rw [hψ x]; ring
    simp_rw [h2]
    rw [integral_mul_const, integral_gaussE_sq he, ← mul_assoc, inv_mul_cancel₀ hZ, one_mul]
  have h3 : ⟪ψ - vacAvg R e ψ, ψ - vacAvg R e ψ⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_vacAvg_vacAvg R hc he,
      vacAvg_symm R hc he ψ ψ, h1]
    ring
  exact (sub_eq_zero.1 (inner_self_eq_zero.1 h3)).symm

include hc he in
/-- The range of the vacuum projection decreases when modes are added. -/
lemma vacAvg_eq_of_subfamily {m' : Type*} [Fintype m'] {e' : m' → h} (he' : Orthonormal ℂ e')
    (hsub : ∀ a : m ⊕ m → ℝ, ∃ a' : m' ⊕ m' → ℝ, modeVec e a = modeVec e' a') {ψ : K}
    (hψ : vacAvg R e' ψ = ψ) : vacAvg R e ψ = ψ := by
  refine vacAvg_eq_of_inner_W R hc he fun a => ?_
  obtain ⟨a', ha'⟩ := hsub a
  rw [ha']
  exact inner_W_of_vacAvg_eq R hc he' hψ a'

/-! ### The limit of a decreasing net of projections -/

/-- A net `P s` of symmetric idempotent contractions whose ranges decrease, applied to a vector `Ω` with
`c ≤ ‖P s Ω‖²` for all `s`, converges to a vector fixed by every `P s`, of squared norm at least `c`. -/
theorem exists_fixed_of_decreasing_projections {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    (P : ι → K → K) (hsymm : ∀ s φ ψ, ⟪P s φ, ψ⟫_ℂ = ⟪φ, P s ψ⟫_ℂ)
    (hidem : ∀ s ψ, P s (P s ψ) = P s ψ) (hsub : ∀ s φ ψ, P s (φ - ψ) = P s φ - P s ψ)
    (hnorm : ∀ s ψ, ‖P s ψ‖ ≤ ‖ψ‖) (hmono : ∀ s t, s ≤ t → ∀ ψ, P t ψ = ψ → P s ψ = ψ)
    (Ω : K) (c : ℝ) (hlow : ∀ s, c ≤ ‖P s Ω‖ ^ 2) :
    ∃ Ω' : K, c ≤ ‖Ω'‖ ^ 2 ∧ ∀ s, P s Ω' = Ω' := by
  have key : ∀ s t, s ≤ t → ∀ ψ, P t (P s ψ) = P t ψ := by
    intro s t hst ψ
    refine ext_inner_left ℂ fun φ => ?_
    rw [← hsymm t, ← hsymm s, hmono s t hst _ (hidem t φ), hsymm t]
  have hdist : ∀ s t, s ≤ t → ‖P s Ω - P t Ω‖ ^ 2 = ‖P s Ω‖ ^ 2 - ‖P t Ω‖ ^ 2 := by
    intro s t hst
    have h1 := norm_sub_sq (𝕜 := ℂ) (P s Ω) (P t Ω)
    have h2 : ⟪P s Ω, P t Ω⟫_ℂ = ⟪P t Ω, P t Ω⟫_ℂ := by
      calc ⟪P s Ω, P t Ω⟫_ℂ = ⟪P s Ω, P t (P t Ω)⟫_ℂ := by rw [hidem]
        _ = ⟪P t (P s Ω), P t Ω⟫_ℂ := (hsymm t _ _).symm
        _ = ⟪P t Ω, P t Ω⟫_ℂ := by rw [key s t hst]
    have h3 : RCLike.re ⟪P s Ω, P t Ω⟫_ℂ = ‖P t Ω‖ ^ 2 := by
      rw [h2]; exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [h3] at h1
    linarith
  have hbdd : BddBelow (Set.range fun s => ‖P s Ω‖ ^ 2) :=
    ⟨0, by rintro _ ⟨s, rfl⟩; positivity⟩
  have hC : CauchySeq fun s => P s Ω := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlt : (⨅ s, ‖P s Ω‖ ^ 2) < (⨅ s, ‖P s Ω‖ ^ 2) + ε ^ 2 := by
      have : 0 < ε ^ 2 := by positivity
      linarith
    obtain ⟨N, hN⟩ := exists_lt_of_ciInf_lt hlt
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hdist N n hn
    have h2 : (⨅ s, ‖P s Ω‖ ^ 2) ≤ ‖P n Ω‖ ^ 2 := ciInf_le hbdd n
    have h3 : ‖P N Ω - P n Ω‖ ^ 2 < ε ^ 2 := by linarith
    rw [dist_comm, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨Ω', hΩ'⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨Ω', ge_of_tendsto' (hΩ'.norm.pow 2) hlow, fun s => ?_⟩
  have hlim : Tendsto (fun t => P s (P t Ω)) atTop (𝓝 (P s Ω')) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun t => ‖P t Ω - Ω'‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hΩ'
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) h0
    rw [← hsub]
    exact hnorm s _
  have heq : (fun t => P s (P t Ω)) =ᶠ[atTop] fun t => P t Ω :=
    (eventually_ge_atTop s).mono fun t ht => hmono s t ht _ (hidem t Ω)
  exact tendsto_nhds_unique hlim (hΩ'.congr' heq.symm)

end Lightlike.OperatorAlgebras

module

public import Lightlike.Oscillatory.PhaseReduction

/-!
# Non-stationary phase and localisation

Integrals `∫ u e^{iτF}` with a smooth, compactly supported amplitude `u` and a smooth phase
`F : ℝⁿ → ℂ` with `Im F ≥ 0` on the support of `u`, following Hörmander, *The Analysis of Linear
Partial Differential Operators I*, Theorem 7.7.1 and the first step of the proof of
Theorem 7.7.5.

Where `dF ≠ 0`, the vector field `cₗ = conj(∂ₗF) / ∑ₘ |∂ₘF|²` satisfies `∑ₗ cₗ ∂ₗF = 1`
(`exists_coeff_nonstationary`), and `k` integrations by parts against it give `O(τ^{-k})`
(`exists_bound_nonstationary`). Where `Im F > 0`, the integrand decays like `e^{-cτ}`
(`exists_bound_exp`), which is `O(τ^{-k})` for every `k` (`exp_neg_le_inv_pow`). A smooth partition
of unity (`exists_smooth_partition`, from Mathlib's `SmoothPartitionOfUnity`) joins the two.

* `nonstationary_phase`: if `dF ≠ 0` on the support of `u`, then `∫ u e^{iτF} = O(τ^{-k})` for
  every `k`.
* `exists_bound_noncritical`: the same when every point of the support has `Im F > 0` or `dF ≠ 0`.
* `integral_localise`: if the critical points (`Im F = 0`, `dF = 0`) on the support of `a` lie in a
  finite set `K`, then `∫ a e^{iτF}` equals `∑_{x₀ ∈ K} ∫ χ_{x₀} a e^{iτF}` up to `O(τ^{-k})` for
  every `k`, with smooth cutoffs `χ_{x₀}` supported in arbitrarily small balls around `x₀` and equal
  to `1` at `x₀`.
-/

@[expose] public section

namespace Lightlike.Oscillatory

open MeasureTheory Complex Matrix Finset Set Filter
open scoped Real ContDiff Topology Manifold

variable {n : ℕ} {K : Set (Fin n → ℝ)}

/-- A partial derivative of a function that vanishes off a closed set `K` vanishes off `K`. -/
theorem coordDeriv_eq_zero_of_notMem (hK : IsClosed K) {f : (Fin n → ℝ) → ℂ}
    (hf : ∀ x ∉ K, f x = 0) (l : Fin n) {x : Fin n → ℝ} (hx : x ∉ K) :
    coordDeriv f l x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => 0 :=
    Filter.mem_of_superset (hK.isOpen_compl.mem_nhds hx) fun y hy => hf y hy
  show fderiv ℝ f x (Pi.single l 1) = 0
  rw [hev.fderiv_eq]
  simp

/-- One integration by parts away from critical points: if `∑ₗ cₗ ∂ₗF = 1` on `K` and `w`
vanishes off `K`, then `∫ w e^{iτF} = -(iτ)⁻¹ ∑ₗ ∫ ∂ₗ(cₗ w) e^{iτF}`. -/
theorem integral_ibp_one {F : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (hK : IsCompact K)
    {w : (Fin n → ℝ) → ℂ} (hw : ContDiff ℝ ∞ w) (hwK : ∀ x ∉ K, w x = 0)
    {c : Fin n → (Fin n → ℝ) → ℂ} (hc : ∀ l, ContDiff ℝ ∞ (c l))
    (hid : ∀ x ∈ K, ∑ l, c l x * coordDeriv F l x = 1) {τ : ℝ} (hτ : τ ≠ 0) :
    ∫ x, w x * cexp (I * τ * F x) =
      -(1 / (I * τ)) * ∑ l, ∫ x, coordDeriv (fun y => c l y * w y) l x * cexp (I * τ * F x) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hEc : ContDiff ℝ ∞ (fun y => cexp (I * τ * F y)) := (contDiff_const.mul hF).cexp
  have hEd := hasFDerivAt_cexp_phase hFd τ
  have hIτ : I * (τ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hτ)
  have hh : ∀ l, ContDiff ℝ ∞ (fun y => c l y * w y) := fun l => (hc l).mul hw
  have hhs : ∀ l, HasCompactSupport (fun y => c l y * w y) := fun l =>
    HasCompactSupport.intro hK fun x hx => by rw [hwK x hx, mul_zero]
  have hpt : ∀ x, w x * cexp (I * τ * F x) =
      ∑ l, (1 / (I * τ)) * ((c l x * w x) *
        fderiv ℝ (fun y => cexp (I * τ * F y)) x (Pi.single l 1)) := by
    intro x
    rw [(hEd x).fderiv]
    simp only [_root_.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ K
    · have h1 : ∑ l, (1 / (I * τ)) * ((c l x * w x) *
          (cexp (I * τ * F x) * ((I * τ) * fderiv ℝ F x (Pi.single l 1)))) =
          w x * cexp (I * τ * F x) * ∑ l, c l x * coordDeriv F l x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold coordDeriv
        field_simp [ofReal_ne_zero.mpr hτ]
      rw [h1, hid x hx, mul_one]
    · simp [hwK x hx]
  have hint : ∀ l, Integrable (fun x => (c l x * w x) *
      fderiv ℝ (fun y => cexp (I * τ * F y)) x (Pi.single l 1)) := fun l =>
    ((hh l).continuous.mul ((hEc.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport (hhs l).mul_right
  rw [show (fun x => w x * cexp (I * τ * F x)) = _ from funext hpt,
    integral_finsetSum _ fun l _ => (hint l).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y => c l y * w y) (g := fun y => cexp (I * τ * F y)) (v := Pi.single l 1)
    ((((hh l).continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hEc.continuous |>.integrable_of_hasCompactSupport
        ((hhs l).fderiv_apply (𝕜 := ℝ) _).mul_right)
    (hint l)
    (((hh l).continuous.mul hEc.continuous).integrable_of_hasCompactSupport (hhs l).mul_right)
    (fun x _ => ((hh l).differentiable (by simp)) x)
    (fun x _ => (hEc.differentiable (by simp)) x)
  rw [hibp]
  unfold coordDeriv
  ring

/-- **Non-stationary phase, quantitative** (Hörmander, *ALPDO I*, Theorem 7.7.1): if
`Im F ≥ 0` on the compact set `K` and smooth coefficients satisfy `∑ₗ cₗ ∂ₗF = 1` on `K`, then
every smooth `w` that vanishes off `K` gives `|∫ w e^{iτF}| ≤ C τ^{-k}` for `τ ≥ 1`, for every
`k`. -/
theorem exists_bound_nonstationary (hK : IsCompact K) {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFim : ∀ x ∈ K, 0 ≤ (F x).im) {c : Fin n → (Fin n → ℝ) → ℂ}
    (hc : ∀ l, ContDiff ℝ ∞ (c l)) (hid : ∀ x ∈ K, ∑ l, c l x * coordDeriv F l x = 1) :
    ∀ (k : ℕ) {w : (Fin n → ℝ) → ℂ}, ContDiff ℝ ∞ w → (∀ x ∉ K, w x = 0) →
      ∃ C, ∀ τ : ℝ, 1 ≤ τ → ‖∫ x, w x * cexp (I * τ * F x)‖ ≤ C * (τ ^ k)⁻¹
  | 0, w, hw, hwK => by
    obtain ⟨C, hC⟩ := exists_bound_vanish_zero (v := fun _ => w) (F := fun _ => F) hK
      ⟨hw.comp contDiff_snd, fun _ x hx => hwK x hx⟩ fun _ _ x hx => hFim x hx
    exact ⟨C, fun τ hτ => by simpa using hC 0 ⟨le_rfl, zero_le_one⟩ τ (by linarith)⟩
  | k + 1, w, hw, hwK => by
    have hd : ∀ l, ContDiff ℝ ∞ (coordDeriv (fun y => c l y * w y) l) := fun l =>
      contDiff_coordDeriv ((hc l).mul hw) l
    have hdK : ∀ l, ∀ x ∉ K, coordDeriv (fun y => c l y * w y) l x = 0 := fun l x hx =>
      coordDeriv_eq_zero_of_notMem hK.isClosed (fun y hy => by rw [hwK y hy, mul_zero]) l hx
    have hB := fun l => exists_bound_nonstationary hK hF hFim hc hid k (hd l) (hdK l)
    choose C hC using hB
    refine ⟨∑ l, C l, fun τ hτ => ?_⟩
    have hτ0 : 0 < τ := by linarith
    rw [integral_ibp_one hF hK hw hwK hc hid hτ0.ne', norm_mul, norm_neg_one_div_I_mul hτ0]
    calc τ⁻¹ * ‖∑ l, ∫ x, coordDeriv (fun y => c l y * w y) l x * cexp (I * τ * F x)‖
        ≤ τ⁻¹ * ∑ l, C l * (τ ^ k)⁻¹ := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hC l τ hτ)
      _ = (∑ l, C l) * (τ ^ (k + 1))⁻¹ := by
          rw [← Finset.sum_mul, pow_succ, mul_inv]; ring

/-- A continuous linear map on `ℝⁿ` that vanishes on the standard basis vectors is zero. -/
theorem clm_eq_zero_of_basis {L : (Fin n → ℝ) →L[ℝ] ℂ} (h : ∀ l, L (Pi.single l 1) = 0) :
    L = 0 := by
  ext x
  rw [show x = ∑ l, x l • Pi.single l (1 : ℝ) from by
    ext i; simp [Pi.single_apply]]
  simp [map_sum, map_smul, h]

/-- Coefficients for non-stationary phase: if `dF ≠ 0` on the compact set `K`, there are smooth
`cₗ` with `∑ₗ cₗ ∂ₗF = 1` on `K`, namely `cₗ = conj(∂ₗF)/|∇F|²` near `K`, with the denominator
smoothly kept away from zero elsewhere. -/
theorem exists_coeff_nonstationary {F : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (hK : IsCompact K) (hd : ∀ x ∈ K, fderiv ℝ F x ≠ 0) :
    ∃ c : Fin n → (Fin n → ℝ) → ℂ, (∀ l, ContDiff ℝ ∞ (c l)) ∧
      ∀ x ∈ K, ∑ l, c l x * coordDeriv F l x = 1 := by
  set g : (Fin n → ℝ) → ℝ := fun x => ∑ l, ‖coordDeriv F l x‖ ^ 2 with hg
  have hgc : ContDiff ℝ ∞ g := ContDiff.sum fun l _ =>
    (contDiff_norm_sq ℝ).comp (contDiff_coordDeriv hF l)
  have hg0 : ∀ x, 0 ≤ g x := fun x => Finset.sum_nonneg fun l _ => by positivity
  have hgpos : ∀ x ∈ K, 0 < g x := by
    intro x hx
    refine lt_of_le_of_ne (hg0 x) fun h0 => hd x hx (clm_eq_zero_of_basis fun l => ?_)
    have hl := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => by positivity).mp h0.symm l
      (Finset.mem_univ l)
    simpa [coordDeriv] using hl
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨fun _ _ => 0, fun _ => contDiff_const, by simp [hKe]⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne hgc.continuous.continuousOn
  set m := g x₀ with hm
  have hm0 : 0 < m := hgpos x₀ hx₀
  set h : ℝ → ℝ := fun t => t + m * (1 - Real.smoothTransition (t / m)) with hh
  have hhc : ContDiff ℝ ∞ h := contDiff_id.add (contDiff_const.mul (contDiff_const.sub
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.div_const m))))
  have hpos : ∀ t, 0 ≤ t → 0 < h t := by
    intro t ht
    have h1 := Real.smoothTransition.le_one (t / m)
    rcases ht.lt_or_eq with ht' | ht'
    · simp only [hh]; nlinarith
    · subst ht'
      simp [hh, Real.smoothTransition.zero_of_nonpos, hm0]
  have hhK : ∀ x ∈ K, h (g x) = g x := by
    intro x hx
    have : 1 ≤ g x / m := (one_le_div hm0).mpr (hmin hx)
    simp [hh, Real.smoothTransition.one_of_one_le this]
  refine ⟨fun l x => (starRingEnd ℂ) (coordDeriv F l x) * (((h (g x))⁻¹ : ℝ) : ℂ),
    fun l => ?_, ?_⟩
  · exact (Complex.conjCLE.contDiff.comp (contDiff_coordDeriv hF l)).mul
      (ofRealCLM.contDiff.comp ((hhc.comp hgc).inv fun x => (hpos _ (hg0 x)).ne'))
  · intro x hx
    have hgx : (g x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hgpos x hx).ne'
    have hs : ∑ l, (starRingEnd ℂ) (coordDeriv F l x) * coordDeriv F l x = (g x : ℂ) := by
      simp only [hg, ofReal_sum, ofReal_pow]
      exact Finset.sum_congr rfl fun l _ => Complex.conj_mul' _
    calc ∑ l, (starRingEnd ℂ) (coordDeriv F l x) * (((h (g x))⁻¹ : ℝ) : ℂ) * coordDeriv F l x
        = (∑ l, (starRingEnd ℂ) (coordDeriv F l x) * coordDeriv F l x) * (((g x)⁻¹ : ℝ) : ℂ) := by
          rw [hhK x hx, Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = 1 := by rw [hs, ofReal_inv]; exact mul_inv_cancel₀ hgx

/-- **Exponential decay**: if `Im F ≥ c` on the compact set `K` and `w` is continuous and vanishes
off `K`, then `|∫ w e^{iτF}| ≤ M e^{-cτ}` for `τ ≥ 0`. -/
theorem exists_bound_exp (hK : IsCompact K) {F w : (Fin n → ℝ) → ℂ} (hw : Continuous w)
    (hwK : ∀ x ∉ K, w x = 0) {c : ℝ} (hFim : ∀ x ∈ K, c ≤ (F x).im) :
    ∃ M, ∀ τ : ℝ, 0 ≤ τ → ‖∫ x, w x * cexp (I * τ * F x)‖ ≤ M * Real.exp (-(c * τ)) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hw.continuousOn
  refine ⟨B * volume.real K, fun τ hτ => ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    fun x hx => by rw [hwK x hx, zero_mul]]
  rw [mul_right_comm]
  refine norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun x hx => ?_
  have h1 : ‖w x‖ ≤ B := hB x hx
  have h2 : ‖cexp (I * τ * F x)‖ ≤ Real.exp (-(c * τ)) := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    have : (I * τ * F x).re = -(τ * (F x).im) := by
      simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]; ring
    rw [this]
    nlinarith [hFim x hx]
  rw [norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- `e^{-cτ} ≤ k! c^{-k} τ^{-k}` for `c, τ > 0`. -/
theorem exp_neg_le_inv_pow {c : ℝ} (hc : 0 < c) (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Real.exp (-(c * τ)) ≤ (k.factorial / c ^ k) * (τ ^ k)⁻¹ := by
  have h := Real.pow_div_factorial_le_exp _ (mul_pos hc hτ).le k
  rw [Real.exp_neg]
  have hpos : 0 < (c * τ) ^ k / k.factorial := by positivity
  calc (Real.exp (c * τ))⁻¹ ≤ ((c * τ) ^ k / k.factorial)⁻¹ := by
        gcongr
    _ = (k.factorial / c ^ k) * (τ ^ k)⁻¹ := by
        rw [mul_pow]; field_simp

/-- A positive continuous function on a compact set has a positive lower bound there. -/
theorem exists_pos_le_of_isCompact {f : (Fin n → ℝ) → ℝ} (hK : IsCompact K) (hf : Continuous f)
    (hpos : ∀ x ∈ K, 0 < f x) : ∃ c, 0 < c ∧ ∀ x ∈ K, c ≤ f x := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, by simp [hKe]⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
  exact ⟨f x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

/-- A finite smooth partition of unity on a closed set `s`, subordinate to an open cover
(Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate` on `ℝⁿ`, with a finite index set). -/
theorem exists_smooth_partition {ι : Type} [Fintype ι] {s : Set (Fin n → ℝ)} (hs : IsClosed s)
    (U : ι → Set (Fin n → ℝ)) (hU : ∀ i, IsOpen (U i)) (hcov : s ⊆ ⋃ i, U i) :
    ∃ ρ : ι → (Fin n → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i, tsupport (ρ i) ⊆ U i) ∧
      ∀ x ∈ s, ∑ i, ρ i x = 1 := by
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℝ) hs U hU hcov
  refine ⟨fun i => f i, fun i => contMDiff_iff_contDiff.mp (f i).contMDiff, fun i => hf i,
    fun x hx => ?_⟩
  have h := f.sum_eq_one hx
  rwa [finsum_eq_sum_of_fintype] at h

/-- Splitting an oscillatory integral along a partition of unity on the support of the
amplitude: `∫ a E = ∑ᵢ ∫ (ρᵢ a) E`. -/
theorem integral_eq_sum_partition {ι : Type} [Fintype ι] {a E : (Fin n → ℝ) → ℂ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hE : Continuous E)
    {ρ : ι → (Fin n → ℝ) → ℝ} (hρ : ∀ i, Continuous (ρ i))
    (hsum : ∀ x ∈ tsupport a, ∑ i, ρ i x = 1) :
    ∫ x, a x * E x = ∑ i, ∫ x, ((ρ i x : ℂ) * a x) * E x := by
  have hpt : (fun x => a x * E x) = fun x => ∑ i, ((ρ i x : ℂ) * a x) * E x := by
    funext x
    by_cases hx : x ∈ tsupport a
    · rw [← Finset.sum_mul, ← Finset.sum_mul, ← ofReal_sum, hsum x hx, ofReal_one, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [hpt, integral_finsetSum _ fun i _ => ?_]
  exact (((continuous_ofReal.comp (hρ i)).mul ha).mul hE).integrable_of_hasCompactSupport
    hc.mul_left.mul_right

/-- **No critical points** (Hörmander, *ALPDO I*, Theorem 7.7.1, combined with the trivial
bound where `Im F > 0`): if `Im F ≥ 0` on the support of the smooth, compactly supported `u` and
every point of the support has `Im F > 0` or `dF ≠ 0`, then `∫ u e^{iτF} = O(τ^{-k})` for every
`k`. -/
theorem exists_bound_noncritical {F u : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hIm : ∀ x ∈ tsupport u, 0 ≤ (F x).im)
    (hnc : ∀ x ∈ tsupport u, 0 < (F x).im ∨ fderiv ℝ F x ≠ 0) (k : ℕ) :
    ∃ C, ∀ τ : ℝ, 1 ≤ τ → ‖∫ x, u x * cexp (I * τ * F x)‖ ≤ C * (τ ^ k)⁻¹ := by
  have hFc : Continuous F := hF.continuous
  have hdc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  set U : Bool → Set (Fin n → ℝ) := fun b => if b then {x | fderiv ℝ F x ≠ 0}
    else {x | 0 < (F x).im} with hUdef
  have hUo : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · exact isOpen_lt continuous_const (continuous_im.comp hFc)
    · exact isOpen_ne_fun hdc continuous_const
  have hcov : tsupport u ⊆ ⋃ b, U b := fun x hx => by
    rcases hnc x hx with h | h
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
  obtain ⟨ρ, hρc, hρU, hρs⟩ := exists_smooth_partition (isClosed_tsupport u) U hUo hcov
  set w : Bool → (Fin n → ℝ) → ℂ := fun b x => (ρ b x : ℂ) * u x with hw
  have hwc : ∀ b, ContDiff ℝ ∞ (w b) := fun b =>
    (ofRealCLM.contDiff.comp (hρc b)).mul hu
  have hwK : ∀ b, IsCompact (tsupport (w b)) := fun b => (hc.mul_left).isCompact
  have hw0 : ∀ b, ∀ x ∉ tsupport (w b), w b x = 0 := fun b x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have hwsub : ∀ b, tsupport (w b) ⊆ U b ∩ tsupport u := fun b x hx =>
    ⟨hρU b (tsupport_comp_subset ofReal_zero (ρ b) (tsupport_mul_subset_left hx)),
      tsupport_mul_subset_right hx⟩
  have hbound : ∀ b, ∃ C, ∀ τ : ℝ, 1 ≤ τ → ‖∫ x, w b x * cexp (I * τ * F x)‖ ≤ C * (τ ^ k)⁻¹ := by
    intro b
    cases b
    · obtain ⟨c, hc0, hcK⟩ := exists_pos_le_of_isCompact (hwK false)
        (continuous_im.comp hFc) fun x hx => (hwsub false hx).1
      obtain ⟨M, hM⟩ := exists_bound_exp (hwK false) (hwc false).continuous (hw0 false) hcK
      refine ⟨|M| * (k.factorial / c ^ k), fun τ hτ => ?_⟩
      have hτ0 : 0 < τ := by linarith
      calc _ ≤ M * Real.exp (-(c * τ)) := hM τ hτ0.le
        _ ≤ |M| * Real.exp (-(c * τ)) := by gcongr; exact le_abs_self M
        _ ≤ |M| * ((k.factorial / c ^ k) * (τ ^ k)⁻¹) := by
            gcongr; exact exp_neg_le_inv_pow hc0 k hτ0
        _ = _ := by ring
    · obtain ⟨c, hcs, hid⟩ := exists_coeff_nonstationary hF (hwK true)
        fun x hx => (hwsub true hx).1
      exact exists_bound_nonstationary (hwK true) hF (fun x hx => hIm x (hwsub true hx).2)
        hcs hid k (hwc true) (hw0 true)
  choose C hC using hbound
  refine ⟨∑ b, C b, fun τ hτ => ?_⟩
  rw [integral_eq_sum_partition hu.continuous hc ((contDiff_const.mul hF).cexp.continuous)
    (fun b => (hρc b).continuous) hρs, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hC b τ hτ)

/-- **Non-stationary phase** (Hörmander, *ALPDO I*, Theorem 7.7.1): if `Im F ≥ 0` and `dF ≠ 0`
on the support of the smooth, compactly supported `u`, then `∫ u e^{iτF} = O(τ^{-k})` for every
`k`. -/
theorem nonstationary_phase {F u : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hIm : ∀ x ∈ tsupport u, 0 ≤ (F x).im)
    (hd : ∀ x ∈ tsupport u, fderiv ℝ F x ≠ 0) (k : ℕ) :
    ∃ C, ∀ τ : ℝ, 1 ≤ τ → ‖∫ x, u x * cexp (I * τ * F x)‖ ≤ C * (τ ^ k)⁻¹ :=
  exists_bound_noncritical hF hu hc hIm (fun x hx => Or.inr (hd x hx)) k

/-- Every point of a finite set has a positive distance to the other points. -/
theorem exists_sep_radius (K : Finset (Fin n → ℝ)) (x₀ : Fin n → ℝ) :
    ∃ ε, 0 < ε ∧ ∀ x₁ ∈ K, x₁ ≠ x₀ → ε ≤ dist x₀ x₁ := by
  rcases (K.erase x₀).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x₁ hx₁ hne => ?_⟩
    have : x₁ ∈ K.erase x₀ := Finset.mem_erase.mpr ⟨hne, hx₁⟩
    simp [he] at this
  obtain ⟨y, hy, hmin⟩ := (K.erase x₀).exists_min_image (dist x₀) hne
  refine ⟨dist x₀ y, dist_pos.mpr (Finset.ne_of_mem_erase hy).symm, fun x₁ hx₁ hne => ?_⟩
  exact hmin x₁ (Finset.mem_erase.mpr ⟨hne, hx₁⟩)

/-- **Localisation at finitely many critical points.** Let `Im F ≥ 0` on the support of the
smooth, compactly supported `a`, and let every critical point of the support (`Im F = 0`,
`dF = 0`) lie in the finite set `K ⊆ tsupport a`. For any radii `δ x₀ > 0` there are smooth cutoffs
`χ x₀`, supported in `ball x₀ (δ x₀)` with `χ x₀ x₀ = 1`, such that
`∫ a e^{iτF} - ∑_{x₀ ∈ K} ∫ χ_{x₀} a e^{iτF} = O(τ^{-k})` for every `k`. -/
theorem integral_localise {F a : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (hIm : ∀ x ∈ tsupport a, 0 ≤ (F x).im)
    (K : Finset (Fin n → ℝ)) (hK : ∀ x ∈ tsupport a, (F x).im = 0 → fderiv ℝ F x = 0 → x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport a) (δ : (Fin n → ℝ) → ℝ) (hδ : ∀ x ∈ K, 0 < δ x) :
    ∃ χ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ, (∀ x₀ ∈ K, ContDiff ℝ ∞ (χ x₀)) ∧
      (∀ x₀ ∈ K, tsupport (χ x₀) ⊆ Metric.ball x₀ (δ x₀)) ∧ (∀ x₀ ∈ K, χ x₀ x₀ = 1) ∧
      ∀ k : ℕ, ∃ C, ∀ τ : ℝ, 1 ≤ τ →
        ‖(∫ x, a x * cexp (I * τ * F x)) -
          ∑ x₀ ∈ K, ∫ x, ((χ x₀ x : ℂ) * a x) * cexp (I * τ * F x)‖ ≤ C * (τ ^ k)⁻¹ := by
  choose ε hε hεs using exists_sep_radius (n := n) K
  set r : (Fin n → ℝ) → ℝ := fun x₀ => min (δ x₀) (ε x₀) with hr
  have hr0 : ∀ x₀ ∈ K, 0 < r x₀ := fun x₀ hx₀ => lt_min (hδ x₀ hx₀) (hε x₀)
  set U : Option K → Set (Fin n → ℝ) := fun i => match i with
    | none => (↑K : Set (Fin n → ℝ))ᶜ
    | some x₀ => Metric.ball (x₀ : Fin n → ℝ) (r x₀) with hU
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none => exact K.finite_toSet.isClosed.isOpen_compl
    | some x₀ => exact Metric.isOpen_ball
  have hcov : tsupport a ⊆ ⋃ i, U i := fun x hx => by
    by_cases hxK : x ∈ K
    · exact Set.mem_iUnion.mpr ⟨some ⟨x, hxK⟩, Metric.mem_ball_self (hr0 x hxK)⟩
    · exact Set.mem_iUnion.mpr ⟨none, hxK⟩
  obtain ⟨ρ, hρc, hρU, hρs⟩ := exists_smooth_partition (isClosed_tsupport a) U hUo hcov
  have hρ0 : ∀ i, ∀ x ∉ U i, ρ i x = 0 := fun i x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hρU i h)
  set χ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun x₀ =>
    if h : x₀ ∈ K then ρ (some ⟨x₀, h⟩) else 0 with hχ
  have hχK : ∀ x₀ (h : x₀ ∈ K), χ x₀ = ρ (some ⟨x₀, h⟩) := fun x₀ h => by
    simp only [hχ, h, ↓reduceDIte]
  refine ⟨χ, fun x₀ h => by rw [hχK x₀ h]; exact hρc _, fun x₀ h => ?_, fun x₀ h => ?_, ?_⟩
  · rw [hχK x₀ h]
    exact (hρU _).trans (Metric.ball_subset_ball (min_le_left _ _))
  · rw [hχK x₀ h]
    have hs := hρs x₀ (hKs x₀ h)
    rw [Fintype.sum_option, hρ0 none x₀ (by simp [hU, h]), zero_add,
      Finset.sum_eq_single (⟨x₀, h⟩ : K)] at hs
    · exact hs
    · intro x₁ _ hne
      refine hρ0 (some x₁) x₀ fun hb => ?_
      have hne' : (x₁ : Fin n → ℝ) ≠ x₀ := fun he => hne (Subtype.ext he)
      have h1 := hεs x₁ x₀ h hne'.symm
      have h2 : dist x₀ x₁ < r x₁ := hb
      rw [dist_comm] at h2
      linarith [min_le_right (δ x₁) (ε x₁)]
    · simp
  · intro k
    set w : (Fin n → ℝ) → ℂ := fun x => (ρ none x : ℂ) * a x with hw
    have hwc : ContDiff ℝ ∞ w := (ofRealCLM.contDiff.comp (hρc none)).mul ha
    have hwsub : tsupport w ⊆ (↑K : Set (Fin n → ℝ))ᶜ ∩ tsupport a := fun x hx =>
      ⟨hρU none (tsupport_comp_subset ofReal_zero (ρ none) (tsupport_mul_subset_left hx)),
        tsupport_mul_subset_right hx⟩
    obtain ⟨C, hC⟩ := exists_bound_noncritical hF hwc hc.mul_left
      (fun x hx => hIm x (hwsub hx).2) (fun x hx => by
        rcases (hIm x (hwsub hx).2).lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr fun hd => (hwsub hx).1 (hK x (hwsub hx).2 h.symm hd)) k
    refine ⟨C, fun τ hτ => ?_⟩
    have hsplit := integral_eq_sum_partition ha.continuous hc
      ((contDiff_const.mul hF).cexp.continuous) (fun i => (hρc i).continuous) hρs
      (E := fun x => cexp (I * τ * F x))
    rw [Fintype.sum_option] at hsplit
    have hsum : ∑ x₀ ∈ K, ∫ x, ((χ x₀ x : ℂ) * a x) * cexp (I * τ * F x) =
        ∑ x₀ : K, ∫ x, ((ρ (some x₀) x : ℂ) * a x) * cexp (I * τ * F x) := by
      rw [← Finset.sum_coe_sort K]
      refine Finset.sum_congr rfl fun x₀ _ => ?_
      rw [hχK x₀ x₀.2]
    rw [hsplit, hsum, add_sub_cancel_right]
    exact hC τ hτ

end Lightlike.Oscillatory

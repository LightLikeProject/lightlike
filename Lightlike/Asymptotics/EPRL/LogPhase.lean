import Lightlike.Oscillatory.StationaryPhase
import Lightlike.Asymptotics.EPRL.HessianSlice
import Lightlike.Asymptotics.EPRL.HessianChart
import Lightlike.Asymptotics.EPRL.InvSqrtDet
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The logarithmic phase of a unimodular maximum

If `G` is smooth with `|G| ≤ 1`, `G(0) = v` of modulus one and `dG(0) = 0`, then near `0`
`G^λ = v^λ exp(λ log (G/v))`, so `G^λ = v^λ e^{iλφ}` with the phase `φ = -i log (G/v)`, which has
`Im φ = -log |G| ≥ 0`. To make `φ` globally smooth the logarithm is cut off (`logCut`).
This file proves the smoothness and the sign of the cutoff logarithm, and that `φ` has Hessian
`-i H_G / v` at `0`.
-/

open Complex Filter Asymptotics
open scoped ContDiff

namespace Lightlike.Asymptotics.EPRL

variable {n : ℕ}

open Lightlike.Oscillatory

/-- A smooth bump on `ℂ`: `1` on the ball of radius `1/4` around `1`, supported in radius `1/2`. -/
noncomputable def logBump : ContDiffBump (1 : ℂ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

/-- A smooth, globally defined cutoff of the logarithm near `1`. -/
noncomputable def logCut (z : ℂ) : ℂ := (logBump z : ℂ) * Complex.log z

lemma norm_sub_one_lt_of_mem_support {z : ℂ} (hz : logBump z ≠ 0) : ‖z - 1‖ < 1/2 := by
  have : z ∈ Function.support logBump := hz
  rw [logBump.support_eq] at this
  simpa [logBump, dist_eq_norm] using this

lemma mem_slit_of_bump {z : ℂ} (hz : logBump z ≠ 0) : z ∈ Complex.slitPlane := by
  have := mem_slitPlane_of_norm_lt_one (z := z - 1)
    (by linarith [norm_sub_one_lt_of_mem_support hz])
  simpa using this

/-- The cutoff logarithm is smooth on all of `ℂ`. -/
lemma contDiff_logCut : ContDiff ℝ ∞ logCut := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport logBump
  · have hs : z ∈ Complex.slitPlane := by
      rw [logBump.tsupport_eq] at hz
      have : ‖z - 1‖ ≤ 1/2 := by simpa [logBump, dist_eq_norm] using hz
      have := mem_slitPlane_of_norm_lt_one (z := z - 1) (by linarith)
      simpa using this
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => (logBump z : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.comp logBump.contDiff).contDiffAt
    exact h1.mul ((Complex.contDiffAt_log hs).restrict_scalars ℝ)
  · have : logCut =ᶠ[nhds z] fun _ => 0 := by
      have hc : (tsupport logBump)ᶜ ∈ nhds z := (isClosed_tsupport _).isOpen_compl.mem_nhds hz
      filter_upwards [hc] with w hw
      have : logBump w = 0 := by simpa using image_eq_zero_of_notMem_tsupport hw
      simp [logCut, this]
    exact (contDiffAt_const).congr_of_eventuallyEq this

/-- Near `1` the cutoff logarithm is the logarithm. -/
lemma logCut_eq {z : ℂ} (hz : ‖z - 1‖ < 1/4) : logCut z = Complex.log z := by
  have : logBump z = 1 := logBump.one_of_mem_closedBall (by simp [logBump, dist_eq_norm]; linarith)
  simp [logCut, this]

/-- The real part of the cutoff logarithm is nonpositive on the closed unit disc. -/
lemma re_logCut_le {z : ℂ} (hz : ‖z‖ ≤ 1) : (logCut z).re ≤ 0 := by
  by_cases h : logBump z = 0
  · simp [logCut, h]
  · have h1 : Real.log ‖z‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hz
    have h01 := logBump.nonneg (x := z)
    simp only [logCut, Complex.re_ofReal_mul, Complex.log_re]
    exact mul_nonpos_of_nonneg_of_nonpos h01 (by simpa using h1)

/-- **The second derivative of `log ∘ c` at a point where `c = 1` and `c' = 0`** is `c''`. -/
lemma iteratedDeriv_two_logCut {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (h0 : c 0 = 1)
    (h1 : deriv c 0 = 0) :
    iteratedDeriv 2 (fun t => logCut (c t)) 0 = iteratedDeriv 2 c 0 := by
  have hcc : Continuous c := hc.continuous
  have hnb : ∀ᶠ t in nhds (0 : ℝ), ‖c t - 1‖ < 1/4 := by
    have : ContinuousAt (fun t => ‖c t - 1‖) 0 := (hcc.sub continuous_const).norm.continuousAt
    exact this.eventually (gt_mem_nhds (by simp [h0]))
  have hslit : ∀ t, ‖c t - 1‖ < 1/4 → c t ∈ Complex.slitPlane := fun t ht => by
    have := mem_slitPlane_of_norm_lt_one (z := c t - 1) (by linarith)
    simpa using this
  have hd : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  have hcd : ∀ t, HasDerivAt c (deriv c t) t := fun t =>
    ((hc.differentiable (by simp)) t).hasDerivAt
  have hdd : ∀ t, HasDerivAt (deriv c) (deriv (deriv c) t) t := fun t =>
    ((hd.differentiable (by simp)) t).hasDerivAt
  -- first derivative of the logarithm, near `0`
  have e1 : deriv (fun t => logCut (c t)) =ᶠ[nhds 0] fun t => deriv c t / c t := by
    have hopen : ∀ᶠ t in nhds (0 : ℝ), ‖c t - 1‖ < 1/4 ∧ ∀ᶠ s in nhds t, ‖c s - 1‖ < 1/4 := by
      have ho : IsOpen {t : ℝ | ‖c t - 1‖ < 1/4} :=
        isOpen_lt (hcc.sub continuous_const).norm continuous_const
      filter_upwards [hnb] with t ht
      exact ⟨ht, ho.mem_nhds ht⟩
    filter_upwards [hopen] with t ⟨ht, hts⟩
    have hl : (fun s => logCut (c s)) =ᶠ[nhds t] fun s => Complex.log (c s) := by
      filter_upwards [hts] with s hs using logCut_eq hs
    rw [hl.deriv_eq]
    exact (HasDerivAt.clog_real (hcd t) (hslit t ht)).deriv
  have hdiv : HasDerivAt (fun t => deriv c t / c t)
      ((deriv (deriv c) 0 * c 0 - deriv c 0 * deriv c 0) / c 0 ^ 2) 0 :=
    (hdd 0).div (hcd 0) (by simp [h0])
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
  rw [e1.deriv_eq, hdiv.deriv]
  simp [h0, h1]

/-- The logarithmic phase `φ = -i log (G / v)` (cut off). -/
noncomputable def logPhase (G : (Fin n → ℝ) → ℂ) (v : ℂ) (x : Fin n → ℝ) : ℂ :=
  -Complex.I * logCut (G x / v)

lemma contDiff_logPhase {G : (Fin n → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (v : ℂ) :
    ContDiff ℝ ∞ (logPhase G v) :=
  contDiff_const.mul (contDiff_logCut.comp (hG.div_const v))

/-- **The Hessian of the logarithmic phase** at a critical point of `G` with value `v` is
`-i H_G / v`. -/
theorem hessMat_logPhase {G : (Fin n → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) {v : ℂ} (hv : v ≠ 0)
    (hG0 : G 0 = v) (hd : fderiv ℝ G 0 = 0) :
    hessMat (logPhase G v) 0 = (-Complex.I * v⁻¹) • hessMat G 0 := by
  have hφ := contDiff_logPhase hG v
  rw [← sub_eq_zero]
  refine eq_zero_of_isSymm_of_qform ?_ fun u => ?_
  · exact (hessMat_isSymm hφ 0).sub ((hessMat_isSymm hG 0).smul _)
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [← iteratedDeriv_two_line hφ u]
    have hGl : ContDiff ℝ ∞ (fun t : ℝ => G (t • u)) := hG.comp (contDiff_id.smul contDiff_const)
    have hc : ContDiff ℝ ∞ (fun t : ℝ => G (t • u) / v) := hGl.div_const v
    have hcc : (fun t : ℝ => G (t • u) / v) = fun t => v⁻¹ * G (t • u) := by
      funext t; rw [div_eq_inv_mul]
    have h0 : (fun t : ℝ => G (t • u) / v) 0 = 1 := by simp [hG0, hv]
    have h1 : deriv (fun t : ℝ => G (t • u) / v) 0 = 0 := by
      rw [hcc, deriv_const_mul _ ((hGl.differentiable (by simp)) 0), deriv_line hG, hd]; simp
    have e : (fun t : ℝ => logPhase G v (t • u)) =
        fun t => -Complex.I * logCut (G (t • u) / v) := rfl
    have hcl : ContDiffAt ℝ 2 (fun t : ℝ => logCut (G (t • u) / v)) 0 :=
      (contDiff_logCut.comp hc).contDiffAt.of_le (by simp)
    have hgl : ContDiffAt ℝ 2 (fun t : ℝ => G (t • u)) 0 := hGl.contDiffAt.of_le (by simp)
    have h2 : iteratedDeriv 2 (fun t : ℝ => logCut (G (t • u) / v)) 0 =
        iteratedDeriv 2 (fun t : ℝ => G (t • u) / v) 0 := iteratedDeriv_two_logCut hc h0 h1
    rw [e, iteratedDeriv_const_mul (-Complex.I) hcl, h2, hcc,
      iteratedDeriv_const_mul v⁻¹ hgl, iteratedDeriv_two_line hG u]
    rw [sub_eq_zero]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

lemma logPhase_zero {G : (Fin n → ℝ) → ℂ} {v : ℂ} (hG0 : G 0 = v) (hv : v ≠ 0) :
    logPhase G v 0 = 0 := by
  have : logCut (G 0 / v) = 0 := by
    rw [hG0, div_self hv, logCut_eq (by simp)]; simp
  simp [logPhase, this]

lemma fderiv_logPhase_zero {G : (Fin n → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) {v : ℂ}
    (hd : fderiv ℝ G 0 = 0) : fderiv ℝ (logPhase G v) 0 = 0 := by
  have h1 : HasFDerivAt G (fderiv ℝ G 0) 0 := ((hG.differentiable (by simp)) 0).hasFDerivAt
  have h2 : HasFDerivAt (fun x => G x / v) (0 : (Fin n → ℝ) →L[ℝ] ℂ) 0 := by
    have := h1.const_smul v⁻¹
    rw [hd, smul_zero] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp [div_eq_inv_mul]
  have h3 : HasFDerivAt logCut (fderiv ℝ logCut (G 0 / v)) (G 0 / v) :=
    ((contDiff_logCut.differentiable (by simp)) _).hasFDerivAt
  have h4 := (h3.comp (0 : Fin n → ℝ) h2).const_mul (-Complex.I)
  have h5 : logPhase G v = fun x => -Complex.I * logCut (G x / v) := rfl
  rw [h5]
  exact h4.fderiv.trans (by ext u; simp)

/-- **Local asymptotics at a unimodular maximum.** If `|G| ≤ 1` with `G(0) = v`, `|v| = 1`,
`dG(0) = 0`, `0` is the only point of `|G| = 1` on the support of the smooth compactly supported
amplitude `a`, `G / v` stays within `1/4` of `1` there, and `-H_G(0)/v` is nondegenerate, then
`∫ a G^λ = v^λ (2π/λ)^{n/2} det(-H_G(0)/v)^{-1/2} a(0) + O(λ^{-n/2-1})`. -/
theorem local_asymptotics {G a : (Fin n → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) {v : ℂ} (hv : ‖v‖ = 1)
    (hG0 : G 0 = v) (hd : fderiv ℝ G 0 = 0) (hle : ∀ x, ‖G x‖ ≤ 1)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hnb : ∀ x ∈ tsupport a, ‖G x / v - 1‖ < 1/4)
    (hmax : ∀ x ∈ tsupport a, ‖G x‖ = 1 → x = 0) (h0 : (0 : Fin n → ℝ) ∈ tsupport a)
    (hnd : (-(v⁻¹ • hessMat G 0)).det ≠ 0) :
    (fun lam : ℕ => (∫ x, a x * G x ^ lam) -
        v ^ lam * (((2 * Real.pi / lam) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-(v⁻¹ • hessMat G 0)) * a 0))
      =O[atTop] fun lam : ℕ => (lam : ℝ) ^ (-((n : ℝ) / 2) - 1) := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hφ := contDiff_logPhase hG v
  have hH : -Complex.I • hessMat (logPhase G v) 0 = -(v⁻¹ • hessMat G 0) := by
    rw [hessMat_logPhase hG hv0 hG0 hd, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    have : (-Complex.I * (-Complex.I * v⁻¹)) = -v⁻¹ := by
      rw [← mul_assoc, neg_mul_neg, Complex.I_mul_I]; ring
    rw [this]; ring
  -- the phase hypotheses
  have hw : ∀ x ∈ tsupport a, logPhase G v x = -Complex.I * Complex.log (G x / v) := fun x hx => by
    simp only [logPhase, logCut_eq (hnb x hx)]
  have hne : ∀ x ∈ tsupport a, G x / v ≠ 0 := fun x hx h => by
    have := hnb x hx
    rw [h] at this
    norm_num at this
  have hIm : ∀ x ∈ tsupport a, 0 ≤ (logPhase G v x).im := fun x hx => by
    have := re_logCut_le (z := G x / v) (by rw [norm_div, hv, div_one]; exact hle x)
    simpa [logPhase] using this
  have hK : ∀ x ∈ tsupport a, ((logPhase G v x).im = 0 ∧ fderiv ℝ (logPhase G v) x = 0) ↔
      x ∈ ({0} : Finset (Fin n → ℝ)) := fun x hx => by
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨him, -⟩
      apply hmax x hx
      rw [hw x hx] at him
      have him' : (Complex.log (G x / v)).re = 0 := by simpa using him
      have hre : Real.log ‖G x / v‖ = 0 := by rwa [Complex.log_re] at him'
      have hpos : 0 < ‖G x / v‖ := norm_pos_iff.mpr (hne x hx)
      rcases Real.log_eq_zero.mp hre with h | h | h
      · exact absurd h hpos.ne'
      · simpa [norm_div, hv] using h
      · linarith [norm_nonneg (G x / v)]
    · rintro rfl
      exact ⟨by simp [logPhase_zero hG0 hv0], fderiv_logPhase_zero hG hd⟩
  have hsp := stationary_phase_pi hφ ha hc hIm {0} hK (fun x hx => by simp only [Finset.mem_singleton] at hx; subst hx; exact h0)
    (fun x hx => by simp only [Finset.mem_singleton] at hx; subst hx; rw [hH]; exact hnd)
  -- rewrite the integrand and compare
  have hpt : ∀ (lam : ℕ) (x : Fin n → ℝ), a x * G x ^ lam =
      v ^ lam * (a x * cexp (I * (lam : ℝ) * logPhase G v x)) := by
    intro lam x
    by_cases hx : x ∈ tsupport a
    · have hex : cexp (I * (lam : ℝ) * logPhase G v x) = (G x / v) ^ lam := by
        rw [hw x hx]
        have : I * (lam : ℝ) * (-Complex.I * Complex.log (G x / v)) =
            lam * Complex.log (G x / v) := by
          have : Complex.I * Complex.I = -1 := Complex.I_mul_I
          linear_combination (-(lam : ℂ) * Complex.log (G x / v)) * this
        rw [this, Complex.exp_nat_mul, Complex.exp_log (hne x hx)]
      rw [hex, div_pow]
      field_simp [pow_ne_zero lam hv0]
    · have : a x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hint : ∀ lam : ℕ, (∫ x, a x * G x ^ lam) =
      v ^ lam * ∫ x, a x * cexp (I * (lam : ℝ) * logPhase G v x) := fun lam => by
    simp_rw [hpt lam]
    exact MeasureTheory.integral_const_mul _ _
  have hsp' := hsp.comp_tendsto tendsto_natCast_atTop_atTop
  have hunit : (fun lam : ℕ => v ^ lam) =O[atTop] fun _ : ℕ => (1 : ℝ) :=
    Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun lam => by simp [norm_pow, hv])
  have := hunit.mul hsp'
  have this := this.congr_right fun lam => one_mul _
  refine this.congr_left fun lam => ?_
  simp only [Function.comp, Finset.sum_singleton, hint, logPhase_zero hG0 hv0, mul_zero, Complex.exp_zero,
    one_mul, hH]
  ring

end Lightlike.Asymptotics.EPRL

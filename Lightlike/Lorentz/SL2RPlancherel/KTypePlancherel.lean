import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.CasimirPlancherel

/-!
# Plancherel formulae for the radial `K`-types `(l, 0)` by induction on `l`

For `F` smooth with compact support write `K_l(F) = ∫_{v>1} (v² - 1)^l |F^{(l)}(v)|² dv`; in the variable `ξ` (`v = cosh ξ`)
`sinh^l ξ · F^{(l)}(cosh ξ)` is the `l`-fold ladder image of `F ∘ cosh`, and `K_l` is its `L²(sinh ξ dξ)` norm. The induction
step is the identity `K_{l+1}(F) = S_l(F, Q F) + l (l + 1) K_l(F)` (integration by parts against the weight `(v² - 1)^l`),
which multiplies the Plancherel weight by `1/4 + ρ² + l (l + 1) = (l + 1/2)² + ρ²`.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The `l`-th derivative of the radial Laplacian**:
`(Q F)^{(l)} = -((v² - 1) F^{(l+2)} + 2 (l+1) v F^{(l+1)} + l (l+1) F^{(l)})`. -/
theorem iteratedDeriv_radialQ {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (l : ℕ) (v : ℝ) :
    iteratedDeriv l (radialQ F) v =
      -((((v ^ 2 - 1 : ℝ)) : ℂ) * iteratedDeriv (l + 2) F v
        + ((2 * (l + 1) * v : ℝ) : ℂ) * iteratedDeriv (l + 1) F v
        + (((l * (l + 1) : ℝ)) : ℂ) * iteratedDeriv l F v) := by
  induction l generalizing v with
  | zero =>
    simp only [iteratedDeriv_zero, radialQ, iteratedDeriv_succ, zero_add]
    push_cast
    simp only [zero_mul, add_zero]
    ring
  | succ l ih =>
    have hd : ∀ k : ℕ, HasDerivAt (iteratedDeriv k F) (iteratedDeriv (k + 1) F v) v := fun k => by
      rw [iteratedDeriv_succ]
      exact ((hF.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)) v).hasDerivAt
    have hp : HasDerivAt (fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ)) ((2 * v : ℝ) : ℂ) v := by
      have := ((hasDerivAt_pow 2 v).sub_const 1).ofReal_comp
      simpa using this
    have hq : HasDerivAt (fun v : ℝ => ((2 * ((l : ℝ) + 1) * v : ℝ) : ℂ)) ((2 * ((l : ℝ) + 1) : ℝ) : ℂ) v := by
      have := ((hasDerivAt_id v).const_mul (2 * ((l : ℝ) + 1))).ofReal_comp
      simpa using this
    have hA := (((hp.mul (hd (l + 2))).add (hq.mul (hd (l + 1)))).add
      ((hd l).const_mul (((l * (l + 1) : ℝ)) : ℂ))).neg
    have hfun : iteratedDeriv l (radialQ F) = fun v : ℝ =>
        -((((v ^ 2 - 1 : ℝ)) : ℂ) * iteratedDeriv (l + 2) F v
        + ((2 * (l + 1) * v : ℝ) : ℂ) * iteratedDeriv (l + 1) F v
        + (((l * (l + 1) : ℝ)) : ℂ) * iteratedDeriv l F v) := funext ih
    have hA' : HasDerivAt (fun v : ℝ =>
        -((((v ^ 2 - 1 : ℝ)) : ℂ) * iteratedDeriv (l + 2) F v
        + ((2 * (l + 1) * v : ℝ) : ℂ) * iteratedDeriv (l + 1) F v
        + (((l * (l + 1) : ℝ)) : ℂ) * iteratedDeriv l F v)) _ v := hA
    rw [iteratedDeriv_succ, hfun, hA'.deriv]
    push_cast
    ring

/-- Integration by parts against the weight `(v² - 1)^l` on `(1, ∞)`:
`-∫ (v²-1)^l conj G ((v²-1) G'' + 2 (l+1) v G') = ∫ (v²-1)^{l+1} |G'|²`. -/
theorem integral_ibp_weight {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (l : ℕ) :
    ∫ v in Ioi (1 : ℝ), (((v ^ 2 - 1) ^ l : ℝ) : ℂ) * (starRingEnd ℂ (G v) *
        (-((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv G) v + ((2 * (l + 1) * v : ℝ) : ℂ) * deriv G v))) =
      ∫ v in Ioi (1 : ℝ), (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ) * (starRingEnd ℂ (deriv G v) * deriv G v) := by
  have h1 : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.1 hG).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv G)) := (contDiff_infty_iff_deriv.1 h1).2
  have hGd : ∀ v, HasDerivAt G (deriv G v) v := fun v => ((hG.differentiable (by simp)) v).hasDerivAt
  have hG1d : ∀ v, HasDerivAt (deriv G) (deriv (deriv G) v) v := fun v =>
    ((h1.differentiable (by simp)) v).hasDerivAt
  set u : ℝ → ℂ := fun v => starRingEnd ℂ (G v) with hu
  set w : ℝ → ℂ := fun v => (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ) * deriv G v with hw
  have hu' : ∀ v, HasDerivAt u (starRingEnd ℂ (deriv G v)) v := fun v => by
    have := (hGd v).star
    simpa using this
  have hw' : ∀ v, HasDerivAt w ((((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
      ((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv G) v + ((2 * (l + 1) * v : ℝ) : ℂ) * deriv G v)) v := by
    intro v
    have hp : HasDerivAt (fun v : ℝ => (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ))
        (((((l + 1 : ℕ) : ℝ) * (v ^ 2 - 1) ^ l * (2 * v) : ℝ)) : ℂ) v := by
      have := (((hasDerivAt_pow 2 v).sub_const 1).pow (l + 1)).ofReal_comp
      simpa using this
    refine (hp.mul (hG1d v)).congr_deriv ?_
    push_cast
    ring
  have hpc : Continuous (fun v : ℝ => (((v ^ 2 - 1) ^ l : ℝ) : ℂ)) := by fun_prop
  have hpc1 : Continuous (fun v : ℝ => (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ)) := by fun_prop
  have hqc : Continuous (fun v : ℝ => ((2 * (l + 1) * v : ℝ) : ℂ)) := by fun_prop
  have hrc : Continuous (fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ)) := by fun_prop
  have hcu : HasCompactSupport u := hc.comp_left (g := starRingEnd ℂ) (map_zero _)
  have hcu' : HasCompactSupport (fun v => starRingEnd ℂ (deriv G v)) :=
    hc.deriv.comp_left (g := starRingEnd ℂ) (map_zero _)
  have huc : Continuous u := (Complex.continuous_conj).comp hG.continuous
  have hu'c : Continuous (fun v => starRingEnd ℂ (deriv G v)) :=
    (Complex.continuous_conj).comp h1.continuous
  have hwc : Continuous w := hpc1.mul h1.continuous
  have hv'c : Continuous (fun v : ℝ => (((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
      ((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv G) v + ((2 * (l + 1) * v : ℝ) : ℂ) * deriv G v)) :=
    hpc.mul ((hrc.mul h2.continuous).add (hqc.mul h1.continuous))
  have hz1 : Tendsto (u * w) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h0 : (u * w) 1 = 0 := by simp [hu, hw]
    have := ((huc.mul hwc).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    rwa [h0] at this
  have hz2 : Tendsto (u * w) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_zero_translate hcu 0] with v hv
    have hv' : u v = 0 := by simpa using hv
    simp [Pi.mul_apply, hv']
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (a' := 0) (b' := 0)
    (u := u) (v := w) (u' := fun v => starRingEnd ℂ (deriv G v))
    (v' := fun v => (((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
      ((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv G) v + ((2 * (l + 1) * v : ℝ) : ℂ) * deriv G v))
    (fun v _ => hu' v) (fun v _ => hw' v)
    ((huc.mul hv'c).integrable_of_hasCompactSupport hcu.mul_right).integrableOn
    ((hu'c.mul hwc).integrable_of_hasCompactSupport hcu'.mul_right).integrableOn hz1 hz2
  have e1 : ∀ v : ℝ, (((v ^ 2 - 1) ^ l : ℝ) : ℂ) * (starRingEnd ℂ (G v) *
        (-((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv G) v + ((2 * (l + 1) * v : ℝ) : ℂ) * deriv G v))) =
      -(u v * ((((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
        ((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv G) v + ((2 * (l + 1) * v : ℝ) : ℂ) * deriv G v))) := by
    intro v; simp only [hu]; ring
  have e2 : ∀ v : ℝ, starRingEnd ℂ (deriv G v) * w v =
      (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ) * (starRingEnd ℂ (deriv G v) * deriv G v) := by
    intro v; simp only [hw]; ring
  simp only [e1, integral_neg, key, e2]
  simp

theorem hasCompactSupport_iteratedDeriv {F : ℝ → ℂ} (hc : HasCompactSupport F) (l : ℕ) :
    HasCompactSupport (iteratedDeriv l F) := by
  induction l with
  | zero => simpa using hc
  | succ l ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem contDiff_iteratedDeriv_infty {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (l : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv l F) := by
  induction l with
  | zero => simpa using hF
  | succ l ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.1 ih).2

/-- The real part of the `l`-th Sobolev-type form `∫_{v>1} (v² - 1)^l Re (conj F^{(l)} G^{(l)})`. -/
def Kform (l : ℕ) (F G : ℝ → ℂ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), (v ^ 2 - 1) ^ l * (starRingEnd ℂ (iteratedDeriv l F v) * iteratedDeriv l G v).re

/-- **The induction step of the `K`-type recursion**:
`K_{l+1}(F, F) = K_l(F, Q F) + l (l + 1) K_l(F, F)`. -/
theorem Kform_succ {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (l : ℕ) :
    Kform (l + 1) F F = Kform l F (radialQ F) + ((l * (l + 1) : ℝ)) * Kform l F F := by
  set G := iteratedDeriv l F with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_iteratedDeriv_infty hF l
  have hGc : HasCompactSupport G := hasCompactSupport_iteratedDeriv hc l
  have hQs : ContDiff ℝ ∞ (radialQ F) := contDiff_radialQ hF
  have hQc : HasCompactSupport (radialQ F) := hasCompactSupport_radialQ hc
  have hd1 : deriv G = iteratedDeriv (l + 1) F := (iteratedDeriv_succ).symm
  have hd2 : deriv (deriv G) = iteratedDeriv (l + 2) F := by rw [hd1]; exact (iteratedDeriv_succ).symm
  have hibp := integral_ibp_weight hGs hGc l
  rw [hd2, hd1] at hibp
  -- complex versions of the three integrals
  have hQ : ∀ v : ℝ, iteratedDeriv l (radialQ F) v =
      (-((((v ^ 2 - 1 : ℝ)) : ℂ) * iteratedDeriv (l + 2) F v
        + ((2 * (l + 1) * v : ℝ) : ℂ) * iteratedDeriv (l + 1) F v)) - (((l * (l + 1) : ℝ)) : ℂ) * G v := by
    intro v; rw [iteratedDeriv_radialQ hF l v]; simp only [hG]; ring
  have cG := hGs.continuous
  have cQ := (contDiff_iteratedDeriv_infty hQs l).continuous
  have cw : Continuous (fun v : ℝ => (((v ^ 2 - 1) ^ l : ℝ) : ℂ)) := by fun_prop
  have iI1 : IntegrableOn (fun v : ℝ => (((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
      (starRingEnd ℂ (G v) * iteratedDeriv l (radialQ F) v)) (Ioi (1 : ℝ)) :=
    ((cw.mul ((Complex.continuous_conj.comp cG).mul cQ)).integrable_of_hasCompactSupport
      ((hGc.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right.mul_left)).integrableOn
  have iI3 : IntegrableOn (fun v : ℝ => (((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
      (starRingEnd ℂ (G v) * G v)) (Ioi (1 : ℝ)) :=
    ((cw.mul ((Complex.continuous_conj.comp cG).mul cG)).integrable_of_hasCompactSupport
      ((hGc.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right.mul_left)).integrableOn
  have cG1 := (contDiff_iteratedDeriv_infty hF (l + 1)).continuous
  have iI4 : IntegrableOn (fun v : ℝ => (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ) *
      (starRingEnd ℂ (iteratedDeriv (l + 1) F v) * iteratedDeriv (l + 1) F v)) (Ioi (1 : ℝ)) := by
    have cw1 : Continuous (fun v : ℝ => (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ)) := by fun_prop
    exact ((cw1.mul ((Complex.continuous_conj.comp cG1).mul cG1)).integrable_of_hasCompactSupport
      ((hasCompactSupport_iteratedDeriv hc (l + 1)).comp_left (g := starRingEnd ℂ)
        (map_zero _) |>.mul_right.mul_left)).integrableOn
  have hsplit : ∫ v in Ioi (1 : ℝ), (((v ^ 2 - 1) ^ (l + 1) : ℝ) : ℂ) *
      (starRingEnd ℂ (iteratedDeriv (l + 1) F v) * iteratedDeriv (l + 1) F v) =
      (∫ v in Ioi (1 : ℝ), (((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
        (starRingEnd ℂ (G v) * iteratedDeriv l (radialQ F) v))
      + (((l * (l + 1) : ℝ)) : ℂ) * ∫ v in Ioi (1 : ℝ), (((v ^ 2 - 1) ^ l : ℝ) : ℂ) *
        (starRingEnd ℂ (G v) * G v) := by
    rw [← hibp, ← integral_const_mul, ← integral_add iI1 (iI3.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [hQ v]
    ring
  have hre := congrArg Complex.re hsplit
  have r1 := integral_re iI4
  have r2 := integral_re iI1
  have r3 := integral_re iI3
  simp only [RCLike.re_to_complex] at r1 r2 r3
  have hpt : ∀ (w : ℝ) (z : ℂ), (((w : ℝ) : ℂ) * z).re = w * z.re := fun w z => by
    simp [Complex.re_ofReal_mul]
  simp only [hpt] at r1 r2 r3
  rw [Complex.add_re, Complex.re_ofReal_mul, ← r1, ← r2, ← r3] at hre
  unfold Kform
  exact hre


theorem iteratedDeriv_add_smooth {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    iteratedDeriv l (F + G) = iteratedDeriv l F + iteratedDeriv l G := by
  induction l with
  | zero => simp
  | succ l ih =>
    funext v
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ, iteratedDeriv_succ]
    exact deriv_add (((contDiff_iteratedDeriv_infty hF l).differentiable (by simp)) v)
      (((contDiff_iteratedDeriv_infty hG l).differentiable (by simp)) v)

theorem integrableOn_Kint {A B : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (hB : ContDiff ℝ ∞ B) (l : ℕ) :
    IntegrableOn (fun v : ℝ => (v ^ 2 - 1) ^ l *
      (starRingEnd ℂ (iteratedDeriv l A v) * iteratedDeriv l B v).re) (Ioi (1 : ℝ)) := by
  have h1 : Continuous (fun v : ℝ => (v ^ 2 - 1) ^ l *
      (starRingEnd ℂ (iteratedDeriv l A v) * iteratedDeriv l B v).re) := by
    have a := (contDiff_iteratedDeriv_infty hA l).continuous
    have b := (contDiff_iteratedDeriv_infty hB l).continuous
    have : Continuous (fun v : ℝ => (starRingEnd ℂ (iteratedDeriv l A v) * iteratedDeriv l B v).re) :=
      Complex.continuous_re.comp ((Complex.continuous_conj.comp a).mul b)
    exact (by fun_prop : Continuous fun v : ℝ => (v ^ 2 - 1) ^ l).mul this
  have h2 : HasCompactSupport (fun v : ℝ => (v ^ 2 - 1) ^ l *
      (starRingEnd ℂ (iteratedDeriv l A v) * iteratedDeriv l B v).re) := by
    have := (hasCompactSupport_iteratedDeriv hAc l).comp_left (g := starRingEnd ℂ) (map_zero _)
    have h3 : HasCompactSupport (fun v : ℝ => starRingEnd ℂ (iteratedDeriv l A v) * iteratedDeriv l B v) :=
      this.mul_right
    exact (h3.comp_left (g := Complex.re) (by simp)).mul_left
  exact (h1.integrable_of_hasCompactSupport h2).integrableOn

theorem Kform_add_self {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (l : ℕ) :
    Kform l (F + G) (F + G) = Kform l F F + Kform l G G + 2 * Kform l F G := by
  unfold Kform
  have e : ∀ v : ℝ, (((v ^ 2 - 1) ^ l) *
      (starRingEnd ℂ (iteratedDeriv l (F + G) v) * iteratedDeriv l (F + G) v).re) =
      (v ^ 2 - 1) ^ l * (starRingEnd ℂ (iteratedDeriv l F v) * iteratedDeriv l F v).re
      + (v ^ 2 - 1) ^ l * (starRingEnd ℂ (iteratedDeriv l G v) * iteratedDeriv l G v).re
      + 2 * ((v ^ 2 - 1) ^ l * (starRingEnd ℂ (iteratedDeriv l F v) * iteratedDeriv l G v).re) := by
    intro v
    rw [iteratedDeriv_add_smooth hF hG, Pi.add_apply]
    simp only [map_add, add_mul, mul_add, Complex.add_re]
    have : (starRingEnd ℂ (iteratedDeriv l G v) * iteratedDeriv l F v).re =
        (starRingEnd ℂ (iteratedDeriv l F v) * iteratedDeriv l G v).re := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
    rw [this]; ring
  simp only [e]
  have iFF := integrableOn_Kint hF hc hF l
  have iGG := integrableOn_Kint hG hGc hG l
  have iFG := integrableOn_Kint hF hc hG l
  have iAB : IntegrableOn (fun v : ℝ =>
      (v ^ 2 - 1) ^ l * (starRingEnd ℂ (iteratedDeriv l F v) * iteratedDeriv l F v).re
      + (v ^ 2 - 1) ^ l * (starRingEnd ℂ (iteratedDeriv l G v) * iteratedDeriv l G v).re)
      (Ioi (1 : ℝ)) := iFF.add iGG
  have iC : IntegrableOn (fun v : ℝ =>
      2 * ((v ^ 2 - 1) ^ l * (starRingEnd ℂ (iteratedDeriv l F v) * iteratedDeriv l G v).re))
      (Ioi (1 : ℝ)) := iFG.const_mul 2
  rw [integral_add iAB iC, integral_add iFF iGG, integral_const_mul]


/-- **Polarisation, abstractly**: if the quadratic identities hold for `F`, `Q F`, `F + Q F` with transforms
`F^`, `c F^`, `(1 + c) F^`, then the bilinear identity holds for the pair `(F, Q F)`. -/
theorem polarize {S : Set ℝ} (hS : MeasurableSet S) (W c N : ℝ → ℝ) {π2 Kf Kg Kfg Kh : ℝ}
    (j1 : IntegrableOn (fun ρ => W ρ * N ρ) S)
    (j2 : IntegrableOn (fun ρ => W ρ * (c ρ ^ 2 * N ρ)) S)
    (j3 : IntegrableOn (fun ρ => W ρ * ((1 + c ρ) ^ 2 * N ρ)) S)
    (e1 : π2 * Kf = (1 / 4 : ℝ) * ∫ ρ in S, W ρ * N ρ)
    (e2 : π2 * Kg = (1 / 4 : ℝ) * ∫ ρ in S, W ρ * (c ρ ^ 2 * N ρ))
    (e3 : π2 * Kh = (1 / 4 : ℝ) * ∫ ρ in S, W ρ * ((1 + c ρ) ^ 2 * N ρ))
    (hK : Kh = Kf + Kg + 2 * Kfg) :
    IntegrableOn (fun ρ => W ρ * (c ρ * N ρ)) S ∧
      π2 * Kfg = (1 / 4 : ℝ) * ∫ ρ in S, W ρ * (c ρ * N ρ) := by
  have jM : IntegrableOn (fun ρ => W ρ * (c ρ * N ρ)) S := by
    have h : IntegrableOn (fun ρ : ℝ => (1 / 2 : ℝ) * (W ρ * ((1 + c ρ) ^ 2 * N ρ)
        - W ρ * N ρ - W ρ * (c ρ ^ 2 * N ρ))) S := ((j3.sub j1).sub j2).const_mul (1 / 2 : ℝ)
    refine MeasureTheory.IntegrableOn.congr_fun h (fun ρ _ => ?_) hS
    ring
  refine ⟨jM, ?_⟩
  have j12 : IntegrableOn (fun ρ : ℝ => W ρ * N ρ + W ρ * (c ρ ^ 2 * N ρ)) S := j1.add j2
  have jM2 : IntegrableOn (fun ρ : ℝ => 2 * (W ρ * (c ρ * N ρ))) S := jM.const_mul 2
  have hR : ∫ ρ in S, W ρ * ((1 + c ρ) ^ 2 * N ρ) =
      (∫ ρ in S, W ρ * N ρ) + (∫ ρ in S, W ρ * (c ρ ^ 2 * N ρ))
      + 2 * ∫ ρ in S, W ρ * (c ρ * N ρ) := by
    rw [setIntegral_congr_fun hS (fun ρ _ => (by ring : W ρ * ((1 + c ρ) ^ 2 * N ρ) =
      (W ρ * N ρ + W ρ * (c ρ ^ 2 * N ρ)) + 2 * (W ρ * (c ρ * N ρ)))),
      integral_add j12 jM2, integral_add j1 j2, integral_const_mul]
  rw [hK] at e3
  linear_combination (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e2 + (1 / 8 : ℝ) * hR


/-- The Plancherel weight of the `K`-type `(l, 0)` relative to the spherical one:
`∏_{k<l} ((k + 1/2)² + ρ²) = ∏_{k<l} (1/4 + ρ² + k (k+1))`. -/
def wl (l : ℕ) (ρ : ℝ) : ℝ := ∏ k ∈ Finset.range l, ((1 / 4 : ℝ) + ρ ^ 2 + (k * (k + 1) : ℝ))

theorem wl_zero (ρ : ℝ) : wl 0 ρ = 1 := by simp [wl]

theorem wl_succ (l : ℕ) (ρ : ℝ) :
    wl (l + 1) ρ = wl l ρ * ((1 / 4 : ℝ) + ρ ^ 2 + (l * (l + 1) : ℝ)) := by
  simp [wl, Finset.prod_range_succ]

/-- The Plancherel formula for the `K`-type `(l, 0)` of radial functions, with integrability. -/
def KClaim (l : ℕ) : Prop := ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
  IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * ‖sphTransformH F ρ‖ ^ 2)
      (Ioi (0 : ℝ)) ∧
    Real.pi ^ 2 * Kform l F F = (1 / 4 : ℝ) *
      ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * ‖sphTransformH F ρ‖ ^ 2

theorem KClaim_zero : KClaim 0 := by
  intro F hF hc
  refine ⟨?_, ?_⟩
  · simpa [wl_zero] using integrableOn_sph_weight F hF hc
  · have h := norm_sq_eq_sph F hF hc
    have hw : (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl 0 ρ * ‖sphTransformH F ρ‖ ^ 2) =
        fun ρ => ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 := by
      funext ρ; rw [wl_zero, mul_one]
    rw [hw, ← h]
    congr 1
    unfold Kform
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    rw [Complex.conj_mul']
    rw [← Complex.ofReal_pow, Complex.ofReal_re]


/-- **The induction step**: the Plancherel formula for the `K`-type `(l, 0)` implies the one for `(l + 1, 0)`. -/
theorem KClaim_succ {l : ℕ} (h : KClaim l) : KClaim (l + 1) := by
  intro F hF hc
  set G := radialQ F with hGdef
  have hG : ContDiff ℝ ∞ G := contDiff_radialQ hF
  have hGc : HasCompactSupport G := hasCompactSupport_radialQ hc
  have hH : ContDiff ℝ ∞ (F + G) := hF.add hG
  have hHc : HasCompactSupport (F + G) := hc.add hGc
  obtain ⟨iF, eF⟩ := h F hF hc
  obtain ⟨iG, eG⟩ := h G hG hGc
  obtain ⟨iH, eH⟩ := h (F + G) hH hHc
  have hĜ : ∀ ρ : ℝ, sphTransformH G ρ = (((1 / 4 : ℝ) + ρ ^ 2 : ℝ) : ℂ) * sphTransformH F ρ := by
    intro ρ; rw [hGdef, sphTransformH_radialQ hF hc]; push_cast; ring
  have hŜ : ∀ ρ : ℝ, sphTransformH (F + G) ρ =
      (((1 : ℝ) + ((1 / 4 : ℝ) + ρ ^ 2) : ℝ) : ℂ) * sphTransformH F ρ := by
    intro ρ; rw [sphTransformH_add hF hc hG hGc, hĜ]; push_cast; ring
  have nG : ∀ ρ : ℝ, ‖sphTransformH G ρ‖ ^ 2 =
      ((1 / 4 : ℝ) + ρ ^ 2) ^ 2 * ‖sphTransformH F ρ‖ ^ 2 := by
    intro ρ
    rw [hĜ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
  have nH : ∀ ρ : ℝ, ‖sphTransformH (F + G) ρ‖ ^ 2 =
      (1 + ((1 / 4 : ℝ) + ρ ^ 2)) ^ 2 * ‖sphTransformH F ρ‖ ^ 2 := by
    intro ρ
    rw [hŜ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
  simp only [nG] at iG eG
  simp only [nH] at iH eH
  obtain ⟨jM, eM⟩ := polarize measurableSet_Ioi (fun ρ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ)
    (fun ρ => (1 / 4 : ℝ) + ρ ^ 2) (fun ρ => ‖sphTransformH F ρ‖ ^ 2) (π2 := Real.pi ^ 2)
    (Kf := Kform l F F) (Kg := Kform l G G) (Kfg := Kform l F G) (Kh := Kform l (F + G) (F + G))
    iF iG iH eF eG eH (Kform_add_self hF hc hG hGc l)
  have hint : (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl (l + 1) ρ * ‖sphTransformH F ρ‖ ^ 2) =
      fun ρ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2)
        + ((l * (l + 1) : ℝ)) * (ρ * Real.tanh (Real.pi * ρ) * wl l ρ * ‖sphTransformH F ρ‖ ^ 2) := by
    funext ρ; rw [wl_succ]; ring
  refine ⟨?_, ?_⟩
  · rw [hint]; exact jM.add (iF.const_mul _)
  · rw [Kform_succ hF hc l, hint, integral_add jM (iF.const_mul _), integral_const_mul, mul_add,
      mul_add, mul_left_comm (Real.pi ^ 2), eF]
    rw [← hGdef, eM]
    ring


theorem KClaim_all (l : ℕ) : KClaim l := by
  induction l with
  | zero => exact KClaim_zero
  | succ l ih => exact KClaim_succ ih

/-- **Plancherel formula for the radial `K`-types `(l, 0)`**: for `F` smooth with compact support and `l ∈ ℕ`,
`π² ∫_{v>1} (v² - 1)^l |F^{(l)}(v)|² dv = ¼ ∫_{ρ>0} ρ tanh(πρ) ∏_{k<l} ((k + 1/2)² + ρ²) |F^(ρ)|² dρ`.
In the variable `v = cosh ξ` the left side is the `L²(sinh ξ dξ)`-norm of `sinh^l ξ · F^{(l)}(cosh ξ)`, the `l`-fold
ladder image of `F ∘ cosh` (type `(l, 0)`), and the factor `(k + 1/2)² + ρ²` is the ladder factor of the principal series. -/
theorem norm_sq_ktype_eq_sph {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (l : ℕ) :
    Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), (v ^ 2 - 1) ^ l * ‖iteratedDeriv l F v‖ ^ 2 =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) *
        (∏ k ∈ Finset.range l, (((k : ℝ) + 1 / 2) ^ 2 + ρ ^ 2)) * ‖sphTransformH F ρ‖ ^ 2 := by
  have h := (KClaim_all l F hF hc).2
  have hK : Kform l F F = ∫ v in Ioi (1 : ℝ), (v ^ 2 - 1) ^ l * ‖iteratedDeriv l F v‖ ^ 2 := by
    unfold Kform
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hw : ∀ ρ : ℝ, wl l ρ = ∏ k ∈ Finset.range l, (((k : ℝ) + 1 / 2) ^ 2 + ρ ^ 2) := by
    intro ρ; unfold wl
    refine Finset.prod_congr rfl (fun k _ => ?_)
    ring
  rw [← hK, h]
  simp only [hw]

end Lightlike.Lorentz.SL2RPlancherel

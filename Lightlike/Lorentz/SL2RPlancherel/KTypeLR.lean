import Lightlike.Lorentz.SL2RPlancherel.KTypePlancherel
import Lightlike.Lorentz.SL2RPlancherel.LadderRecursion
import Lightlike.Lorentz.SL2RPlancherel.LadderLocal

/-!
# The Plancherel formula for the `K`-types `(l, r)`: the induction step

For `G` smooth with compact support, the ladder image `h_{l,r}[G]` of the profile `sinh^r G^{(r)}(cosh)` is
`sinh^{l+r} ξ · u_l(cosh ξ)` (`hLR_eq`), a function that extends to a smooth function of `ξ ∈ ℝ` vanishing for large `ξ`.
`Nform r l F G = Re ∫_{ξ>0} conj (h_{l,r}[F]) h_{l,r}[G] sinh ξ dξ` is the pairing of the `K`-type `(l, r)`. The step
`Nform r (l+1) F F = Nform r l F (Q F) + l (l+1) Nform r l F F` (`Nform_succ`) is the adjointness of the ladders
(`ladder_adjoint_boundary`), the Casimir factorisation (`ladDown_ladUp_local`) and the Casimir on ladder images
(`radialCasimir_hLR`).
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The closed form `sinh^{l+r} ξ · u_l(cosh ξ)` of the ladder image, defined for every `ξ ∈ ℝ`. -/
def Hc (r : ℕ) (G : ℝ → ℂ) (l : ℕ) (ξ : ℝ) : ℂ :=
  ((Real.sinh ξ ^ (l + r) : ℝ) : ℂ) * uRec r G l (Real.cosh ξ)

/-- `Hc` is the ladder image on `ξ > 0`. -/
theorem Hc_eq_hLR (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    Hc r G l ξ = hLR r G l ξ := (hLR_eq r hG l ξ hξ).symm

/-- `Hc` is continuous on all of `ℝ`. -/
theorem continuous_Hc (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) : Continuous (Hc r G l) := by
  have h1 : Continuous (fun y : ℝ => ((Real.sinh y ^ (l + r) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sinh.pow _)
  have h2 : Continuous (fun y : ℝ => uRec r G l (Real.cosh y)) :=
    ((uRec_contDiffOn r hG l).continuousOn).comp_continuous Real.continuous_cosh
      (fun y => by show (-1 : ℝ) < Real.cosh y; linarith [Real.one_le_cosh y])
  exact h1.mul h2

theorem tsupport_iteratedDeriv_subset (G : ℝ → ℂ) (k : ℕ) :
    tsupport (iteratedDeriv k G) ⊆ tsupport G := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset (f := iteratedDeriv k G)).trans ih

/-- For `G` with compact support, every `uRec` vanishes beyond a common radius. -/
theorem uRec_eq_zero (r : ℕ) {G : ℝ → ℂ} (hc : HasCompactSupport G) :
    ∃ R : ℝ, ∀ l : ℕ, ∀ v : ℝ, R < v → uRec r G l v = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hnot : ∀ v : ℝ, R < v → v ∉ tsupport G := fun v hv hmem => by
    have := hR hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self v]
  refine ⟨R, fun l => ?_⟩
  induction l with
  | zero =>
    intro v hv
    exact image_eq_zero_of_notMem_tsupport (fun h => hnot v hv (tsupport_iteratedDeriv_subset G r h))
  | succ l ih =>
    intro v hv
    have hev : uRec r G l =ᶠ[nhds v] fun _ => 0 :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hv) (fun y hy => ih y hy)
    show deriv (uRec r G l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r G l v = 0
    rw [hev.deriv_eq, ih v hv]
    simp

/-- `cosh ξ ≥ (ξ + 1) / 2`. -/
theorem cosh_ge_half (ξ : ℝ) : (ξ + 1) / 2 ≤ Real.cosh ξ := by
  have h1 := Real.add_one_le_exp ξ
  have h2 : 0 < Real.exp (-ξ) := Real.exp_pos _
  rw [Real.cosh_eq]
  linarith

/-- `Hc` vanishes beyond a common radius. -/
theorem Hc_eq_zero (r : ℕ) {G : ℝ → ℂ} (hc : HasCompactSupport G) :
    ∃ B : ℝ, 0 < B ∧ ∀ l : ℕ, ∀ ξ : ℝ, B ≤ ξ → Hc r G l ξ = 0 := by
  obtain ⟨R, hR⟩ := uRec_eq_zero r hc
  refine ⟨2 * |R| + 2, by positivity, fun l ξ hξ => ?_⟩
  have hcosh := cosh_ge_half ξ
  have hRlt : R < Real.cosh ξ := by
    have := le_abs_self R
    linarith
  simp [Hc, hR l _ hRlt]

/-- The ladder step on the closed forms, on `ξ > 0`. -/
theorem ladUp_Hc (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladUp (l : ℝ) (r : ℝ) (Hc r G l) ξ = Hc r G (l + 1) ξ := by
  have h : Hc r G l =ᶠ[nhds ξ] hLR r G l :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun _ hy => Hc_eq_hLR r hG l hy)
  rw [ladUp_congr _ _ h, Hc_eq_hLR r hG (l + 1) hξ]
  rfl

/-- `Hc` is smooth on `ξ > 0`. -/
theorem contDiffOn_Hc (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ContDiffOn ℝ ∞ (Hc r G l) (Ioi 0) :=
  (contDiffOn_hLR r hG l).congr (fun _ hy => Hc_eq_hLR r hG l hy)

/-- The Casimir of the closed form is the closed form of `Q G`, on `ξ > 0`. -/
theorem radialCasimir_Hc (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    radialCasimir (l : ℝ) (r : ℝ) (Hc r G l) ξ = Hc r (radialQ G) l ξ := by
  have h : Hc r G l =ᶠ[nhds ξ] hLR r G l :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun _ hy => Hc_eq_hLR r hG l hy)
  rw [radialCasimir_congr _ _ h, radialCasimir_hLR r hG l ξ hξ,
    Hc_eq_hLR r (contDiff_radialQ hG) l hξ]

/-- A continuous function: the integral from `a` to `B` depends continuously on `a`. -/
theorem continuous_integral_lower {f : ℝ → ℂ} (hf : Continuous f) (B : ℝ) :
    Continuous (fun a : ℝ => ∫ x in a..B, f x) := by
  have h := (intervalIntegral.continuous_primitive (μ := volume) (fun a b => hf.intervalIntegrable a b) B).neg
  refine h.congr (fun a => ?_)
  simp [intervalIntegral.integral_symm a B]

/-- **The integral identity of the ladder step on `[0, B]`**, with `B` beyond the support:
`∫ |h_{l+1}|² sinh = ∫ h_l conj (h_l[Q F] + l (l+1) h_l) sinh`. -/
theorem step_identity (r : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) {B : ℝ} (hB : 0 < B) (l : ℕ)
    (hBl : ∀ ξ : ℝ, B ≤ ξ → Hc r F l ξ = 0) :
    ∫ ξ in (0 : ℝ)..B, Hc r F (l + 1) ξ * (starRingEnd ℂ) (Hc r F (l + 1) ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in (0 : ℝ)..B, Hc r F l ξ * (starRingEnd ℂ) (Hc r (radialQ F) l ξ
        + ((l * (l + 1) : ℝ) : ℂ) * Hc r F l ξ) * (Real.sinh ξ : ℂ) := by
  set H0 := Hc r F l with hH0
  set H1 := Hc r F (l + 1) with hH1
  set K0 := Hc r (radialQ F) l with hK0
  have c0 : Continuous H0 := continuous_Hc r hF l
  have c1 : Continuous H1 := continuous_Hc r hF (l + 1)
  have cK : Continuous K0 := continuous_Hc r (contDiff_radialQ hF) l
  have cs : Continuous (fun ξ : ℝ => (Real.sinh ξ : ℂ)) := Complex.continuous_ofReal.comp Real.continuous_sinh
  have cc : ∀ g : ℝ → ℂ, Continuous g → Continuous (fun ξ => (starRingEnd ℂ) (g ξ)) :=
    fun g hg => Complex.continuous_conj.comp hg
  have f1c : Continuous (fun ξ : ℝ => H1 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ)) :=
    (c1.mul (cc _ c1)).mul cs
  have f2c : Continuous (fun ξ : ℝ => H0 ξ * (starRingEnd ℂ) (K0 ξ + ((l * (l + 1) : ℝ) : ℂ) * H0 ξ) *
      (Real.sinh ξ : ℂ)) :=
    (c0.mul (cc _ (cK.add (continuous_const.mul c0)))).mul cs
  have bdc : Continuous (fun a : ℝ => H0 a * (starRingEnd ℂ) (H1 a) * (Real.sinh a : ℂ)) :=
    (c0.mul (cc _ c1)).mul cs
  -- the identity for `0 < a ≤ B`
  have key : ∀ a ∈ Ioc (0 : ℝ) B,
      (∫ ξ in a..B, H1 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ)) +
        H0 a * (starRingEnd ℂ) (H1 a) * (Real.sinh a : ℂ) =
      ∫ ξ in a..B, H0 ξ * (starRingEnd ℂ) (K0 ξ + ((l * (l + 1) : ℝ) : ℂ) * H0 ξ) *
        (Real.sinh ξ : ℂ) := by
    intro a ha
    have h0a := ha.1
    have haB := ha.2
    have hpos : ∀ x ∈ uIcc a B, 0 < x := fun x hx => by
      rw [uIcc_of_le haB] at hx; exact lt_of_lt_of_le h0a hx.1
    have hadj := ladder_adjoint_boundary (l : ℝ) (r : ℝ) h0a haB
      (F := H0) (G := H1) ((contDiffOn_Hc r hF l).of_le (by simp))
      ((contDiffOn_Hc r hF (l + 1)).of_le (by simp))
    have hL : (∫ ξ in a..B, ladUp (l : ℝ) (r : ℝ) H0 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ)) =
        ∫ ξ in a..B, H1 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ) :=
      intervalIntegral.integral_congr (fun x hx => by
        show ladUp (l : ℝ) (r : ℝ) H0 x * (starRingEnd ℂ) (H1 x) * (Real.sinh x : ℂ) =
          H1 x * (starRingEnd ℂ) (H1 x) * (Real.sinh x : ℂ)
        rw [show ladUp (l : ℝ) (r : ℝ) H0 x = H1 x from ladUp_Hc r hF l (hpos x hx)])
    have hR : (∫ ξ in a..B, H0 ξ * (starRingEnd ℂ) (ladDown ((l : ℝ) + 1) (r : ℝ) H1 ξ) *
        (Real.sinh ξ : ℂ)) =
        ∫ ξ in a..B, H0 ξ * (starRingEnd ℂ) (K0 ξ + ((l * (l + 1) : ℝ) : ℂ) * H0 ξ) *
          (Real.sinh ξ : ℂ) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hx0 := hpos x hx
      have hev : H1 =ᶠ[nhds x] ladUp (l : ℝ) (r : ℝ) H0 :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx0) (fun y hy => (ladUp_Hc r hF l hy).symm)
      have hld : ladDown ((l : ℝ) + 1) (r : ℝ) H1 x =
          ladDown ((l : ℝ) + 1) (r : ℝ) (ladUp (l : ℝ) (r : ℝ) H0) x := by
        unfold ladDown
        rw [hev.deriv_eq, hev.self_of_nhds]
      rw [hld, ladDown_ladUp_local (l : ℝ) (r : ℝ)
        ((contDiffOn_Hc r hF l).of_le (by simp)) hx0, radialCasimir_Hc r hF l hx0]
    rw [hL, hR] at hadj
    have hBz : H0 B = 0 := hBl B le_rfl
    rw [hBz] at hadj
    simp only [zero_mul] at hadj
    linear_combination hadj
  -- pass to the limit `a → 0`
  have hlim : (∫ ξ in (0 : ℝ)..B, H1 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ)) +
        H0 0 * (starRingEnd ℂ) (H1 0) * (Real.sinh 0 : ℂ) =
      ∫ ξ in (0 : ℝ)..B, H0 ξ * (starRingEnd ℂ) (K0 ξ + ((l * (l + 1) : ℝ) : ℂ) * H0 ξ) *
        (Real.sinh ξ : ℂ) := by
    have e := Set.EqOn.closure (s := Ioc (0 : ℝ) B)
      (f := fun a => (∫ ξ in a..B, H1 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ)) +
        H0 a * (starRingEnd ℂ) (H1 a) * (Real.sinh a : ℂ))
      (g := fun a => ∫ ξ in a..B, H0 ξ * (starRingEnd ℂ) (K0 ξ + ((l * (l + 1) : ℝ) : ℂ) * H0 ξ) *
        (Real.sinh ξ : ℂ))
      key ((continuous_integral_lower f1c B).add bdc) (continuous_integral_lower f2c B)
    have h0 : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) B) := by
      rw [closure_Ioc hB.ne]; exact ⟨le_rfl, hB.le⟩
    exact e h0
  simpa using hlim

/-- The pairing of the `K`-type `(l, r)`: `∫_{ξ>0} Re (conj h_{l,r}[F] · h_{l,r}[G]) sinh ξ dξ`. -/
def Nform (r : ℕ) (l : ℕ) (F G : ℝ → ℂ) : ℝ :=
  ∫ ξ in Ioi (0 : ℝ), ((starRingEnd ℂ) (Hc r F l ξ) * Hc r G l ξ).re * Real.sinh ξ

/-- An integral over `(0, ∞)` of a function vanishing beyond `B` is the integral over `[0, B]`. -/
theorem integral_Ioi_eq_interval {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B) (hf : ∀ ξ : ℝ, B ≤ ξ → f ξ = 0) :
    ∫ ξ in Ioi (0 : ℝ), f ξ = ∫ ξ in (0 : ℝ)..B, f ξ := by
  rw [intervalIntegral.integral_of_le hB.le]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_
  intro ξ hξ
  have hξ' : B ≤ ξ := by
    by_contra h
    exact hξ.2 ⟨hξ.1, le_of_lt (not_le.mp h)⟩
  exact hf ξ hξ'

/-- The real part of an interval integral of a continuous complex function. -/
theorem re_intervalIntegral {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ ξ in a..b, f ξ).re = ∫ ξ in a..b, (f ξ).re := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hi : IntegrableOn f (Ioc a b) := (hf.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  exact (integral_re hi).symm

/-- **The induction step of the `K`-type `(l, r)` recursion**:
`N_{l+1,r}(F, F) = N_{l,r}(F, Q F) + l (l + 1) N_{l,r}(F, F)`. -/
theorem Nform_succ (r : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (l : ℕ) :
    Nform r (l + 1) F F = Nform r l F (radialQ F) + ((l * (l + 1) : ℝ)) * Nform r l F F := by
  obtain ⟨B, hB, hBz⟩ := Hc_eq_zero r hc
  have hE := step_identity r hF hB l (fun ξ hξ => hBz l ξ hξ)
  have hre := congrArg Complex.re hE
  have hQ : ContDiff ℝ ∞ (radialQ F) := contDiff_radialQ hF
  have c0 : Continuous (Hc r F l) := continuous_Hc r hF l
  have c1 : Continuous (Hc r F (l + 1)) := continuous_Hc r hF (l + 1)
  have cK : Continuous (Hc r (radialQ F) l) := continuous_Hc r hQ l
  have cs : Continuous (fun ξ : ℝ => (Real.sinh ξ : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_sinh
  have cc : ∀ g : ℝ → ℂ, Continuous g → Continuous (fun ξ => (starRingEnd ℂ) (g ξ)) :=
    fun g hg => Complex.continuous_conj.comp hg
  have f1c : Continuous (fun ξ : ℝ => Hc r F (l + 1) ξ * (starRingEnd ℂ) (Hc r F (l + 1) ξ) *
      (Real.sinh ξ : ℂ)) := (c1.mul (cc _ c1)).mul cs
  have f2c : Continuous (fun ξ : ℝ => Hc r F l ξ * (starRingEnd ℂ) (Hc r (radialQ F) l ξ
      + ((l * (l + 1) : ℝ) : ℂ) * Hc r F l ξ) * (Real.sinh ξ : ℂ)) :=
    (c0.mul (cc _ (cK.add (continuous_const.mul c0)))).mul cs
  rw [re_intervalIntegral f1c hB.le, re_intervalIntegral f2c hB.le] at hre
  have p1 : ∀ ξ : ℝ, (Hc r F (l + 1) ξ * (starRingEnd ℂ) (Hc r F (l + 1) ξ) * (Real.sinh ξ : ℂ)).re =
      ((starRingEnd ℂ) (Hc r F (l + 1) ξ) * Hc r F (l + 1) ξ).re * Real.sinh ξ := by
    intro ξ
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have p2 : ∀ ξ : ℝ, (Hc r F l ξ * (starRingEnd ℂ) (Hc r (radialQ F) l ξ
      + ((l * (l + 1) : ℝ) : ℂ) * Hc r F l ξ) * (Real.sinh ξ : ℂ)).re =
      ((starRingEnd ℂ) (Hc r F l ξ) * Hc r (radialQ F) l ξ).re * Real.sinh ξ
        + ((l * (l + 1) : ℝ)) * (((starRingEnd ℂ) (Hc r F l ξ) * Hc r F l ξ).re * Real.sinh ξ) := by
    intro ξ
    simp only [map_add, map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  simp only [p1, p2] at hre
  have i1 : ∀ g : ℝ → ℂ, Continuous g → ∀ k : ℕ, Continuous (fun ξ : ℝ => ((starRingEnd ℂ) (Hc r F l ξ) *
      g ξ).re * Real.sinh ξ) := fun g hg k => by
    have := ((cc _ c0).mul hg)
    exact (Complex.continuous_re.comp this).mul Real.continuous_sinh
  have iA : IntervalIntegrable (fun ξ : ℝ => ((starRingEnd ℂ) (Hc r F l ξ) * Hc r (radialQ F) l ξ).re *
      Real.sinh ξ) volume 0 B := (i1 _ cK 0).intervalIntegrable _ _
  have iB : IntervalIntegrable (fun ξ : ℝ => (((starRingEnd ℂ) (Hc r F l ξ) * Hc r F l ξ).re *
      Real.sinh ξ)) volume 0 B := (i1 _ c0 0).intervalIntegrable _ _
  rw [intervalIntegral.integral_add iA (iB.const_mul _), intervalIntegral.integral_const_mul] at hre
  unfold Nform
  rw [integral_Ioi_eq_interval hB (fun ξ hξ => by simp [hBz (l + 1) ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [hBz l ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [hBz l ξ hξ])]
  exact hre

/-- `cosh ξ → ∞` as `ξ → ∞`. -/
theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop :=
  tendsto_atTop_mono cosh_ge_half
    (Filter.Tendsto.atTop_div_const (by norm_num) (tendsto_atTop_add_const_right _ 1 tendsto_id))

/-- A continuous function vanishing beyond `B` is integrable on `[0, ∞)`. -/
theorem integrableOn_Ici_of_zero {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ} (hB : 0 < B)
    (hz : ∀ ξ : ℝ, B ≤ ξ → f ξ = 0) : IntegrableOn f (Ici (0 : ℝ)) := by
  have h1 : IntegrableOn f (Icc (0 : ℝ) B) := hf.integrableOn_Icc
  have h2 : IntegrableOn f (Ioi B) :=
    (integrableOn_zero (s := Ioi B)).congr_fun (fun ξ hξ => (hz ξ hξ.le).symm) measurableSet_Ioi
  have hset : Ici (0 : ℝ) = Icc 0 B ∪ Ioi B := by
    ext x
    simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
    constructor
    · intro hx
      rcases le_or_gt x B with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, _⟩ | h)
      · exact hx
      · linarith
  rw [hset]
  exact h1.union h2

/-- **The `K`-type `(0, r)` pairing is the `K`-type `(r, 0)` pairing** (change of variables `v = cosh ξ`). -/
theorem Nform_zero (r : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Nform r 0 F F = Kform r F F := by
  set g : ℝ → ℝ := fun v => (v ^ 2 - 1) ^ r * ((starRingEnd ℂ) (iteratedDeriv r F v) * iteratedDeriv r F v).re
    with hg
  have gc : Continuous g := by
    have a := (contDiff_iteratedDeriv_infty hF r).continuous
    exact (by fun_prop : Continuous fun v : ℝ => (v ^ 2 - 1) ^ r).mul
      (Complex.continuous_re.comp ((Complex.continuous_conj.comp a).mul a))
  have gcs : HasCompactSupport g := by
    have := (hasCompactSupport_iteratedDeriv hc r).comp_left (g := starRingEnd ℂ) (map_zero _)
    have h3 : HasCompactSupport (fun v : ℝ => starRingEnd ℂ (iteratedDeriv r F v) * iteratedDeriv r F v) :=
      this.mul_right
    exact (h3.comp_left (g := Complex.re) (by simp)).mul_left
  have gi : Integrable g := gc.integrable_of_hasCompactSupport gcs
  obtain ⟨B, hB, hBz⟩ := Hc_eq_zero r hc
  have hpt : ∀ ξ : ℝ, ((starRingEnd ℂ) (Hc r F 0 ξ) * Hc r F 0 ξ).re * Real.sinh ξ =
      (g ∘ Real.cosh) ξ * Real.sinh ξ := by
    intro ξ
    simp only [Function.comp, hg, Hc, uRec, zero_add]
    have : Real.sinh ξ ^ 2 = Real.cosh ξ ^ 2 - 1 := by
      have := Real.cosh_sq ξ; linarith [Real.sinh_sq ξ]
    have hr : ((Real.cosh ξ ^ 2 - 1) ^ r) = (Real.sinh ξ ^ r) ^ 2 := by
      rw [← this, ← pow_mul, ← pow_mul, mul_comm]
    rw [hr]
    simp only [map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hf0 : ∀ ξ : ℝ, B ≤ ξ → ((g ∘ Real.cosh) ξ * Real.sinh ξ) = 0 := by
    intro ξ hξ
    rw [← hpt ξ]
    simp [hBz 0 ξ hξ]
  have hmain := integral_comp_mul_deriv_Ioi (f := Real.cosh) (f' := Real.sinh) (g := g) (a := 0)
    Real.continuous_cosh.continuousOn tendsto_cosh_atTop
    (fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt)
    gc.continuousOn gi.integrableOn
    (integrableOn_Ici_of_zero ((gc.comp Real.continuous_cosh).mul Real.continuous_sinh) hB hf0)
  rw [Real.cosh_zero] at hmain
  unfold Nform Kform
  rw [← hmain]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ξ _ => ?_)
  exact hpt ξ

/-- `uRec` is additive on `v > -1`. -/
theorem uRec_add (r : ℕ) {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ∀ v : ℝ, -1 < v → uRec r (F + G) l v = uRec r F l v + uRec r G l v := by
  induction l with
  | zero =>
    intro v _
    simp only [uRec]
    rw [iteratedDeriv_add_smooth hF hG r]; rfl
  | succ l ih =>
    intro v hv
    have hev : uRec r (F + G) l =ᶠ[nhds v] uRec r F l + uRec r G l :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hv) (fun y hy => ih y hy)
    have dF : DifferentiableAt ℝ (uRec r F l) v :=
      ((uRec_contDiffOn r hF l).differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hv)
    have dG : DifferentiableAt ℝ (uRec r G l) v :=
      ((uRec_contDiffOn r hG l).differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hv)
    show deriv (uRec r (F + G) l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r (F + G) l v =
      (deriv (uRec r F l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r F l v) +
        (deriv (uRec r G l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r G l v)
    rw [hev.deriv_eq, ih v hv, deriv_add dF dG]
    ring

theorem Hc_add (r : ℕ) {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (l : ℕ) (ξ : ℝ) :
    Hc r (F + G) l ξ = Hc r F l ξ + Hc r G l ξ := by
  unfold Hc
  rw [uRec_add r hF hG l _ (by linarith [Real.one_le_cosh ξ]), mul_add]

/-- Additivity of the `K`-type pairing on the diagonal. -/
theorem Nform_add_self (r l : ℕ) {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    Nform r l (F + G) (F + G) = Nform r l F F + Nform r l G G + 2 * Nform r l F G := by
  obtain ⟨B1, hB1, hz1⟩ := Hc_eq_zero r hFc
  obtain ⟨B2, hB2, hz2⟩ := Hc_eq_zero r hGc
  set B := max B1 B2 with hBdef
  have hB : 0 < B := lt_max_of_lt_left hB1
  have z1 : ∀ ξ : ℝ, B ≤ ξ → Hc r F l ξ = 0 := fun ξ hξ => hz1 l ξ (le_trans (le_max_left _ _) hξ)
  have z2 : ∀ ξ : ℝ, B ≤ ξ → Hc r G l ξ = 0 := fun ξ hξ => hz2 l ξ (le_trans (le_max_right _ _) hξ)
  have c1 := continuous_Hc r hF l
  have c2 := continuous_Hc r hG l
  have cc : ∀ g : ℝ → ℂ, Continuous g → Continuous (fun ξ => (starRingEnd ℂ) (g ξ)) :=
    fun g hg => Complex.continuous_conj.comp hg
  have cont : ∀ a b : ℝ → ℂ, Continuous a → Continuous b →
      Continuous (fun ξ : ℝ => ((starRingEnd ℂ) (a ξ) * b ξ).re * Real.sinh ξ) :=
    fun a b ha hb => (Complex.continuous_re.comp ((cc a ha).mul hb)).mul Real.continuous_sinh
  have iFF := (cont _ _ c1 c1).intervalIntegrable (μ := volume) 0 B
  have iGG := (cont _ _ c2 c2).intervalIntegrable (μ := volume) 0 B
  have iFG := (cont _ _ c1 c2).intervalIntegrable (μ := volume) 0 B
  unfold Nform
  have e0 : ∀ ξ : ℝ, ((starRingEnd ℂ) (Hc r (F + G) l ξ) * Hc r (F + G) l ξ).re * Real.sinh ξ =
      ((starRingEnd ℂ) (Hc r F l ξ) * Hc r F l ξ).re * Real.sinh ξ
      + ((starRingEnd ℂ) (Hc r G l ξ) * Hc r G l ξ).re * Real.sinh ξ
      + 2 * (((starRingEnd ℂ) (Hc r F l ξ) * Hc r G l ξ).re * Real.sinh ξ) := by
    intro ξ
    rw [Hc_add r hF hG l ξ]
    simp only [map_add, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hz12 : ∀ ξ : ℝ, B ≤ ξ → ((starRingEnd ℂ) (Hc r (F + G) l ξ) * Hc r (F + G) l ξ).re *
      Real.sinh ξ = 0 := fun ξ hξ => by rw [Hc_add r hF hG l ξ, z1 ξ hξ, z2 ξ hξ]; simp
  rw [integral_Ioi_eq_interval hB hz12,
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [z1 ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [z2 ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [z1 ξ hξ])]
  simp only [e0]
  rw [intervalIntegral.integral_add (iFF.add iGG) (iFG.const_mul 2),
    intervalIntegral.integral_add iFF iGG, intervalIntegral.integral_const_mul]

/-- The Plancherel formula for the `K`-type `(l, r)` of radial functions, with integrability. -/
def LRClaim (r l : ℕ) : Prop := ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
  IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ * ‖sphTransformH F ρ‖ ^ 2)
      (Ioi (0 : ℝ)) ∧
    Real.pi ^ 2 * Nform r l F F = (1 / 4 : ℝ) *
      ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ * ‖sphTransformH F ρ‖ ^ 2

/-- The base `l = 0`: the `K`-type `(0, r) = (r, 0)`. -/
theorem LRClaim_zero (r : ℕ) : LRClaim r 0 := by
  intro F hF hc
  obtain ⟨i, e⟩ := KClaim_all r F hF hc
  have hw : (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl 0 ρ * wl r ρ * ‖sphTransformH F ρ‖ ^ 2) =
      fun ρ => ρ * Real.tanh (Real.pi * ρ) * wl r ρ * ‖sphTransformH F ρ‖ ^ 2 := by
    funext ρ; rw [wl_zero]; ring
  rw [hw]
  exact ⟨i, by rw [Nform_zero r hF hc]; exact e⟩

/-- **The induction step**: the formula for the `K`-type `(l, r)` implies the one for `(l + 1, r)`. -/
theorem LRClaim_succ {r l : ℕ} (h : LRClaim r l) : LRClaim r (l + 1) := by
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
  obtain ⟨jM, eM⟩ := polarize measurableSet_Ioi
    (fun ρ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ)
    (fun ρ => (1 / 4 : ℝ) + ρ ^ 2) (fun ρ => ‖sphTransformH F ρ‖ ^ 2) (π2 := Real.pi ^ 2)
    (Kf := Nform r l F F) (Kg := Nform r l G G) (Kfg := Nform r l F G)
    (Kh := Nform r l (F + G) (F + G)) iF iG iH eF eG eH (Nform_add_self r l hF hc hG hGc)
  have hint : (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl (l + 1) ρ * wl r ρ *
        ‖sphTransformH F ρ‖ ^ 2) =
      fun ρ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ *
          (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2)
        + ((l * (l + 1) : ℝ)) * (ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ *
          ‖sphTransformH F ρ‖ ^ 2) := by
    funext ρ; rw [wl_succ]; ring
  refine ⟨?_, ?_⟩
  · rw [hint]; exact jM.add (iF.const_mul _)
  · rw [Nform_succ r hF hc l, hint, integral_add jM (iF.const_mul _), integral_const_mul, mul_add,
      mul_add, mul_left_comm (Real.pi ^ 2), eF]
    rw [← hGdef, eM]
    ring

/-- The Plancherel formula holds for every `K`-type `(l, r)` of radial functions. -/
theorem LRClaim_all (r l : ℕ) : LRClaim r l := by
  induction l with
  | zero => exact LRClaim_zero r
  | succ l ih => exact LRClaim_succ ih

/-- **Plancherel formula for the `K`-types `(l, r)`** of radial functions: for `G` smooth with compact support,
`π² ∫_{ξ>0} |h_{l,r}[G](ξ)|² sinh ξ dξ = ¼ ∫_{ρ>0} ρ tanh(πρ) w_l(ρ) w_r(ρ) |G^(ρ)|² dρ`, with `h_{l,r}[G]` the
`l`-fold ladder image of `sinh^r ξ · G^{(r)}(cosh ξ)` and `w_n(ρ) = ∏_{k<n} ((k + 1/2)² + ρ²)`. -/
theorem norm_sq_ktype_lr {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (r l : ℕ) :
    Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ), ‖hLR r F l ξ‖ ^ 2 * Real.sinh ξ =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ *
        ‖sphTransformH F ρ‖ ^ 2 := by
  have h := (LRClaim_all r l F hF hc).2
  have hN : Nform r l F F = ∫ ξ in Ioi (0 : ℝ), ‖hLR r F l ξ‖ ^ 2 * Real.sinh ξ := by
    unfold Nform
    refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
    rw [← Hc_eq_hLR r hF l hξ, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← hN]
  exact h

end Lightlike.Lorentz.SL2RPlancherel

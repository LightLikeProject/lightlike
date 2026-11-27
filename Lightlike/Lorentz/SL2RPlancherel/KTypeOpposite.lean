import Lightlike.Lorentz.SL2RPlancherel.KTypeLR
import Lightlike.Lorentz.SL2RPlancherel.LadderOpposite

/-!
# The Plancherel formula for the opposite-sign `K`-types `(l, -s)`: the ladder images

For `G` smooth with compact support, the opposite-sign ladder image `hLRN s G l` (the `l`-fold image of
the profile `sinh^s G^{(s)}(cosh)` under `ladUp k (-s)`) satisfies the same Plancherel identity as the
same-sign one: `π² ∫ |hLRN s G l|² sinh = ¼ ∫ ρ tanh(πρ) w_l(ρ) w_s(ρ) |Ĝ(ρ)|²`
(`norm_sq_ktype_opp`).  The proof is the induction of `KTypeLR.lean` with the closed form `HcN` of
`LadderOpposite.lean` (continuous on `ℝ`, so the boundary terms at the identity vanish) in place of
`Hc`; the Casimir factorisation `ladDown_ladUp_local` has the same shift `l (l + 1)` for every `r`.
These images do not exhaust the block: its orthocomplement is the discrete part (the kernel of the
adjoint chain, `LadderChain.lean`).  Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`,
milestone HA3.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- At `l = 0` the opposite-sign closed form is the same-sign one (the profile). -/
theorem HcN_zero_eq_Hc (s : ℕ) (G : ℝ → ℂ) : HcN s G 0 = Hc s G 0 := by
  funext ξ; simp [HcN, Hc, qRec, uRec]

/-- The ladder step on the opposite-sign closed forms, on `ξ > 0`. -/
theorem ladUp_HcN (s : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladUp (l : ℝ) (-(s : ℝ)) (HcN s G l) ξ = HcN s G (l + 1) ξ := by
  have h : HcN s G l =ᶠ[nhds ξ] hLRN s G l :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun _ hy => HcN_eq_hLRN s hG l hy)
  rw [ladUp_congr _ _ h, HcN_eq_hLRN s hG (l + 1) hξ]
  rfl

/-- `HcN` is smooth on `ξ > 0`. -/
theorem contDiffOn_HcN (s : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ContDiffOn ℝ ∞ (HcN s G l) (Ioi 0) :=
  (contDiffOn_hLRN s hG l).congr (fun _ hy => HcN_eq_hLRN s hG l hy)

/-- The Casimir of the opposite-sign closed form is the closed form of `Q G`, on `ξ > 0`. -/
theorem radialCasimir_HcN (s : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    radialCasimir (l : ℝ) (-(s : ℝ)) (HcN s G l) ξ = HcN s (radialQ G) l ξ := by
  have h : HcN s G l =ᶠ[nhds ξ] hLRN s G l :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun _ hy => HcN_eq_hLRN s hG l hy)
  rw [radialCasimir_congr _ _ h, radialCasimir_hLRN s hG l ξ hξ,
    HcN_eq_hLRN s (contDiff_radialQ hG) l hξ]

/-- `qRec` vanishes where the generator vanishes on a half-line. -/
theorem qRec_eq_zero_of_gt (s : ℕ) {G : ℝ → ℂ} {R : ℝ} (hGR : ∀ v, R < v → G v = 0) (l : ℕ) :
    ∀ v, R < v → qRec s G l v = 0 := by
  induction l with
  | zero =>
    intro v hv
    have hev : G =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using hGR w hw
    simp only [qRec]
    rw [hev.iteratedDeriv_eq]
    simp
  | succ l ih =>
    intro v hv
    have hev : qRec s G l =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using ih w hw
    simp only [qRec]
    rw [hev.deriv_eq, ih v hv]
    simp

/-- The opposite-sign closed forms vanish for large `ξ`. -/
theorem HcN_eq_zero (s : ℕ) {G : ℝ → ℂ} (hc : HasCompactSupport G) :
    ∃ B : ℝ, 0 < B ∧ ∀ l : ℕ, ∀ ξ : ℝ, B ≤ ξ → HcN s G l ξ = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hGR : ∀ v, R < v → G v = 0 := fun v hv => image_eq_zero_of_notMem_tsupport fun h => by
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self v]
  refine ⟨2 * |R| + 2, by positivity, fun l ξ hξ => ?_⟩
  have hcosh := cosh_ge_half ξ
  have hRlt : R < Real.cosh ξ := by
    have := le_abs_self R
    linarith
  unfold HcN
  split_ifs
  · simp [qRec_eq_zero_of_gt s hGR l _ hRlt]
  · have hev : qRec s G s =ᶠ[𝓝 (Real.cosh ξ)] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hRlt] with w hw using qRec_eq_zero_of_gt s hGR s w hw
    rw [hev.iteratedDeriv_eq]
    simp

/-- `qRec` is additive. -/
theorem qRec_add (s : ℕ) {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    qRec s (F + G) l = qRec s F l + qRec s G l := by
  induction l with
  | zero => simp only [qRec]; exact iteratedDeriv_add_smooth hF hG s
  | succ l ih =>
    funext v
    have dF := ((contDiff_qRec s hF l).differentiable (by simp)) v
    have dG := ((contDiff_qRec s hG l).differentiable (by simp)) v
    simp only [qRec, Pi.add_apply]
    rw [ih, Pi.add_apply, deriv_add dF dG]
    ring

/-- `HcN` is additive. -/
theorem HcN_add (s : ℕ) {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (l : ℕ) (ξ : ℝ) :
    HcN s (F + G) l ξ = HcN s F l ξ + HcN s G l ξ := by
  unfold HcN
  split_ifs
  · rw [qRec_add s hF hG l, Pi.add_apply, mul_add]
  · rw [qRec_add s hF hG s, iteratedDeriv_add_smooth (contDiff_qRec s hF s) (contDiff_qRec s hG s),
      Pi.add_apply, mul_add]

/-- **The integral identity of the ladder step on `[0, B]`**, with `B` beyond the support:
`∫ |h_{l+1}|² sinh = ∫ h_l conj (h_l[Q F] + l (l+1) h_l) sinh`. -/
theorem step_identityN (s : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) {B : ℝ} (hB : 0 < B) (l : ℕ)
    (hBl : ∀ ξ : ℝ, B ≤ ξ → HcN s F l ξ = 0) :
    ∫ ξ in (0 : ℝ)..B, HcN s F (l + 1) ξ * (starRingEnd ℂ) (HcN s F (l + 1) ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in (0 : ℝ)..B, HcN s F l ξ * (starRingEnd ℂ) (HcN s (radialQ F) l ξ
        + ((l * (l + 1) : ℝ) : ℂ) * HcN s F l ξ) * (Real.sinh ξ : ℂ) := by
  set H0 := HcN s F l with hH0
  set H1 := HcN s F (l + 1) with hH1
  set K0 := HcN s (radialQ F) l with hK0
  have c0 : Continuous H0 := continuous_HcN s hF l
  have c1 : Continuous H1 := continuous_HcN s hF (l + 1)
  have cK : Continuous K0 := continuous_HcN s (contDiff_radialQ hF) l
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
    have hadj := ladder_adjoint_boundary (l : ℝ) (-(s : ℝ)) h0a haB
      (F := H0) (G := H1) ((contDiffOn_HcN s hF l).of_le (by simp))
      ((contDiffOn_HcN s hF (l + 1)).of_le (by simp))
    have hL : (∫ ξ in a..B, ladUp (l : ℝ) (-(s : ℝ)) H0 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ)) =
        ∫ ξ in a..B, H1 ξ * (starRingEnd ℂ) (H1 ξ) * (Real.sinh ξ : ℂ) :=
      intervalIntegral.integral_congr (fun x hx => by
        show ladUp (l : ℝ) (-(s : ℝ)) H0 x * (starRingEnd ℂ) (H1 x) * (Real.sinh x : ℂ) =
          H1 x * (starRingEnd ℂ) (H1 x) * (Real.sinh x : ℂ)
        rw [show ladUp (l : ℝ) (-(s : ℝ)) H0 x = H1 x from ladUp_HcN s hF l (hpos x hx)])
    have hR : (∫ ξ in a..B, H0 ξ * (starRingEnd ℂ) (ladDown ((l : ℝ) + 1) (-(s : ℝ)) H1 ξ) *
        (Real.sinh ξ : ℂ)) =
        ∫ ξ in a..B, H0 ξ * (starRingEnd ℂ) (K0 ξ + ((l * (l + 1) : ℝ) : ℂ) * H0 ξ) *
          (Real.sinh ξ : ℂ) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hx0 := hpos x hx
      have hev : H1 =ᶠ[nhds x] ladUp (l : ℝ) (-(s : ℝ)) H0 :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx0) (fun y hy => (ladUp_HcN s hF l hy).symm)
      have hld : ladDown ((l : ℝ) + 1) (-(s : ℝ)) H1 x =
          ladDown ((l : ℝ) + 1) (-(s : ℝ)) (ladUp (l : ℝ) (-(s : ℝ)) H0) x := by
        unfold ladDown
        rw [hev.deriv_eq, hev.self_of_nhds]
      rw [hld, ladDown_ladUp_local (l : ℝ) (-(s : ℝ))
        ((contDiffOn_HcN s hF l).of_le (by simp)) hx0, radialCasimir_HcN s hF l hx0]
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


/-- The pairing of the `K`-type `(l, -s)`: `∫_{ξ>0} Re (conj h_{l,-s}[F] · h_{l,-s}[G]) sinh ξ dξ`. -/
def NformN (s : ℕ) (l : ℕ) (F G : ℝ → ℂ) : ℝ :=
  ∫ ξ in Ioi (0 : ℝ), ((starRingEnd ℂ) (HcN s F l ξ) * HcN s G l ξ).re * Real.sinh ξ

/-- At `l = 0` the opposite-sign pairing is the same-sign one. -/
theorem NformN_zero_eq {s : ℕ} {F G : ℝ → ℂ} : NformN s 0 F G = Nform s 0 F G := by
  unfold NformN Nform
  rw [HcN_zero_eq_Hc, HcN_zero_eq_Hc]


/-- **The induction step of the `K`-type `(l, -s)` recursion**:
`N_{l+1,s}(F, F) = N_{l,s}(F, Q F) + l (l + 1) N_{l,s}(F, F)`. -/
theorem NformN_succ (s : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (l : ℕ) :
    NformN s (l + 1) F F = NformN s l F (radialQ F) + ((l * (l + 1) : ℝ)) * NformN s l F F := by
  obtain ⟨B, hB, hBz⟩ := HcN_eq_zero s hc
  have hE := step_identityN s hF hB l (fun ξ hξ => hBz l ξ hξ)
  have hre := congrArg Complex.re hE
  have hQ : ContDiff ℝ ∞ (radialQ F) := contDiff_radialQ hF
  have c0 : Continuous (HcN s F l) := continuous_HcN s hF l
  have c1 : Continuous (HcN s F (l + 1)) := continuous_HcN s hF (l + 1)
  have cK : Continuous (HcN s (radialQ F) l) := continuous_HcN s hQ l
  have cs : Continuous (fun ξ : ℝ => (Real.sinh ξ : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_sinh
  have cc : ∀ g : ℝ → ℂ, Continuous g → Continuous (fun ξ => (starRingEnd ℂ) (g ξ)) :=
    fun g hg => Complex.continuous_conj.comp hg
  have f1c : Continuous (fun ξ : ℝ => HcN s F (l + 1) ξ * (starRingEnd ℂ) (HcN s F (l + 1) ξ) *
      (Real.sinh ξ : ℂ)) := (c1.mul (cc _ c1)).mul cs
  have f2c : Continuous (fun ξ : ℝ => HcN s F l ξ * (starRingEnd ℂ) (HcN s (radialQ F) l ξ
      + ((l * (l + 1) : ℝ) : ℂ) * HcN s F l ξ) * (Real.sinh ξ : ℂ)) :=
    (c0.mul (cc _ (cK.add (continuous_const.mul c0)))).mul cs
  rw [re_intervalIntegral f1c hB.le, re_intervalIntegral f2c hB.le] at hre
  have p1 : ∀ ξ : ℝ, (HcN s F (l + 1) ξ * (starRingEnd ℂ) (HcN s F (l + 1) ξ) * (Real.sinh ξ : ℂ)).re =
      ((starRingEnd ℂ) (HcN s F (l + 1) ξ) * HcN s F (l + 1) ξ).re * Real.sinh ξ := by
    intro ξ
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have p2 : ∀ ξ : ℝ, (HcN s F l ξ * (starRingEnd ℂ) (HcN s (radialQ F) l ξ
      + ((l * (l + 1) : ℝ) : ℂ) * HcN s F l ξ) * (Real.sinh ξ : ℂ)).re =
      ((starRingEnd ℂ) (HcN s F l ξ) * HcN s (radialQ F) l ξ).re * Real.sinh ξ
        + ((l * (l + 1) : ℝ)) * (((starRingEnd ℂ) (HcN s F l ξ) * HcN s F l ξ).re * Real.sinh ξ) := by
    intro ξ
    simp only [map_add, map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  simp only [p1, p2] at hre
  have i1 : ∀ g : ℝ → ℂ, Continuous g → ∀ k : ℕ, Continuous (fun ξ : ℝ => ((starRingEnd ℂ) (HcN s F l ξ) *
      g ξ).re * Real.sinh ξ) := fun g hg k => by
    have := ((cc _ c0).mul hg)
    exact (Complex.continuous_re.comp this).mul Real.continuous_sinh
  have iA : IntervalIntegrable (fun ξ : ℝ => ((starRingEnd ℂ) (HcN s F l ξ) * HcN s (radialQ F) l ξ).re *
      Real.sinh ξ) volume 0 B := (i1 _ cK 0).intervalIntegrable _ _
  have iB : IntervalIntegrable (fun ξ : ℝ => (((starRingEnd ℂ) (HcN s F l ξ) * HcN s F l ξ).re *
      Real.sinh ξ)) volume 0 B := (i1 _ c0 0).intervalIntegrable _ _
  rw [intervalIntegral.integral_add iA (iB.const_mul _), intervalIntegral.integral_const_mul] at hre
  unfold NformN
  rw [integral_Ioi_eq_interval hB (fun ξ hξ => by simp [hBz (l + 1) ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [hBz l ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [hBz l ξ hξ])]
  exact hre


theorem NformN_add_self (s l : ℕ) {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    NformN s l (F + G) (F + G) = NformN s l F F + NformN s l G G + 2 * NformN s l F G := by
  obtain ⟨B1, hB1, hz1⟩ := HcN_eq_zero s hFc
  obtain ⟨B2, hB2, hz2⟩ := HcN_eq_zero s hGc
  set B := max B1 B2 with hBdef
  have hB : 0 < B := lt_max_of_lt_left hB1
  have z1 : ∀ ξ : ℝ, B ≤ ξ → HcN s F l ξ = 0 := fun ξ hξ => hz1 l ξ (le_trans (le_max_left _ _) hξ)
  have z2 : ∀ ξ : ℝ, B ≤ ξ → HcN s G l ξ = 0 := fun ξ hξ => hz2 l ξ (le_trans (le_max_right _ _) hξ)
  have c1 := continuous_HcN s hF l
  have c2 := continuous_HcN s hG l
  have cc : ∀ g : ℝ → ℂ, Continuous g → Continuous (fun ξ => (starRingEnd ℂ) (g ξ)) :=
    fun g hg => Complex.continuous_conj.comp hg
  have cont : ∀ a b : ℝ → ℂ, Continuous a → Continuous b →
      Continuous (fun ξ : ℝ => ((starRingEnd ℂ) (a ξ) * b ξ).re * Real.sinh ξ) :=
    fun a b ha hb => (Complex.continuous_re.comp ((cc a ha).mul hb)).mul Real.continuous_sinh
  have iFF := (cont _ _ c1 c1).intervalIntegrable (μ := volume) 0 B
  have iGG := (cont _ _ c2 c2).intervalIntegrable (μ := volume) 0 B
  have iFG := (cont _ _ c1 c2).intervalIntegrable (μ := volume) 0 B
  unfold NformN
  have e0 : ∀ ξ : ℝ, ((starRingEnd ℂ) (HcN s (F + G) l ξ) * HcN s (F + G) l ξ).re * Real.sinh ξ =
      ((starRingEnd ℂ) (HcN s F l ξ) * HcN s F l ξ).re * Real.sinh ξ
      + ((starRingEnd ℂ) (HcN s G l ξ) * HcN s G l ξ).re * Real.sinh ξ
      + 2 * (((starRingEnd ℂ) (HcN s F l ξ) * HcN s G l ξ).re * Real.sinh ξ) := by
    intro ξ
    rw [HcN_add s hF hG l ξ]
    simp only [map_add, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hz12 : ∀ ξ : ℝ, B ≤ ξ → ((starRingEnd ℂ) (HcN s (F + G) l ξ) * HcN s (F + G) l ξ).re *
      Real.sinh ξ = 0 := fun ξ hξ => by rw [HcN_add s hF hG l ξ, z1 ξ hξ, z2 ξ hξ]; simp
  rw [integral_Ioi_eq_interval hB hz12,
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [z1 ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [z2 ξ hξ]),
    integral_Ioi_eq_interval hB (fun ξ hξ => by simp [z1 ξ hξ])]
  simp only [e0]
  rw [intervalIntegral.integral_add (iFF.add iGG) (iFG.const_mul 2),
    intervalIntegral.integral_add iFF iGG, intervalIntegral.integral_const_mul]


/-- The Plancherel formula for the `K`-type `(l, -s)` of radial functions, with integrability. -/
def LRClaimN (s l : ℕ) : Prop := ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
  IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ * ‖sphTransformH F ρ‖ ^ 2)
      (Ioi (0 : ℝ)) ∧
    Real.pi ^ 2 * NformN s l F F = (1 / 4 : ℝ) *
      ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ * ‖sphTransformH F ρ‖ ^ 2


/-- The base `l = 0`: the opposite-sign block `(0, -s)` is the block `(0, s)`. -/
theorem LRClaimN_zero (s : ℕ) : LRClaimN s 0 := by
  intro F hF hc
  obtain ⟨i, e⟩ := LRClaim_zero s F hF hc
  exact ⟨i, by rw [NformN_zero_eq]; exact e⟩

/-- **The induction step**: the formula for the `K`-type `(l, -s)` implies the one for `(l + 1, -s)`. -/
theorem LRClaimN_succ {s l : ℕ} (h : LRClaimN s l) : LRClaimN s (l + 1) := by
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
    (fun ρ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ)
    (fun ρ => (1 / 4 : ℝ) + ρ ^ 2) (fun ρ => ‖sphTransformH F ρ‖ ^ 2) (π2 := Real.pi ^ 2)
    (Kf := NformN s l F F) (Kg := NformN s l G G) (Kfg := NformN s l F G)
    (Kh := NformN s l (F + G) (F + G)) iF iG iH eF eG eH (NformN_add_self s l hF hc hG hGc)
  have hint : (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl (l + 1) ρ * wl s ρ *
        ‖sphTransformH F ρ‖ ^ 2) =
      fun ρ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ *
          (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2)
        + ((l * (l + 1) : ℝ)) * (ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ *
          ‖sphTransformH F ρ‖ ^ 2) := by
    funext ρ; rw [wl_succ]; ring
  refine ⟨?_, ?_⟩
  · rw [hint]; exact jM.add (iF.const_mul _)
  · rw [NformN_succ s hF hc l, hint, integral_add jM (iF.const_mul _), integral_const_mul, mul_add,
      mul_add, mul_left_comm (Real.pi ^ 2), eF]
    rw [← hGdef, eM]
    ring

/-- The Plancherel formula holds for every `K`-type `(l, -s)` of radial functions. -/
theorem LRClaimN_all (s l : ℕ) : LRClaimN s l := by
  induction l with
  | zero => exact LRClaimN_zero s
  | succ l ih => exact LRClaimN_succ ih

/-- **Plancherel formula for the `K`-types `(l, -s)`** of radial functions: for `G` smooth with compact support,
`π² ∫_{ξ>0} |h_{l,-s}[G](ξ)|² sinh ξ dξ = ¼ ∫_{ρ>0} ρ tanh(πρ) w_l(ρ) w_s(ρ) |G^(ρ)|² dρ`, with `h_{l,-s}[G]` the
`l`-fold ladder image of `sinh^s ξ · G^{(s)}(cosh ξ)` and `w_n(ρ) = ∏_{k<n} ((k + 1/2)² + ρ²)`. -/
theorem norm_sq_ktype_opp {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (s l : ℕ) :
    Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ), ‖hLRN s F l ξ‖ ^ 2 * Real.sinh ξ =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ *
        ‖sphTransformH F ρ‖ ^ 2 := by
  have h := (LRClaimN_all s l F hF hc).2
  have hN : NformN s l F F = ∫ ξ in Ioi (0 : ℝ), ‖hLRN s F l ξ‖ ^ 2 * Real.sinh ξ := by
    unfold NformN
    refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
    rw [← HcN_eq_hLRN s hF l hξ, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← hN]
  exact h


/-- Non-vacuity: `norm_sq_ktype_opp` applies to the zero generator for every opposite-sign block. -/
example (s l : ℕ) :
    Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ), ‖hLRN s (fun _ => (0 : ℂ)) l ξ‖ ^ 2 * Real.sinh ξ =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ *
        ‖sphTransformH (fun _ => (0 : ℂ)) ρ‖ ^ 2 :=
  norm_sq_ktype_opp contDiff_const HasCompactSupport.zero s l

end Lightlike.Lorentz.SL2RPlancherel

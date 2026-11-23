import Lightlike.Upstream.GeodesicExpansion.ExpansionLocal
import Mathlib

/-!
# The expansion of the squared distance: the lower bound

For a Riemannian coordinate metric `g` on an open `U ⊆ ℝⁿ`, the quartic jet
`F_x(w) = distJet g x w` of `Expansion.lean` bounds the chart distance from below
(calibration): `√F_x` grows along any `C¹` curve at most `1 + κ ρ³` times as fast as its
`g`-length (`LocalJet.abs_distJetDeriv_le`), so a curve from `x` to `x + w` that stays in the ball
of radius `ρ = A ‖w‖` has length at least `√F_x(w) / (1 + κ ρ³)`; a curve that leaves the ball has
length at least `√l ρ`, which is more.

## Main declarations

* `LocalJet.sqrt_le_length_of_calib`: calibration along a curve, for any calibrated jet
* `LocalJet.sqrt_distJet_le_length`
* `LocalJet.length_ge_of_exit`
* `LocalJet.sqrt_distJet_le_dist`: `√F_x(w) ≤ (1 + κ (A ‖w‖)³) d(x, x + w)`
-/

open Matrix Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The jet vanishes at `w = 0`. -/
theorem distJet_zero (x : Fin n → ℝ) : distJet g x 0 = 0 := by
  simp [distJet, chr_zero_left, dmat_zero, ddmat_zero_left]

/-- A lower bound `a ≤ k L(c)` for the length of every admissible curve from `x` to `y` gives
`a ≤ k d(x, y)`, provided some admissible curve exists. -/
theorem le_mul_chartDist_of_le_mul_length {a k : ℝ} (hk : 0 < k) {x y : Fin n → ℝ}
    (hne : ∃ c, IsAdmissible U c x y)
    (hlen : ∀ c, IsAdmissible U c x y → a ≤ k * length g c 0 1) : a ≤ k * chartDist g U x y := by
  rw [← div_le_iff₀' hk]
  obtain ⟨c₀, hc₀⟩ := hne
  refine le_csInf ⟨_, c₀, hc₀, rfl⟩ ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [div_le_iff₀' hk]
  exact hlen c hc

namespace LocalJet

variable {x : Fin n → ℝ} {B δ l : ℝ}

/-- Where `B³ ‖u‖ ≤ l / 2`, the jet is at least `(l / 2) ‖u‖²`. -/
theorem distJet_ge_half (h : LocalJet g U x B δ l) {u : Fin n → ℝ} (hu : ‖u‖ ≤ 1)
    (hul : B ^ 3 * ‖u‖ ≤ l / 2) : l / 2 * ‖u‖ ^ 2 ≤ distJet g x u := by
  have h1 := h.distJet_ge hu
  have h2 : B ^ 3 * ‖u‖ ^ 3 ≤ l / 2 * ‖u‖ ^ 2 :=
    calc B ^ 3 * ‖u‖ ^ 3 = B ^ 3 * ‖u‖ * ‖u‖ ^ 2 := by ring
      _ ≤ l / 2 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hul (sq_nonneg _)
  linarith

/-- **Calibration along a curve, for any calibrated jet.** Let `Φ` vanish at `0`, have derivative
`Φ'` along curves, and on the ball of radius `ρ ≤ δ` be nonnegative and calibrated with constant
`k ≥ 0`: `|Φ'(u)(v)| ≤ 2 √Φ(u) ‖v‖_{g(x+u)} k`. Then a `C¹` curve starting at `x` that stays in the
ball of radius `ρ` about `x` has length at least `√Φ(c T - x) / k` on `[0, T]`. -/
theorem sqrt_le_length_of_calib (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l)
    {Φ : (Fin n → ℝ) → ℝ} {Φ' : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hΦd : ∀ {W : ℝ → Fin n → ℝ} {W' : Fin n → ℝ} {t : ℝ}, HasDerivAt W W' t →
      HasDerivAt (fun s => Φ (W s)) (Φ' (W t) W') t)
    (hΦ0 : Φ 0 = 0) {ρ k : ℝ} (hk : 0 ≤ k) (hρ : ρ ≤ δ)
    (hpos : ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → 0 ≤ Φ u)
    (hcal : ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → ∀ v,
      |Φ' u v| ≤ 2 * √(Φ u) * √(normSq g (x + u) v) * k)
    {c : ℝ → Fin n → ℝ} (hc : ContDiff ℝ 1 c) (hc0 : c 0 = x) {T : ℝ} (hT : 0 ≤ T)
    (hball : ∀ t ∈ Icc 0 T, ‖c t - x‖ ≤ ρ) :
    √(Φ (c T - x)) ≤ k * length g c 0 T := by
  have hdiff : Differentiable ℝ c := hc.differentiable one_ne_zero
  have hF : ∀ t, HasDerivAt (fun s => Φ (c s - x)) (Φ' (c t - x) (deriv c t)) t :=
    fun t => hΦd ((hdiff t).hasDerivAt.sub_const x)
  have hu : ∀ t ∈ Icc 0 T, ‖c t - x‖ ≤ δ := fun t ht => (hball t ht).trans hρ
  have hF0 : ∀ t ∈ Icc 0 T, 0 ≤ Φ (c t - x) := fun t ht => hpos _ (hball t ht)
  have hmem : ∀ t ∈ Icc 0 T, c t ∈ U := fun t ht => by
    simpa using h.mem _ (hu t ht)
  have hspeed : ContinuousOn (fun t => √(normSq g (c t) (deriv c t))) (Icc 0 T) :=
    (hg.continuousOn_normSq.comp
      ((hc.continuous.prodMk (hc.continuous_deriv le_rfl)).continuousOn)
      (fun t ht => mk_mem_prod (hmem t ht) (mem_univ _))).sqrt
  have key : ∀ η : ℝ, 0 < η → √(Φ (c T - x)) ≤ η + k * length g c 0 T := by
    intro η hη
    have hpos' : ∀ t ∈ Icc 0 T, 0 < Φ (c t - x) + η ^ 2 := fun t ht => by
      have := hF0 t ht; positivity
    have hφ : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => √(Φ (c s - x) + η ^ 2))
        (Φ' (c t - x) (deriv c t) / (2 * √(Φ (c t - x) + η ^ 2))) t :=
      fun t ht => ((hF t).add_const _).sqrt (hpos' t (Ioo_subset_Icc_self ht)).ne'
    have hcont : ContinuousOn (fun s => √(Φ (c s - x) + η ^ 2)) (Icc 0 T) :=
      fun t _ => (((hF t).continuousAt.add continuousAt_const).sqrt).continuousWithinAt
    have hbd : ∀ t ∈ Ioo 0 T, Φ' (c t - x) (deriv c t) /
        (2 * √(Φ (c t - x) + η ^ 2)) ≤ k * √(normSq g (c t) (deriv c t)) := by
      intro t ht
      have ht' := Ioo_subset_Icc_self ht
      have hd := hcal _ (hball t ht') (deriv c t)
      rw [add_sub_cancel] at hd
      have hs : 0 < √(Φ (c t - x) + η ^ 2) := Real.sqrt_pos.2 (hpos' t ht')
      have hFs : √(Φ (c t - x)) ≤ √(Φ (c t - x) + η ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rw [div_le_iff₀ (by positivity)]
      calc Φ' (c t - x) (deriv c t)
          ≤ |Φ' (c t - x) (deriv c t)| := le_abs_self _
        _ ≤ 2 * √(Φ (c t - x)) * √(normSq g (c t) (deriv c t)) * k := hd
        _ ≤ 2 * √(Φ (c t - x) + η ^ 2) * √(normSq g (c t) (deriv c t)) * k := by
          gcongr
        _ = _ := by ring
    have hint : IntegrableOn (fun t => k * √(normSq g (c t) (deriv c t))) (Icc 0 T) :=
      (continuousOn_const.mul hspeed).integrableOn_Icc
    have hI := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hT hcont
      (fun t ht => (hφ t ht).hasDerivWithinAt) hint hbd
    rw [intervalIntegral.integral_const_mul] at hI
    simp only [hc0, sub_self, hΦ0, zero_add, Real.sqrt_sq hη.le] at hI
    have hle : √(Φ (c T - x)) ≤ √(Φ (c T - x) + η ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    unfold length
    linarith
  by_contra hlt
  rw [not_le] at hlt
  have := key ((√(Φ (c T - x)) - k * length g c 0 T) / 2) (by linarith)
  linarith

/-- On the ball of radius `ρ ≤ δ` with `B³ ρ ≤ l / 2`, the quartic jet `F_x` is nonnegative and
calibrated with constant `1 + κ ρ³` (`κ = calibConst B l`). -/
theorem distJet_calib (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l) {ρ : ℝ} (hρ : ρ ≤ δ)
    (hρl : B ^ 3 * ρ ≤ l / 2) :
    (∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → 0 ≤ distJet g x u) ∧
      ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → ∀ v, |distJetDeriv g x u v| ≤
        2 * √(distJet g x u) * √(normSq g (x + u) v) * (1 + calibConst B l * ρ ^ 3) := by
  have hκ := calibConst_nonneg h.B_nonneg h.l_pos
  have hul : ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → B ^ 3 * ‖u‖ ≤ l / 2 := fun u hu =>
    (mul_le_mul_of_nonneg_left hu (pow_nonneg h.B_nonneg 3)).trans hρl
  refine ⟨fun u hu => le_trans (by have := h.l_pos; positivity)
    (h.distJet_ge_half ((hu.trans hρ).trans h.δ_le_one) (hul u hu)), fun u hu v => ?_⟩
  refine (h.abs_distJetDeriv_le hg (hu.trans hρ) (hul u hu) v).trans ?_
  have := pow_le_pow_left₀ (norm_nonneg _) hu 3
  gcongr

/-- **Calibration along a curve**: a `C¹` curve starting at `x` that stays in the ball of radius
`ρ` about `x` (with `ρ ≤ δ` and `B³ ρ ≤ l / 2`) has length at least `√F_x(c T - x) / (1 + κ ρ³)`
on `[0, T]`, where `κ = calibConst B l`. -/
theorem sqrt_distJet_le_length (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l) {ρ : ℝ}
    (hρ : ρ ≤ δ) (hρl : B ^ 3 * ρ ≤ l / 2) {c : ℝ → Fin n → ℝ} (hc : ContDiff ℝ 1 c)
    (hc0 : c 0 = x) {T : ℝ} (hT : 0 ≤ T) (hball : ∀ t ∈ Icc 0 T, ‖c t - x‖ ≤ ρ) :
    √(distJet g x (c T - x)) ≤ (1 + calibConst B l * ρ ^ 3) * length g c 0 T := by
  have hκ := calibConst_nonneg h.B_nonneg h.l_pos
  have hρ0 : 0 ≤ ρ := by simpa [hc0] using hball 0 ⟨le_rfl, hT⟩
  obtain ⟨hpos, hcal⟩ := h.distJet_calib hg hρ hρl
  exact h.sqrt_le_length_of_calib hg (fun hW => hasDerivAt_distJet x hW) (distJet_zero x)
    (by positivity) hρ hpos hcal hc hc0 hT hball

/-- **Leaving the ball costs length**: an admissible curve from `x` that reaches the sphere of
radius `ρ ≤ δ` about `x` has length at least `√l ρ`. -/
theorem length_ge_of_exit (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ : ρ ≤ δ) {c : ℝ → Fin n → ℝ} {y : Fin n → ℝ}
    (hc : IsAdmissible U c x y) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hexit : ρ ≤ ‖c t₀ - x‖) : √l * ρ ≤ length g c 0 1 := by
  have hcont : Continuous fun t => ‖c t - x‖ := (hc.smooth.continuous.sub continuous_const).norm
  set S := Icc (0 : ℝ) 1 ∩ {t | ρ ≤ ‖c t - x‖} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hcont)
  have hSne : S.Nonempty := ⟨t₀, ht₀, hexit⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set t₁ := sInf S with ht₁def
  have ht₁ : t₁ ∈ S := hSc.csInf_mem hSne hSb
  have ht₁ρ : ρ ≤ ‖c t₁ - x‖ := ht₁.2
  have ht₁0 : t₁ ≠ 0 := by
    intro h0
    rw [h0, hc.start, sub_self, norm_zero] at ht₁ρ
    linarith
  have hin : Ico 0 t₁ ⊆ {t | ‖c t - x‖ ≤ ρ} := by
    intro t ht
    by_contra hlt
    change ¬ ‖c t - x‖ ≤ ρ at hlt
    rw [not_le] at hlt
    have : t₁ ≤ t := csInf_le hSb ⟨⟨ht.1, ht.2.le.trans ht₁.1.2⟩, hlt.le⟩
    linarith [ht.2]
  have hin' : Icc 0 t₁ ⊆ {t | ‖c t - x‖ ≤ ρ} := by
    have := (isClosed_le hcont continuous_const).closure_subset_iff.2 hin
    rwa [closure_Ico (Ne.symm ht₁0)] at this
  have hbd : ∀ t ∈ Icc 0 t₁, ∀ v, l * eNormSq v ≤ normSq g (c t) v := fun t ht v => by
    simpa using h.low _ ((hin' ht).trans hρ) v
  have hint := (hg.intervalIntegrable_speed hc).mono_set (by
    rw [uIcc_of_le ht₁.1.1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht₁.1.2)
  have h1 := length_ge_of_bounds hc.smooth ht₁.1.1 h.l_pos.le hbd hint
  rw [hc.start] at h1
  have h2 : length g c 0 t₁ ≤ length g c 0 1 :=
    intervalIntegral.integral_mono_interval le_rfl ht₁.1.1 ht₁.1.2
      (ae_of_all _ fun _ => Real.sqrt_nonneg _) (hg.intervalIntegrable_speed hc)
  have h3 : ρ ≤ √(eNormSq (c t₁ - x)) := by
    have := Real.sqrt_le_sqrt (norm_sq_le_eNormSq (c t₁ - x))
    rw [Real.sqrt_sq (norm_nonneg _)] at this
    exact ht₁ρ.trans this
  calc √l * ρ ≤ √l * √(eNormSq (c t₁ - x)) := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ ≤ _ := h1.trans h2

/-- **The lower bound for one curve, for any calibrated jet**: if `Φ` is calibrated with constant
`k ≥ 1` on the ball of radius `ρ` (as in `sqrt_le_length_of_calib`) and `Φ(w) ≤ l ρ²`, then every
admissible curve from `x` to `x + w` has length at least `√Φ(w) / k`. A curve that leaves the ball
is longer than `√l ρ ≥ √Φ(w)`. -/
theorem sqrt_le_length_of_calib_admissible (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l)
    {Φ : (Fin n → ℝ) → ℝ} {Φ' : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hΦd : ∀ {W : ℝ → Fin n → ℝ} {W' : Fin n → ℝ} {t : ℝ}, HasDerivAt W W' t →
      HasDerivAt (fun s => Φ (W s)) (Φ' (W t) W') t)
    (hΦ0 : Φ 0 = 0) {ρ k : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ δ) (hk1 : 1 ≤ k)
    (hpos : ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → 0 ≤ Φ u)
    (hcal : ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → ∀ v,
      |Φ' u v| ≤ 2 * √(Φ u) * √(normSq g (x + u) v) * k)
    {w : Fin n → ℝ} (hΦw : Φ w ≤ l * ρ ^ 2) {c : ℝ → Fin n → ℝ}
    (hc : IsAdmissible U c x (x + w)) : √(Φ w) ≤ k * length g c 0 1 := by
  have hL : 0 ≤ length g c 0 1 := length_nonneg zero_le_one
  by_cases hin : ∀ t ∈ Icc (0 : ℝ) 1, ‖c t - x‖ ≤ ρ
  · have := h.sqrt_le_length_of_calib hg hΦd hΦ0 (by linarith) hρ hpos hcal hc.smooth hc.start
      zero_le_one hin
    rwa [hc.finish, add_sub_cancel_left] at this
  · rw [not_forall] at hin
    obtain ⟨t, ht⟩ := hin
    rw [not_imp, not_le] at ht
    have hex := h.length_ge_of_exit hg hρ0 hρ hc ht.1 ht.2.le
    calc √(Φ w) ≤ √(l * ρ ^ 2) := Real.sqrt_le_sqrt hΦw
      _ = √l * ρ := by rw [Real.sqrt_mul h.l_pos.le, Real.sqrt_sq hρ0.le]
      _ ≤ length g c 0 1 := hex
      _ ≤ _ := le_mul_of_one_le_left hL hk1

/-- **The lower bound for one curve**: with `A ≥ 1`, `2 B³ ≤ l A` and the ball of radius
`A ‖w‖` inside the region of `LocalJet` and of the calibration, every admissible curve from `x` to
`x + w` has length at least `√F_x(w) / (1 + κ (A ‖w‖)³)`. -/
theorem sqrt_distJet_le_length_of_admissible (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l)
    {A : ℝ} (hA : 1 ≤ A) (hAl : 2 * B ^ 3 ≤ l * A) {w : Fin n → ℝ} (hw : A * ‖w‖ ≤ δ)
    (hwl : B ^ 3 * (A * ‖w‖) ≤ l / 2) {c : ℝ → Fin n → ℝ} (hc : IsAdmissible U c x (x + w)) :
    √(distJet g x w) ≤ (1 + calibConst B l * (A * ‖w‖) ^ 3) * length g c 0 1 := by
  have hκ := calibConst_nonneg h.B_nonneg h.l_pos
  have hL : 0 ≤ length g c 0 1 := length_nonneg zero_le_one
  have hk1 : 1 ≤ 1 + calibConst B l * (A * ‖w‖) ^ 3 := by
    have : 0 ≤ calibConst B l * (A * ‖w‖) ^ 3 := by have := h.B_nonneg; positivity
    linarith
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [distJet_zero, Real.sqrt_zero]; positivity
  have hρ0 : 0 < A * ‖w‖ := mul_pos (by linarith) (norm_pos_iff.2 hw0)
  have hw1 : ‖w‖ ≤ 1 :=
    le_trans (le_mul_of_one_le_left (norm_nonneg w) hA) (hw.trans h.δ_le_one)
  have hA2 : 2 * B ^ 3 ≤ l * A ^ 2 :=
    hAl.trans (mul_le_mul_of_nonneg_left (by nlinarith) h.l_pos.le)
  have hFl : distJet g x w ≤ l * (A * ‖w‖) ^ 2 :=
    calc distJet g x w ≤ 2 * (B ^ 3 * ‖w‖ ^ 2) := h.distJet_le hw1
      _ = 2 * B ^ 3 * ‖w‖ ^ 2 := by ring
      _ ≤ l * A ^ 2 * ‖w‖ ^ 2 := by gcongr
      _ = _ := by ring
  obtain ⟨hpos, hcal⟩ := h.distJet_calib hg hw hwl
  exact h.sqrt_le_length_of_calib_admissible hg (fun hW => hasDerivAt_distJet x hW)
    (distJet_zero x) hρ0 hw hk1 hpos hcal hFl hc

/-- **The lower bound for the distance**: under the hypotheses of
`sqrt_distJet_le_length_of_admissible`, if some admissible curve joins `x` and `x + w`, then
`√F_x(w) ≤ (1 + κ (A ‖w‖)³) d(x, x + w)`. -/
theorem sqrt_distJet_le_dist (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l)
    {A : ℝ} (hA : 1 ≤ A) (hAl : 2 * B ^ 3 ≤ l * A) {w : Fin n → ℝ} (hw : A * ‖w‖ ≤ δ)
    (hwl : B ^ 3 * (A * ‖w‖) ≤ l / 2) (hne : ∃ c, IsAdmissible U c x (x + w)) :
    √(distJet g x w) ≤ (1 + calibConst B l * (A * ‖w‖) ^ 3) * chartDist g U x (x + w) := by
  have hk : 0 < 1 + calibConst B l * (A * ‖w‖) ^ 3 := by
    have := calibConst_nonneg h.B_nonneg h.l_pos
    have := h.B_nonneg
    positivity
  exact le_mul_chartDist_of_le_mul_length hk hne fun c hc =>
    h.sqrt_distJet_le_length_of_admissible hg hA hAl hw hwl hc

end LocalJet

end Lightlike.Upstream.GeodesicExpansion

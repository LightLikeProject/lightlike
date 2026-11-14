import Lightlike.Regge.Geodesic.Expansion

/-!
# The expansion of the squared distance for nearby points

For a Riemannian coordinate metric `g` on an open `U ⊆ ℝⁿ` and a compact `K ⊆ U`, the squared
distance of `(U, g)` satisfies, uniformly for `x ∈ K`,

  `d(x, x + w)² = F_x(w) + O(‖w‖⁵)`,

where `F_x(w) = g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))` is the
quartic jet `distJet` of `Expansion.lean` (all coefficients at `x`).

* **Lower bound** (calibration). On the ball where `LocalJet` holds, `√F_x` grows along any `C¹`
  curve at most `1 + κ ρ³` times as fast as its `g`-length (`LocalJet.abs_distJetDeriv_le`), so a
  curve from `x` to `x + w` that stays in the ball of radius `ρ = A ‖w‖` has length at least
  `√F_x(w) / (1 + κ ρ³)`; a curve that leaves the ball has length at least `√l ρ`, which is more.
* **Upper bound** (trial curve). The curve `x + t w + ½ t (1 - t) Γ_x(w, w)` solves the geodesic
  equation to second order; its energy is `F_x(w) + O(‖w‖⁵)`, and `d² ≤ length² ≤ energy`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The jet vanishes at `w = 0`. -/
theorem distJet_zero (x : Fin n → ℝ) : distJet g x 0 = 0 := by
  simp [distJet, chr_zero_left, dmat_zero, ddmat_zero_left]

/-- A lower bound `a ≤ k L(c)` for the length of every admissible curve from `x` to `y` gives
`a ≤ k d(x, y)`, provided some admissible curve exists. -/
theorem le_mul_dist_of_le_mul_length {a k : ℝ} (hk : 0 < k) {x y : Fin n → ℝ}
    (hne : ∃ c, IsAdmissible U c x y)
    (hlen : ∀ c, IsAdmissible U c x y → a ≤ k * length g c 0 1) : a ≤ k * dist g U x y := by
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
    √(distJet g x w) ≤ (1 + calibConst B l * (A * ‖w‖) ^ 3) * dist g U x (x + w) := by
  have hk : 0 < 1 + calibConst B l * (A * ‖w‖) ^ 3 := by
    have := calibConst_nonneg h.B_nonneg h.l_pos
    have := h.B_nonneg
    positivity
  exact le_mul_dist_of_le_mul_length hk hne fun c hc =>
    h.sqrt_distJet_le_length_of_admissible hg hA hAl hw hwl hc

end LocalJet

/-! ## The upper bound: a trial curve -/

/-- The **trial curve** `x + t w + ½ t (1 - t) Γ_x(w, w)` from `x` to `x + w`; it solves the
geodesic equation `c'' + Γ_x(c', c') = 0` to second order. -/
noncomputable def trial (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) (t : ℝ) :
    Fin n → ℝ :=
  x + t • w + (t * (1 - t) / 2) • chr g x w w

/-- The velocity `w + ½ (1 - 2t) Γ_x(w, w)` of the trial curve. -/
noncomputable def trialVel (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
    (t : ℝ) : Fin n → ℝ :=
  w + ((1 - 2 * t) / 2) • chr g x w w

/-- The main part of the energy density of the trial curve: the terms of order at most four in
`w` of `g(c', c')`, with the metric replaced by its Taylor polynomial at `x`. -/
noncomputable def trialPoly (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  w ⬝ᵥ (g x *ᵥ w)
    + (1 - 2 * t) / 2 * (w ⬝ᵥ (g x *ᵥ chr g x w w) + chr g x w w ⬝ᵥ (g x *ᵥ w))
    + ((1 - 2 * t) / 2) ^ 2 * (chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w))
    + t * (w ⬝ᵥ (dmat g x w *ᵥ w))
    + t * ((1 - 2 * t) / 2) * (w ⬝ᵥ (dmat g x w *ᵥ chr g x w w)
      + chr g x w w ⬝ᵥ (dmat g x w *ᵥ w))
    + t * (1 - t) / 2 * (w ⬝ᵥ (dmat g x (chr g x w w) *ᵥ w))
    + 1 / 2 * t ^ 2 * (w ⬝ᵥ (ddmat g x w w *ᵥ w))

/-- The remainder of the energy density of the trial curve: the Taylor remainder of the metric
and the terms of order at least five in `w`. -/
noncomputable def trialRem (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  trialVel g x w t ⬝ᵥ ((g (trial g x w t) - taylorMetric g x (trial g x w t - x)) *ᵥ
      trialVel g x w t)
    + t * ((1 - 2 * t) / 2) ^ 2 * (chr g x w w ⬝ᵥ (dmat g x w *ᵥ chr g x w w))
    + t * (1 - t) / 2 * ((1 - 2 * t) / 2) * (w ⬝ᵥ (dmat g x (chr g x w w) *ᵥ chr g x w w))
    + t * (1 - t) / 2 * ((1 - 2 * t) / 2) * (chr g x w w ⬝ᵥ (dmat g x (chr g x w w) *ᵥ w))
    + t * (1 - t) / 2 * ((1 - 2 * t) / 2) ^ 2 *
      (chr g x w w ⬝ᵥ (dmat g x (chr g x w w) *ᵥ chr g x w w))
    + 1 / 2 * t ^ 2 * ((1 - 2 * t) / 2) * (w ⬝ᵥ (ddmat g x w w *ᵥ chr g x w w))
    + 1 / 2 * t ^ 2 * ((1 - 2 * t) / 2) * (chr g x w w ⬝ᵥ (ddmat g x w w *ᵥ w))
    + 1 / 2 * t ^ 2 * ((1 - 2 * t) / 2) ^ 2 * (chr g x w w ⬝ᵥ (ddmat g x w w *ᵥ chr g x w w))
    + 1 / 2 * t * (t * (1 - t) / 2) *
      (trialVel g x w t ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ trialVel g x w t))
    + 1 / 2 * t * (t * (1 - t) / 2) *
      (trialVel g x w t ⬝ᵥ (ddmat g x (chr g x w w) w *ᵥ trialVel g x w t))
    + 1 / 2 * (t * (1 - t) / 2) ^ 2 *
      (trialVel g x w t ⬝ᵥ (ddmat g x (chr g x w w) (chr g x w w) *ᵥ trialVel g x w t))

/-- The trial curve minus its starting point. -/
theorem trial_sub (x w : Fin n → ℝ) (t : ℝ) :
    trial g x w t - x = t • w + (t * (1 - t) / 2) • chr g x w w := by
  unfold trial; abel

/-- The trial curve is `C¹` (it is a polynomial in `t`). -/
theorem contDiff_trial (x w : Fin n → ℝ) : ContDiff ℝ 1 (trial g x w) := by
  unfold trial; fun_prop

/-- The derivative of the trial curve. -/
theorem hasDerivAt_trial (x w : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (trial g x w) (trialVel g x w t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * (1 - s) / 2) ((1 - 2 * t) / 2) t :=
    (((hasDerivAt_id' t).mul ((hasDerivAt_id' t).const_sub 1)).div_const 2).congr_deriv
      (by ring)
  have := (((hasDerivAt_id' t).smul_const w).const_add x).add (h1.smul_const (chr g x w w))
  rw [one_smul] at this
  exact this

/-- **The energy density of the trial curve** splits into its main part and the remainder. -/
theorem normSq_trial_eq (x w : Fin n → ℝ) (t : ℝ) :
    normSq g (trial g x w t) (trialVel g x w t) = trialPoly g x w t + trialRem g x w t := by
  have e : normSq g (trial g x w t) (trialVel g x w t) =
      trialVel g x w t ⬝ᵥ (taylorMetric g x (trial g x w t - x) *ᵥ trialVel g x w t) +
      trialVel g x w t ⬝ᵥ ((g (trial g x w t) - taylorMetric g x (trial g x w t - x)) *ᵥ
        trialVel g x w t) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]; unfold normSq; ring
  rw [e, trialRem, trial_sub]
  simp only [trialPoly, trialVel, taylorMetric, dmat_add, dmat_smul, ddmat_add_left,
    ddmat_add_right, ddmat_smul_left, ddmat_smul_right, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

/-- `c X ≤ b` when `|c| ≤ 1` and `|X| ≤ b`. -/
theorem mul_le_of_abs_coef_le_one {c X b : ℝ} (hc : |c| ≤ 1) (hX : |X| ≤ b) : c * X ≤ b :=
  (le_abs_self _).trans (by
    rw [abs_mul]
    exact (mul_le_mul hc hX (abs_nonneg _) zero_le_one).trans_eq (one_mul b))

/-- Products of numbers of absolute value at most `1`. -/
theorem abs_mul_le_one_of {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]; exact (mul_le_mul ha hb (abs_nonneg b) zero_le_one).trans_eq (one_mul 1)

/-- Squares of numbers of absolute value at most `1`. -/
theorem abs_sq_le_one_of {a : ℝ} (ha : |a| ≤ 1) : |a ^ 2| ≤ 1 := by
  rw [sq]; exact abs_mul_le_one_of ha ha

/-- **The integral of the main part**, for arbitrary coefficients. -/
theorem integral_trialShape (A0 A1 A2 A3 A4 A5 A6 K : ℝ) :
    ∫ t in (0 : ℝ)..1, (A0 + (1 - 2 * t) / 2 * A1 + ((1 - 2 * t) / 2) ^ 2 * A2 + t * A3
      + t * ((1 - 2 * t) / 2) * A4 + t * (1 - t) / 2 * A5 + 1 / 2 * t ^ 2 * A6 + K) =
    A0 + A2 / 12 + A3 / 2 - A4 / 12 + A5 / 12 + A6 / 6 + K := by
  have hQ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => (A0 + A1 / 2 + A2 / 4 + K) * t
      + (-A1 - A2 + A3 + A4 / 2 + A5 / 2) / 2 * t ^ 2 + (A2 - A4 - A5 / 2 + A6 / 2) / 3 * t ^ 3)
      (A0 + (1 - 2 * t) / 2 * A1 + ((1 - 2 * t) / 2) ^ 2 * A2 + t * A3
        + t * ((1 - 2 * t) / 2) * A4 + t * (1 - t) / 2 * A5 + 1 / 2 * t ^ 2 * A6 + K) t := by
    intro t _
    exact ((((hasDerivAt_id' t).const_mul _).add ((hasDerivAt_pow 2 t).const_mul _)).add
      ((hasDerivAt_pow 3 t).const_mul _)).congr_deriv (by norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

namespace LocalJet

variable {x : Fin n → ℝ} {B δ l : ℝ}

/-- With `2 B ‖w‖ ≤ δ` we have `‖w‖ ≤ 1`. -/
theorem norm_le_one_of (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : 2 * B * ‖w‖ ≤ δ) :
    ‖w‖ ≤ 1 := by
  have : ‖w‖ ≤ 2 * B * ‖w‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith [h.one_le])
  linarith [h.δ_le_one]

/-- `‖w‖ + B ‖w‖² ≤ 2 B ‖w‖` for `‖w‖ ≤ 1`. -/
theorem add_sq_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw1 : ‖w‖ ≤ 1) :
    ‖w‖ + B * ‖w‖ ^ 2 ≤ 2 * B * ‖w‖ := by
  have a : ‖w‖ ≤ B * ‖w‖ := le_mul_of_one_le_left (norm_nonneg _) h.one_le
  have b : B * ‖w‖ * ‖w‖ ≤ B * ‖w‖ * 1 :=
    mul_le_mul_of_nonneg_left hw1 (mul_nonneg h.B_nonneg (norm_nonneg w))
  nlinarith

/-- On `[0, 1]` the trial curve stays in the ball of radius `2 B ‖w‖` about `x`. -/
theorem norm_trial_sub_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : 2 * B * ‖w‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖trial g x w t - x‖ ≤ 2 * B * ‖w‖ := by
  have hΓ := h.norm_chr_le w
  have h1 : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have h2 : |t * (1 - t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
  rw [trial_sub]
  calc ‖t • w + (t * (1 - t) / 2) • chr g x w w‖
      ≤ ‖t • w‖ + ‖(t * (1 - t) / 2) • chr g x w w‖ := norm_add_le _ _
    _ = |t| * ‖w‖ + |t * (1 - t) / 2| * ‖chr g x w w‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖w‖ + 1 * (B * ‖w‖ ^ 2) := by gcongr
    _ ≤ 2 * B * ‖w‖ := by linarith [h.add_sq_le (h.norm_le_one_of hw)]

/-- On `[0, 1]` the speed of the trial curve is at most `2 B ‖w‖` (sup norm). -/
theorem norm_trialVel_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : 2 * B * ‖w‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖trialVel g x w t‖ ≤ 2 * B * ‖w‖ := by
  have hΓ := h.norm_chr_le w
  have h1 : |(1 - 2 * t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  unfold trialVel
  calc ‖w + ((1 - 2 * t) / 2) • chr g x w w‖
      ≤ ‖w‖ + ‖((1 - 2 * t) / 2) • chr g x w w‖ := norm_add_le _ _
    _ = ‖w‖ + |(1 - 2 * t) / 2| * ‖chr g x w w‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖w‖ + 1 * (B * ‖w‖ ^ 2) := by gcongr
    _ ≤ 2 * B * ‖w‖ := by linarith [h.add_sq_le (h.norm_le_one_of hw)]

/-- **The remainder of the trial curve** is at most `51 B⁶ ‖w‖⁵` on `[0, 1]`. -/
theorem trialRem_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : 2 * B * ‖w‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : trialRem g x w t ≤ 51 * (B ^ 6 * ‖w‖ ^ 5) := by
  have hB0 := h.B_nonneg
  have hw1 := h.norm_le_one_of hw
  have hV := h.norm_trialVel_le hw ht
  have hu := h.norm_trial_sub_le hw ht
  have htay := h.tay_le _ (hu.trans hw) (trialVel g x w t) (trialVel g x w t)
  rw [add_sub_cancel] at htay
  have hΓ := h.norm_chr_le w
  have cT : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have cS : |(1 - 2 * t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have cτ : |t * (1 - t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
  have ch : |(1 / 2 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  unfold trialRem
  set Γ := chr g x w w
  set V := trialVel g x w t
  have mono : ∀ {a b : ℕ}, a ≤ 6 → 5 ≤ b → B ^ a * ‖w‖ ^ b ≤ B ^ 6 * ‖w‖ ^ 5 :=
    fun ha hb => h.monom_le hw1 ha hb
  have t0 : |V ⬝ᵥ ((g (trial g x w t) - taylorMetric g x (trial g x w t - x)) *ᵥ V)| ≤
      32 * (B ^ 6 * ‖w‖ ^ 5) :=
    calc _ ≤ B * ‖trial g x w t - x‖ ^ 3 * ‖V‖ * ‖V‖ := htay
      _ ≤ B * (2 * B * ‖w‖) ^ 3 * (2 * B * ‖w‖) * (2 * B * ‖w‖) := by gcongr
      _ = 32 * (B ^ 6 * ‖w‖ ^ 5) := by ring
  have x1 : |Γ ⬝ᵥ (dmat g x w *ᵥ Γ)| ≤ B ^ 6 * ‖w‖ ^ 5 :=
    calc _ ≤ B * ‖w‖ * ‖Γ‖ * ‖Γ‖ := h.d_le _ _ _
      _ ≤ B * ‖w‖ * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) := by gcongr
      _ = B ^ 3 * ‖w‖ ^ 5 := by ring
      _ ≤ _ := mono (by norm_num) le_rfl
  have x2 : |w ⬝ᵥ (dmat g x Γ *ᵥ Γ)| ≤ B ^ 6 * ‖w‖ ^ 5 :=
    calc _ ≤ B * ‖Γ‖ * ‖w‖ * ‖Γ‖ := h.d_le _ _ _
      _ ≤ B * (B * ‖w‖ ^ 2) * ‖w‖ * (B * ‖w‖ ^ 2) := by gcongr
      _ = B ^ 3 * ‖w‖ ^ 5 := by ring
      _ ≤ _ := mono (by norm_num) le_rfl
  have x3 : |Γ ⬝ᵥ (dmat g x Γ *ᵥ w)| ≤ B ^ 6 * ‖w‖ ^ 5 :=
    calc _ ≤ B * ‖Γ‖ * ‖Γ‖ * ‖w‖ := h.d_le _ _ _
      _ ≤ B * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) * ‖w‖ := by gcongr
      _ = B ^ 3 * ‖w‖ ^ 5 := by ring
      _ ≤ _ := mono (by norm_num) le_rfl
  have x4 : |Γ ⬝ᵥ (dmat g x Γ *ᵥ Γ)| ≤ B ^ 6 * ‖w‖ ^ 5 :=
    calc _ ≤ B * ‖Γ‖ * ‖Γ‖ * ‖Γ‖ := h.d_le _ _ _
      _ ≤ B * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) := by gcongr
      _ = B ^ 4 * ‖w‖ ^ 6 := by ring
      _ ≤ _ := mono (by norm_num) (by norm_num)
  have x5 : |w ⬝ᵥ (ddmat g x w w *ᵥ Γ)| ≤ B ^ 6 * ‖w‖ ^ 5 :=
    calc _ ≤ B * ‖w‖ * ‖w‖ * ‖w‖ * ‖Γ‖ := h.dd_le _ _ _ _
      _ ≤ B * ‖w‖ * ‖w‖ * ‖w‖ * (B * ‖w‖ ^ 2) := by gcongr
      _ = B ^ 2 * ‖w‖ ^ 5 := by ring
      _ ≤ _ := mono (by norm_num) le_rfl
  have x6 : |Γ ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ B ^ 6 * ‖w‖ ^ 5 :=
    calc _ ≤ B * ‖w‖ * ‖w‖ * ‖Γ‖ * ‖w‖ := h.dd_le _ _ _ _
      _ ≤ B * ‖w‖ * ‖w‖ * (B * ‖w‖ ^ 2) * ‖w‖ := by gcongr
      _ = B ^ 2 * ‖w‖ ^ 5 := by ring
      _ ≤ _ := mono (by norm_num) le_rfl
  have x7 : |Γ ⬝ᵥ (ddmat g x w w *ᵥ Γ)| ≤ B ^ 6 * ‖w‖ ^ 5 :=
    calc _ ≤ B * ‖w‖ * ‖w‖ * ‖Γ‖ * ‖Γ‖ := h.dd_le _ _ _ _
      _ ≤ B * ‖w‖ * ‖w‖ * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) := by gcongr
      _ = B ^ 3 * ‖w‖ ^ 6 := by ring
      _ ≤ _ := mono (by norm_num) (by norm_num)
  have x8 : |V ⬝ᵥ (ddmat g x w Γ *ᵥ V)| ≤ 4 * (B ^ 6 * ‖w‖ ^ 5) :=
    calc _ ≤ B * ‖w‖ * ‖Γ‖ * ‖V‖ * ‖V‖ := h.dd_le _ _ _ _
      _ ≤ B * ‖w‖ * (B * ‖w‖ ^ 2) * (2 * B * ‖w‖) * (2 * B * ‖w‖) := by gcongr
      _ = 4 * (B ^ 4 * ‖w‖ ^ 5) := by ring
      _ ≤ _ := by gcongr 4 * ?_; exact mono (by norm_num) le_rfl
  have x9 : |V ⬝ᵥ (ddmat g x Γ w *ᵥ V)| ≤ 4 * (B ^ 6 * ‖w‖ ^ 5) :=
    calc _ ≤ B * ‖Γ‖ * ‖w‖ * ‖V‖ * ‖V‖ := h.dd_le _ _ _ _
      _ ≤ B * (B * ‖w‖ ^ 2) * ‖w‖ * (2 * B * ‖w‖) * (2 * B * ‖w‖) := by gcongr
      _ = 4 * (B ^ 4 * ‖w‖ ^ 5) := by ring
      _ ≤ _ := by gcongr 4 * ?_; exact mono (by norm_num) le_rfl
  have x10 : |V ⬝ᵥ (ddmat g x Γ Γ *ᵥ V)| ≤ 4 * (B ^ 6 * ‖w‖ ^ 5) :=
    calc _ ≤ B * ‖Γ‖ * ‖Γ‖ * ‖V‖ * ‖V‖ := h.dd_le _ _ _ _
      _ ≤ B * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) * (2 * B * ‖w‖) * (2 * B * ‖w‖) := by gcongr
      _ = 4 * (B ^ 5 * ‖w‖ ^ 6) := by ring
      _ ≤ _ := by gcongr 4 * ?_; exact mono (by norm_num) (by norm_num)
  have y0 := (le_abs_self _).trans t0
  have y1 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of cT (abs_sq_le_one_of cS)) x1
  have y2 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of cτ cS) x2
  have y3 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of cτ cS) x3
  have y4 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of cτ (abs_sq_le_one_of cS)) x4
  have y5 := mul_le_of_abs_coef_le_one
    (abs_mul_le_one_of (abs_mul_le_one_of ch (abs_sq_le_one_of cT)) cS) x5
  have y6 := mul_le_of_abs_coef_le_one
    (abs_mul_le_one_of (abs_mul_le_one_of ch (abs_sq_le_one_of cT)) cS) x6
  have y7 := mul_le_of_abs_coef_le_one
    (abs_mul_le_one_of (abs_mul_le_one_of ch (abs_sq_le_one_of cT)) (abs_sq_le_one_of cS)) x7
  have y8 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of (abs_mul_le_one_of ch cT) cτ) x8
  have y9 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of (abs_mul_le_one_of ch cT) cτ) x9
  have y10 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of ch (abs_sq_le_one_of cτ)) x10
  linarith

end LocalJet

/-- `F - d² ≤ 2 (k - 1) F` when `√F ≤ k d` with `k ≥ 1`. -/
theorem sub_sq_le_of_sqrt_le {F d k : ℝ} (hF : 0 ≤ F) (hk : 1 ≤ k)
    (h : √F ≤ k * d) : F - d ^ 2 ≤ 2 * (k - 1) * F := by
  have h1 : F ≤ (k * d) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg F) h 2
    rwa [Real.sq_sqrt hF] at this
  have hk2 : 0 < k ^ 2 := by positivity
  have e1 : (k - 1) * F * (k + 1) ≤ (k - 1) * F * (2 * k ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by linarith) hF)
  have h2 : k ^ 2 * (F - d ^ 2) ≤ k ^ 2 * (2 * (k - 1) * F) := by nlinarith
  exact le_of_mul_le_mul_left h2 hk2

namespace LocalJet

variable {x : Fin n → ℝ} {B δ l : ℝ}

/-- The trial curve is an admissible curve from `x` to `x + w` when `2 B ‖w‖ ≤ δ`. -/
theorem isAdmissible_trial (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : 2 * B * ‖w‖ ≤ δ) :
    IsAdmissible U (trial g x w) x (x + w) where
  smooth := contDiff_trial x w
  mem t ht := by simpa using h.mem _ ((h.norm_trial_sub_le hw ht).trans hw)
  start := by simp [trial]
  finish := by simp [trial]

/-- The energy density of the trial curve is integrable on `[0, 1]`. -/
theorem intervalIntegrable_normSq_trial (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l)
    {w : Fin n → ℝ} (hw : 2 * B * ‖w‖ ≤ δ) :
    IntervalIntegrable (fun t => normSq g (trial g x w t) (deriv (trial g x w) t)) volume 0 1 := by
  have hadm := h.isAdmissible_trial hw
  have hd : deriv (trial g x w) = trialVel g x w :=
    funext fun t => (hasDerivAt_trial x w t).deriv
  have hcV : Continuous (trialVel g x w) := by unfold trialVel; fun_prop
  rw [hd]
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact hg.continuousOn_normSq.comp ((hadm.smooth.continuous.prodMk hcV).continuousOn)
    (fun t ht => mk_mem_prod (hadm.mem t ht) (mem_univ _))

/-- **The energy of the trial curve** is at most `F_x(w) + 51 B⁶ ‖w‖⁵`. -/
theorem energy_trial_le (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l) {w : Fin n → ℝ}
    (hw : 2 * B * ‖w‖ ≤ δ) :
    energy g (trial g x w) 0 1 ≤ distJet g x w + 51 * (B ^ 6 * ‖w‖ ^ 5) := by
  have hx : x ∈ U := by simpa using h.mem 0 (by simpa using h.δ_pos.le)
  have hd : deriv (trial g x w) = trialVel g x w :=
    funext fun t => (hasDerivAt_trial x w t).deriv
  have hint := h.intervalIntegrable_normSq_trial hg hw
  rw [hd] at hint
  have hint2 : IntervalIntegrable (fun t => trialPoly g x w t + 51 * (B ^ 6 * ‖w‖ ^ 5))
      volume 0 1 := by
    apply Continuous.intervalIntegrable; unfold trialPoly; fun_prop
  have hle : energy g (trial g x w) 0 1 ≤
      ∫ t in (0 : ℝ)..1, (trialPoly g x w t + 51 * (B ^ 6 * ‖w‖ ^ 5)) := by
    unfold energy; rw [hd]
    refine intervalIntegral.integral_mono_on zero_le_one hint hint2 fun t ht => ?_
    rw [normSq_trial_eq]
    linarith [h.trialRem_le hw ht]
  refine hle.trans (le_of_eq ?_)
  unfold trialPoly
  rw [integral_trialShape]
  have hchr := hg.coord.dot_mulVec_chr hx (chr g x w w) w w
  have hsym := dot_mulVec_comm (hg.coord.dmat_transpose hx w) w (chr g x w w)
  unfold distJet
  linarith

/-- **The upper bound**: `d(x, x + w)² ≤ F_x(w) + 51 B⁶ ‖w‖⁵` when `2 B ‖w‖ ≤ δ`. -/
theorem dist_sq_le (hg : IsRiemMetric g U) (h : LocalJet g U x B δ l) {w : Fin n → ℝ}
    (hw : 2 * B * ‖w‖ ≤ δ) :
    dist g U x (x + w) ^ 2 ≤ distJet g x w + 51 * (B ^ 6 * ‖w‖ ^ 5) := by
  have hadm := h.isAdmissible_trial hw
  have hLE := length_sq_le_energy hg zero_le_one hadm.mem (hg.intervalIntegrable_speed hadm)
    (h.intervalIntegrable_normSq_trial hg hw)
  rw [sub_zero, one_mul] at hLE
  have hdl := pow_le_pow_left₀ dist_nonneg (dist_le_length (g := g) hadm) 2
  linarith [h.energy_trial_le hg hw]

end LocalJet

/-- **The expansion of the squared distance for nearby points.** For a Riemannian coordinate
metric `g` on `U` and a compact `K ⊆ U` there are `C` and `r > 0` such that for `x ∈ K` and
`‖w‖ ≤ r`,
`|d(x, x + w)² - F_x(w)| ≤ C ‖w‖⁵`, with
`F_x(w) = g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))` at `x`
(`distJet`). -/
theorem IsRiemMetric.dist_sq_expansion (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ w : Fin n → ℝ, ‖w‖ ≤ r →
      |dist g U x (x + w) ^ 2 - distJet g x w| ≤ C * ‖w‖ ^ 5 := by
  obtain ⟨B, δ, l, hJ⟩ := hg.exists_localJet hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have h₀ := hJ x₀ hx₀
  have hB1 := h₀.one_le
  have hB : 0 < B := by linarith
  have hl := h₀.l_pos
  have hδ := h₀.δ_pos
  set A := 2 * B ^ 3 / l + 1 with hAdef
  have hA : 1 ≤ A := by have : 0 ≤ 2 * B ^ 3 / l := by positivity
                        linarith
  have hA0 : 0 < A := by linarith
  have hAl : 2 * B ^ 3 ≤ l * A := by
    have : l * A = 2 * B ^ 3 + l := by rw [hAdef]; field_simp
    linarith
  set κ := calibConst B l
  have hκ : 0 ≤ κ := calibConst_nonneg hB.le hl
  refine ⟨4 * κ * A ^ 3 * B ^ 3 + 51 * B ^ 6,
    min (min (δ / A) (l / (2 * B ^ 3 * A))) (δ / (2 * B)), by positivity, ?_⟩
  intro x hx w hwr
  have h := hJ x hx
  have hr1 : ‖w‖ ≤ δ / A := (hwr.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hr2 : ‖w‖ ≤ l / (2 * B ^ 3 * A) := (hwr.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hr3 : ‖w‖ ≤ δ / (2 * B) := hwr.trans (min_le_right _ _)
  rw [le_div_iff₀ hA0] at hr1
  rw [le_div_iff₀ (by positivity)] at hr2
  rw [le_div_iff₀ (by positivity)] at hr3
  have hw1 : A * ‖w‖ ≤ δ := by linarith
  have hw2 : B ^ 3 * (A * ‖w‖) ≤ l / 2 := by nlinarith
  have hw3 : 2 * B * ‖w‖ ≤ δ := by linarith
  have hwle1 : ‖w‖ ≤ 1 := h.norm_le_one_of hw3
  -- upper bound
  have hup := h.dist_sq_le hg hw3
  -- lower bound
  have hlow := h.sqrt_distJet_le_dist hg hA hAl hw1 hw2 ⟨_, h.isAdmissible_trial hw3⟩
  have hBw : B ^ 3 * ‖w‖ ≤ l / 2 :=
    le_trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (norm_nonneg w) hA)
      (by positivity)) hw2
  have hF0 : 0 ≤ distJet g x w :=
    le_trans (by positivity) (h.distJet_ge_half hwle1 hBw)
  have hF1 := h.distJet_le hwle1
  have hk : 1 ≤ 1 + κ * (A * ‖w‖) ^ 3 := by
    have : 0 ≤ κ * (A * ‖w‖) ^ 3 := by positivity
    linarith
  have hsub := sub_sq_le_of_sqrt_le hF0 hk hlow
  have hsub' : 2 * (1 + κ * (A * ‖w‖) ^ 3 - 1) * distJet g x w ≤
      4 * κ * A ^ 3 * B ^ 3 * ‖w‖ ^ 5 :=
    calc 2 * (1 + κ * (A * ‖w‖) ^ 3 - 1) * distJet g x w
        ≤ 2 * (1 + κ * (A * ‖w‖) ^ 3 - 1) * (2 * (B ^ 3 * ‖w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hF1 (by positivity)
      _ = 4 * κ * A ^ 3 * B ^ 3 * ‖w‖ ^ 5 := by ring
  have h51 : 0 ≤ 51 * B ^ 6 * ‖w‖ ^ 5 := by positivity
  have h4 : 0 ≤ 4 * κ * A ^ 3 * B ^ 3 * ‖w‖ ^ 5 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The expansion about the midpoint -/

/-- The jet of the squared distance about the midpoint `m` of two points with difference `Δ`:
`g(Δ, Δ) + (1/24) ∂_Δ ∂_Δ g(Δ, Δ) - (1/12) g(Γ(Δ, Δ), Γ(Δ, Δ))`, all at `m`. -/
noncomputable def midJet (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (m Δ : Fin n → ℝ) : ℝ :=
  Δ ⬝ᵥ (g m *ᵥ Δ) + (1 / 24) * (Δ ⬝ᵥ (ddmat g m Δ Δ *ᵥ Δ))
    - (1 / 12) * (chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ))

/-- `p ⬝ (M q) = Σ_i p_i Σ_j q_j M_ij`. -/
theorem dot_mulVec_eq_nest (M : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n → ℝ) :
    p ⬝ᵥ (M *ᵥ q) = ∑ i, p i * ∑ j, q j * M i j := by
  simp only [dotProduct, Matrix.mulVec]
  exact Finset.sum_congr rfl fun i _ => by
    congr 1; exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Differentiating `Σ_k a_k F_k(s)` term by term. -/
theorem hasDerivAt_wsum {a : Fin n → ℝ} {F : Fin n → ℝ → ℝ} {F' : Fin n → ℝ} {s : ℝ}
    (h : ∀ k, HasDerivAt (F k) (F' k) s) :
    HasDerivAt (fun s => ∑ k, a k * F k s) (∑ k, a k * F' k) s :=
  HasDerivAt.fun_sum fun k _ => (h k).const_mul (a k)

/-- `|Σ_k a_k b_k| ≤ n ‖a‖ B` if `|b_k| ≤ B`. -/
theorem abs_wsum_le {a b : Fin n → ℝ} {B : ℝ} (hb : ∀ k, |b k| ≤ B) :
    |∑ k, a k * b k| ≤ n * ‖a‖ * B :=
  abs_sum_mul_le (norm_nonneg a) (abs_le_norm_apply a) hb

/-- The one-variable identity behind the midpoint form: expanding about `0`,
`ψ(-½) + ½ ψ'(-½) + ⅙ ψ''(-½) = ψ(0) + ψ''(0)/24` up to `K/3` if the third derivative is bounded
by `K` on `[-½, 0]` (the coefficient of `ψ''(0)` is `⅛ - ¼ + ⅙ = 1/24`). -/
theorem abs_midComb_le {ψ0 ψ1 ψ2 ψ3 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ0 (ψ1 s) s)
    (d1 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ1 (ψ2 s) s)
    (d2 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ2 (ψ3 s) s)
    (hb : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, |ψ3 s| ≤ K) :
    |ψ0 (-1 / 2) + 1 / 2 * ψ1 (-1 / 2) + 1 / 6 * ψ2 (-1 / 2) - ψ0 0 - 1 / 24 * ψ2 0| ≤ K / 3 := by
  have hm : ∀ s ∈ Icc (0 : ℝ) 1, -s / 2 ∈ Icc (-1 / 2 : ℝ) 0 := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have c : ∀ (φ φ' : ℝ → ℝ) (c₀ : ℝ), (∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt φ (φ' s) s) →
      ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => c₀ * φ (-t / 2)) (-1 / 2 * c₀ * φ' (-s / 2)) s := by
    intro φ φ' c₀ h s hs
    have h1 : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    exact (((h _ (hm s hs)).comp s h1).const_mul c₀).congr_deriv (by ring)
  have hb' : ∀ (c₀ : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, |c₀ * ψ3 (-s / 2)| ≤ |c₀| * K := fun c₀ s hs => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb _ (hm s hs)) (abs_nonneg _)
  have t3 := taylor_aux_three (c ψ0 ψ1 1 d0) (c ψ1 ψ2 _ d1) (c ψ2 ψ3 _ d2)
    (hb' (-1 / 2 * (-1 / 2 * (-1 / 2 * 1))))
  have t2 := taylor_aux_two (c ψ1 ψ2 1 d1) (c ψ2 ψ3 _ d2) (hb' (-1 / 2 * (-1 / 2 * 1)))
  have t1 := taylor_aux_one (c ψ2 ψ3 1 d2) (hb' (-1 / 2 * 1))
  simp only [neg_zero, zero_div] at t1 t2 t3
  norm_num at t1 t2 t3
  rw [abs_le] at t1 t2 t3 ⊢
  constructor <;> nlinarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]

/-- **The polynomial part about the midpoint.** If the third partial derivatives of `g` are
bounded by `M` on the segment from `m - Δ/2` to `m`, then the polynomial part of `distJet` at
`m - Δ/2` differs from `g(Δ, Δ) + (1/24) ∂_Δ ∂_Δ g(Δ, Δ)` at `m` by at most `n⁵ M ‖Δ‖⁵ / 3`. -/
theorem abs_jetPoly_mid_le (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {M : ℝ}
    (hseg : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, m + s • Δ ∈ U)
    (hM : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, ∀ i j k l p : Fin n,
      |Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) (m + s • Δ)| ≤ M) :
    |Δ ⬝ᵥ (g (m - (1 / 2 : ℝ) • Δ) *ᵥ Δ)
      + (1 / 2) * (Δ ⬝ᵥ (dmat g (m - (1 / 2 : ℝ) • Δ) Δ *ᵥ Δ))
      + (1 / 6) * (Δ ⬝ᵥ (ddmat g (m - (1 / 2 : ℝ) • Δ) Δ Δ *ᵥ Δ))
      - Δ ⬝ᵥ (g m *ᵥ Δ) - (1 / 24) * (Δ ⬝ᵥ (ddmat g m Δ Δ *ᵥ Δ))| ≤ n ^ 5 * M * ‖Δ‖ ^ 5 / 3 := by
  have e0 : ∀ z, Δ ⬝ᵥ (g z *ᵥ Δ) = ∑ i, Δ i * ∑ j, Δ j * g z i j := fun z =>
    dot_mulVec_eq_nest _ _ _
  have e1 : ∀ z, Δ ⬝ᵥ (dmat g z Δ *ᵥ Δ) =
      ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * Lightlike.pd k (fun y => g y i j) z := fun z => by
    rw [dot_mulVec_eq_nest]; rfl
  have e2 : ∀ z, Δ ⬝ᵥ (ddmat g z Δ Δ *ᵥ Δ) =
      ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l * Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) z :=
    fun z => by
      rw [dot_mulVec_eq_nest]
      simp only [ddmat, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  have key := abs_midComb_le
    (ψ0 := fun s => ∑ i, Δ i * ∑ j, Δ j * g (m + s • Δ) i j)
    (ψ1 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * Lightlike.pd k (fun y => g y i j) (m + s • Δ))
    (ψ2 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l *
      Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) (m + s • Δ))
    (ψ3 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l * ∑ p, Δ p *
      Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) (m + s • Δ))
    (K := n ^ 5 * M * ‖Δ‖ ^ 5)
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j =>
      hasDerivAt_line (hg.smooth i j) hg.isOpen (hseg s hs))
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
      hasDerivAt_line (hg.contDiffOn_pdg k i j) hg.isOpen (hseg s hs))
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
      hasDerivAt_wsum fun l =>
        hasDerivAt_line (Lightlike.contDiffOn_pd (hg.contDiffOn_pdg k i j) hg.isOpen l) hg.isOpen
          (hseg s hs))
    (fun s hs => (abs_wsum_le fun i => abs_wsum_le fun j => abs_wsum_le fun k =>
      abs_wsum_le fun l => abs_wsum_le fun p => hM s hs i j k l p).trans_eq (by ring))
  have hx : m + (-1 / 2 : ℝ) • Δ = m - (1 / 2 : ℝ) • Δ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, neg_smul, ← sub_eq_add_neg]
  simp only [hx, zero_smul, add_zero] at key
  simp only [e0, e1, e2]
  exact key

/-- **The Christoffel term at nearby points.** If on the segment from `m` to `m + w` the entries of
`g`, their first partial derivatives, the Christoffel symbols and their first partial derivatives
are bounded by `M`, then `g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m + w` and at `m` differ by at most
`3 n⁷ M³ ‖w‖ ‖Δ‖⁴`. -/
theorem abs_chrTerm_sub_le (hg : Lightlike.IsCoordMetric g U) {m w Δ : Fin n → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hseg : ∀ s ∈ Icc (0 : ℝ) 1, m + s • w ∈ U)
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j k l : Fin n,
      |g (m + s • w) i j| ≤ M ∧ |Lightlike.pd k (fun y => g y i j) (m + s • w)| ≤ M ∧
      |Lightlike.christoffel g i j k (m + s • w)| ≤ M ∧
      |Lightlike.pd l (Lightlike.christoffel g i j k) (m + s • w)| ≤ M) :
    |chr g (m + w) Δ Δ ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)
      - chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ)| ≤ 3 * n ^ 7 * M ^ 3 * ‖w‖ * ‖Δ‖ ^ 4 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hm0 : m + (0 : ℝ) • w = m := by simp
  have hm1 : m + (1 : ℝ) • w = m + w := by simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have gx : ∀ i j, |g (m + w) i j| ≤ M := fun i j => by
    simpa [hm1] using (hM 1 h1 i j i i).1
  have cm : ∀ i j k, |Lightlike.christoffel g i j k m| ≤ M := fun i j k => by
    simpa [hm0] using (hM 0 h0 i j k k).2.2.1
  have cx : ∀ i j k, |Lightlike.christoffel g i j k (m + w)| ≤ M := fun i j k => by
    simpa [hm1] using (hM 1 h1 i j k k).2.2.1
  have dg : ∀ i j, |g (m + w) i j - g m i j| ≤ n * M * ‖w‖ := fun i j =>
    taylor_one (hg.smooth i j) hg.isOpen hseg fun s hs k => (hM s hs i j k k).2.1
  have dc : ∀ i j k, |Lightlike.christoffel g i j k (m + w) - Lightlike.christoffel g i j k m| ≤
      n * M * ‖w‖ := fun i j k =>
    taylor_one (hg.contDiffOn_christoffel i j k) hg.isOpen hseg fun s hs l =>
      (hM s hs i j k l).2.2.2
  have nΓm : ‖chr g m Δ Δ‖ ≤ n ^ 2 * M * ‖Δ‖ * ‖Δ‖ := norm_chr_le hM0 cm
  have nΓx : ‖chr g (m + w) Δ Δ‖ ≤ n ^ 2 * M * ‖Δ‖ * ‖Δ‖ := norm_chr_le hM0 cx
  have nΓd : ‖chr g (m + w) Δ Δ - chr g m Δ Δ‖ ≤ n * ‖Δ‖ * (n * ‖Δ‖ * (n * M * ‖w‖)) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have e : (chr g (m + w) Δ Δ - chr g m Δ Δ) i = ∑ j, Δ j * ∑ k, Δ k *
        (Lightlike.christoffel g i j k (m + w) - Lightlike.christoffel g i j k m) := by
      simp only [Pi.sub_apply, chr, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact abs_wsum_le fun j => abs_wsum_le fun k => dc i j k
  have bx : ∀ p q, |p ⬝ᵥ (g (m + w) *ᵥ q)| ≤ n ^ 2 * M * ‖p‖ * ‖q‖ := abs_dot_mulVec_le hM0 gx
  have bd : ∀ p q, |p ⬝ᵥ ((g (m + w) - g m) *ᵥ q)| ≤ n ^ 2 * (n * M * ‖w‖) * ‖p‖ * ‖q‖ :=
    abs_dot_mulVec_le (by positivity) fun i j => by rw [Matrix.sub_apply]; exact dg i j
  have e : chr g (m + w) Δ Δ ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)
        - chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ)
      = (chr g (m + w) Δ Δ - chr g m Δ Δ) ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)
        + chr g m Δ Δ ⬝ᵥ (g (m + w) *ᵥ (chr g (m + w) Δ Δ - chr g m Δ Δ))
        + chr g m Δ Δ ⬝ᵥ ((g (m + w) - g m) *ᵥ chr g m Δ Δ) := by
    simp only [sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub, Matrix.sub_mulVec]
    ring
  have ha : |(chr g (m + w) Δ Δ - chr g m Δ Δ) ⬝ᵥ (g (m + w) *ᵥ chr g (m + w) Δ Δ)| ≤
      n ^ 2 * M * (n * ‖Δ‖ * (n * ‖Δ‖ * (n * M * ‖w‖))) * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) := by
    refine (bx _ _).trans ?_; gcongr
  have hb : |chr g m Δ Δ ⬝ᵥ (g (m + w) *ᵥ (chr g (m + w) Δ Δ - chr g m Δ Δ))| ≤
      n ^ 2 * M * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) * (n * ‖Δ‖ * (n * ‖Δ‖ * (n * M * ‖w‖))) := by
    refine (bx _ _).trans ?_; gcongr
  have hc : |chr g m Δ Δ ⬝ᵥ ((g (m + w) - g m) *ᵥ chr g m Δ Δ)| ≤
      n ^ 2 * (n * M * ‖w‖) * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) * (n ^ 2 * M * ‖Δ‖ * ‖Δ‖) := by
    refine (bd _ _).trans ?_; gcongr
  rw [e]
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ _ := add_le_add_three ha hb hc
    _ = 3 * n ^ 7 * M ^ 3 * ‖w‖ * ‖Δ‖ ^ 4 := by ring

/-- **The expansion of the squared distance about the midpoint.** For a Riemannian coordinate
metric `g` on `U` and a compact `K ⊆ U` there are `C` and `r > 0` such that for `m ∈ K` and
`‖Δ‖ ≤ r`,
`|d(m - Δ/2, m + Δ/2)² - g(Δ, Δ) - Q_m(Δ)| ≤ C ‖Δ‖⁵`, with the quartic form
`Q_m(Δ) = (1/24) ∂_Δ ∂_Δ g(Δ, Δ) - (1/12) g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m` (`midJet`). About the
midpoint there is no cubic term. -/
theorem IsRiemMetric.dist_sq_expansion_midpoint (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ m ∈ K, ∀ Δ : Fin n → ℝ, ‖Δ‖ ≤ r →
      |dist g U (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2 - midJet g m Δ| ≤
        C * ‖Δ‖ ^ 5 := by
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hK' : IsCompact (Metric.cthickening ρ K) := hK.cthickening
  obtain ⟨C₁, r₁, hr₁, h₁⟩ := hg.dist_sq_expansion hK' hρU
  obtain ⟨M, hM0, hM⟩ := hg.coord.exists_jet_bound hK' hρU
  refine ⟨C₁ + n ^ 5 * M / 3 + n ^ 7 * M ^ 3 / 8, min r₁ ρ, lt_min hr₁ hρ, fun m hm Δ hΔ => ?_⟩
  have hΔ1 : ‖Δ‖ ≤ r₁ := hΔ.trans (min_le_left _ _)
  have hΔ2 : ‖Δ‖ ≤ ρ := hΔ.trans (min_le_right _ _)
  have hin : ∀ v : Fin n → ℝ, ‖v‖ ≤ ρ → m + v ∈ Metric.cthickening ρ K := fun v hv =>
    Metric.closedBall_subset_cthickening hm _
      (by rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hv)
  have hs1 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, ‖s • Δ‖ ≤ ρ := fun s hs => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hs.2]
    nlinarith [mul_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s + 1 / 2) (norm_nonneg Δ)]
  have hmw : m + (-(1 / 2 : ℝ)) • Δ = m - (1 / 2 : ℝ) • Δ := by
    rw [neg_smul, ← sub_eq_add_neg]
  have hnw : ‖(-(1 / 2 : ℝ)) • Δ‖ = ‖Δ‖ / 2 := by
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hs2 : ∀ s ∈ Icc (0 : ℝ) 1, ‖s • (-(1 / 2 : ℝ)) • Δ‖ ≤ ρ := fun s hs => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1, hnw]
    nlinarith [mul_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) (norm_nonneg Δ)]
  have hx : m - (1 / 2 : ℝ) • Δ ∈ Metric.cthickening ρ K := by
    rw [← hmw]; exact hin _ (by rw [hnw]; linarith [norm_nonneg Δ])
  have hy : m - (1 / 2 : ℝ) • Δ + Δ = m + (1 / 2 : ℝ) • Δ := by module
  have E1 := h₁ _ hx Δ hΔ1
  rw [hy] at E1
  have E2 := abs_jetPoly_mid_le hg.coord (m := m) (Δ := Δ) (M := M)
    (fun s hs => hρU (hin _ (hs1 s hs)))
    (fun s hs i j k l p => (hM _ (hin _ (hs1 s hs)) i j k l p).2.2.2.2.1)
  have E3 := abs_chrTerm_sub_le hg.coord (m := m) (w := (-(1 / 2 : ℝ)) • Δ) (Δ := Δ) hM0
    (fun s hs => hρU (hin _ (hs2 s hs)))
    (fun s hs i j k l => by
      have h := hM _ (hin _ (hs2 s hs)) i j k l l
      exact ⟨h.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
  rw [hmw, hnw] at E3
  unfold distJet at E1
  unfold midJet
  rw [abs_le] at E1 E2 E3 ⊢
  constructor <;> nlinarith [E1.1, E1.2, E2.1, E2.2, E3.1, E3.2]

end Lightlike.Geodesic

import Lightlike.Regge.Geodesic.Quintic

/-!
# The squared distance to sixth order

The last step of RC6a. For a Riemannian coordinate metric `g` on an open set `U` and a compact `K ⊆ U`:

* `IsRiemMetric.dist_sq_expansion6`: `|d(x, x + w)² − F₅_x(w)| ≤ C ‖w‖⁶` for `x ∈ K` and small
  `w`, where `F₅ = distJet + quint` (`distJet5`, `Quintic.lean`) is the jet of the squared
  distance to order five at one end point.
* `IsRiemMetric.dist_sq_expansion_midpoint6`:
  `|d(m − Δ/2, m + Δ/2)² − g_m(Δ, Δ) − Q_m(Δ)| ≤ C ‖Δ‖⁶` for `m ∈ K` and small `Δ`, with the
  quartic form `Q_m(Δ) = (1/24) ∂_Δ ∂_Δ g(Δ, Δ) − (1/12) g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m`
  (`midJet`, `DistExpansion.lean`). About the midpoint the terms of order three and five vanish,
  so the error is of order six, one order better than `dist_sq_expansion_midpoint`.

The upper bound of the first theorem comes from the trial curve `x + t w + ½ t (1 − t) Γ_x(w, w)`
of `DistExpansion.lean`: with the metric replaced by its third-order Taylor polynomial, its energy
is `F₅_x(w)` up to `O(‖w‖⁶)` (`energy_trial_le6`). The lower bound is the calibration of
`Quintic.lean`.

The second theorem applies the first at `x = m − Δ/2` and re-expands `F₅` about `m` along the
segment: the metric part by a fourth-order Taylor estimate on `[−½, 0]` (`abs_midComb4_le`,
`abs_jetPoly_mid6_le`), and the Christoffel term `g(Γ(Δ, Δ), Γ(Δ, Δ))` by a second-order one
(`abs_chrTerm_mid_le`), whose first-order term is computed from the identity
`g(p, Γ(Δ, Δ)) = g(p, ∂_Δ g Δ) − ½ ∂_p g(Δ, Δ)` (`dot_mulVec_chrDeriv`).

The expansion is the coordinate form of the expansion of Synge's world function about one end
point; see L. Brewin, *Riemann normal coordinate expansions using Cadabra*, arXiv:0903.2087
(2009), Section 9.
-/

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## The energy of the trial curve to sixth order -/

/-- The terms of order five in `w` of the energy density of the trial curve, with the metric
replaced by its Taylor polynomial at `x` (`γ = Γ_x(w, w)`, `β = ½ (1 − 2t)`, `b = ½ t (1 − t)`):
`t β² γ·A(w)γ + b β (w·A(γ)γ + γ·A(γ)w) + ½ t² β (w·B(w,w)γ + γ·B(w,w)w)
+ ½ t b (w·B(w,γ)w + w·B(γ,w)w) + ⅙ t³ w·C(w,w,w)w`. -/
noncomputable def trialQuint (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  t * ((1 - 2 * t) / 2) ^ 2 * (chr g x w w ⬝ᵥ (dmat g x w *ᵥ chr g x w w))
    + t * (1 - t) / 2 * ((1 - 2 * t) / 2) * (w ⬝ᵥ (dmat g x (chr g x w w) *ᵥ chr g x w w)
      + chr g x w w ⬝ᵥ (dmat g x (chr g x w w) *ᵥ w))
    + 1 / 2 * t ^ 2 * ((1 - 2 * t) / 2) * (w ⬝ᵥ (ddmat g x w w *ᵥ chr g x w w)
      + chr g x w w ⬝ᵥ (ddmat g x w w *ᵥ w))
    + 1 / 2 * t * (t * (1 - t) / 2) * (w ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ w)
      + w ⬝ᵥ (ddmat g x (chr g x w w) w *ᵥ w))
    + 1 / 6 * t ^ 3 * (w ⬝ᵥ (dddmat g x w w w *ᵥ w))

/-- The remainder of the energy density of the trial curve at sixth order: the Taylor remainder
of the metric beyond `taylorMetric3` and the terms of order at least six in `w`. -/
noncomputable def trialRem6 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  trialVel g x w t ⬝ᵥ ((g (trial g x w t) - taylorMetric3 g x (trial g x w t - x)) *ᵥ
      trialVel g x w t)
    + t * (1 - t) / 2 * ((1 - 2 * t) / 2) ^ 2 *
      (chr g x w w ⬝ᵥ (dmat g x (chr g x w w) *ᵥ chr g x w w))
    + 1 / 2 * t ^ 2 * ((1 - 2 * t) / 2) ^ 2 * (chr g x w w ⬝ᵥ (ddmat g x w w *ᵥ chr g x w w))
    + 1 / 2 * t * (t * (1 - t) / 2) * ((1 - 2 * t) / 2) *
      (chr g x w w ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ trialVel g x w t)
        + w ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ chr g x w w))
    + 1 / 2 * t * (t * (1 - t) / 2) * ((1 - 2 * t) / 2) *
      (chr g x w w ⬝ᵥ (ddmat g x (chr g x w w) w *ᵥ trialVel g x w t)
        + w ⬝ᵥ (ddmat g x (chr g x w w) w *ᵥ chr g x w w))
    + 1 / 2 * (t * (1 - t) / 2) ^ 2 *
      (trialVel g x w t ⬝ᵥ (ddmat g x (chr g x w w) (chr g x w w) *ᵥ trialVel g x w t))
    + 1 / 6 * t ^ 3 * ((1 - 2 * t) / 2) *
      (chr g x w w ⬝ᵥ (dddmat g x w w w *ᵥ trialVel g x w t)
        + w ⬝ᵥ (dddmat g x w w w *ᵥ chr g x w w))
    + 1 / 6 * (trialVel g x w t ⬝ᵥ (dddmat g x ((t * (1 - t) / 2) • chr g x w w)
          (trial g x w t - x) (trial g x w t - x) *ᵥ trialVel g x w t)
      + trialVel g x w t ⬝ᵥ (dddmat g x (t • w) ((t * (1 - t) / 2) • chr g x w w)
          (trial g x w t - x) *ᵥ trialVel g x w t)
      + trialVel g x w t ⬝ᵥ (dddmat g x (t • w) (t • w) ((t * (1 - t) / 2) • chr g x w w) *ᵥ
          trialVel g x w t))

/-- **The energy density of the trial curve to sixth order** splits into the terms of order at
most four, the terms of order five and the remainder. -/
theorem normSq_trial_eq6 (x w : Fin n → ℝ) (t : ℝ) :
    normSq g (trial g x w t) (trialVel g x w t) =
      trialPoly g x w t + trialQuint g x w t + trialRem6 g x w t := by
  have e : normSq g (trial g x w t) (trialVel g x w t) =
      trialVel g x w t ⬝ᵥ (taylorMetric3 g x (trial g x w t - x) *ᵥ trialVel g x w t) +
      trialVel g x w t ⬝ᵥ ((g (trial g x w t) - taylorMetric3 g x (trial g x w t - x)) *ᵥ
        trialVel g x w t) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]; unfold normSq; ring
  rw [e, trialRem6, trial_sub]
  simp only [trialPoly, trialQuint, trialVel, taylorMetric3, taylorMetric, dmat_add, dmat_smul,
    ddmat_add_left, ddmat_add_right, ddmat_smul_left, ddmat_smul_right, dddmat_add_left,
    dddmat_add_mid, dddmat_add_right, dddmat_smul_left, dddmat_smul_mid, dddmat_smul_right,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- **The integral of the energy density to sixth order**, for arbitrary coefficients. -/
theorem integral_trialShape6 (A0 A1 A2 A3 A4 A5 A6 Q1 Q2 Q3 Q4 Q5 K : ℝ) :
    ∫ t in (0 : ℝ)..1, (A0 + (1 - 2 * t) / 2 * A1 + ((1 - 2 * t) / 2) ^ 2 * A2 + t * A3
      + t * ((1 - 2 * t) / 2) * A4 + t * (1 - t) / 2 * A5 + 1 / 2 * t ^ 2 * A6
      + (t * ((1 - 2 * t) / 2) ^ 2 * Q1 + t * (1 - t) / 2 * ((1 - 2 * t) / 2) * Q2
        + 1 / 2 * t ^ 2 * ((1 - 2 * t) / 2) * Q3 + 1 / 2 * t * (t * (1 - t) / 2) * Q4
        + 1 / 6 * t ^ 3 * Q5) + K) =
    A0 + A2 / 12 + A3 / 2 - A4 / 12 + A5 / 12 + A6 / 6 + Q1 / 24 - Q3 / 24 + Q4 / 48 + Q5 / 24
      + K := by
  have hQ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => (A0 + A1 / 2 + A2 / 4 + K) * t
      + (-A1 - A2 + A3 + A4 / 2 + A5 / 2 + Q1 / 4 + Q2 / 4) / 2 * t ^ 2
      + (A2 - A4 - A5 / 2 + A6 / 2 - Q1 - 3 * Q2 / 4 + Q3 / 4 + Q4 / 4) / 3 * t ^ 3
      + (Q1 + Q2 / 2 - Q3 / 2 - Q4 / 4 + Q5 / 6) / 4 * t ^ 4)
      (A0 + (1 - 2 * t) / 2 * A1 + ((1 - 2 * t) / 2) ^ 2 * A2 + t * A3
        + t * ((1 - 2 * t) / 2) * A4 + t * (1 - t) / 2 * A5 + 1 / 2 * t ^ 2 * A6
        + (t * ((1 - 2 * t) / 2) ^ 2 * Q1 + t * (1 - t) / 2 * ((1 - 2 * t) / 2) * Q2
          + 1 / 2 * t ^ 2 * ((1 - 2 * t) / 2) * Q3 + 1 / 2 * t * (t * (1 - t) / 2) * Q4
          + 1 / 6 * t ^ 3 * Q5) + K) t := by
    intro t _
    exact (((((hasDerivAt_id' t).const_mul _).add ((hasDerivAt_pow 2 t).const_mul _)).add
      ((hasDerivAt_pow 3 t).const_mul _)).add ((hasDerivAt_pow 4 t).const_mul _)).congr_deriv
      (by norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

namespace LocalJet3

variable {x : Fin n → ℝ} {B δ l : ℝ}

/-- **The remainder of the trial curve at sixth order** is at most `107 B⁷ ‖w‖⁶` on `[0, 1]`. -/
theorem trialRem6_le (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : 2 * B * ‖w‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : trialRem6 g x w t ≤ 107 * (B ^ 7 * ‖w‖ ^ 6) := by
  have j := h.toLocalJet
  have hB0 := j.B_nonneg
  have hw1 := j.norm_le_one_of hw
  have hV := j.norm_trialVel_le hw ht
  have hu := j.norm_trial_sub_le hw ht
  have htay := h.tay3_le _ (hu.trans hw) (trialVel g x w t) (trialVel g x w t)
  rw [add_sub_cancel] at htay
  have hΓ := j.norm_chr_le w
  have cT : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have cT3 : |t ^ 3| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) cT
  have cS : |(1 - 2 * t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have cτ : |t * (1 - t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
  have ch : |(1 / 2 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have c6 : |(1 / 6 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have htw : ‖t • w‖ ≤ ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) cT
  have hbγ : ‖(t * (1 - t) / 2) • chr g x w w‖ ≤ B * ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]; exact (mul_le_of_le_one_left (norm_nonneg _) cτ).trans hΓ
  unfold trialRem6
  set Γ := chr g x w w
  set V := trialVel g x w t
  set u := trial g x w t - x
  set bΓ := (t * (1 - t) / 2) • Γ
  have mono : ∀ {a b : ℕ}, a ≤ 7 → 6 ≤ b → B ^ a * ‖w‖ ^ b ≤ B ^ 7 * ‖w‖ ^ 6 :=
    fun ha hb => j.monom_le hw1 ha hb
  have t0 : |V ⬝ᵥ ((g (trial g x w t) - taylorMetric3 g x u) *ᵥ V)| ≤ 64 * (B ^ 7 * ‖w‖ ^ 6) :=
    calc _ ≤ B * ‖u‖ ^ 4 * ‖V‖ * ‖V‖ := htay
      _ ≤ B * (2 * B * ‖w‖) ^ 4 * (2 * B * ‖w‖) * (2 * B * ‖w‖) := by gcongr
      _ = 64 * (B ^ 7 * ‖w‖ ^ 6) := by ring
  have x1 : |Γ ⬝ᵥ (dmat g x Γ *ᵥ Γ)| ≤ B ^ 7 * ‖w‖ ^ 6 :=
    calc _ ≤ B * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) := j.d_le_of hΓ hΓ hΓ
      _ = B ^ 4 * ‖w‖ ^ 6 := by ring
      _ ≤ _ := mono (by norm_num) le_rfl
  have x2 : |Γ ⬝ᵥ (ddmat g x w w *ᵥ Γ)| ≤ B ^ 7 * ‖w‖ ^ 6 :=
    calc _ ≤ B * ‖w‖ * ‖w‖ * (B * ‖w‖ ^ 2) * (B * ‖w‖ ^ 2) := j.dd_le_of le_rfl le_rfl hΓ hΓ
      _ = B ^ 3 * ‖w‖ ^ 6 := by ring
      _ ≤ _ := mono (by norm_num) le_rfl
  have m4 := mono (a := 4) (b := 6) (by norm_num) le_rfl
  have m3 := mono (a := 3) (b := 6) (by norm_num) le_rfl
  have m2 := mono (a := 2) (b := 6) (by norm_num) le_rfl
  have m5 := mono (a := 5) (b := 6) (by norm_num) le_rfl
  have m6 := mono (a := 6) (b := 6) (by norm_num) le_rfl
  have x3 : |Γ ⬝ᵥ (ddmat g x w Γ *ᵥ V) + w ⬝ᵥ (ddmat g x w Γ *ᵥ Γ)| ≤
      3 * (B ^ 7 * ‖w‖ ^ 6) := by
    have a := j.dd_le_of (le_refl ‖w‖) hΓ hΓ hV
    have b := j.dd_le_of (le_refl ‖w‖) hΓ (le_refl ‖w‖) hΓ
    refine (abs_add_le _ _).trans ?_
    linarith
  have x4 : |Γ ⬝ᵥ (ddmat g x Γ w *ᵥ V) + w ⬝ᵥ (ddmat g x Γ w *ᵥ Γ)| ≤
      3 * (B ^ 7 * ‖w‖ ^ 6) := by
    have a := j.dd_le_of hΓ (le_refl ‖w‖) hΓ hV
    have b := j.dd_le_of hΓ (le_refl ‖w‖) (le_refl ‖w‖) hΓ
    refine (abs_add_le _ _).trans ?_
    linarith
  have x5 : |V ⬝ᵥ (ddmat g x Γ Γ *ᵥ V)| ≤ 4 * (B ^ 7 * ‖w‖ ^ 6) := by
    have a := j.dd_le_of hΓ hΓ hV hV
    linarith
  have x6 : |Γ ⬝ᵥ (dddmat g x w w w *ᵥ V) + w ⬝ᵥ (dddmat g x w w w *ᵥ Γ)| ≤
      3 * (B ^ 7 * ‖w‖ ^ 6) := by
    have a := h.ddd_le_of (le_refl ‖w‖) (le_refl ‖w‖) (le_refl ‖w‖) hΓ hV
    have b := h.ddd_le_of (le_refl ‖w‖) (le_refl ‖w‖) (le_refl ‖w‖) (le_refl ‖w‖) hΓ
    refine (abs_add_le _ _).trans ?_
    linarith
  have x7 : |V ⬝ᵥ (dddmat g x bΓ u u *ᵥ V) + V ⬝ᵥ (dddmat g x (t • w) bΓ u *ᵥ V)
      + V ⬝ᵥ (dddmat g x (t • w) (t • w) bΓ *ᵥ V)| ≤ 28 * (B ^ 7 * ‖w‖ ^ 6) := by
    have a := h.ddd_le_of hbγ hu hu hV hV
    have b := h.ddd_le_of htw hbγ hu hV hV
    have c := h.ddd_le_of htw htw hbγ hV hV
    refine (abs_add_three _ _ _).trans ?_
    linarith
  have y0 := (le_abs_self _).trans t0
  have y1 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of cτ (abs_sq_le_one_of cS)) x1
  have y2 := mul_le_of_abs_coef_le_one
    (abs_mul_le_one_of (abs_mul_le_one_of ch (abs_sq_le_one_of cT)) (abs_sq_le_one_of cS)) x2
  have y3 := mul_le_of_abs_coef_le_one
    (abs_mul_le_one_of (abs_mul_le_one_of (abs_mul_le_one_of ch cT) cτ) cS) x3
  have y4 := mul_le_of_abs_coef_le_one
    (abs_mul_le_one_of (abs_mul_le_one_of (abs_mul_le_one_of ch cT) cτ) cS) x4
  have y5 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of ch (abs_sq_le_one_of cτ)) x5
  have y6 := mul_le_of_abs_coef_le_one (abs_mul_le_one_of (abs_mul_le_one_of c6 cT3) cS) x6
  have y7 := mul_le_of_abs_coef_le_one c6 x7
  linarith

/-- **The energy of the trial curve** is at most `F₅_x(w) + 107 B⁷ ‖w‖⁶`. -/
theorem energy_trial_le6 (hg : IsRiemMetric g U) (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ}
    (hw : 2 * B * ‖w‖ ≤ δ) :
    energy g (trial g x w) 0 1 ≤ distJet5 g x w + 107 * (B ^ 7 * ‖w‖ ^ 6) := by
  have j := h.toLocalJet
  have hx : x ∈ U := by simpa using j.mem 0 (by simpa using j.δ_pos.le)
  have hd : deriv (trial g x w) = trialVel g x w :=
    funext fun t => (hasDerivAt_trial x w t).deriv
  have hint := j.intervalIntegrable_normSq_trial hg hw
  rw [hd] at hint
  have hint2 : IntervalIntegrable (fun t => trialPoly g x w t + trialQuint g x w t
      + 107 * (B ^ 7 * ‖w‖ ^ 6)) volume 0 1 := by
    apply Continuous.intervalIntegrable; unfold trialPoly trialQuint; fun_prop
  have hle : energy g (trial g x w) 0 1 ≤
      ∫ t in (0 : ℝ)..1, (trialPoly g x w t + trialQuint g x w t + 107 * (B ^ 7 * ‖w‖ ^ 6)) := by
    unfold energy; rw [hd]
    refine intervalIntegral.integral_mono_on zero_le_one hint hint2 fun t ht => ?_
    rw [normSq_trial_eq6]
    linarith [h.trialRem6_le hw ht]
  refine hle.trans (le_of_eq ?_)
  unfold trialPoly trialQuint
  rw [integral_trialShape6]
  have hchr := hg.coord.dot_mulVec_chr hx (chr g x w w) w w
  have hsym := dot_mulVec_comm (hg.coord.dmat_transpose hx w) w (chr g x w w)
  have hsym2 := dot_mulVec_comm (hg.coord.ddmat_transpose hx w w) w (chr g x w w)
  have hcomm : w ⬝ᵥ (ddmat g x (chr g x w w) w *ᵥ w) = w ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ w) := by
    rw [hg.coord.ddmat_comm hx]
  unfold distJet5 quint distJet
  linarith

/-- **The upper bound to sixth order**: `d(x, x + w)² ≤ F₅_x(w) + 107 B⁷ ‖w‖⁶` when
`2 B ‖w‖ ≤ δ`. -/
theorem dist_sq_le6 (hg : IsRiemMetric g U) (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ}
    (hw : 2 * B * ‖w‖ ≤ δ) :
    dist g U x (x + w) ^ 2 ≤ distJet5 g x w + 107 * (B ^ 7 * ‖w‖ ^ 6) := by
  have j := h.toLocalJet
  have hadm := j.isAdmissible_trial hw
  have hLE := length_sq_le_energy hg zero_le_one hadm.mem (hg.intervalIntegrable_speed hadm)
    (j.intervalIntegrable_normSq_trial hg hw)
  rw [sub_zero, one_mul] at hLE
  have hdl := pow_le_pow_left₀ dist_nonneg (dist_le_length (g := g) hadm) 2
  linarith [h.energy_trial_le6 hg hw]

end LocalJet3

/-- **The expansion of the squared distance to sixth order.** For a Riemannian coordinate metric
`g` on `U` and a compact `K ⊆ U` there are `C` and `r > 0` such that for `x ∈ K` and `‖w‖ ≤ r`,
`|d(x, x + w)² - F₅_x(w)| ≤ C ‖w‖⁶`, with `F₅ = distJet + quint` (`distJet5`). -/
theorem IsRiemMetric.dist_sq_expansion6 (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ w : Fin n → ℝ, ‖w‖ ≤ r →
      |dist g U x (x + w) ^ 2 - distJet5 g x w| ≤ C * ‖w‖ ^ 6 := by
  obtain ⟨B, δ, l, hJ⟩ := hg.exists_localJet3 hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have h₀ := (hJ x₀ hx₀).toLocalJet
  have hB1 := h₀.one_le
  have hB : 0 < B := by linarith
  have hl := h₀.l_pos
  have hδ := h₀.δ_pos
  set A := 3 * B ^ 3 / l + 1 with hAdef
  have hA : 1 ≤ A := by have : 0 ≤ 3 * B ^ 3 / l := by positivity
                        linarith
  have hA0 : 0 < A := by linarith
  have hAl : 3 * B ^ 3 ≤ l * A := by
    have : l * A = 3 * B ^ 3 + l := by rw [hAdef]; field_simp
    linarith
  set κ := calibConst5 B l
  have hκ : 0 ≤ κ := calibConst5_nonneg hB.le hl
  refine ⟨6 * κ * A ^ 4 * B ^ 3 + 107 * B ^ 7,
    min (min (δ / A) (l / (4 * B ^ 3 * A))) (δ / (2 * B)), by positivity, ?_⟩
  intro x hx w hwr
  have h := hJ x hx
  have j := h.toLocalJet
  have hr1 : ‖w‖ ≤ δ / A := (hwr.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hr2 : ‖w‖ ≤ l / (4 * B ^ 3 * A) := (hwr.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hr3 : ‖w‖ ≤ δ / (2 * B) := hwr.trans (min_le_right _ _)
  rw [le_div_iff₀ hA0] at hr1
  rw [le_div_iff₀ (by positivity)] at hr2
  rw [le_div_iff₀ (by positivity)] at hr3
  have hw1 : A * ‖w‖ ≤ δ := by linarith
  have hw2 : B ^ 3 * (A * ‖w‖) ≤ l / 4 := by nlinarith
  have hw3 : 2 * B * ‖w‖ ≤ δ := by linarith
  have hwle1 : ‖w‖ ≤ 1 := j.norm_le_one_of hw3
  have hup := h.dist_sq_le6 hg hw3
  have hlow := h.sqrt_distJet5_le_dist hg hA hAl hw1 hw2 ⟨_, j.isAdmissible_trial hw3⟩
  have hBw : B ^ 3 * ‖w‖ ≤ l / 4 :=
    le_trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (norm_nonneg w) hA)
      (by positivity)) hw2
  have hF0 : 0 ≤ distJet5 g x w :=
    le_trans (by positivity) (h.distJet5_ge_half hwle1 hBw)
  have hF1 := h.distJet5_le hwle1
  have hk : 1 ≤ 1 + κ * (A * ‖w‖) ^ 4 := by
    have : 0 ≤ κ * (A * ‖w‖) ^ 4 := by positivity
    linarith
  have hsub := sub_sq_le_of_sqrt_le hF0 hk hlow
  have hsub' : 2 * (1 + κ * (A * ‖w‖) ^ 4 - 1) * distJet5 g x w ≤
      6 * κ * A ^ 4 * B ^ 3 * ‖w‖ ^ 6 :=
    calc 2 * (1 + κ * (A * ‖w‖) ^ 4 - 1) * distJet5 g x w
        ≤ 2 * (1 + κ * (A * ‖w‖) ^ 4 - 1) * (3 * (B ^ 3 * ‖w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hF1 (by positivity)
      _ = 6 * κ * A ^ 4 * B ^ 3 * ‖w‖ ^ 6 := by ring
  have h107 : 0 ≤ 107 * B ^ 7 * ‖w‖ ^ 6 := by positivity
  have h6 : 0 ≤ 6 * κ * A ^ 4 * B ^ 3 * ‖w‖ ^ 6 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The squared distance about the midpoint to sixth order -/

/-- `|Σ_k b_k| ≤ n B` if `|b_k| ≤ B`. -/
theorem abs_usum_le {b : Fin n → ℝ} {B : ℝ} (hb : ∀ k, |b k| ≤ B) : |∑ k, b k| ≤ n * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hb k

/-- The one-variable identity behind the midpoint form to the next order: expanding about `0`,
`ψ(-½) + ½ ψ'(-½) + ⅙ ψ''(-½) + (1/24) ψ'''(-½) = ψ(0) + ψ''(0)/24` up to `3K/16` if the fourth
derivative is bounded by `K` on `[-½, 0]` (the coefficients of `ψ'(0)`, `ψ''(0)` and `ψ'''(0)` on
the left are `0`, `1/24` and `0`). -/
theorem abs_midComb4_le {ψ0 ψ1 ψ2 ψ3 ψ4 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ0 (ψ1 s) s)
    (d1 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ1 (ψ2 s) s)
    (d2 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ2 (ψ3 s) s)
    (d3 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ3 (ψ4 s) s)
    (hb : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, |ψ4 s| ≤ K) :
    |ψ0 (-1 / 2) + 1 / 2 * ψ1 (-1 / 2) + 1 / 6 * ψ2 (-1 / 2) + 1 / 24 * ψ3 (-1 / 2)
      - ψ0 0 - 1 / 24 * ψ2 0| ≤ 3 * K / 16 := by
  have hm : ∀ s ∈ Icc (0 : ℝ) 1, -s / 2 ∈ Icc (-1 / 2 : ℝ) 0 := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have c : ∀ (φ φ' : ℝ → ℝ) (c₀ : ℝ), (∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt φ (φ' s) s) →
      ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => c₀ * φ (-t / 2)) (-1 / 2 * c₀ * φ' (-s / 2)) s := by
    intro φ φ' c₀ h s hs
    have h1 : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    exact (((h _ (hm s hs)).comp s h1).const_mul c₀).congr_deriv (by ring)
  have hb' : ∀ (c₀ : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, |c₀ * ψ4 (-s / 2)| ≤ |c₀| * K := fun c₀ s hs => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb _ (hm s hs)) (abs_nonneg _)
  have t4 := taylor_aux_four (c ψ0 ψ1 1 d0) (c ψ1 ψ2 _ d1) (c ψ2 ψ3 _ d2) (c ψ3 ψ4 _ d3)
    (hb' (-1 / 2 * (-1 / 2 * (-1 / 2 * (-1 / 2 * 1)))))
  have t3 := taylor_aux_three (c ψ1 ψ2 1 d1) (c ψ2 ψ3 _ d2) (c ψ3 ψ4 _ d3)
    (hb' (-1 / 2 * (-1 / 2 * (-1 / 2 * 1))))
  have t2 := taylor_aux_two (c ψ2 ψ3 1 d2) (c ψ3 ψ4 _ d3) (hb' (-1 / 2 * (-1 / 2 * 1)))
  have t1 := taylor_aux_one (c ψ3 ψ4 1 d3) (hb' (-1 / 2 * 1))
  simp only [neg_zero, zero_div] at t1 t2 t3 t4
  norm_num at t1 t2 t3 t4
  rw [abs_le] at t1 t2 t3 t4 ⊢
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]

/-- **The metric part about the midpoint to sixth order.** If the fourth partial derivatives of
`g` are bounded by `M` on the segment from `m - Δ/2` to `m`, then the terms of `F₅` at `m - Δ/2`
built from `g` and its derivatives alone differ from `g(Δ, Δ) + (1/24) ∂_Δ ∂_Δ g(Δ, Δ)` at `m` by
at most `3 n⁶ M ‖Δ‖⁶ / 16`. -/
theorem abs_jetPoly_mid6_le (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {M : ℝ}
    (hseg : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, m + s • Δ ∈ U)
    (hM : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, ∀ i j k l p q : Fin n,
      |Lightlike.pd q (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j)))) (m + s • Δ)| ≤ M) :
    |Δ ⬝ᵥ (g (m - (1 / 2 : ℝ) • Δ) *ᵥ Δ)
      + (1 / 2) * (Δ ⬝ᵥ (dmat g (m - (1 / 2 : ℝ) • Δ) Δ *ᵥ Δ))
      + (1 / 6) * (Δ ⬝ᵥ (ddmat g (m - (1 / 2 : ℝ) • Δ) Δ Δ *ᵥ Δ))
      + (1 / 24) * (Δ ⬝ᵥ (dddmat g (m - (1 / 2 : ℝ) • Δ) Δ Δ Δ *ᵥ Δ))
      - Δ ⬝ᵥ (g m *ᵥ Δ) - (1 / 24) * (Δ ⬝ᵥ (ddmat g m Δ Δ *ᵥ Δ))| ≤
      3 * (n ^ 6 * M * ‖Δ‖ ^ 6) / 16 := by
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
  have e3 : ∀ z, Δ ⬝ᵥ (dddmat g z Δ Δ Δ *ᵥ Δ) =
      ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l * ∑ p, Δ p *
        Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) z :=
    fun z => by
      rw [dot_mulVec_eq_nest]
      simp only [dddmat, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  have key := abs_midComb4_le
    (ψ0 := fun s => ∑ i, Δ i * ∑ j, Δ j * g (m + s • Δ) i j)
    (ψ1 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * Lightlike.pd k (fun y => g y i j) (m + s • Δ))
    (ψ2 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l *
      Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) (m + s • Δ))
    (ψ3 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l * ∑ p, Δ p *
      Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) (m + s • Δ))
    (ψ4 := fun s => ∑ i, Δ i * ∑ j, Δ j * ∑ k, Δ k * ∑ l, Δ l * ∑ p, Δ p * ∑ q, Δ q *
      Lightlike.pd q (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j)))) (m + s • Δ))
    (K := n ^ 6 * M * ‖Δ‖ ^ 6)
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j =>
      hasDerivAt_line (hg.smooth i j) hg.isOpen (hseg s hs))
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
      hasDerivAt_line (hg.contDiffOn_pdg k i j) hg.isOpen (hseg s hs))
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
      hasDerivAt_wsum fun l =>
        hasDerivAt_line (Lightlike.contDiffOn_pd (hg.contDiffOn_pdg k i j) hg.isOpen l) hg.isOpen
          (hseg s hs))
    (fun s hs => hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
      hasDerivAt_wsum fun l => hasDerivAt_wsum fun p =>
        hasDerivAt_line (Lightlike.contDiffOn_pd (Lightlike.contDiffOn_pd (hg.contDiffOn_pdg k i j)
          hg.isOpen l) hg.isOpen p) hg.isOpen (hseg s hs))
    (fun s hs => (abs_wsum_le fun i => abs_wsum_le fun j => abs_wsum_le fun k =>
      abs_wsum_le fun l => abs_wsum_le fun p => abs_wsum_le fun q =>
        hM s hs i j k l p q).trans_eq (by ring))
  have hx : m + (-1 / 2 : ℝ) • Δ = m - (1 / 2 : ℝ) • Δ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, neg_smul, ← sub_eq_add_neg]
  simp only [hx, zero_smul, add_zero] at key
  simp only [e0, e1, e2, e3]
  exact key

/-- The products `Γ^i_{ab} g_{ij} Γ^j_{cd}` of the Christoffel symbols and the metric, whose
contraction with `Δ` four times is `g(Γ(Δ, Δ), Γ(Δ, Δ))` (`chrTerm_eq_sum`). -/
noncomputable def chrProd (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i a b j c d : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  Lightlike.christoffel g i a b y * g y i j * Lightlike.christoffel g j c d y

/-- The products `chrProd` are smooth on `U`. -/
theorem contDiffOn_chrProd (hg : Lightlike.IsCoordMetric g U) (i a b j c d : Fin n) :
    ContDiffOn ℝ ∞ (chrProd g i a b j c d) U := by
  unfold chrProd
  exact ((hg.contDiffOn_christoffel i a b).mul (hg.smooth i j)).mul
    (hg.contDiffOn_christoffel j c d)

/-- The second partial derivatives of the products `chrProd` are bounded on a compact set. -/
theorem exists_chrProd_bound (hg : Lightlike.IsCoordMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M, 0 ≤ M ∧ ∀ z ∈ K, ∀ i a b j c d k l : Fin n,
      |Lightlike.pd l (Lightlike.pd k (chrProd g i a b j c d)) z| ≤ M := by
  obtain ⟨M, h0, hM⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n × Fin n × Fin n × Fin n × Fin n) =>
      Lightlike.pd t.2.2.2.2.2.2.2 (Lightlike.pd t.2.2.2.2.2.2.1
        (chrProd g t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1)))
    fun t => (Lightlike.contDiffOn_pd (Lightlike.contDiffOn_pd (contDiffOn_chrProd hg _ _ _ _ _ _) hg.isOpen _)
      hg.isOpen _).continuousOn.mono hKU
  exact ⟨M, h0, fun z hz i a b j c d k l => hM (i, a, b, j, c, d, k, l) z hz⟩

/-- `g(Γ(Δ, Δ), Γ(Δ, Δ)) = Σ Δ^a Δ^b Δ^c Δ^d Γ^i_{ab} g_{ij} Γ^j_{cd}`. -/
theorem chrTerm_eq_sum (y Δ : Fin n → ℝ) :
    chr g y Δ Δ ⬝ᵥ (g y *ᵥ chr g y Δ Δ) =
      ∑ i, ∑ a, Δ a * ∑ b, Δ b * ∑ j, ∑ c, Δ c * ∑ d, Δ d * chrProd g i a b j c d y := by
  simp only [dotProduct, Matrix.mulVec, chr, chrProd]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- The derivative of `s ↦ g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m + s Δ`, in the form of `chrTerm_eq_sum`. -/
noncomputable def chrLine1 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (m Δ : Fin n → ℝ)
    (s : ℝ) : ℝ :=
  ∑ i, ∑ a, Δ a * ∑ b, Δ b * ∑ j, ∑ c, Δ c * ∑ d, Δ d * ∑ k, Δ k *
    Lightlike.pd k (chrProd g i a b j c d) (m + s • Δ)

/-- The second derivative of `s ↦ g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m + s Δ`. -/
noncomputable def chrLine2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (m Δ : Fin n → ℝ)
    (s : ℝ) : ℝ :=
  ∑ i, ∑ a, Δ a * ∑ b, Δ b * ∑ j, ∑ c, Δ c * ∑ d, Δ d * ∑ k, Δ k * ∑ l, Δ l *
    Lightlike.pd l (Lightlike.pd k (chrProd g i a b j c d)) (m + s • Δ)

/-- The derivative of `s ↦ g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m + s Δ` along the line is `chrLine1`. -/
theorem hasDerivAt_chrTerm_line (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {s : ℝ}
    (hs : m + s • Δ ∈ U) :
    HasDerivAt (fun s => chr g (m + s • Δ) Δ Δ ⬝ᵥ (g (m + s • Δ) *ᵥ chr g (m + s • Δ) Δ Δ))
      (chrLine1 g m Δ s) s := by
  simp only [chrTerm_eq_sum]
  unfold chrLine1
  exact HasDerivAt.fun_sum fun i _ => hasDerivAt_wsum fun a => hasDerivAt_wsum fun b =>
    HasDerivAt.fun_sum fun j _ => hasDerivAt_wsum fun c => hasDerivAt_wsum fun d =>
      hasDerivAt_line (contDiffOn_chrProd hg i a b j c d) hg.isOpen hs

/-- The derivative of `chrLine1` along the line is `chrLine2`. -/
theorem hasDerivAt_chrLine1 (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {s : ℝ}
    (hs : m + s • Δ ∈ U) : HasDerivAt (fun s => chrLine1 g m Δ s) (chrLine2 g m Δ s) s := by
  unfold chrLine1 chrLine2
  exact HasDerivAt.fun_sum fun i _ => hasDerivAt_wsum fun a => hasDerivAt_wsum fun b =>
    HasDerivAt.fun_sum fun j _ => hasDerivAt_wsum fun c => hasDerivAt_wsum fun d =>
      hasDerivAt_wsum fun k =>
        hasDerivAt_line (Lightlike.contDiffOn_pd (contDiffOn_chrProd hg i a b j c d) hg.isOpen k)
          hg.isOpen hs

/-- `|chrLine2| ≤ n⁸ M ‖Δ‖⁶` if the second partial derivatives of the products `chrProd` are
bounded by `M` at `m + s Δ`. -/
theorem abs_chrLine2_le {m Δ : Fin n → ℝ} {s M : ℝ}
    (hM : ∀ i a b j c d k l : Fin n, |Lightlike.pd l (Lightlike.pd k (chrProd g i a b j c d)) (m + s • Δ)| ≤ M) :
    |chrLine2 g m Δ s| ≤ n ^ 8 * M * ‖Δ‖ ^ 6 := by
  unfold chrLine2
  exact (abs_usum_le fun i => abs_wsum_le fun a => abs_wsum_le fun b => abs_usum_le fun j =>
    abs_wsum_le fun c => abs_wsum_le fun d => abs_wsum_le fun k => abs_wsum_le fun l =>
      hM i a b j c d k l).trans_eq (by ring)

/-- The derivative of the Christoffel term `Γ(u, v)` along a line in the direction `Δ`. -/
noncomputable def chrDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y Δ u v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, ∑ k, (∑ l, Δ l * Lightlike.pd l (Lightlike.christoffel g i j k) y) * u j * v k

/-- The derivative of `s ↦ Γ_{m + s Δ}(u, v)` is `chrDeriv`. -/
theorem hasDerivAt_chr_line (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {s : ℝ}
    (hs : m + s • Δ ∈ U) (u v : Fin n → ℝ) :
    HasDerivAt (fun s => chr g (m + s • Δ) u v) (chrDeriv g (m + s • Δ) Δ u v) s := by
  rw [hasDerivAt_pi]
  intro i
  simp only [chr, chrDeriv]
  exact HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ =>
    ((hasDerivAt_line (hg.contDiffOn_christoffel i j k) hg.isOpen hs).mul_const _).mul_const _

/-- Product rule for `s ↦ g(m + s Δ) q(s)`: the derivative is `∂_Δ g q + g q'`. -/
theorem hasDerivAt_mulVec_line (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {s : ℝ}
    (hs : m + s • Δ ∈ U) {q : ℝ → Fin n → ℝ} {q' : Fin n → ℝ} (hq : HasDerivAt q q' s) :
    HasDerivAt (fun s => g (m + s • Δ) *ᵥ q s)
      (dmat g (m + s • Δ) Δ *ᵥ q s + g (m + s • Δ) *ᵥ q') s := by
  rw [hasDerivAt_pi]
  intro i
  simp only [Matrix.mulVec, dotProduct, dmat, Matrix.of_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun j _ =>
    (hasDerivAt_line (hg.smooth i j) hg.isOpen hs).mul (hasDerivAt_pi.1 hq j)

/-- The derivative of `s ↦ ∂_u g(p, q)` at `m + s Δ` along the line is `∂_Δ ∂_u g(p, q)`. -/
theorem hasDerivAt_dot_dmat_line (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {s : ℝ}
    (hs : m + s • Δ ∈ U) (p u q : Fin n → ℝ) :
    HasDerivAt (fun s => p ⬝ᵥ (dmat g (m + s • Δ) u *ᵥ q))
      (p ⬝ᵥ (ddmat g (m + s • Δ) u Δ *ᵥ q)) s := by
  have e : ∀ z, p ⬝ᵥ (dmat g z u *ᵥ q) =
      ∑ i, p i * ∑ j, q j * ∑ k, u k * Lightlike.pd k (fun y => g y i j) z := fun z => by
    rw [dot_mulVec_eq_nest]; rfl
  have e' : ∀ z, p ⬝ᵥ (ddmat g z u Δ *ᵥ q) =
      ∑ i, p i * ∑ j, q j * ∑ k, u k * ∑ l, Δ l * Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) z :=
    fun z => by
      rw [dot_mulVec_eq_nest]
      simp only [ddmat, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  simp only [e, e']
  exact hasDerivAt_wsum fun i => hasDerivAt_wsum fun j => hasDerivAt_wsum fun k =>
    hasDerivAt_line (hg.contDiffOn_pdg k i j) hg.isOpen hs

/-- **The derivative of the Christoffel term**, contracted with the metric: differentiating
`g(p, Γ(Δ, Δ)) = g(p, ∂_Δ g Δ) - ½ ∂_p g(Δ, Δ)` along the line in the direction `Δ`. -/
theorem dot_mulVec_chrDeriv (hg : Lightlike.IsCoordMetric g U) {m Δ : Fin n → ℝ} {s : ℝ}
    (hs : m + s • Δ ∈ U) (p : Fin n → ℝ) :
    p ⬝ᵥ (dmat g (m + s • Δ) Δ *ᵥ chr g (m + s • Δ) Δ Δ)
      + p ⬝ᵥ (g (m + s • Δ) *ᵥ chrDeriv g (m + s • Δ) Δ Δ Δ) =
      p ⬝ᵥ (ddmat g (m + s • Δ) Δ Δ *ᵥ Δ) - 1 / 2 * (Δ ⬝ᵥ (ddmat g (m + s • Δ) p Δ *ᵥ Δ)) := by
  have hcont : Continuous fun s : ℝ => m + s • Δ := by fun_prop
  have hU : ∀ᶠ s' in 𝓝 s, m + s' • Δ ∈ U :=
    hcont.continuousAt.preimage_mem_nhds (hg.isOpen.mem_nhds hs)
  have hL := hasDerivAt_dot (hasDerivAt_const s p)
    (hasDerivAt_mulVec_line hg hs (hasDerivAt_chr_line hg hs Δ Δ))
  have hR := (hasDerivAt_dot_dmat_line hg hs p Δ Δ).sub
    ((hasDerivAt_dot_dmat_line hg hs Δ p Δ).const_mul (1 / 2 : ℝ))
  have heq : (fun s' => p ⬝ᵥ (g (m + s' • Δ) *ᵥ chr g (m + s' • Δ) Δ Δ)) =ᶠ[𝓝 s]
      (fun s' => p ⬝ᵥ (dmat g (m + s' • Δ) Δ *ᵥ Δ)
        - 1 / 2 * (Δ ⬝ᵥ (dmat g (m + s' • Δ) p *ᵥ Δ))) := by
    filter_upwards [hU] with s' hs'
    rw [hg.dot_mulVec_chr hs']
    ring
  have h := hL.unique (hR.congr_of_eventuallyEq heq)
  rw [zero_dotProduct, zero_add, dotProduct_add] at h
  exact h

/-- Second-order Taylor estimate from `-½` to `0`:
`|ψ(0) - ψ(-½) - ½ ψ'(-½)| ≤ K/4` if `|ψ''| ≤ K` on `[-½, 0]`. -/
theorem abs_halfTaylor2_le {ψ0 ψ1 ψ2 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ0 (ψ1 s) s)
    (d1 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt ψ1 (ψ2 s) s)
    (hb : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, |ψ2 s| ≤ K) :
    |ψ0 0 - ψ0 (-1 / 2) - 1 / 2 * ψ1 (-1 / 2)| ≤ K / 4 := by
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, -1 / 2 + t / 2 ∈ Icc (-1 / 2 : ℝ) 0 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have c : ∀ (φ φ' : ℝ → ℝ) (c₀ : ℝ), (∀ s ∈ Icc (-1 / 2 : ℝ) 0, HasDerivAt φ (φ' s) s) →
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => c₀ * φ (-1 / 2 + t / 2))
        (1 / 2 * c₀ * φ' (-1 / 2 + t / 2)) t := by
    intro φ φ' c₀ h t ht
    have h1 : HasDerivAt (fun t : ℝ => -1 / 2 + t / 2) (1 / 2) t :=
      ((hasDerivAt_id' t).div_const 2).const_add (-1 / 2)
    exact (((h _ (hm t ht)).comp t h1).const_mul c₀).congr_deriv (by ring)
  have hb' : ∀ (c₀ : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, |c₀ * ψ2 (-1 / 2 + t / 2)| ≤ |c₀| * K :=
    fun c₀ t ht => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb _ (hm t ht)) (abs_nonneg _)
  have t2 := taylor_aux_two (c ψ0 ψ1 1 d0) (c ψ1 ψ2 _ d1) (hb' (1 / 2 * (1 / 2 * 1)))
  norm_num at t2
  rw [abs_le] at t2 ⊢
  constructor <;> linarith [t2.1, t2.2]

/-- **The Christoffel part about the midpoint to sixth order.** With `x = m - Δ/2` and
`γ = Γ_x(Δ, Δ)`, if the second partial derivatives of the products `chrProd` are bounded by `M`
on the segment from `x` to `m`, then
`g_m(Γ_m(Δ,Δ), Γ_m(Δ,Δ)) - g_x(γ, γ) - (g_x(γ, ∂²_Δ g Δ) - ½ ∂_γ ∂_Δ g(Δ, Δ) - ½ ∂_Δ g(γ, γ))`
is at most `n⁸ M ‖Δ‖⁶ / 4`; the subtracted bracket is half the derivative of
`s ↦ g(Γ(Δ, Δ), Γ(Δ, Δ))` at `x`. -/
theorem abs_chrTerm_mid_le (hg : Lightlike.IsCoordMetric g U) {m Δ x : Fin n → ℝ} {M : ℝ}
    (hx : m + (-1 / 2 : ℝ) • Δ = x)
    (hseg : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, m + s • Δ ∈ U)
    (hM : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, ∀ i a b j c d k l : Fin n,
      |Lightlike.pd l (Lightlike.pd k (chrProd g i a b j c d)) (m + s • Δ)| ≤ M) :
    |chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ) - chr g x Δ Δ ⬝ᵥ (g x *ᵥ chr g x Δ Δ)
      - (chr g x Δ Δ ⬝ᵥ (ddmat g x Δ Δ *ᵥ Δ) - 1 / 2 * (Δ ⬝ᵥ (ddmat g x (chr g x Δ Δ) Δ *ᵥ Δ))
        - 1 / 2 * (chr g x Δ Δ ⬝ᵥ (dmat g x Δ *ᵥ chr g x Δ Δ)))| ≤ n ^ 8 * M * ‖Δ‖ ^ 6 / 4 := by
  have h₀ : (-1 / 2 : ℝ) ∈ Icc (-1 / 2 : ℝ) 0 := ⟨le_rfl, by norm_num⟩
  have key := abs_halfTaylor2_le
    (ψ0 := fun s => chr g (m + s • Δ) Δ Δ ⬝ᵥ (g (m + s • Δ) *ᵥ chr g (m + s • Δ) Δ Δ))
    (fun s hs => hasDerivAt_chrTerm_line hg (hseg s hs))
    (fun s hs => hasDerivAt_chrLine1 hg (hseg s hs))
    (fun s hs => abs_chrLine2_le (hM s hs))
  have hy := hseg _ h₀
  have hφ := hasDerivAt_dot (hasDerivAt_chr_line hg hy Δ Δ)
    (hasDerivAt_mulVec_line hg hy (hasDerivAt_chr_line hg hy Δ Δ))
  have hu := hφ.unique (hasDerivAt_chrTerm_line hg hy)
  have h4 := dot_mulVec_chrDeriv hg hy (chr g (m + (-1 / 2 : ℝ) • Δ) Δ Δ)
  have hsy := dot_mulVec_comm (hg.symm _ hy) (chrDeriv g (m + (-1 / 2 : ℝ) • Δ) Δ Δ Δ)
    (chr g (m + (-1 / 2 : ℝ) • Δ) Δ Δ)
  simp only [zero_smul, add_zero] at key
  rw [hx] at key hu h4 hsy
  rw [dotProduct_add] at hu
  rw [abs_le] at key ⊢
  constructor <;> linarith [key.1, key.2]

/-- **The expansion of the squared distance about the midpoint to sixth order.** For a Riemannian
coordinate metric `g` on `U` and a compact `K ⊆ U` there are `C` and `r > 0` such that for
`m ∈ K` and `‖Δ‖ ≤ r`,
`|d(m - Δ/2, m + Δ/2)² - g(Δ, Δ) - Q_m(Δ)| ≤ C ‖Δ‖⁶`, with the quartic form
`Q_m(Δ) = (1/24) ∂_Δ ∂_Δ g(Δ, Δ) - (1/12) g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m` (`midJet`). About the
midpoint the terms of odd order three and five vanish. -/
theorem IsRiemMetric.dist_sq_expansion_midpoint6 (hg : IsRiemMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ m ∈ K, ∀ Δ : Fin n → ℝ, ‖Δ‖ ≤ r →
      |dist g U (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2 - midJet g m Δ| ≤
        C * ‖Δ‖ ^ 6 := by
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hK' : IsCompact (Metric.cthickening ρ K) := hK.cthickening
  obtain ⟨C₁, r₁, hr₁, h₁⟩ := hg.dist_sq_expansion6 hK' hρU
  obtain ⟨M, hM0, hM⟩ := hg.coord.exists_jet_bound4 hK' hρU
  obtain ⟨MH, hMH0, hMH⟩ := exists_chrProd_bound hg.coord hK' hρU
  refine ⟨C₁ + 3 * n ^ 6 * M / 16 + n ^ 8 * MH / 48, min r₁ ρ, lt_min hr₁ hρ,
    fun m hm Δ hΔ => ?_⟩
  have hΔ1 : ‖Δ‖ ≤ r₁ := hΔ.trans (min_le_left _ _)
  have hΔ2 : ‖Δ‖ ≤ ρ := hΔ.trans (min_le_right _ _)
  have hin : ∀ v : Fin n → ℝ, ‖v‖ ≤ ρ → m + v ∈ Metric.cthickening ρ K := fun v hv =>
    Metric.closedBall_subset_cthickening hm _
      (by rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hv)
  have hs1 : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, ‖s • Δ‖ ≤ ρ := fun s hs => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hs.2]
    nlinarith [mul_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s + 1 / 2) (norm_nonneg Δ)]
  have hseg : ∀ s ∈ Icc (-1 / 2 : ℝ) 0, m + s • Δ ∈ U := fun s hs => hρU (hin _ (hs1 s hs))
  have hmw : m + (-1 / 2 : ℝ) • Δ = m - (1 / 2 : ℝ) • Δ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, neg_smul, ← sub_eq_add_neg]
  have hx : m - (1 / 2 : ℝ) • Δ ∈ Metric.cthickening ρ K := by
    rw [← hmw]; exact hin _ (hs1 _ ⟨le_rfl, by norm_num⟩)
  have hxU : m - (1 / 2 : ℝ) • Δ ∈ U := hρU hx
  have hy : m - (1 / 2 : ℝ) • Δ + Δ = m + (1 / 2 : ℝ) • Δ := by module
  have E1 := h₁ _ hx Δ hΔ1
  rw [hy] at E1
  have E2 := abs_jetPoly_mid6_le hg.coord (m := m) (Δ := Δ) (M := M) hseg
    (fun s hs i j k l p q => hM _ (hin _ (hs1 s hs)) i j k l p q)
  have E3 := abs_chrTerm_mid_le hg.coord hmw hseg
    (fun s hs i a b j c d k l => hMH _ (hin _ (hs1 s hs)) i a b j c d k l)
  have hsym2 := dot_mulVec_comm (hg.coord.ddmat_transpose hxU Δ Δ) Δ
    (chr g (m - (1 / 2 : ℝ) • Δ) Δ Δ)
  have hcomm : Δ ⬝ᵥ (ddmat g (m - (1 / 2 : ℝ) • Δ) (chr g (m - (1 / 2 : ℝ) • Δ) Δ Δ) Δ *ᵥ Δ) =
      Δ ⬝ᵥ (ddmat g (m - (1 / 2 : ℝ) • Δ) Δ (chr g (m - (1 / 2 : ℝ) • Δ) Δ Δ) *ᵥ Δ) := by
    rw [hg.coord.ddmat_comm hxU]
  unfold distJet5 quint distJet at E1
  unfold midJet
  rw [abs_le] at E1 E2 E3 ⊢
  constructor <;> linarith [E1.1, E1.2, E2.1, E2.2, E3.1, E3.2]

end Lightlike.Geodesic

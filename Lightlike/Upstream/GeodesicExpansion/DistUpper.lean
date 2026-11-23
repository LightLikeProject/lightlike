import Lightlike.Upstream.GeodesicExpansion.DistLower
import Mathlib

/-!
# The expansion of the squared distance: the upper bound

For a Riemannian coordinate metric `g` on an open `U ⊆ ℝⁿ`, the *trial curve*
`x + t w + ½ t (1 - t) Γ_x(w, w)` from `x` to `x + w` solves the geodesic equation
`c'' + Γ_x(c', c') = 0` to second order. Its energy is `F_x(w) + O(‖w‖⁵)` where `F_x = distJet g x`
is the quartic jet, and `d² ≤ length² ≤ energy`.

## Main declarations

* `trial`, `trialVel`: the trial curve and its velocity
* `normSq_trial_eq`: the energy density splits into `trialPoly` and `trialRem`
* `LocalJet.trialRem_le`: the remainder is at most `51 B⁶ ‖w‖⁵`
* `LocalJet.energy_trial_le`: the energy of the trial curve is at most `F_x(w) + 51 B⁶ ‖w‖⁵`
* `LocalJet.dist_sq_le`: `d(x, x + w)² ≤ F_x(w) + 51 B⁶ ‖w‖⁵`
-/

open Matrix Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The **trial curve** `x + t w + ½ t (1 - t) Γ_x(w, w)` from `x` to `x + w`; it solves the
geodesic equation `c'' + Γ_x(c', c') = 0` to second order. -/
def trial (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) (t : ℝ) :
    Fin n → ℝ :=
  x + t • w + (t * (1 - t) / 2) • chr g x w w

/-- The velocity `w + ½ (1 - 2t) Γ_x(w, w)` of the trial curve. -/
def trialVel (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
    (t : ℝ) : Fin n → ℝ :=
  w + ((1 - 2 * t) / 2) • chr g x w w

/-- The main part of the energy density of the trial curve: the terms of order at most four in
`w` of `g(c', c')`, with the metric replaced by its Taylor polynomial at `x`. -/
def trialPoly (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
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
def trialRem (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ)
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
    chartDist g U x (x + w) ^ 2 ≤ distJet g x w + 51 * (B ^ 6 * ‖w‖ ^ 5) := by
  have hadm := h.isAdmissible_trial hw
  have hLE := length_sq_le_energy hg zero_le_one hadm.mem (hg.intervalIntegrable_speed hadm)
    (h.intervalIntegrable_normSq_trial hg hw)
  rw [sub_zero, one_mul] at hLE
  have hdl := pow_le_pow_left₀ chartDist_nonneg (chartDist_le_length (g := g) hadm) 2
  linarith [h.energy_trial_le hg hw]

end LocalJet

end Lightlike.Upstream.GeodesicExpansion

import Lightlike.Upstream.GeodesicExpansion.Expansion
import Mathlib

/-!
# The expansion of the distance: bounds on the jet and the radial field

Consequences of the uniform bounds packaged in `LocalJet`: the norms of the radial field and its
pieces, the remainders `radialErr1`, `radialErr2`, and the two-sided estimate of the jet by the
quadratic form (`LocalJet.distJet_le`, `LocalJet.distJet_ge`).

## Main declarations

* `LocalJet.abs_radialErr1_le`, `LocalJet.abs_radialErr2_le`
* `LocalJet.abs_distJet_sub_le`, `LocalJet.distJet_le`, `LocalJet.distJet_ge`
-/

open Matrix Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

namespace LocalJet

variable {x : Fin n → ℝ} {B δ l : ℝ}

theorem B_nonneg (h : LocalJet g U x B δ l) : 0 ≤ B := zero_le_one.trans h.one_le

theorem pow_le_pow (h : LocalJet g U x B δ l) {a b : ℕ} (hab : a ≤ b) : B ^ a ≤ B ^ b :=
  pow_le_pow_right₀ h.one_le hab

theorem le_pow (h : LocalJet g U x B δ l) {k : ℕ} (hk : 1 ≤ k) : B ≤ B ^ k := by
  simpa using h.pow_le_pow hk

/-- Monomials `B^a ‖w‖^b` decrease as `a` decreases and `b` increases, for `‖w‖ ≤ 1`. -/
theorem monom_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) {a a' b b' : ℕ}
    (ha : a ≤ a') (hb : b' ≤ b) : B ^ a * ‖w‖ ^ b ≤ B ^ a' * ‖w‖ ^ b' :=
  mul_le_mul (h.pow_le_pow ha) (pow_le_pow_of_le_one (norm_nonneg w) hw hb) (by positivity)
    (pow_nonneg h.B_nonneg _)

theorem norm_chr_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖chr g x w w‖ ≤ B * ‖w‖ ^ 2 :=
  (h.chr_le w w).trans_eq (by ring)

theorem norm_radial2_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖radial2 g x w‖ ≤ B * ‖w‖ ^ 2 := by
  unfold radial2
  rw [norm_smul, Real.norm_eq_abs, show |(-(1 / 2) : ℝ)| = 1 / 2 by norm_num]
  have := h.norm_chr_le w
  have := norm_nonneg (chr g x w w)
  linarith

/-- The cubic form `ell` is bounded by `3 B³ ‖w‖³ ‖v‖`. -/
theorem abs_ell_le (h : LocalJet g U x B δ l) (w v : Fin n → ℝ) :
    |ell g x w v| ≤ 3 * B ^ 3 * ‖w‖ ^ 3 * ‖v‖ := by
  have hB := h.B_nonneg
  have hε := norm_nonneg w
  have hν := norm_nonneg v
  have hX : 0 ≤ ‖w‖ ^ 3 * ‖v‖ := by positivity
  have hB1 : B * (‖w‖ ^ 3 * ‖v‖) ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖) :=
    mul_le_mul_of_nonneg_right (h.le_pow (by norm_num)) hX
  have hB2 : B ^ 2 * (‖w‖ ^ 3 * ‖v‖) ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖) :=
    mul_le_mul_of_nonneg_right (h.pow_le_pow (by norm_num)) hX
  have hΓ := h.norm_chr_le w
  have hΓ0 := norm_nonneg (chr g x w w)
  have k1 : ∀ u u' : Fin n → ℝ, ‖chr g x u u'‖ ≤ B * ‖u‖ * ‖u'‖ →
      B * ‖chr g x u u'‖ * ‖chr g x w w‖ ≤ B * (B * ‖u‖ * ‖u'‖) * (B * ‖w‖ ^ 2) :=
    fun u u' hu => mul_le_mul3 le_rfl hu hΓ hB (norm_nonneg _) hΓ0
  have k2 : ∀ u u' : Fin n → ℝ, ‖chr g x u u'‖ ≤ B * ‖u‖ * ‖u'‖ →
      B * ‖chr g x w w‖ * ‖chr g x u u'‖ ≤ B * (B * ‖w‖ ^ 2) * (B * ‖u‖ * ‖u'‖) :=
    fun u u' hu => mul_le_mul3 le_rfl hΓ hu hB hΓ0 (norm_nonneg _)
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.dd_le w w v w).trans_eq (by ring) :
    |v ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.dd_le v w w w).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x v w *ᵥ w)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.dd_le w v w w).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w v *ᵥ w)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a4, b4⟩ := abs_le.mp ((h.dd_le w w w v).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a5, b5⟩ := abs_le.mp (((h.g_le _ _).trans (k1 v w (h.chr_le v w))).trans_eq (by ring) :
    |chr g x v w ⬝ᵥ (g x *ᵥ chr g x w w)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a6, b6⟩ := abs_le.mp (((h.g_le _ _).trans (k1 w v (h.chr_le w v))).trans_eq (by ring) :
    |chr g x w v ⬝ᵥ (g x *ᵥ chr g x w w)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a7, b7⟩ := abs_le.mp (((h.g_le _ _).trans (k2 v w (h.chr_le v w))).trans_eq (by ring) :
    |chr g x w w ⬝ᵥ (g x *ᵥ chr g x v w)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a8, b8⟩ := abs_le.mp (((h.g_le _ _).trans (k2 w v (h.chr_le w v))).trans_eq (by ring) :
    |chr g x w w ⬝ᵥ (g x *ᵥ chr g x w v)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a9, b9⟩ := abs_le.mp (((h.d_le w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hΓ (mul_nonneg hB hε)) hν)).trans_eq (by ring) :
    |chr g x w w ⬝ᵥ (dmat g x w *ᵥ v)| ≤ B ^ 2 * (‖w‖ ^ 3 * ‖v‖))
  unfold ell
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [abs_le]
  constructor <;> nlinarith

/-- The vector of `ell` is bounded by `3 B³ ‖w‖³`. -/
theorem norm_ellVec_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖ellVec g x w‖ ≤ 3 * B ^ 3 * ‖w‖ ^ 3 := by
  have hc : 0 ≤ 3 * B ^ 3 * ‖w‖ ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h.B_nonneg 3)) (pow_nonneg (norm_nonneg w) 3)
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have he : ‖(fun j => if i = j then (1 : ℝ) else 0)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    show ‖(if i = j then (1 : ℝ) else 0)‖ ≤ 1
    split_ifs <;> simp
  calc |ellVec g x w i| = |ell g x w fun j => if i = j then 1 else 0| := rfl
    _ ≤ 3 * B ^ 3 * ‖w‖ ^ 3 * ‖(fun j => if i = j then (1 : ℝ) else 0)‖ := h.abs_ell_le w _
    _ ≤ 3 * B ^ 3 * ‖w‖ ^ 3 * 1 := mul_le_mul_of_nonneg_left he hc
    _ = _ := mul_one _

theorem norm_radial3_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖radial3 g x w‖ ≤ 2 * B ^ 4 * ‖w‖ ^ 3 := by
  unfold radial3
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 : ‖(g x)⁻¹ *ᵥ ellVec g x w‖ ≤ 3 * (B ^ 4 * ‖w‖ ^ 3) :=
    (h.inv_le _).trans ((mul_le_mul_of_nonneg_left (h.norm_ellVec_le w) h.B_nonneg).trans_eq
      (by ring))
  have hM : 0 ≤ B ^ 4 * ‖w‖ ^ 3 := mul_nonneg (by positivity) (pow_nonneg (norm_nonneg w) 3)
  linarith

theorem norm_radial23_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    ‖radial2 g x w + radial3 g x w‖ ≤ 3 * (B ^ 4 * ‖w‖ ^ 2) := by
  have h1 := (norm_add_le _ _).trans (add_le_add (h.norm_radial2_le w) (h.norm_radial3_le w))
  have e1 : B ^ 1 * ‖w‖ ^ 2 ≤ B ^ 4 * ‖w‖ ^ 2 := h.monom_le hw (by norm_num) le_rfl
  have e2 : B ^ 4 * ‖w‖ ^ 3 ≤ B ^ 4 * ‖w‖ ^ 2 := h.monom_le hw le_rfl (by norm_num)
  simp only [pow_one] at e1
  linarith

theorem norm_radial_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    ‖radial g x w‖ ≤ 4 * (B ^ 4 * ‖w‖) := by
  have h1 : ‖radial g x w‖ ≤ ‖w‖ + ‖radial2 g x w + radial3 g x w‖ := by
    unfold radial; rw [add_assoc]; exact norm_add_le _ _
  have h2 := h.norm_radial23_le hw
  have e1 : B ^ 0 * ‖w‖ ^ 1 ≤ B ^ 4 * ‖w‖ ^ 1 := h.monom_le hw (by norm_num) le_rfl
  have e2 : B ^ 4 * ‖w‖ ^ 2 ≤ B ^ 4 * ‖w‖ ^ 1 := h.monom_le hw le_rfl (by norm_num)
  simp only [pow_zero, pow_one, one_mul] at e1 e2
  linarith

/-- `|R₁| ≤ 7 B⁵ ‖w‖⁴ ‖v‖`. -/
theorem abs_radialErr1_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1)
    (v : Fin n → ℝ) : |radialErr1 g x w v| ≤ 7 * (B ^ 5 * ‖w‖ ^ 4) * ‖v‖ := by
  have hB := h.B_nonneg
  have hε := norm_nonneg w
  have hν := norm_nonneg v
  have r2 := h.norm_radial2_le w
  have r3 := h.norm_radial3_le w
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.d_le w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r3 (mul_nonneg hB hε)) hν) |>.trans_eq (by ring) :
    |radial3 g x w ⬝ᵥ (dmat g x w *ᵥ v)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 4) * ‖v‖)
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.dd_le w w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r2 (by positivity)) hν) |>.trans_eq (by ring) :
    |radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ (B ^ 2 * ‖w‖ ^ 4) * ‖v‖)
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.dd_le w w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r3 (by positivity)) hν) |>.trans_eq (by ring) :
    |radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 5) * ‖v‖)
  have e2 := mul_le_mul_of_nonneg_right (h.monom_le hw (a := 2) (a' := 5) (b := 4) (b' := 4)
    (by norm_num) le_rfl) hν
  have e3 := mul_le_mul_of_nonneg_right (h.monom_le hw (a := 5) (a' := 5) (b := 5) (b' := 4)
    le_rfl (by norm_num)) hν
  unfold radialErr1
  rw [abs_le]
  constructor <;> linarith

/-- `|R₂| ≤ 30 B⁹ ‖w‖⁵`. -/
theorem abs_radialErr2_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    |radialErr2 g x w| ≤ 30 * (B ^ 9 * ‖w‖ ^ 5) := by
  have hB := h.B_nonneg
  have hε := norm_nonneg w
  have r2 := h.norm_radial2_le w
  have r3 := h.norm_radial3_le w
  have rs := h.norm_radial23_le hw
  have n2 := norm_nonneg (radial2 g x w)
  have n3 := norm_nonneg (radial3 g x w)
  have ns := norm_nonneg (radial2 g x w + radial3 g x w)
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl r2 r3 hB n2 n3)
    |>.trans_eq (by ring) : |radial2 g x w ⬝ᵥ (g x *ᵥ radial3 g x w)| ≤ 2 * (B ^ 6 * ‖w‖ ^ 5))
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl r3 r2 hB n3 n2)
    |>.trans_eq (by ring) : |radial3 g x w ⬝ᵥ (g x *ᵥ radial2 g x w)| ≤ 2 * (B ^ 6 * ‖w‖ ^ 5))
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl r3 r3 hB n3 n3)
    |>.trans_eq (by ring) : |radial3 g x w ⬝ᵥ (g x *ᵥ radial3 g x w)| ≤ 4 * (B ^ 9 * ‖w‖ ^ 6))
  obtain ⟨a4, b4⟩ := abs_le.mp ((h.d_le w w _).trans (mul_le_mul_of_nonneg_left r3
    (by positivity)) |>.trans_eq (by ring) :
    |w ⬝ᵥ (dmat g x w *ᵥ radial3 g x w)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a5, b5⟩ := abs_le.mp ((h.d_le w _ w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r3 (mul_nonneg hB hε)) hε) |>.trans_eq (by ring) :
    |radial3 g x w ⬝ᵥ (dmat g x w *ᵥ w)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a6, b6⟩ := abs_le.mp ((h.d_le w _ _).trans (mul_le_mul3 le_rfl rs rs
    (mul_nonneg hB hε) ns ns) |>.trans_eq (by ring) :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (dmat g x w *ᵥ (radial2 g x w + radial3 g x w))| ≤
      9 * (B ^ 9 * ‖w‖ ^ 5))
  obtain ⟨a7, b7⟩ := abs_le.mp ((h.dd_le w w w _).trans (mul_le_mul_of_nonneg_left rs
    (by positivity)) |>.trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w))| ≤ 3 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a8, b8⟩ := abs_le.mp ((h.dd_le w w _ w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left rs (by positivity)) hε) |>.trans_eq (by ring) :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ 3 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a9, b9⟩ := abs_le.mp ((h.dd_le w w _ _).trans (mul_le_mul3 le_rfl rs rs
    (by positivity) ns ns) |>.trans_eq (by ring) :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w))| ≤
      9 * (B ^ 9 * ‖w‖ ^ 6))
  have e6 := h.monom_le hw (a := 6) (a' := 9) (b := 5) (b' := 5) (by norm_num) le_rfl
  have e5 := h.monom_le hw (a := 5) (a' := 9) (b := 5) (b' := 5) (by norm_num) le_rfl
  have e96 := h.monom_le hw (a := 9) (a' := 9) (b := 6) (b' := 5) le_rfl (by norm_num)
  unfold radialErr2
  rw [abs_le]
  constructor <;> linarith

/-- The jet differs from `g(w, w)` by at most `B³ ‖w‖³`. -/
theorem abs_distJet_sub_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    |distJet g x w - w ⬝ᵥ (g x *ᵥ w)| ≤ B ^ 3 * ‖w‖ ^ 3 := by
  have hB := h.B_nonneg
  have hΓ := h.norm_chr_le w
  have hΓ0 := norm_nonneg (chr g x w w)
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.d_le w w w).trans_eq (by ring) :
    |w ⬝ᵥ (dmat g x w *ᵥ w)| ≤ B ^ 1 * ‖w‖ ^ 3)
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.dd_le w w w w).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ B ^ 1 * ‖w‖ ^ 4)
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl hΓ hΓ hB hΓ0 hΓ0)
    |>.trans_eq (by ring) : |chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w)| ≤ B ^ 3 * ‖w‖ ^ 4)
  have e1 := h.monom_le hw (a := 1) (a' := 3) (b := 3) (b' := 3) (by norm_num) le_rfl
  have e2 := h.monom_le hw (a := 1) (a' := 3) (b := 4) (b' := 3) (by norm_num) (by norm_num)
  have e3 := h.monom_le hw (a := 3) (a' := 3) (b := 4) (b' := 3) le_rfl (by norm_num)
  unfold distJet
  rw [abs_le]
  constructor <;> linarith

/-- The jet is at most `2 B³ ‖w‖²`. -/
theorem distJet_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    distJet g x w ≤ 2 * (B ^ 3 * ‖w‖ ^ 2) := by
  have h1 := (abs_le.mp (h.abs_distJet_sub_le hw)).2
  have h2 := (abs_le.mp ((h.g_le w w).trans_eq (by ring) :
    |w ⬝ᵥ (g x *ᵥ w)| ≤ B ^ 1 * ‖w‖ ^ 2)).2
  have e1 := h.monom_le hw (a := 1) (a' := 3) (b := 2) (b' := 2) (by norm_num) le_rfl
  have e2 := h.monom_le hw (a := 3) (a' := 3) (b := 3) (b' := 2) le_rfl (by norm_num)
  linarith

/-- The jet is at least `l ‖w‖² - B³ ‖w‖³`. -/
theorem distJet_ge (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    l * ‖w‖ ^ 2 - B ^ 3 * ‖w‖ ^ 3 ≤ distJet g x w := by
  have h1 := (abs_le.mp (h.abs_distJet_sub_le hw)).1
  have h2 := h.low 0 (by simpa using h.δ_pos.le) w
  rw [add_zero] at h2
  unfold normSq at h2
  have h3 := mul_le_mul_of_nonneg_left (norm_sq_le_eNormSq w) h.l_pos.le
  linarith

end LocalJet

end Lightlike.Upstream.GeodesicExpansion

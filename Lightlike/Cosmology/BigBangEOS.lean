import Lightlike.Cosmology.BigBangSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The big bang singularity for the equation of state `p = wρ` (G1-025)

Carroll (gr-qc/9712019, p. 224): "set Λ = 0, and consider the behavior of universes filled with fluids of positive energy
(ρ > 0) and nonnegative pressure (p ≥ 0) ... if we trace the evolution backwards in time, we necessarily reach a singularity
at a = 0". Two readings:

* (a) as printed, for any `ρ > 0`, `p ≥ 0`: false, by `onePlusSqrt_friedmann` (`a = 1 + √t`, `BigBangSingularity.lean`);
  with the extra hypothesis `p ≤ ρ` it holds (`bigBang_singularity`);
* (b) in the setting of Carroll's (8.21)-(8.23), the equation of state `p = wρ` with a constant `w`: proved here for every
  `w > -1/3` (`bigBang_singularity_of_eos`; Carroll's `p ≥ 0` is `w ≥ 0`): either `a → 0` as `t ↓ t₁`, or `a'`, `a''`, `ρ`, `p`
  stay bounded on `(t₁, t₀]`. The key is that `(a'² + k) a^{1+3w}` is constant (`ρ ∝ a^{-3(1+w)}`, Carroll's (8.23)):
  its derivative is `a' a^{3w} (2 a a'' + (1 + 3w)(a'² + k)) = 0` by Friedmann's equations (8.35), (8.36).
-/

open Set Filter Topology

namespace Lightlike
namespace Cosmology

variable {a ρ p : ℝ → ℝ} {Gn t₁ t₂ t₀ : ℝ}

/-- **The big bang singularity is at `a = 0` for `p = wρ`, `w > -1/3`.** -/
theorem bigBang_singularity_of_eos {k w : ℝ} (hG : 0 < Gn) (hw : -1 / 3 < w) (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t) (hF1 : ∀ t ∈ Ioo t₁ t₂, FirstFriedmann a ρ k 0 Gn t)
    (hF2 : ∀ t ∈ Ioo t₁ t₂, SecondFriedmann a ρ p 0 Gn t) (hρ : ∀ t ∈ Ioo t₁ t₂, 0 ≤ ρ t)
    (heos : ∀ t ∈ Ioo t₁ t₂, p t = w * ρ t) (ht₀ : t₀ ∈ Ioo t₁ t₂) (hH : 0 < deriv a t₀) :
    Tendsto a (𝓝[>] t₁) (𝓝 0) ∨
      ∃ M, ∀ t ∈ Ioc t₁ t₀, |deriv a t| ≤ M ∧ |deriv (deriv a) t| ≤ M ∧ |ρ t| ≤ M ∧ |p t| ≤ M := by
  set r : ℝ := 1 + 3 * w with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hS : ∀ t ∈ Ioo t₁ t₂, 0 ≤ ρ t + 3 * p t := fun t ht => by
    rw [heos t ht]; nlinarith [hρ t ht]
  have hdd := deriv2_nonpos_of_strong_energy hG hpos hF2 hS
  have hsub : Ioc t₁ t₀ ⊆ Ioo t₁ t₂ := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 ht₀.2⟩
  have hd1 : ContDiffOn ℝ 1 (deriv a) (Ioo t₁ t₂) := hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hda : ∀ t ∈ Ioo t₁ t₂, HasDerivAt a (deriv a t) t := fun t ht =>
    (((hC.differentiableOn (by norm_num)) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hdda : ∀ t ∈ Ioo t₁ t₂, HasDerivAt (deriv a) (deriv (deriv a) t) t := fun t ht =>
    (((hd1.differentiableOn (by norm_num)) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hge : ∀ t ∈ Ioc t₁ t₀, deriv a t₀ ≤ deriv a t := fun t ht =>
    deriv_ge_of_strong_energy hC hdd (hsub ht) ht₀ ht.2
  have hmono : MonotoneOn a (Ioc t₁ t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc t₁ t₀) ?_ ?_ ?_
    · exact fun t ht => (hda t (hsub ht)).continuousAt.continuousWithinAt
    · exact fun t ht => (hda t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hda t (hsub (interior_subset ht))).deriv]
      linarith [hge t (interior_subset ht)]
  -- `Q = (a'² + k) a^r` has zero derivative
  set Q : ℝ → ℝ := fun t => (deriv a t ^ 2 + k) * a t ^ r with hQ
  have hQd : ∀ t ∈ Ioo t₁ t₂, HasDerivAt Q
      ((2 * deriv a t * deriv (deriv a) t) * a t ^ r + (deriv a t ^ 2 + k) * (deriv a t * r * a t ^ (r - 1))) t := by
    intro t ht
    have h1 := ((hdda t ht).pow 2).add_const k
    have h2 := (hda t ht).rpow_const (p := r) (Or.inl (hpos t ht).ne')
    have := h1.mul h2
    convert this using 1
    simp
  have hQ0 : ∀ t ∈ Ioo t₁ t₂,
      (2 * deriv a t * deriv (deriv a) t) * a t ^ r + (deriv a t ^ 2 + k) * (deriv a t * r * a t ^ (r - 1)) = 0 := by
    intro t ht
    have hat := hpos t ht
    have h1 := hF1 t ht
    have h2 := hF2 t ht
    unfold FirstFriedmann at h1
    unfold SecondFriedmann at h2
    rw [heos t ht] at h2
    have hrp : a t ^ r = a t ^ (r - 1) * a t := by
      rw [Real.rpow_sub_one hat.ne']; field_simp
    rw [hrp]
    have hk : deriv a t ^ 2 + k = 8 * Real.pi * Gn / 3 * ρ t * a t ^ 2 := by
      rw [div_pow] at h1; field_simp at h1; linarith
    have hdd' : deriv (deriv a) t = -(4 * Real.pi * Gn / 3) * (r * ρ t) * a t := by
      rw [hr]; field_simp at h2 ⊢; linarith
    rw [hk, hdd']
    ring
  have hQmono : MonotoneOn Q (Ioc t₁ t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc t₁ t₀) ?_ ?_ ?_
    · exact fun t ht => (hQd t (hsub ht)).continuousAt.continuousWithinAt
    · exact fun t ht => (hQd t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hQd t (hsub (interior_subset ht))).deriv, hQ0 t (hsub (interior_subset ht))]
  by_cases hL : ∀ ε > 0, ∃ t ∈ Ioc t₁ t₀, a t < ε
  · left
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨s, hs, has⟩ := hL ε hε
    refine ⟨s - t₁, by linarith [hs.1], fun t ht htd => ?_⟩
    rw [Real.dist_eq] at htd ⊢
    have ht1 : t₁ < t := ht
    have hts : t < s := by rw [abs_lt] at htd; linarith
    have htI : t ∈ Ioc t₁ t₀ := ⟨ht1, by linarith [hs.2]⟩
    have := hmono htI hs hts.le
    have hat := hpos t (hsub htI)
    rw [sub_zero, abs_of_pos hat]
    linarith
  · right
    push Not at hL
    obtain ⟨L, hL0, hLa⟩ := hL
    have ht₀I : t₀ ∈ Ioc t₁ t₀ := ⟨ht₀.1, le_rfl⟩
    have hp8 : 0 < 8 * Real.pi * Gn / 3 := by positivity
    set C := Q t₀
    have hQle : ∀ t ∈ Ioc t₁ t₀, Q t ≤ C := fun t ht => hQmono ht ht₀I ht.2
    have hρeq : ∀ t ∈ Ioo t₁ t₂, ρ t * a t ^ 2 = (deriv a t ^ 2 + k) / (8 * Real.pi * Gn / 3) := by
      intro t ht
      have h := hF1 t ht
      have hat := hpos t ht
      unfold FirstFriedmann at h
      rw [eq_div_iff hp8.ne']
      rw [div_pow] at h
      field_simp at h
      nlinarith [h]
    have hLr : 0 < L ^ r := Real.rpow_pos_of_pos hL0 r
    have hdbound : ∀ t ∈ Ioc t₁ t₀, deriv a t ^ 2 + k ≤ max C 0 / L ^ r := by
      intro t ht
      have hat : L ≤ a t := hLa t ht
      have hq := hQle t ht
      simp only [hQ] at hq
      have h4 : L ^ r ≤ a t ^ r := Real.rpow_le_rpow hL0.le hat hr0.le
      rw [le_div_iff₀ hLr]
      by_cases hs : 0 ≤ deriv a t ^ 2 + k
      · calc (deriv a t ^ 2 + k) * L ^ r ≤ (deriv a t ^ 2 + k) * a t ^ r := mul_le_mul_of_nonneg_left h4 hs
          _ ≤ C := hq
          _ ≤ max C 0 := le_max_left _ _
      · push Not at hs
        have : (deriv a t ^ 2 + k) * L ^ r < 0 := mul_neg_of_neg_of_pos hs hLr
        linarith [le_max_right C 0]
    set B := max C 0 / L ^ r + |k|
    set R := 3 / (8 * Real.pi * Gn) * (B / L ^ 2 + |k| / L ^ 2)
    refine ⟨max (max (Real.sqrt B) (R * (1 + |w|))) (4 * Real.pi * Gn / 3 * (r * R) * a t₀), fun t ht => ?_⟩
    have hat : L ≤ a t := hLa t ht
    have hat0 : 0 < a t := hpos t (hsub ht)
    have hata : a t ≤ a t₀ := hmono ht ht₀I ht.2
    have hdt : 0 < deriv a t := lt_of_lt_of_le hH (hge t ht)
    have hd2 : deriv a t ^ 2 ≤ B := by
      have := hdbound t ht; have := neg_abs_le k; simp only [B]; linarith
    have hA : |deriv a t| ≤ Real.sqrt B := by
      rw [abs_of_pos hdt]; exact Real.le_sqrt_of_sq_le hd2
    have hρ' : ρ t = (deriv a t ^ 2 + k) / (8 * Real.pi * Gn / 3) / a t ^ 2 := by
      rw [← hρeq t (hsub ht)]; field_simp
    have hL2 : L ^ 2 ≤ a t ^ 2 := pow_le_pow_left₀ hL0.le hat 2
    have hρb : |ρ t| ≤ R := by
      rw [hρ', abs_div, abs_div, abs_of_pos hp8, abs_of_pos (by positivity : (0 : ℝ) < a t ^ 2)]
      have hnum : |deriv a t ^ 2 + k| ≤ B + |k| := by
        calc |deriv a t ^ 2 + k| ≤ |deriv a t ^ 2| + |k| := abs_add_le _ _
          _ ≤ B + |k| := by rw [abs_of_nonneg (sq_nonneg _)]; linarith
      have hL2p : 0 < L ^ 2 := by positivity
      rw [div_div, div_le_iff₀ (by positivity)]
      calc |deriv a t ^ 2 + k| ≤ B + |k| := hnum
        _ = R * (8 * Real.pi * Gn / 3 * L ^ 2) := by simp only [R]; field_simp
        _ ≤ R * (8 * Real.pi * Gn / 3 * a t ^ 2) := by
          have : 0 ≤ R := by simp only [R]; positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hp8.le) this
    have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hρb
    have hpb : |p t| ≤ R * (1 + |w|) := by
      rw [heos t (hsub ht), abs_mul]
      nlinarith [abs_nonneg w, abs_nonneg (ρ t)]
    have h2 := hF2 t (hsub ht)
    unfold SecondFriedmann at h2
    rw [heos t (hsub ht)] at h2
    have hdd' : deriv (deriv a) t = -(4 * Real.pi * Gn / 3) * (r * ρ t) * a t := by
      rw [hr]; field_simp at h2 ⊢; linarith
    have hρ0 := hρ t (hsub ht)
    have hAA : |deriv (deriv a) t| ≤ 4 * Real.pi * Gn / 3 * (r * R) * a t₀ := by
      rw [hdd', abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi * Gn / 3),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ r * ρ t), abs_of_pos hat0]
      have h1 : r * ρ t ≤ r * R := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hρb) hr0.le
      have : 0 ≤ 4 * Real.pi * Gn / 3 := by positivity
      calc 4 * Real.pi * Gn / 3 * (r * ρ t) * a t ≤ 4 * Real.pi * Gn / 3 * (r * R) * a t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 this) hat0.le
        _ ≤ 4 * Real.pi * Gn / 3 * (r * R) * a t₀ := by
            have : 0 ≤ 4 * Real.pi * Gn / 3 * (r * R) := by positivity
            exact mul_le_mul_of_nonneg_left hata this
    have hRw : R ≤ R * (1 + |w|) := by nlinarith [abs_nonneg w]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_trans hA (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact le_trans hAA (le_max_right _ _)
    · exact le_trans (le_trans hρb hRw) (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact le_trans hpb (le_trans (le_max_right _ _) (le_max_left _ _))

end Cosmology
end Lightlike

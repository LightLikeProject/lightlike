import Lightlike.Regge.Conv3.Exp2

/-!
# Second-order expansions at `η = 0`: inverse, square root, uniqueness

Continues `Exp2`: the inverse (`Exp2.inv`) and the square root (`Exp2.sqrt`) of a function with `a0 = 1`, the limit of an
expansion (`Exp2.tendsto`) and the uniqueness of its coefficients (`Exp2.unique`, from `poly2_unique`).

## Main results

* `Exp2.tendsto`, `Exp2.inv`, `Exp2.sqrt`, `Exp2.unique`.

**Limits.** Real functions of one real variable at `0`, order two only.
-/

open Asymptotics Filter Topology Finset

namespace Lightlike.Regge.Conv3

/-- The constant coefficient is the limit. -/
theorem Exp2.tendsto {f : ℝ → ℝ} {a0 a1 a2 : ℝ} (hf : Exp2 f a0 a1 a2) : Tendsto f (𝓝 0) (𝓝 a0) := by
  have h1 : Tendsto (fun η : ℝ => f η - (a0 + a1 * η + a2 * η ^ 2)) (𝓝 0) (𝓝 0) := by
    refine hf.trans_tendsto ?_
    have : Tendsto (fun η : ℝ => η ^ 3) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_pow 3).tendsto (0 : ℝ))
    exact this
  have h2 : Tendsto (fun η : ℝ => a0 + a1 * η + a2 * η ^ 2) (𝓝 0) (𝓝 a0) := by
    have := (show Continuous fun η : ℝ => a0 + a1 * η + a2 * η ^ 2 by fun_prop).tendsto 0
    simpa using this
  simpa using h1.add h2

/-- The inverse of a function with expansion `1 + a1 η + a2 η²`. -/
theorem Exp2.inv {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : Exp2 f 1 a1 a2) :
    Exp2 (fun η => (f η)⁻¹) 1 (-a1) (a1 ^ 2 - a2) := by
  have hG := Exp2.poly 1 (-a1) (a1 ^ 2 - a2) 0 0
  have hm := hf.mul hG
  have hm' : Exp2 (fun η => f η * (1 + -a1 * η + (a1 ^ 2 - a2) * η ^ 2 + 0 * η ^ 3 + 0 * η ^ 4)) 1 0 0 := by
    have := hm
    rwa [show (1 : ℝ) * 1 = 1 by ring, show (1 : ℝ) * -a1 + a1 * 1 = 0 by ring,
      show (1 : ℝ) * (a1 ^ 2 - a2) + a1 * -a1 + a2 * 1 = 0 by ring] at this
  have hg : Tendsto (fun η => (f η)⁻¹) (𝓝 0) (𝓝 1) := by
    simpa using (hf.tendsto).inv₀ (by norm_num)
  have hb : (fun η => (f η)⁻¹) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := hg.isBigO_one ℝ
  have hne : ∀ᶠ η in 𝓝 (0 : ℝ), f η ≠ 0 := hf.tendsto.eventually_ne (by norm_num)
  unfold Exp2 at hm' ⊢
  simp only [zero_mul, add_zero, zero_add, one_mul] at hm'
  have := hb.mul hm'.neg_left
  simp only [one_mul] at this
  refine this.congr' ?_ EventuallyEq.rfl
  filter_upwards [hne] with η hη
  field_simp
  ring

/-- A number bounded by `C t` for all small `t > 0` is zero. -/
theorem zero_of_small {x C r : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (h : ∀ t : ℝ, 0 < t → t ≤ r → |x| ≤ C * t) :
    x = 0 := by
  by_contra hx
  have hx' : 0 < |x| := abs_pos.mpr hx
  set t := min r (|x| / (2 * (C + 1))) with ht
  have h1 : 0 < t := lt_min hr (by positivity)
  have h2 : t ≤ r := min_le_left _ _
  have h3 : t ≤ |x| / (2 * (C + 1)) := min_le_right _ _
  have := h t h1 h2
  have h4 : C * t ≤ C * (|x| / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h3 hC
  have h5 : C * (|x| / (2 * (C + 1))) < |x| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- A polynomial of degree two bounded by `C |η|³` near `0` is zero. -/
theorem poly2_unique {d0 d1 d2 C r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (h : ∀ η : ℝ, |η| ≤ r → |d0 + d1 * η + d2 * η ^ 2| ≤ C * |η| ^ 3) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 := by
  have key : ∀ t : ℝ, 0 < t → t ≤ r →
      |d0 + d1 * t + d2 * t ^ 2| ≤ C * t ^ 3 ∧ |d0 + d1 * (-t) + d2 * (-t) ^ 2| ≤ C * t ^ 3 := fun t ht htr => by
    have h1 := h t (by rw [abs_of_pos ht]; exact htr)
    have h2 := h (-t) (by rw [abs_neg, abs_of_pos ht]; exact htr)
    rw [abs_of_pos ht] at h1
    rw [abs_neg, abs_of_pos ht] at h2
    exact ⟨h1, h2⟩
  have hd1 : d1 = 0 := by
    refine zero_of_small (C := C) hr hC fun t ht htr => ?_
    obtain ⟨k1, k2⟩ := key t ht htr
    rw [abs_le] at k1 k2 ⊢
    have t1 : t ≤ 1 := htr.trans hr1
    have h3 : t ^ 3 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    have h4 : t ^ 2 ≤ t := by nlinarith
    have h5 : d1 * t ≤ C * t ^ 3 := by nlinarith [k1.2, k2.1]
    have h6 : -(C * t ^ 3) ≤ d1 * t := by nlinarith [k1.1, k2.2]
    have h7 : d1 ≤ C * t ^ 2 := by
      by_contra hc; push_neg at hc
      nlinarith [mul_pos ht ht, mul_lt_mul_of_pos_right hc ht]
    have h8 : -(C * t ^ 2) ≤ d1 := by
      by_contra hc; push_neg at hc
      nlinarith [mul_pos ht ht, mul_lt_mul_of_pos_right hc ht]
    have h9 : C * t ^ 2 ≤ C * t := mul_le_mul_of_nonneg_left h4 hC
    constructor <;> linarith
  have hd2 : d2 = 0 := by
    refine zero_of_small (C := 2 * C) hr (by linarith) fun t ht htr => ?_
    obtain ⟨k1, -⟩ := key t ht htr
    obtain ⟨k2, -⟩ := key (t / 2) (by positivity) (by linarith)
    subst hd1
    rw [abs_le] at k1 k2 ⊢
    have h3 : (t / 2) ^ 3 = t ^ 3 / 8 := by ring
    have h4 : (t / 2) ^ 2 = t ^ 2 / 4 := by ring
    rw [h3, h4] at k2
    have h5 : d2 * t ^ 2 ≤ 3 / 2 * C * t ^ 3 := by nlinarith [k1.1, k1.2, k2.1, k2.2]
    have h6 : -(3 / 2 * C * t ^ 3) ≤ d2 * t ^ 2 := by nlinarith [k1.1, k1.2, k2.1, k2.2]
    have ht2 : 0 < t ^ 2 := by positivity
    have h7 : d2 ≤ 3 / 2 * C * t := by
      by_contra hc; push_neg at hc
      nlinarith [mul_lt_mul_of_pos_right hc ht2]
    have h8 : -(3 / 2 * C * t) ≤ d2 := by
      by_contra hc; push_neg at hc
      nlinarith [mul_lt_mul_of_pos_right hc ht2]
    constructor <;> nlinarith [mul_nonneg hC ht.le]
  refine ⟨?_, hd1, hd2⟩
  refine zero_of_small (C := C) hr hC fun t ht htr => ?_
  obtain ⟨k1, -⟩ := key t ht htr
  subst hd1 hd2
  simp only [zero_mul, add_zero] at k1
  have t1 : t ≤ 1 := htr.trans hr1
  have h3 : t ^ 3 ≤ t := by nlinarith [sq_nonneg t, mul_pos ht ht]
  nlinarith [mul_le_mul_of_nonneg_left h3 hC]

/-- The coefficients of an expansion are unique. -/
theorem Exp2.unique {f : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (ha : Exp2 f a0 a1 a2) (hb : Exp2 f b0 b1 b2) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  have hd : (fun η : ℝ => (a0 - b0) + (a1 - b1) * η + (a2 - b2) * η ^ 2) =O[𝓝 0] fun η : ℝ => η ^ 3 := by
    refine (hb.sub ha).congr_left fun η => ?_
    ring
  obtain ⟨C, hC0, hC⟩ := hd.exists_pos
  have hev := hC.bound
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  have hr : 0 < min (ε / 2) 1 := lt_min (by positivity) one_pos
  have := poly2_unique (C := C) hr (min_le_right _ _) hC0.le fun η hη => by
    have := hball (y := η) (by
      rw [dist_zero_right, Real.norm_eq_abs]
      exact lt_of_le_of_lt hη (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
    simpa [Real.norm_eq_abs, abs_pow] using this
  obtain ⟨h0, h1, h2⟩ := this
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The square root of a function with expansion `1 + a1 η + a2 η²`. -/
theorem Exp2.sqrt {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : Exp2 f 1 a1 a2) :
    Exp2 (fun η => √(f η)) 1 (a1 / 2) (a2 / 2 - a1 ^ 2 / 8) := by
  set S : ℝ → ℝ := fun η => 1 + a1 / 2 * η + (a2 / 2 - a1 ^ 2 / 8) * η ^ 2 + 0 * η ^ 3 + 0 * η ^ 4 with hSdef
  have hS : Exp2 S 1 (a1 / 2) (a2 / 2 - a1 ^ 2 / 8) := Exp2.poly _ _ _ _ _
  have hS2 := (hS.mul hS).sub hf
  have h0 : Exp2 (fun η => S η * S η - f η) 0 0 0 :=
    hS2.congr (by ring) (by ring) (by ring)
  have hdiff : (fun η => S η * S η - f η) =O[𝓝 0] fun η : ℝ => η ^ 3 := by
    refine h0.congr_left fun η => ?_
    ring
  have hu : Tendsto f (𝓝 0) (𝓝 1) := hf.tendsto
  have hs : Tendsto (fun η => √(f η)) (𝓝 0) (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hu
    simpa [Function.comp_def] using this
  have hSt : Tendsto S (𝓝 0) (𝓝 1) := hS.tendsto
  have hsum : Tendsto (fun η => √(f η) + S η) (𝓝 0) (𝓝 2) := by
    have := hs.add hSt
    norm_num at this
    exact this
  have hinv : Tendsto (fun η => (√(f η) + S η)⁻¹) (𝓝 0) (𝓝 (2 : ℝ)⁻¹) := hsum.inv₀ (by norm_num)
  have hb : (fun η => (√(f η) + S η)⁻¹) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := hinv.isBigO_one ℝ
  have hpos : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < f η := hu.eventually (lt_mem_nhds one_pos)
  have hne : ∀ᶠ η in 𝓝 (0 : ℝ), √(f η) + S η ≠ 0 := hsum.eventually_ne (by norm_num)
  have := hdiff.mul hb
  simp only [mul_one] at this
  unfold Exp2
  refine (this.neg_left).congr' ?_ EventuallyEq.rfl
  filter_upwards [hpos, hne] with η h1 h2
  have hSη : S η = 1 + a1 / 2 * η + (a2 / 2 - a1 ^ 2 / 8) * η ^ 2 := by simp [hSdef]
  have e1 : √(f η) * √(f η) = f η := Real.mul_self_sqrt h1.le
  rw [← hSη]
  generalize √(f η) = r at e1 h2 ⊢
  rw [← e1]
  field_simp
  ring

end Lightlike.Regge.Conv3

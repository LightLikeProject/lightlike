import Mathlib
import Lightlike.Dirac.ModeSeries
import Lightlike.Dirac.GaussSum

/-!
# The regular mode solution as a hypergeometric series

`G(x) = Σ hgTerm a (m+1) n · xⁿ` is `₂F₁(a, −a; m+1; x)`.  It is differentiable twice on `(-1, 1)` and satisfies
`x(1−x) G'' + (m+1−x) G' + a² G = 0`.
-/

namespace Lightlike.Dirac

/-- The coefficients of `₂F₁(a, −a; m+1; x)`. -/
noncomputable def hgCoef (a : ℂ) (m : ℕ) : ℕ → ℂ := hgTerm a ((m : ℂ) + 1)

/-- Recurrence of the coefficients. -/
lemma hgCoef_succ (a : ℂ) (m n : ℕ) :
    ((n : ℂ) + 1) * ((n : ℂ) + m + 1) * hgCoef a m (n + 1) = ((n : ℂ) ^ 2 - a ^ 2) * hgCoef a m n := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : ((n : ℂ) + m + 1) ≠ 0 := by
    have : (0 : ℝ) < n + m + 1 := by positivity
    exact_mod_cast this.ne'
  unfold hgCoef
  rw [hgTerm]
  have : ((m : ℂ) + 1 + n) = ((n : ℂ) + m + 1) := by ring
  rw [this]
  field_simp
  ring

/-- The sum `G(x)`. -/
noncomputable def hgSum (a : ℂ) (m : ℕ) : ℝ → ℂ := powerSum (hgCoef a m)

/-- First derivative coefficients `(n+1) γ_{n+1}`. -/
noncomputable def hgCoef1 (a : ℂ) (m : ℕ) (n : ℕ) : ℂ := ((n : ℂ) + 1) * hgCoef a m (n + 1)

/-- Second derivative coefficients `(n+1)(n+2) γ_{n+2}`. -/
noncomputable def hgCoef2 (a : ℂ) (m : ℕ) (n : ℕ) : ℂ := ((n : ℂ) + 1) * hgCoef1 a m (n + 1)

/-- Growth bound of the hypergeometric coefficients. -/
lemma hgCoef_bound (a : ℂ) (m n : ℕ) : ‖hgCoef a m n‖ ≤ 1 * ((n : ℝ) + 1) ^ (2 * max ‖a‖ 1) := by
  rw [one_mul]; exact hgTerm_bound a m n

/-- `G' = Σ (n+1) γ_{n+1} xⁿ`. -/
theorem hasDerivAt_hgSum (a : ℂ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (hgSum a m) (powerSum (hgCoef1 a m) x) x :=
  hasDerivAt_powerSum zero_le_one (hgCoef_bound a m) hx

/-- Growth bound of the first derivative coefficients. -/
lemma hgCoef1_bound (a : ℂ) (m n : ℕ) :
    ‖hgCoef1 a m n‖ ≤ (1 * 2 ^ (2 * max ‖a‖ 1)) * ((n : ℝ) + 1) ^ (2 * max ‖a‖ 1 + 1) :=
  deriv_coeff_bound (by positivity) zero_le_one (hgCoef_bound a m) n

/-- `G'' = Σ (n+1)(n+2) γ_{n+2} xⁿ`. -/
theorem hasDerivAt_hgSum1 (a : ℂ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (powerSum (hgCoef1 a m)) (powerSum (hgCoef2 a m) x) x :=
  hasDerivAt_powerSum (by positivity) (hgCoef1_bound a m) hx

/-- Polynomially bounded coefficient sequences. -/
def PB (c : ℕ → ℂ) : Prop := ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ K

/-- Sums of polynomially bounded sequences are polynomially bounded. -/
lemma PB.add {c d : ℕ → ℂ} (hc : PB c) (hd : PB d) : PB fun n => c n + d n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  obtain ⟨D, L, hD, hL, hdb⟩ := hd
  refine ⟨C + D, max K L, by positivity, le_max_of_le_left hK, fun n => ?_⟩
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  calc ‖c n + d n‖ ≤ ‖c n‖ + ‖d n‖ := norm_add_le _ _
    _ ≤ C * ((n : ℝ) + 1) ^ K + D * ((n : ℝ) + 1) ^ L := add_le_add (hcb n) (hdb n)
    _ ≤ C * ((n : ℝ) + 1) ^ (max K L) + D * ((n : ℝ) + 1) ^ (max K L) :=
        add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)) hC)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (le_max_right _ _)) hD)
    _ = (C + D) * ((n : ℝ) + 1) ^ (max K L) := by ring

/-- Scalar multiples stay polynomially bounded. -/
lemma PB.const_mul {c : ℕ → ℂ} (r : ℂ) (hc : PB c) : PB fun n => r * c n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  refine ⟨‖r‖ * C, K, by positivity, hK, fun n => ?_⟩
  rw [norm_mul]
  calc ‖r‖ * ‖c n‖ ≤ ‖r‖ * (C * ((n : ℝ) + 1) ^ K) := mul_le_mul_of_nonneg_left (hcb n) (norm_nonneg _)
    _ = ‖r‖ * C * ((n : ℝ) + 1) ^ K := by ring

/-- Multiplying by `n` keeps polynomial growth. -/
lemma PB.mul_nat {c : ℕ → ℂ} (hc : PB c) : PB fun n => (n : ℂ) * c n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  refine ⟨C, K + 1, hC, by linarith, fun n => ?_⟩
  rw [norm_mul]
  have h1 : ‖(n : ℂ)‖ = n := by simp
  rw [h1, Real.rpow_add (by positivity), Real.rpow_one]
  calc (n : ℝ) * ‖c n‖ ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 1) ^ K) :=
        mul_le_mul (by linarith) (hcb n) (norm_nonneg _) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ K * ((n : ℝ) + 1)) := by ring

/-- Shifting keeps polynomial growth. -/
lemma PB.shift {c : ℕ → ℂ} (hc : PB c) : PB fun n => c (n + 1) := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  refine ⟨C * 2 ^ K, K, by positivity, hK, fun n => ?_⟩
  have h2 : (((n + 1 : ℕ) : ℝ) + 1) ^ K ≤ 2 ^ K * ((n : ℝ) + 1) ^ K := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hK
    push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ‖c (n + 1)‖ ≤ C * (((n + 1 : ℕ) : ℝ) + 1) ^ K := hcb (n + 1)
    _ ≤ C * (2 ^ K * ((n : ℝ) + 1) ^ K) := mul_le_mul_of_nonneg_left h2 hC
    _ = C * 2 ^ K * ((n : ℝ) + 1) ^ K := by ring

/-- A polynomially bounded sequence gives an absolutely convergent series on `(-1, 1)`. -/
lemma PB.summable {c : ℕ → ℂ} (hc : PB c) {t : ℝ} (ht : |t| < 1) : Summable fun n : ℕ => c n * (t : ℂ) ^ n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  exact summable_powerTerms hC hcb ht

/-- Shift a sequence to the right by one place (inserting a zero). -/
def shr (c : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => c n

/-- Shifting to the right keeps polynomial growth. -/
lemma pb_shr {c : ℕ → ℂ} (hc : PB c) : PB (shr c) := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  refine ⟨C, K, hC, hK, fun n => ?_⟩
  cases n with
  | zero =>
    have h0 : ‖shr c 0‖ = 0 := by simp [shr]
    rw [h0]; positivity
  | succ n =>
    show ‖c n‖ ≤ _
    calc ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ K := hcb n
      _ ≤ C * (((n + 1 : ℕ) : ℝ) + 1) ^ K := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.rpow_le_rpow (by positivity) _ hK
          push_cast; linarith

/-- Multiplying the sum by `x` shifts the coefficients. -/
lemma powerSum_shr {c : ℕ → ℂ} (hc : PB c) {t : ℝ} (ht : |t| < 1) :
    powerSum (shr c) t = (t : ℂ) * powerSum c t := by
  unfold powerSum
  have hs := (pb_shr hc).summable ht
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [shr, zero_mul, zero_add]
  refine tsum_congr fun n => ?_
  ring

/-- Power sums are additive. -/
lemma powerSum_add {c d : ℕ → ℂ} (hc : PB c) (hd : PB d) {t : ℝ} (ht : |t| < 1) :
    powerSum (fun n => c n + d n) t = powerSum c t + powerSum d t := by
  unfold powerSum
  rw [← (hc.summable ht).tsum_add (hd.summable ht)]
  exact tsum_congr fun n => by ring

/-- Power sums commute with scalars. -/
lemma powerSum_const_mul (r : ℂ) (c : ℕ → ℂ) (t : ℝ) :
    powerSum (fun n => r * c n) t = r * powerSum c t := by
  unfold powerSum
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- The sum of `n c_n tⁿ` is `t` times the derivative series. -/
lemma powerSum_mul_nat {c : ℕ → ℂ} (hc : PB c) {t : ℝ} (ht : |t| < 1) :
    powerSum (fun n => (n : ℂ) * c n) t = (t : ℂ) * powerSum (fun n => ((n : ℂ) + 1) * c (n + 1)) t := by
  have h1 : (fun n : ℕ => (n : ℂ) * c n) = shr (fun n => ((n : ℂ) + 1) * c (n + 1)) := by
    funext n
    cases n with
    | zero => simp [shr]
    | succ n => simp [shr]
  have h2 : PB fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) := by
    obtain ⟨C, K, hC, hK, hb⟩ := hc.mul_nat.shift
    refine ⟨C, K, hC, hK, fun n => ?_⟩
    have := hb n
    simpa using this
  rw [h1]
  exact powerSum_shr h2 ht

/-- The hypergeometric coefficients are polynomially bounded. -/
lemma pb_hgCoef (a : ℂ) (m : ℕ) : PB (hgCoef a m) :=
  ⟨1, 2 * max ‖a‖ 1, zero_le_one, by positivity, hgCoef_bound a m⟩

/-- The first derivative coefficients are polynomially bounded. -/
lemma pb_hgCoef1 (a : ℂ) (m : ℕ) : PB (hgCoef1 a m) := by
  have := (pb_hgCoef a m).mul_nat.shift
  obtain ⟨C, K, hC, hK, hb⟩ := this
  refine ⟨C, K, hC, hK, fun n => ?_⟩
  have := hb n
  simpa [hgCoef1] using this

/-- The second derivative coefficients are polynomially bounded. -/
lemma pb_hgCoef2 (a : ℂ) (m : ℕ) : PB (hgCoef2 a m) := by
  have := (pb_hgCoef1 a m).mul_nat.shift
  obtain ⟨C, K, hC, hK, hb⟩ := this
  refine ⟨C, K, hC, hK, fun n => ?_⟩
  have := hb n
  simpa [hgCoef2] using this

/-- **The hypergeometric differential equation**: `x(1−x) G'' + (m+1−x) G' + a² G = 0` on `(-1, 1)`. -/
theorem hgSum_ode (a : ℂ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    (x : ℂ) * (1 - (x : ℂ)) * powerSum (hgCoef2 a m) x + (((m : ℂ) + 1) - (x : ℂ)) * powerSum (hgCoef1 a m) x +
      a ^ 2 * powerSum (hgCoef a m) x = 0 := by
  have h2 := pb_hgCoef2 a m
  have h1 := pb_hgCoef1 a m
  have h0 := pb_hgCoef a m
  have e1 : (x : ℂ) * powerSum (hgCoef2 a m) x = powerSum (shr (hgCoef2 a m)) x := (powerSum_shr h2 hx).symm
  have e2 : (x : ℂ) * ((x : ℂ) * powerSum (hgCoef2 a m) x) = powerSum (shr (shr (hgCoef2 a m))) x := by
    rw [e1, ← powerSum_shr (pb_shr h2) hx]
  have e3 : (x : ℂ) * powerSum (hgCoef1 a m) x = powerSum (shr (hgCoef1 a m)) x := (powerSum_shr h1 hx).symm
  have hE : ∀ n : ℕ, shr (hgCoef2 a m) n + (-1 : ℂ) * shr (shr (hgCoef2 a m)) n + ((m : ℂ) + 1) * hgCoef1 a m n +
      (-1 : ℂ) * shr (hgCoef1 a m) n + a ^ 2 * hgCoef a m n = 0 := by
    intro n
    rcases n with _ | _ | n
    · have := hgCoef_succ a m 0
      simp only [shr, hgCoef1, hgCoef2]
      push_cast at this ⊢
      linear_combination this
    · have h0' := hgCoef_succ a m 0
      have h1' := hgCoef_succ a m 1
      simp only [shr, hgCoef1, hgCoef2]
      push_cast at h0' h1' ⊢
      linear_combination 0 * h0' + h1' * 1
    · have := hgCoef_succ a m (n + 2)
      simp only [shr, hgCoef1, hgCoef2]
      push_cast at this ⊢
      linear_combination this
  -- assemble
  have hlin : powerSum (fun n => shr (hgCoef2 a m) n + (-1 : ℂ) * shr (shr (hgCoef2 a m)) n +
        ((m : ℂ) + 1) * hgCoef1 a m n + (-1 : ℂ) * shr (hgCoef1 a m) n + a ^ 2 * hgCoef a m n) x =
      powerSum (shr (hgCoef2 a m)) x + (-1 : ℂ) * powerSum (shr (shr (hgCoef2 a m))) x +
        ((m : ℂ) + 1) * powerSum (hgCoef1 a m) x + (-1 : ℂ) * powerSum (shr (hgCoef1 a m)) x +
        a ^ 2 * powerSum (hgCoef a m) x := by
    have p2 := pb_shr h2
    have p22 := pb_shr p2
    have p1 := pb_shr h1
    rw [powerSum_add ((((p2.add (p22.const_mul (-1))).add (h1.const_mul ((m : ℂ) + 1))).add (p1.const_mul (-1))))
      (h0.const_mul (a ^ 2)) hx,
      powerSum_add (((p2.add (p22.const_mul (-1))).add (h1.const_mul ((m : ℂ) + 1)))) (p1.const_mul (-1)) hx,
      powerSum_add ((p2.add (p22.const_mul (-1)))) (h1.const_mul ((m : ℂ) + 1)) hx,
      powerSum_add p2 (p22.const_mul (-1)) hx]
    simp only [powerSum_const_mul]
  have hz : powerSum (fun n => shr (hgCoef2 a m) n + (-1 : ℂ) * shr (shr (hgCoef2 a m)) n +
        ((m : ℂ) + 1) * hgCoef1 a m n + (-1 : ℂ) * shr (hgCoef1 a m) n + a ^ 2 * hgCoef a m n) x = 0 := by
    unfold powerSum
    have hz0 : ∀ n : ℕ, (shr (hgCoef2 a m) n + (-1 : ℂ) * shr (shr (hgCoef2 a m)) n +
        ((m : ℂ) + 1) * hgCoef1 a m n + (-1 : ℂ) * shr (hgCoef1 a m) n + a ^ 2 * hgCoef a m n) * (x : ℂ) ^ n = 0 :=
      fun n => by rw [hE n, zero_mul]
    simp only [hz0, tsum_zero]
  rw [hlin, ← e1, ← e2, ← e3] at hz
  linear_combination hz

/-- The variable `x = r² / (1 + r²)`. -/
noncomputable def xOf (r : ℝ) : ℝ := r ^ 2 / (1 + r ^ 2)

/-- `x = r²/(1+r²)` lies in `[0, 1)`. -/
lemma abs_xOf_lt (r : ℝ) : |xOf r| < 1 := by
  unfold xOf
  have h : (0 : ℝ) < 1 + r ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity), div_lt_one h]
  linarith

/-- The derivative of `x(r)`. -/
lemma hasDerivAt_xOf (r : ℝ) : HasDerivAt xOf (2 * r / (1 + r ^ 2) ^ 2) r := by
  have h : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have h2 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := by simpa using h1.const_add 1
  have := h1.div h2 h.ne'
  unfold xOf
  convert this using 1
  field_simp
  ring

/-- The regular solution of the mode system, first component. -/
noncomputable def modeA (a : ℂ) (m : ℕ) (r : ℝ) : ℂ := (r : ℂ) ^ m * hgSum a m (xOf r)

/-- The regular solution of the mode system, second component. -/
noncomputable def modeB (ν a : ℂ) (m : ℕ) (r : ℝ) : ℂ :=
  (2 / ν) * ((r : ℂ) ^ (m + 1) / (1 + (r : ℂ) ^ 2)) * powerSum (hgCoef1 a m) (xOf r)

/-- **The explicit regular solution solves the mode system.** -/
theorem modeHyper_isModeSol {ν a : ℂ} (hν : ν ≠ 0) (ha : a ^ 2 = -ν ^ 2 / 4) (m : ℕ) :
    IsModeSol ν m (modeA a m) (modeB ν a m) := by
  intro r hr
  have hxr := abs_xOf_lt r
  have hK : (1 + (r : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + r ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  -- derivatives of the building blocks
  have dx := hasDerivAt_xOf r
  have dG : HasDerivAt (hgSum a m ∘ xOf) (((2 * r / (1 + r ^ 2) ^ 2 : ℝ) : ℂ) * powerSum (hgCoef1 a m) (xOf r)) r := by
    have := (hasDerivAt_hgSum a m hxr).scomp r dx
    simpa [smul_eq_mul] using this
  have dG1 : HasDerivAt (powerSum (hgCoef1 a m) ∘ xOf)
      (((2 * r / (1 + r ^ 2) ^ 2 : ℝ) : ℂ) * powerSum (hgCoef2 a m) (xOf r)) r := by
    have := (hasDerivAt_hgSum1 a m hxr).scomp r dx
    simpa [smul_eq_mul] using this
  have dpow : ∀ k : ℕ, HasDerivAt (fun r : ℝ => (r : ℂ) ^ k) ((k : ℂ) * (r : ℂ) ^ (k - 1)) r := fun k =>
    (hasDerivAt_pow k (r : ℂ)).comp_ofReal
  have dK : HasDerivAt (fun r : ℝ => 1 + (r : ℂ) ^ 2) (2 * (r : ℂ)) r := by
    have := (dpow 2).const_add 1
    simpa using this
  have hpm : ∀ k : ℕ, (k : ℂ) * (r : ℂ) ^ (k - 1) = (k : ℂ) / r * (r : ℂ) ^ k := by
    intro k
    cases k with
    | zero => simp
    | succ k => simp [pow_succ]; field_simp
  have hx' : ((2 * r / (1 + r ^ 2) ^ 2 : ℝ) : ℂ) = 2 * (r : ℂ) / (1 + (r : ℂ) ^ 2) ^ 2 := by push_cast; ring
  constructor
  · have := (dpow m).mul dG
    refine (this : HasDerivAt (fun y : ℝ => (y : ℂ) ^ m * (hgSum a m ∘ xOf) y) _ r).congr_deriv ?_
    rw [hpm m, hx']
    unfold modeB modeA
    simp only [Int.cast_natCast, Function.comp]
    field_simp
    ring
  · have dQ : HasDerivAt (fun r : ℝ => (r : ℂ) ^ (m + 1) / (1 + (r : ℂ) ^ 2))
        ((((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ (m + 1 - 1) * (1 + (r : ℂ) ^ 2) - (r : ℂ) ^ (m + 1) * (2 * (r : ℂ))) /
          (1 + (r : ℂ) ^ 2) ^ 2) r := (dpow (m + 1)).div dK hK
    have := (dQ.const_mul (2 / ν)).mul dG1
    refine (this : HasDerivAt (fun y : ℝ => (2 / ν) * ((y : ℂ) ^ (m + 1) / (1 + (y : ℂ) ^ 2)) *
      (powerSum (hgCoef1 a m) ∘ xOf) y) _ r).congr_deriv ?_
    have hode := hgSum_ode a m hxr
    have hxc : (xOf r : ℂ) = (r : ℂ) ^ 2 / (1 + (r : ℂ) ^ 2) := by unfold xOf; push_cast; ring
    rw [hxc] at hode
    rw [hx']
    unfold modeB modeA
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Function.comp, hgSum]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [ha] at hode
    set G2 := powerSum (hgCoef2 a m) (xOf r) with hG2
    set G1 := powerSum (hgCoef1 a m) (xOf r) with hG1
    set G0 := powerSum (hgCoef a m) (xOf r) with hG0
    have hr1 : (1 + (r : ℂ) ^ 2) ≠ 0 := hK
    calc _ = (-((↑m + 1) / (r : ℂ)) * (2 / ν * ((r : ℂ) ^ (m + 1) / (1 + (r : ℂ) ^ 2)) * G1) +
          ν / (1 + (r : ℂ) ^ 2) * ((r : ℂ) ^ m * G0)) +
        (4 / ν * (r : ℂ) ^ m / (1 + (r : ℂ) ^ 2)) *
          ((r : ℂ) ^ 2 / (1 + (r : ℂ) ^ 2) * (1 - (r : ℂ) ^ 2 / (1 + (r : ℂ) ^ 2)) * G2 +
            ((m : ℂ) + 1 - (r : ℂ) ^ 2 / (1 + (r : ℂ) ^ 2)) * G1 + (-ν ^ 2 / 4) * G0) := by
          field_simp
          ring
      _ = _ := by rw [hode, mul_zero, add_zero]

/-- `x(r) → 1` from below as `r → ∞`. -/
lemma tendsto_xOf_atTop : Filter.Tendsto xOf Filter.atTop (nhdsWithin 1 (Set.Iio 1)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun r => ?_⟩
  · have h : ∀ r : ℝ, xOf r = 1 - 1 / (1 + r ^ 2) := by
      intro r
      unfold xOf
      have : (1 + r ^ 2) ≠ 0 := by positivity
      field_simp; ring
    rw [show xOf = fun r : ℝ => 1 - 1 / (1 + r ^ 2) from funext h]
    have h1 : Filter.Tendsto (fun r : ℝ => 1 + r ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ _ (Filter.tendsto_pow_atTop (by norm_num))
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  · have h : (0 : ℝ) < 1 + r ^ 2 := by positivity
    show xOf r < 1
    unfold xOf
    rw [div_lt_one h]; linarith

/-- **Abel at `x = 1`**: if the partial sums of the coefficients converge to `L`, then `G(x(r)) → L` as `r → ∞`. -/
theorem tendsto_hgSum_atTop {a : ℂ} {m : ℕ} {L : ℂ}
    (h : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, hgCoef a m i) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun r : ℝ => hgSum a m (xOf r)) Filter.atTop (nhds L) := by
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [Filter.tendsto_map'_iff] at hab
  have := hab.comp tendsto_xOf_atTop
  refine this.congr fun r => ?_
  simp [hgSum, powerSum, Function.comp]

end Lightlike.Dirac

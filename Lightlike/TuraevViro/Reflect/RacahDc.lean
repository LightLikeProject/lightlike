import Lightlike.TuraevViro.Reflect.RacahRoot

/-!
# The denominators of the q-Racah recurrence in closed form

`Dc = u³ p₁ p₄ ∏_{k ∈ {0,2,4}} ((p₂p₃)² - u^k (q₂q₃)²)` and
`Q_k = bk (u^k p₂⁻¹ p₃⁻¹ q₂ q₃)`, so the four nonvanishing hypotheses of the recurrence reduce to
conditions on `u^(2m)`.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

variable {K : Type*} [Field K]

theorem recCoef_Dc (u p1 p2 p3 p4 q2 q3 : K) (hu : u ≠ 0) (h1 : p1 ≠ 0) (h4 : p4 ≠ 0) :
    recCoef Dc u p1 p2 p3 p4 q2 q3 =
      u ^ 3 * p1 * p4 * ((p2 * p3) ^ 2 - (q2 * q3) ^ 2) * ((p2 * p3) ^ 2 - u ^ 2 * (q2 * q3) ^ 2) *
        ((p2 * p3) ^ 2 - u ^ 4 * (q2 * q3) ^ 2) := by
  simp only [recCoef, Dc, A0_0, Poly.eval, Mono.eval, env]
  norm_num
  field_simp
  ring

theorem recCoef_fQ (u p1 p2 p3 p4 q2 q3 : K) (hu : u ≠ 0) (h1 : p1 ≠ 0)
    (h2 : p2 ≠ 0) (h3 : p3 ≠ 0) (h4 : p4 ≠ 0) (h5 : q2 ≠ 0) (h6 : q3 ≠ 0) :
    (recCoef fQ0 u p1 p2 p3 p4 q2 q3 = bk (p2⁻¹ * p3⁻¹ * q2 * q3)) ∧
    (recCoef fQ1 u p1 p2 p3 p4 q2 q3 = bk (u * p2⁻¹ * p3⁻¹ * q2 * q3)) ∧
    (recCoef fQ2 u p1 p2 p3 p4 q2 q3 = bk (u ^ 2 * p2⁻¹ * p3⁻¹ * q2 * q3)) := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold recCoef
  · exact eval_fQ0 hu h1 h2 h3 h4 h5 h6 one_ne_zero
  · exact eval_fQ1 hu h1 h2 h3 h4 h5 h6 one_ne_zero
  · exact eval_fQ2 hu h1 h2 h3 h4 h5 h6 one_ne_zero

/-- `u^(2m) = 1` at `u = e^{iπ/r}` forces `r ∣ m`. -/
lemma uC_two_mul_ne_one {r : ℕ} (hr : 2 ≤ r) {m : ℤ} (hm : ¬ (r : ℤ) ∣ m) :
    uC r ^ (2 * m) ≠ 1 := by
  intro h
  rw [uC_zpow, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply hm
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  refine ⟨n, ?_⟩
  have h2 : ((2 * m : ℤ) * Real.pi / r : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have : ((m : ℝ)) = r * n := by
    field_simp at h2
    push_cast at h2
    linarith
  exact_mod_cast this

/-- `bk (u^m) ≠ 0` at the root of unity unless `r ∣ m`. -/
lemma bk_uC_ne {r : ℕ} (hr : 2 ≤ r) {m : ℤ} (hm : ¬ (r : ℤ) ∣ m) : bk (uC r ^ m) ≠ 0 := by
  intro h
  have hu : uC r ≠ 0 := uC_ne_zero r
  apply uC_two_mul_ne_one hr hm
  unfold bk at h
  have h' : uC r ^ m = (uC r ^ m)⁻¹ := sub_eq_zero.mp h
  have hz : uC r ^ m ≠ 0 := zpow_ne_zero _ hu
  rw [two_mul, zpow_add₀ hu]
  field_simp at h'
  rw [← sq]; exact h'

/-- The four nonvanishing hypotheses of the recurrence at `u = e^{iπ/r}`, `p_i = u^{a_i}`,
`q_j = u^{b_j}`, reduce to `r ∤ b2 + b3 - a2 - a3 + k` for `k = 0, 1, 2`. -/
theorem nonvanishing_root {r : ℕ} (hr : 2 ≤ r) (a1 a2 a3 a4 b2 b3 : ℤ)
    (hD : ∀ k : ℤ, 0 ≤ k → k ≤ 2 → ¬ (r : ℤ) ∣ b2 + b3 - a2 - a3 + k) :
    recCoef fQ0 (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3) ≠ 0 ∧
    recCoef fQ1 (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3) ≠ 0 ∧
    recCoef fQ2 (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3) ≠ 0 ∧
    recCoef Dc (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3) ≠ 0 := by
  have hu : uC r ≠ 0 := uC_ne_zero r
  have z : ∀ n : ℤ, uC r ^ n ≠ 0 := fun n => zpow_ne_zero _ hu
  obtain ⟨e0, e1, e2⟩ := recCoef_fQ (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4)
    (uC r ^ b2) (uC r ^ b3) hu (z _) (z _) (z _) (z _) (z _) (z _)
  have key : ∀ k : ℤ, 0 ≤ k → k ≤ 2 →
      bk (uC r ^ k * (uC r ^ a2)⁻¹ * (uC r ^ a3)⁻¹ * uC r ^ b2 * uC r ^ b3) ≠ 0 := by
    intro k h0 h2
    have := bk_uC_ne hr (hD k h0 h2)
    convert this using 2
    rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu]
    congr 1; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]
    simpa using key 0 le_rfl (by norm_num)
  · rw [e1]
    simpa using key 1 (by norm_num) (by norm_num)
  · rw [e2]
    have := key 2 (by norm_num) le_rfl
    simpa only [zpow_ofNat] using this
  · rw [recCoef_Dc _ _ _ _ _ _ _ hu (z _) (z _)]
    have fac : ∀ j : ℕ, j ≤ 2 →
        ((uC r ^ a2 * uC r ^ a3) ^ 2 - uC r ^ (2 * j) * (uC r ^ b2 * uC r ^ b3) ^ 2) ≠ 0 := by
      intro j hj h
      have hm : ¬ (r : ℤ) ∣ a2 + a3 - b2 - b3 - j := by
        intro hdv
        apply hD j (by positivity) (by exact_mod_cast hj)
        have := (dvd_neg.mpr hdv)
        convert this using 1; ring
      apply uC_two_mul_ne_one hr hm
      have h' : (uC r ^ a2 * uC r ^ a3) ^ 2 = uC r ^ (2 * j) * (uC r ^ b2 * uC r ^ b3) ^ 2 :=
        sub_eq_zero.mp h
      have e1 : (uC r ^ a2 * uC r ^ a3) ^ 2 = uC r ^ (2 * (a2 + a3)) := by
        rw [← zpow_add₀ hu, ← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      have e2 : uC r ^ (2 * (j : ℤ)) * (uC r ^ b2 * uC r ^ b3) ^ 2 = uC r ^ (2 * ((b2 + b3 : ℤ) + j)) := by
        rw [← zpow_add₀ hu, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu]; congr 1; push_cast; ring
      have hh : uC r ^ (2 * (a2 + a3 : ℤ)) = uC r ^ (2 * ((b2 + b3 : ℤ) + j)) := by
        rw [← e1, ← e2]; exact h'
      rw [show 2 * (a2 + a3 - b2 - b3 - (j : ℤ)) = 2 * (a2 + a3 : ℤ) - 2 * ((b2 + b3 : ℤ) + j) by ring,
        zpow_sub₀ hu, hh]
      exact div_self (z _)
    have f0 := fac 0 (by norm_num)
    have f1 := fac 1 (by norm_num)
    have f2 := fac 2 (by norm_num)
    have g0 : (uC r ^ a2 * uC r ^ a3) ^ 2 - (uC r ^ b2 * uC r ^ b3) ^ 2 ≠ 0 := by simpa using f0
    have g1 : (uC r ^ a2 * uC r ^ a3) ^ 2 - uC r ^ 2 * (uC r ^ b2 * uC r ^ b3) ^ 2 ≠ 0 := by
      simpa using f1
    have g2 : (uC r ^ a2 * uC r ^ a3) ^ 2 - uC r ^ 4 * (uC r ^ b2 * uC r ^ b3) ^ 2 ≠ 0 := by
      simpa using f2
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hu) (z _)) (z _)) g0) g1) g2

end Lightlike.TV.Refl

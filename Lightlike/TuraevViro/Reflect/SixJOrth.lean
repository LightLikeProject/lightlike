import Lightlike.TuraevViro.Reflect.SixJBalance
import Lightlike.TuraevViro.Reflect.JacobiOrth
import Lightlike.TuraevViro.Reflect.EndRowCoef

/-!
# Off-diagonal orthogonality of the q-6j symbol in one colour

For fixed `j₁, j₂, j₄, j₅` the vectors `x ↦ Sj … q x` (the q-Racah sum, `q` the sixth colour) are
eigenvectors of the Jacobi matrix of `SixJRow` with eigenvalue `2 cos((q+1)π/r)`, symmetric for the
weight `jOmega`. Different `q` therefore give weighted-orthogonal vectors, provided the rows at the
two ends of the `x`-range are the ones of the recurrence with the outer terms zero.

## Main results

* `sixj_offdiag`: the weighted orthogonality of the q-6j sums for different sixth colours.

## References

* `koekoek-swarttouw-1996`, the q-Racah polynomials; `turaev-1994`, Chapter VI (6j symbols).
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset Real

lemma cz_eq_cos (r : ℕ) (m : ℤ) : cz r m = ((2 * Real.cos (m * π / r) : ℝ) : ℂ) := by
  unfold cz ck
  rw [← zpow_neg, uC_zpow, uC_zpow, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  have e : (((-m : ℤ) : ℝ) * π / r : ℝ) = -((m : ℝ) * π / r) := by push_cast; ring
  rw [e]
  push_cast
  have e2 : Complex.I * (-(↑m * ↑π / ↑r : ℂ)) = -(Complex.I * (↑m * ↑π / ↑r)) := by ring
  rw [e2, show Complex.I * (↑m * ↑π / ↑r : ℂ) = (↑m * ↑π / ↑r) * Complex.I by ring]
  have e3 : -((↑m * ↑π / ↑r : ℂ) * Complex.I) = (-(↑m * ↑π / ↑r)) * Complex.I := by ring
  rw [e3]
  ring

/-- The cosine `cz r (1 + q)` determines `q` among admissible colours. -/
lemma cz_inj {r : ℕ} (hr : 2 ≤ r) {q q' : ℕ} (hq : q + 1 < r) (hq' : q' + 1 < r)
    (h : cz r (1 + q) = cz r (1 + q')) : q = q' := by
  rw [cz_eq_cos, cz_eq_cos] at h
  have h' := Complex.ofReal_injective h
  have h'' : Real.cos (((1 + (q : ℤ) : ℤ) : ℝ) * π / r) = Real.cos (((1 + (q' : ℤ) : ℤ) : ℝ) * π / r) := by
    linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hpi := Real.pi_pos
  have hq1 : ((q : ℝ) + 1) < r := by exact_mod_cast hq
  have hq1' : ((q' : ℝ) + 1) < r := by exact_mod_cast hq'
  push_cast at h''
  have key := Real.injOn_cos (x₁ := (1 + (q : ℝ)) * π / r) (x₂ := (1 + (q' : ℝ)) * π / r)
  have m1 : (1 + (q : ℝ)) * π / r ∈ Set.Icc 0 π := by
    constructor
    · positivity
    · rw [div_le_iff₀ hr0]; nlinarith
  have m2 : (1 + (q' : ℝ)) * π / r ∈ Set.Icc 0 π := by
    constructor
    · positivity
    · rw [div_le_iff₀ hr0]; nlinarith
  have := key m1 m2 h''
  field_simp at this
  have : (q : ℝ) = q' := by nlinarith
  exact_mod_cast this

/-- The row sum of `Sj` vanishes just below the lowest admissible third colour. -/
lemma Sj_below {r : ℕ} (j1 j2 j4 j5 q x0 : ℕ)
    (hpar : (j1 + j2 + x0) % 2 = 0) (h2 : (j1 + j5 + q) % 2 = 0) (h3 : (j4 + j2 + q) % 2 = 0)
    (h4 : (j4 + j5 + x0) % 2 = 0)
    (hlo : (x0 : ℤ) < (j1 : ℤ) - j2 + 2 ∨ (x0 : ℤ) < (j2 : ℤ) - j1 + 2 ∨
      (x0 : ℤ) < (j4 : ℤ) - j5 + 2 ∨ (x0 : ℤ) < (j5 : ℤ) - j4 + 2) :
    Sj r j1 j2 j4 j5 q ((x0 : ℤ) - 2) = 0 := by
  unfold Sj
  apply SR_eq_zero_of_empty
  intro z hz
  omega

/-- The row sum of `Sj` vanishes just above the highest admissible third colour. -/
lemma Sj_above {r : ℕ} (hr : 2 ≤ r) (j1 j2 j4 j5 q xn : ℕ)
    (hpar : (j1 + j2 + xn) % 2 = 0) (h4 : (j4 + j5 + xn) % 2 = 0)
    (hhi : (j1 : ℤ) + j2 < xn + 2 ∨ (j4 : ℤ) + j5 < xn + 2 ∨
      (2 * r : ℤ) - 2 ≤ (j1 : ℤ) + j2 + (xn + 2) ∨ (2 * r : ℤ) - 2 ≤ (j4 : ℤ) + j5 + (xn + 2)) :
    Sj r j1 j2 j4 j5 q ((xn : ℤ) + 2) = 0 := by
  unfold Sj
  rcases hhi with h | h | h | h
  · apply SR_eq_zero_of_empty; intro z hz; omega
  · apply SR_eq_zero_of_empty; intro z hz; omega
  · apply SR_eq_zero_of_big hr; omega
  · apply SR_eq_zero_of_big hr; omega

/-- **Off-diagonal orthogonality** of the q-6j symbol in the sixth colour. For two different
admissible sixth colours `q ≠ q'`, the vectors `x ↦ Sj … q x` and `x ↦ Sj … q' x`, taken over the
admissible third colours `x₀, x₀+2, …, x₀+2n`, are orthogonal for the weight `jOmega`.
The third colours `0` and `r-2` are included: there the recurrence is replaced by the endpoint rows
(`row_at`). -/
theorem sixj_offdiag {r : ℕ} (hr : 2 ≤ r) (j1 j2 j4 j5 x0 n : ℕ)
    (hadm : ∀ k ≤ n, qAdm r j1 j2 (x0 + 2 * k) ∧ qAdm r j4 j5 (x0 + 2 * k))
    (hlo : (x0 : ℤ) < (j1 : ℤ) - j2 + 2 ∨ (x0 : ℤ) < (j2 : ℤ) - j1 + 2 ∨
      (x0 : ℤ) < (j4 : ℤ) - j5 + 2 ∨ (x0 : ℤ) < (j5 : ℤ) - j4 + 2)
    (hhi : (j1 : ℤ) + j2 < (x0 + 2 * n : ℕ) + 2 ∨ (j4 : ℤ) + j5 < (x0 + 2 * n : ℕ) + 2 ∨
      (2 * r : ℤ) - 2 ≤ (j1 : ℤ) + j2 + ((x0 + 2 * n : ℕ) + 2) ∨
      (2 * r : ℤ) - 2 ≤ (j4 : ℤ) + j5 + ((x0 + 2 * n : ℕ) + 2))
    {q q' : ℕ} (hq1 : qAdm r j1 j5 q) (hq2 : qAdm r j4 j2 q)
    (hq1' : qAdm r j1 j5 q') (hq2' : qAdm r j4 j2 q') (hqr : q + 1 < r) (hqr' : q' + 1 < r)
    (hne : q ≠ q') :
    ∑ k ∈ range (n + 1), jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
      Sj r j1 j2 j4 j5 q ((x0 + 2 * k : ℕ) : ℤ) * Sj r j1 j2 j4 j5 q' ((x0 + 2 * k : ℕ) : ℤ) = 0 := by
  have hr3 : 3 ≤ r := by omega
  have h0 := hadm 0 (Nat.zero_le _)
  have hn := hadm n le_rfl
  have hlo' : Sj r j1 j2 j4 j5 q ((x0 : ℤ) - 2) = 0 ∧ Sj r j1 j2 j4 j5 q' ((x0 : ℤ) - 2) = 0 := by
    have := h0.1.1; have := h0.2.1
    unfold qAdm Lightlike.Pentagon.Tri at hq1 hq2 hq1' hq2' h0
    exact ⟨Sj_below j1 j2 j4 j5 q x0 (by omega) (by omega) (by omega) (by omega) hlo,
      Sj_below j1 j2 j4 j5 q' x0 (by omega) (by omega) (by omega) (by omega) hlo⟩
  have hhi' : Sj r j1 j2 j4 j5 q (((x0 + 2 * n : ℕ) : ℤ) + 2) = 0 ∧
      Sj r j1 j2 j4 j5 q' (((x0 + 2 * n : ℕ) : ℤ) + 2) = 0 := by
    unfold qAdm Lightlike.Pentagon.Tri at hn
    exact ⟨Sj_above hr j1 j2 j4 j5 q _ (by omega) (by omega) hhi,
      Sj_above hr j1 j2 j4 j5 q' _ (by omega) (by omega) hhi⟩
  -- the abstract data over ℂ
  set a : ℕ → ℂ := fun k => if k < n then jA r j1 j2 j4 j5 (x0 + 2 * k) else 0 with ha
  set c : ℕ → ℂ := fun k => if k = 0 then 0 else jC r j1 j2 j4 j5 (x0 + 2 * k) with hc
  set b : ℕ → ℂ := fun k => jBsp r j1 j2 j4 j5 (x0 + 2 * k) with hb
  set ω : ℕ → ℂ := fun k => (jOmega r j1 j2 j4 j5 (x0 + 2 * k) : ℂ) with hω
  have row : ∀ (qq : ℕ), qAdm r j1 j5 qq → qAdm r j4 j2 qq →
      Sj r j1 j2 j4 j5 qq ((x0 : ℤ) - 2) = 0 →
      Sj r j1 j2 j4 j5 qq (((x0 + 2 * n : ℕ) : ℤ) + 2) = 0 →
      ∀ k ≤ n, a k * (Sj r j1 j2 j4 j5 qq ((x0 + 2 * (k + 1) : ℕ) : ℤ) : ℂ)
        + b k * (Sj r j1 j2 j4 j5 qq ((x0 + 2 * k : ℕ) : ℤ) : ℂ)
        + c k * (Sj r j1 j2 j4 j5 qq ((x0 + 2 * (k - 1) : ℕ) : ℤ) : ℂ)
        = cz r (1 + qq) * (Sj r j1 j2 j4 j5 qq ((x0 + 2 * k : ℕ) : ℤ) : ℂ) := by
    intro qq g1 g2 lo hi k hk
    have hk' := hadm k hk
    have e1 : ((x0 + 2 * (k + 1) : ℕ) : ℤ) = ((x0 + 2 * k : ℕ) : ℤ) + 2 := by push_cast; ring
    have eA : a k * (Sj r j1 j2 j4 j5 qq ((x0 + 2 * (k + 1) : ℕ) : ℤ) : ℂ)
        = jA r j1 j2 j4 j5 (x0 + 2 * k) * (Sj r j1 j2 j4 j5 qq (((x0 + 2 * k : ℕ) : ℤ) + 2) : ℂ) := by
      rw [e1]
      by_cases hkn : k < n
      · simp [ha, hkn]
      · have : k = n := by omega
        subst this
        rw [hi]
        simp [ha]
    have eC : c k * (Sj r j1 j2 j4 j5 qq ((x0 + 2 * (k - 1) : ℕ) : ℤ) : ℂ)
        = jC r j1 j2 j4 j5 (x0 + 2 * k) * (Sj r j1 j2 j4 j5 qq (((x0 + 2 * k : ℕ) : ℤ) - 2) : ℂ) := by
      by_cases hk0 : k = 0
      · subst hk0
        simp [hc, lo]
      · have e2 : ((x0 + 2 * (k - 1) : ℕ) : ℤ) = ((x0 + 2 * k : ℕ) : ℤ) - 2 := by
          have : 1 ≤ k := by omega
          push_cast [Nat.cast_sub this]; ring
        rw [e2]
        simp [hc, hk0]
    rw [eA, eC, show b k = jBsp r j1 j2 j4 j5 (x0 + 2 * k) from rfl]
    have R := row_at hr3 j1 j2 j4 j5 (x0 + 2 * k) qq hk'.1 g1 g2 hk'.2
    exact R
  have hdb : ∀ k < n, ω k * a k = ω (k + 1) * c (k + 1) := by
    intro k hk
    have hk1 := hadm k hk.le
    have hk2 := hadm (k + 1) hk
    have B := sixj_balance hr hk1.1 (by simpa [Nat.mul_succ, add_assoc] using hk2.1) hk1.2
      (by simpa [Nat.mul_succ, add_assoc] using hk2.2)
    simp only [ha, hc, hω, hk, Nat.succ_ne_zero]
    have e : x0 + 2 * (k + 1) = x0 + 2 * k + 2 := by ring
    rw [e]
    exact B
  have key := jacobi_orth (a := a) (b := b) (c := c) (ω := ω)
    (v := fun k => (Sj r j1 j2 j4 j5 q ((x0 + 2 * k : ℕ) : ℤ) : ℂ))
    (w := fun k => (Sj r j1 j2 j4 j5 q' ((x0 + 2 * k : ℕ) : ℤ) : ℂ))
    (lam := cz r (1 + q)) (mu := cz r (1 + q')) n hdb
    (by simp [hc]) (by simp [ha])
    (row q hq1 hq2 hlo'.1 hhi'.1) (row q' hq1' hq2' hlo'.2 hhi'.2)
  have hne' : cz r (1 + q) - cz r (1 + q') ≠ 0 := by
    intro h
    exact hne (cz_inj hr hqr hqr' (by push_cast; exact sub_eq_zero.mp h))
  have hz := (mul_eq_zero.mp key).resolve_left hne'
  have : ((∑ k ∈ range (n + 1), jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
      Sj r j1 j2 j4 j5 q ((x0 + 2 * k : ℕ) : ℤ) * Sj r j1 j2 j4 j5 q' ((x0 + 2 * k : ℕ) : ℤ) : ℝ) : ℂ) = 0 := by
    simpa [hω] using hz
  exact_mod_cast this

end Lightlike.TV.Refl

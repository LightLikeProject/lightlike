import Lightlike.TuraevViro.Reflect.RacahReal
import Lightlike.TuraevViro.Reflect.EndRowTrig

/-!
# The regularised q-Racah sum at `q = e^{iπ/r}` and its reflection symmetry

At `q = e^{iπ/r}` the quantum integer `[n] = sin(nπ/r)/sin(π/r)` vanishes for `n = r` and for no other
`n` with `1 ≤ n < 2r`. A q-Racah sum whose box `max αᵢ ≤ z ≤ min βⱼ` lies above `z = r - 1` has the
factor `[r]` in the q-factorial `[z+1]!` of every term. Near the root of unity, at `q = e^{iθ}`, the sum
divided by `[r]_θ` has a finite limit: the **regularised sum** `SRg`, the same sum with `[z+1]!`
replaced by the product of `[k]`, `1 ≤ k ≤ z+1`, `k ≠ r` (`qfactReg`).

The limit `θ → π/r` of the generic Biedenharn–Elliott identity (`QSixJLimit.lean`) leaves the summed
colours `x` whose three triads are above the level; their contributions cancel in pairs `x ↔ 2r - 2 - x`
because of the reflection symmetry proved here: in the Racah parameters of the 6j symbol
`{a b x; c d p}` (with `p` in the third column, as in `RacahReal.lean`, so that the recurrence moves `p`),
replacing `x` by `2r - 2 - x` multiplies the regularised sum by the explicit ratio of q-factorials `regFac`.

## Main results

* `qfactReg_of_ge`: `qfactReg r n = [r-1]! (-1)^(n-r) [n-r]!` for `n ≥ r` (from `[r+j] = -[j]`).
* `qfact_reflect`: `[r-1-k]! [k]! = [r-1]!` (from `[r-j] = [j]`).
* `reg_recurrence`: the telescoped q-Racah recurrence for the regularised sums.
* `SRg_reflect`: the reflection symmetry.

The reflection was first measured numerically (mpmath, 40 digits, `r = 5, …, 11`, 713 tuples, ratio
`1` to working precision); it is not termwise (the two sums can have different numbers of terms).
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Real Finset Lightlike.TV

/-! ## Quantum integers and factorials at the root of unity -/

/-- `[r + j] = -[j]` at `q = e^{iπ/r}`. -/
lemma qnum_add_self {r : ℕ} (hr : 2 ≤ r) (j : ℕ) : qnum r (r + j) = - qnum r j := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  unfold qnum
  rw [show ((r + j : ℕ) : ℝ) * π / r = j * π / r + π by push_cast; field_simp; ring, sin_add_pi,
    neg_div]

/-- The q-factorial at `q = e^{iπ/r}` with the vanishing factor `[r]` left out. -/
noncomputable def qfactReg (r n : ℕ) : ℝ := ∏ k ∈ range n, if k + 1 = r then 1 else qnum r (k + 1)

lemma qfactReg_succ (r n : ℕ) :
    qfactReg r (n + 1) = qfactReg r n * (if n + 1 = r then 1 else qnum r (n + 1)) := by
  unfold qfactReg; rw [prod_range_succ]

lemma qfactReg_of_lt {r n : ℕ} (hn : n < r) : qfactReg r n = qfact r n := by
  induction n with
  | zero => simp [qfactReg, qfact]
  | succ n ih =>
    rw [qfactReg_succ, ih (by omega), ite_eq_right (by omega)]
    unfold qfact; rw [prod_range_succ]

/-- Above the level: `qfactReg r n = [r-1]! (-1)^(n-r) [n-r]!`. -/
lemma qfactReg_of_ge {r : ℕ} (hr : 2 ≤ r) {n : ℕ} (hn : r ≤ n) :
    qfactReg r n = qfact r (r - 1) * (-1) ^ (n - r) * qfact r (n - r) := by
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    rw [qfactReg_succ, ite_eq_left rfl, qfactReg_of_lt (by omega)]
    simp [qfact]
  | succ n hrn ih =>
    rw [qfactReg_succ, ih, ite_eq_right (by omega), show n + 1 - r = (n - r) + 1 by omega, pow_succ]
    have e : qnum r (n + 1) = - qnum r (n - r + 1) := by
      rw [← qnum_add_self hr]; congr 1; omega
    rw [e]
    unfold qfact; rw [prod_range_succ]; ring

/-- `[r-1-k]! [k]! = [r-1]!` at `q = e^{iπ/r}`. -/
lemma qfact_reflect {r : ℕ} (hr : 2 ≤ r) {k : ℕ} (hk : k ≤ r - 1) :
    qfact r (r - 1 - k) * qfact r k = qfact r (r - 1) := by
  induction k with
  | zero => simp [qfact]
  | succ k ih =>
    have h1 : qfact r (r - 1 - k) = qfact r (r - 1 - (k + 1)) * qnum r (k + 1) := by
      rw [show r - 1 - k = (r - 1 - (k + 1)) + 1 by omega]
      unfold qfact; rw [prod_range_succ]
      congr 1
      rw [show r - 1 - (k + 1) + 1 = r - (k + 1) by omega, qnum_sub hr (by omega)]
    have h2 : qfact r (k + 1) = qfact r k * qnum r (k + 1) := by
      unfold qfact; rw [prod_range_succ]
    rw [← ih (by omega), h1, h2]; ring

lemma qfact_ne_zero {r n : ℕ} (hr : 2 ≤ r) (hn : n < r) : qfact r n ≠ 0 := (qfact_pos hr hn).ne'

/-- The regularised q-factorial as a function on `ℤ`. -/
noncomputable def PnReg (r : ℕ) (n : ℤ) : ℝ := if 0 ≤ n then qfactReg r n.toNat else 0

lemma PnReg_step {r : ℕ} (n : ℤ) (hn : 0 ≤ n) (hnr : n + 1 ≠ r) :
    PnReg r (n + 1) = qZ r (n + 1) * PnReg r n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  have e : qZ r ((m : ℤ) + 1) = qnum r (m + 1) := by simp [qZ, qnum]
  have h2 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
  simp only [PnReg, hn, h2, ite_true, Int.toNat_natCast]
  rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, e, qfactReg_succ, ite_eq_right (by omega)]
  ring

/-- Complex regularised q-factorial. -/
noncomputable def PnRegC (r : ℕ) (n : ℤ) : ℂ := ((PnReg r n : ℝ) : ℂ)

lemma PnRegC_step {r : ℕ} (hr : 2 ≤ r) (n : ℤ) (hn : 0 ≤ n) (hnr : n + 1 ≠ r) :
    PnRegC r (n + 1) = bk (uC r ^ (n + 1)) / (uC r - (uC r)⁻¹) * PnRegC r n := by
  rw [bk_uC_div hr (n + 1)]
  unfold PnRegC
  rw [PnReg_step n hn hnr]
  push_cast
  ring

/-! ## The regularised Racah sum -/

/-- The summand of the regularised q-Racah sum: `qRacahTerm` with `[z+1]!` replaced by `qfactReg`. -/
noncomputable def regTerm (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) (z : ℕ) : ℝ :=
  (-1 : ℝ) ^ z * PnReg r ((z : ℤ) + 1) *
    (invQFact r (z - a1) * invQFact r (z - a2) * invQFact r (z - a3) * invQFact r (z - a4) *
      (invQFact r (b1 - z) * invQFact r (b2 - z) * invQFact r (b3 - z)))

/-- **The regularised q-Racah sum** over `z = 0, …, β₁`. -/
noncomputable def SRg (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) : ℝ :=
  ∑ z ∈ range (b1.toNat + 1), regTerm r a1 a2 a3 a4 b1 b2 b3 z

lemma invQFact_neg {r : ℕ} {n : ℤ} (h : n < 0) : invQFact r n = 0 := by
  simp only [invQFact, show ¬ (0 ≤ n) by omega, ↓reduceIte]

lemma regTerm_zero_of_lt {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ}
    (h : (z : ℤ) < a1 ∨ (z : ℤ) < a2 ∨ (z : ℤ) < a3 ∨ (z : ℤ) < a4) :
    regTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  unfold regTerm
  rcases h with h | h | h | h
  · simp [invQFact_neg (r := r) (show (z : ℤ) - a1 < 0 by omega)]
  · simp [invQFact_neg (r := r) (show (z : ℤ) - a2 < 0 by omega)]
  · simp [invQFact_neg (r := r) (show (z : ℤ) - a3 < 0 by omega)]
  · simp [invQFact_neg (r := r) (show (z : ℤ) - a4 < 0 by omega)]

lemma regTerm_zero_of_gt {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ}
    (h : b1 < (z : ℤ) ∨ b2 < (z : ℤ) ∨ b3 < (z : ℤ)) :
    regTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  unfold regTerm
  rcases h with h | h | h
  · simp [invQFact_neg (r := r) (show b1 - (z : ℤ) < 0 by omega)]
  · simp [invQFact_neg (r := r) (show b2 - (z : ℤ) < 0 by omega)]
  · simp [invQFact_neg (r := r) (show b3 - (z : ℤ) < 0 by omega)]

/-- An empty box (`βⱼ < αᵢ`) gives the sum `0`. -/
lemma SRg_eq_zero {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ}
    (h : ∃ i ∈ ({a1, a2, a3, a4} : Finset ℤ), ∃ j ∈ ({b1, b2, b3} : Finset ℤ), j < i) :
    SRg r a1 a2 a3 a4 b1 b2 b3 = 0 := by
  obtain ⟨i, hi, j, hj, hji⟩ := h
  refine sum_eq_zero fun z _ => ?_
  by_cases hz : (z : ℤ) < i
  · apply regTerm_zero_of_lt
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  · apply regTerm_zero_of_gt
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> omega

/-- A box with one point `z₀` (some `αᵢ = βⱼ = z₀`) gives the single term at `z₀`. -/
lemma SRg_eq_single {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} (z0 : ℕ)
    (hhi : (z0 : ℤ) ≤ b1 ∧ (z0 : ℤ) ≤ b2 ∧ (z0 : ℤ) ≤ b3)
    (hpt : (a1 = z0 ∨ a2 = z0 ∨ a3 = z0 ∨ a4 = z0) ∧ (b1 = z0 ∨ b2 = z0 ∨ b3 = z0)) :
    SRg r a1 a2 a3 a4 b1 b2 b3 = regTerm r a1 a2 a3 a4 b1 b2 b3 z0 := by
  unfold SRg
  rw [sum_eq_single_of_mem z0 (mem_range.mpr (by omega))]
  intro z _ hz
  rcases lt_or_gt_of_ne hz with h | h
  · apply regTerm_zero_of_lt; omega
  · apply regTerm_zero_of_gt; omega

/-- The regularised term is the recurrence's term `tt` with `Pn = PnRegC`. -/
lemma tt_eq_regTerm (r : ℕ) (A1 A2 A3 A4 B1 B2 B3 : ℤ) (z : ℕ) :
    tt (Fi := FiC r) (Pn := PnRegC r) A1 A2 A3 A4 B1 B2 B3 (z : ℤ) =
      ((regTerm r A1 A2 A3 A4 B1 B2 B3 z : ℝ) : ℂ) := by
  unfold tt regTerm PnRegC
  simp only [FiC, zpow_natCast]
  push_cast
  ring

lemma SRg_eq {r : ℕ} (a1 a2 a3 a4 b1 b2 b3 : ℤ) (L : ℕ) (hb0 : 0 ≤ b1) (hL : (L : ℤ) ≤ b1 + 1)
    (hz : ∀ z : ℕ, z < L → regTerm r a1 a2 a3 a4 b1 b2 b3 z = 0) :
    SRg r a1 a2 a3 a4 b1 b2 b3 =
      ∑ k ∈ range (b1 + 1 - L).toNat, regTerm r a1 a2 a3 a4 b1 b2 b3 (L + k) := by
  unfold SRg
  rw [show b1.toNat + 1 = L + (b1 + 1 - L).toNat by omega, Finset.sum_range_add,
    Finset.sum_eq_zero (fun z hz' => hz z (Finset.mem_range.mp hz')), zero_add]

/-- **The telescoped q-Racah recurrence for the regularised sums** at `q = e^{iπ/r}`, when the box
starts at `L = α₂` or `L = α₃` with `L ≥ r - 1` (so that every `[z+1]!` of the range contains `[r]`). -/
theorem reg_recurrence {r : ℕ} (hr : 2 ≤ r) (a1 a2 a3 a4 b1 b2 b3 : ℤ)
    (hbal : b1 + b2 + b3 = a1 + a2 + a3 + a4) (L : ℕ) (hb0 : 0 ≤ b1) (hL : (L : ℤ) ≤ b1 + 1)
    (hA : (L : ℤ) = a2 ∨ (L : ℤ) = a3) (hLa : a2 ≤ L ∧ a3 ≤ L) (hLr : (r : ℤ) - 1 ≤ L)
    (hb1 : b1 - a1 ≤ (r : ℤ) - 2) (hb2 : b1 - a2 ≤ (r : ℤ) - 2) (hb3 : b1 - a3 ≤ (r : ℤ) - 2)
    (hb4 : b1 - a4 ≤ (r : ℤ) - 2)
    (hb6 : b2 - L ≤ (r : ℤ) - 2) (hb7 : b3 - L ≤ (r : ℤ) - 2)
    (hD : ∀ k : ℤ, 0 ≤ k → k ≤ 2 → ¬ (r : ℤ) ∣ b2 + b3 - a2 - a3 + k) :
    2 * (rcR r a1 a2 a3 a4 b2 b3 fNa / 2 /
          (rcR r a1 a2 a3 a4 b2 b3 fQ1 * rcR r a1 a2 a3 a4 b2 b3 fQ2))
        * (SRg r (a1 + 1) a2 a3 (a4 + 1) b1 (b2 + 1) (b3 + 1) : ℂ)
      + 2 * (rcR r a1 a2 a3 a4 b2 b3 fbn /
          (2 * rcR r a1 a2 a3 a4 b2 b3 fQ0 * rcR r a1 a2 a3 a4 b2 b3 fQ2))
        * (SRg r a1 a2 a3 a4 b1 b2 b3 : ℂ)
      + 2 * (rcR r a1 a2 a3 a4 b2 b3 fNc / 2 /
          (rcR r a1 a2 a3 a4 b2 b3 fQ0 * rcR r a1 a2 a3 a4 b2 b3 fQ1))
        * (SRg r (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) : ℂ)
      - rcR r a1 a2 a3 a4 b2 b3 fCq * (SRg r a1 a2 a3 a4 b1 b2 b3 : ℂ) = 0 := by
  have hu : uC r ≠ 0 := uC_ne_zero r
  have hd : uC r - (uC r)⁻¹ ≠ 0 := by
    have := bk_uC_ne hr (m := 1) (by
      intro h; have := Int.le_of_dvd one_pos h; omega)
    simpa [bk] using this
  obtain ⟨hQ0, hQ1, hQ2, hDc⟩ := nonvanishing_root hr a1 a2 a3 a4 b2 b3 hD
  have hn : ((L : ℤ) + ((b1 + 1 - L).toNat : ℕ)) = b1 + 1 := by omega
  have vz : ∀ (c1 c4 : ℤ) (d1 d2 d3 : ℤ),
      ∀ z : ℕ, z < L → regTerm r c1 a2 a3 c4 d1 d2 d3 z = 0 := by
    intro c1 c4 d1 d2 d3 z hz
    apply regTerm_zero_of_lt
    omega
  have e0 := SRg_eq (r := r) a1 a2 a3 a4 b1 b2 b3 L hb0 hL (vz _ _ _ _ _)
  have e1 := SRg_eq (r := r) (a1 + 1) a2 a3 (a4 + 1) b1 (b2 + 1) (b3 + 1) L hb0 hL (vz _ _ _ _ _)
  have e2 := SRg_eq (r := r) (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) L hb0 hL (vz _ _ _ _ _)
  have hG0 : Gq (Fi := FiC r) (Pn := PnRegC r) (uC r)
      (rhoC (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3))
      a1 a2 a3 a4 b1 b2 b3 L = 0 := by
    unfold Gq
    rcases hA with h | h
    · rw [show (L : ℤ) - a2 = 0 by omega]; simp [bk]
    · rw [show (L : ℤ) - a3 = 0 by omega]; simp [bk]
  have hG1 : Gq (Fi := FiC r) (Pn := PnRegC r) (uC r)
      (rhoC (uC r) (uC r ^ a1) (uC r ^ a2) (uC r ^ a3) (uC r ^ a4) (uC r ^ b2) (uC r ^ b3))
      a1 a2 a3 a4 b1 b2 b3 ((L : ℤ) + ((b1 + 1 - L).toNat : ℕ)) = 0 := by
    unfold Gq Gb
    rw [hn, FiC_neg (r := r) (n := b1 - (b1 + 1)) (by omega)]; simp
  have T := telescope (Fi := FiC r) (Pn := PnRegC r) (N := (r : ℤ) - 2) hu hd two_ne_zero
    (FiC_step hr) a1 a2 a3 a4 b1 b2 b3 (L : ℤ) (b1 + 1 - L).toNat _ _ _ _ _ _
    (fun z hz _ => PnRegC_step hr _ (by omega) (by omega))
    (fun z _ hz => by omega) (fun z _ hz => by omega) (fun z _ hz => by omega)
    (fun z _ hz => by omega) (fun z _ hz => by omega) (fun z _ hz => by omega)
    (fun z _ hz => by omega) rfl rfl rfl rfl rfl rfl
    (by rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu,
      ← zpow_add₀ hu]; congr 1; omega)
    hQ0 hQ1 hQ2 hDc hG0 hG1
  have tc : ∀ (c1 c2 c3 c4 d1 d2 d3 : ℤ) (k : ℕ),
      tt (Fi := FiC r) (Pn := PnRegC r) c1 c2 c3 c4 d1 d2 d3 ((L : ℤ) + k) =
        ((regTerm r c1 c2 c3 c4 d1 d2 d3 (L + k) : ℝ) : ℂ) := by
    intro c1 c2 c3 c4 d1 d2 d3 k
    have := tt_eq_regTerm r c1 c2 c3 c4 d1 d2 d3 (L + k)
    push_cast at this
    exact this
  simp only [tc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at T
  unfold rcR
  rw [e0, e1, e2]
  push_cast
  linear_combination T

/-! ## The recurrence coefficients under the reflection -/

section Coef
variable {K : Type*} [Field K]

/-- Six of the recurrence coefficients depend on `α₂, α₃, β₂, β₃` only through their differences, so
multiplying the four variables by one `t` leaves them unchanged. -/
lemma recCoef_scale {u p1 p2 p3 p4 q2 q3 t : K} (h0 : u ≠ 0) (h1 : p1 ≠ 0) (h2 : p2 ≠ 0)
    (h3 : p3 ≠ 0) (h4 : p4 ≠ 0) (h5 : q2 ≠ 0) (h6 : q3 ≠ 0) (ht : t ≠ 0) (P : Poly)
    (hP : P = fNa ∨ P = fNc ∨ P = fbn ∨ P = fQ0 ∨ P = fQ1 ∨ P = fQ2) :
    recCoef P u p1 (p2 * t) (p3 * t) p4 (q2 * t) (q3 * t) = recCoef P u p1 p2 p3 p4 q2 q3 := by
  have h2' := mul_ne_zero h2 ht
  have h3' := mul_ne_zero h3 ht
  have h5' := mul_ne_zero h5 ht
  have h6' := mul_ne_zero h6 ht
  unfold recCoef
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [eval_fNa h0 h1 h2' h3' h4 h5' h6' one_ne_zero, eval_fNa h0 h1 h2 h3 h4 h5 h6 one_ne_zero]
    field_simp
  · rw [eval_fNc h0 h1 h2' h3' h4 h5' h6' one_ne_zero, eval_fNc h0 h1 h2 h3 h4 h5 h6 one_ne_zero]
    field_simp
  · rw [eval_fbn h0 h1 h2' h3' h4 h5' h6' one_ne_zero, eval_fbn h0 h1 h2 h3 h4 h5 h6 one_ne_zero]
    field_simp
  · rw [eval_fQ0 h0 h1 h2' h3' h4 h5' h6' one_ne_zero, eval_fQ0 h0 h1 h2 h3 h4 h5 h6 one_ne_zero]
    field_simp
  · rw [eval_fQ1 h0 h1 h2' h3' h4 h5' h6' one_ne_zero, eval_fQ1 h0 h1 h2 h3 h4 h5 h6 one_ne_zero]
    field_simp
  · rw [eval_fQ2 h0 h1 h2' h3' h4 h5' h6' one_ne_zero, eval_fQ2 h0 h1 h2 h3 h4 h5 h6 one_ne_zero]
    field_simp

end Coef

lemma uC_zpow_two_mul (r : ℕ) (hr : 2 ≤ r) (k : ℤ) : uC r ^ (2 * r * k) = 1 := by
  have h := uC_pow_self hr
  rw [show (2 * r * k : ℤ) = (r : ℤ) * 2 * k by ring, zpow_mul, zpow_mul, zpow_natCast, h]
  norm_num

lemma rcR_shift (r : ℕ) (a1 a2 a3 a4 b2 b3 δ : ℤ) (P : Poly)
    (hP : P = fNa ∨ P = fNc ∨ P = fbn ∨ P = fQ0 ∨ P = fQ1 ∨ P = fQ2) :
    rcR r a1 (a2 + δ) (a3 + δ) a4 (b2 + δ) (b3 + δ) P = rcR r a1 a2 a3 a4 b2 b3 P := by
  have hu := uC_ne_zero r
  have z : ∀ n : ℤ, uC r ^ n ≠ 0 := fun n => zpow_ne_zero _ hu
  unfold rcR
  simp only [zpow_add₀ hu]
  exact recCoef_scale hu (z _) (z _) (z _) (z _) (z _) (z _) (z δ) P hP

/-- The coefficient `fCq = ck(u^{1-α₁-α₄+β₂+β₃})` is unchanged when the exponent `n` goes to
`n + 2δ` with `n + δ = r` (since `u^{2r} = 1`). -/
lemma rcR_shift_fCq {r : ℕ} (hr : 2 ≤ r) (a1 a2 a3 a4 b2 b3 δ : ℤ)
    (hδ : (1 - a1 - a4 + b2 + b3) + δ = r) :
    rcR r a1 (a2 + δ) (a3 + δ) a4 (b2 + δ) (b3 + δ) fCq = rcR r a1 a2 a3 a4 b2 b3 fCq := by
  have hu := uC_ne_zero r
  have z : ∀ n : ℤ, uC r ^ n ≠ 0 := fun n => zpow_ne_zero _ hu
  unfold rcR recCoef
  rw [eval_fCq hu (z _) (z _) (z _) (z _) (z _) (z _) one_ne_zero,
    eval_fCq hu (z _) (z _) (z _) (z _) (z _) (z _) one_ne_zero]
  have e : ∀ c2 c3 : ℤ, uC r * (uC r ^ a1)⁻¹ * (uC r ^ a4)⁻¹ * uC r ^ c2 * uC r ^ c3 =
      uC r ^ (1 - a1 - a4 + c2 + c3) := by
    intro c2 c3
    rw [show (1 - a1 - a4 + c2 + c3 : ℤ) = 1 + (-a1) + (-a4) + c2 + c3 by ring,
      zpow_add₀ hu, zpow_add₀ hu, zpow_add₀ hu, zpow_add₀ hu, zpow_neg, zpow_neg, zpow_one]
  rw [e, e]
  have h2 : uC r ^ (1 - a1 - a4 + (b2 + δ) + (b3 + δ)) = (uC r ^ (1 - a1 - a4 + b2 + b3))⁻¹ := by
    rw [← zpow_neg, show (1 - a1 - a4 + (b2 + δ) + (b3 + δ)) =
      -(1 - a1 - a4 + b2 + b3) + 2 * r * 1 by omega, zpow_add₀ hu, uC_zpow_two_mul r hr, mul_one]
  rw [h2]
  unfold ck
  rw [inv_inv]; ring

/-! ## The reflection -/

/-- `1/[n]!` for a natural `n`. -/
lemma invQFact_nat (r n : ℕ) : invQFact r (n : ℤ) = (qfact r n)⁻¹ := by
  simp [invQFact]

lemma inv_qfact_reflect {r : ℕ} (hr : 2 ≤ r) {k : ℕ} (hk : k ≤ r - 1) :
    (qfact r (r - 1 - k))⁻¹ = qfact r k / qfact r (r - 1) := by
  have h := qfact_reflect hr hk
  have h1 : qfact r (r - 1 - k) ≠ 0 := qfact_ne_zero hr (by omega)
  have h2 : qfact r k ≠ 0 := qfact_ne_zero hr (by omega)
  rw [← h]; field_simp

/-- The sign and the regularised factorial above the level: `(-1)^z qfactReg(z+1)`. -/
lemma sign_PnReg {r : ℕ} (hr : 2 ≤ r) {z : ℕ} (hz : r - 1 ≤ z) :
    (-1 : ℝ) ^ z * PnReg r ((z : ℤ) + 1) = (-1) ^ (r + 1) * qfact r (r - 1) * qfact r (z + 1 - r) := by
  have h0 : (0 : ℤ) ≤ (z : ℤ) + 1 := by omega
  simp only [PnReg, h0, ite_true]
  rw [show ((z : ℤ) + 1).toNat = z + 1 by omega, qfactReg_of_ge hr (by omega)]
  have : (-1 : ℝ) ^ z * (-1) ^ (z + 1 - r) = (-1) ^ (r + 1) := by
    rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := r + 1)]
    congr 1; omega
  linear_combination qfact r (r - 1) * qfact r (z + 1 - r) * this

/-- The hypotheses of the reflection: every `βⱼ - αᵢ ≥ 0` (the four triads of the 6j symbol are
triangles), the triads `α₁, α₄` are within the level `r - 2`, and `α₂, α₃` are above it. -/
structure ReflHyp (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) : Prop where
  bal : b1 + b2 + b3 = a1 + a2 + a3 + a4
  h11 : a1 ≤ b1
  h12 : a2 ≤ b1
  h13 : a3 ≤ b1
  h14 : a4 ≤ b1
  h21 : a1 ≤ b2
  h22 : a2 ≤ b2
  h23 : a3 ≤ b2
  h24 : a4 ≤ b2
  h31 : a1 ≤ b3
  h32 : a2 ≤ b3
  h33 : a3 ≤ b3
  h34 : a4 ≤ b3
  lo1 : a1 ≤ (r : ℤ) - 2
  lo4 : a4 ≤ (r : ℤ) - 2
  hi2 : (r : ℤ) - 1 ≤ a2
  hi3 : (r : ℤ) - 1 ≤ a3

/-- The shift `δ = r - 1 - x` of the reflection `x ↦ 2r - 2 - x`, where `x = α₂ + α₃ - β₁`. -/
def rd (r : ℕ) (a2 a3 b1 : ℤ) : ℤ := (r : ℤ) - 1 - (a2 + a3 - b1)

/-- The ratio of q-factorials of the reflection. -/
noncomputable def regFac (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) : ℝ :=
  qfact r (b2 - a1).toNat * qfact r (b3 - a4).toNat * qfact r (b1 - a3).toNat *
    qfact r (b2 - a4).toNat * qfact r (b3 - a1).toNat * qfact r (b1 - a2).toNat /
    (qfact r (r - 1) ^ 2 * qfact r (a2 - r + 1).toNat * qfact r (a3 - r + 1).toNat)

/-- The statement of the reflection for one tuple. -/
def ReflAt (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) : Prop :=
  SRg r a1 (a2 + rd r a2 a3 b1) (a3 + rd r a2 a3 b1) a4 b1 (b2 + rd r a2 a3 b1) (b3 + rd r a2 a3 b1) =
    regFac r a1 a2 a3 a4 b1 b2 b3 * SRg r a1 a2 a3 a4 b1 b2 b3

lemma SRg_swap23 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) :
    SRg r a1 a3 a2 a4 b1 b2 b3 = SRg r a1 a2 a3 a4 b1 b2 b3 := by
  unfold SRg regTerm; refine sum_congr rfl fun z _ => ?_; ring

lemma SRg_swapb (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) :
    SRg r a1 a2 a3 a4 b1 b3 b2 = SRg r a1 a2 a3 a4 b1 b2 b3 := by
  unfold SRg regTerm; refine sum_congr rfl fun z _ => ?_; ring

lemma ReflAt_swap23 {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} (h : ReflAt r a1 a3 a2 a4 b1 b2 b3) :
    ReflAt r a1 a2 a3 a4 b1 b2 b3 := by
  unfold ReflAt at *
  rw [show rd r a3 a2 b1 = rd r a2 a3 b1 by unfold rd; ring,
    SRg_swap23 r a1 (a2 + rd r a2 a3 b1), SRg_swap23 r a1 a2 a3] at h
  rw [h]; congr 1; unfold regFac; ring

lemma ReflAt_swapb {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} (h : ReflAt r a1 a2 a3 a4 b1 b3 b2) :
    ReflAt r a1 a2 a3 a4 b1 b2 b3 := by
  unfold ReflAt at *
  rw [SRg_swapb r a1 _ _ a4 b1 (b2 + rd r a2 a3 b1), SRg_swapb r a1 a2 a3 a4 b1 b2] at h
  rw [h]; congr 1; unfold regFac; ring

lemma ReflHyp.swap23 {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} (H : ReflHyp r a1 a2 a3 a4 b1 b2 b3) :
    ReflHyp r a1 a3 a2 a4 b1 b2 b3 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := H
  constructor <;> omega

lemma ReflHyp.swapb {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} (H : ReflHyp r a1 a2 a3 a4 b1 b2 b3) :
    ReflHyp r a1 a2 a3 a4 b1 b3 b2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := H
  constructor <;> omega

/-- **Base case**: a box of one point, `β₂ = α₂`. -/
lemma reflAt_base {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 : ℤ}
    (H : ReflHyp r a1 a2 a3 a4 b1 b2 b3) (h0 : b2 = a2) : ReflAt r a1 a2 a3 a4 b1 b2 b3 := by
  obtain ⟨hbal, h11, h12, h13, h14, h21, h22, h23, h24, h31, h32, h33, h34, lo1, lo4, hi2, hi3⟩ := H
  unfold ReflAt
  set δ := rd r a2 a3 b1 with hδ
  unfold rd at hδ
  obtain ⟨z0, hz0⟩ : ∃ z0 : ℕ, (z0 : ℤ) = a2 := ⟨a2.toNat, by omega⟩
  obtain ⟨z1, hz1⟩ : ∃ z1 : ℕ, (z1 : ℤ) = a2 + δ := ⟨(a2 + δ).toNat, by omega⟩
  rw [SRg_eq_single z1 (by omega) (by omega), SRg_eq_single z0 (by omega) (by omega)]
  unfold regTerm
  rw [sign_PnReg hr (by omega), sign_PnReg hr (by omega)]
  -- the natural numbers that occur
  obtain ⟨K1, hK1⟩ : ∃ k : ℕ, (k : ℤ) = b3 - a4 := ⟨(b3 - a4).toNat, by omega⟩
  obtain ⟨K2, hK2⟩ : ∃ k : ℕ, (k : ℤ) = b3 - a1 := ⟨(b3 - a1).toNat, by omega⟩
  obtain ⟨M, hM⟩ : ∃ k : ℕ, (k : ℤ) = a3 - r + 1 := ⟨(a3 - r + 1).toNat, by omega⟩
  obtain ⟨E, hE⟩ : ∃ k : ℕ, (k : ℤ) = a2 - a3 := ⟨(a2 - a3).toNat, by omega⟩
  obtain ⟨F, hF⟩ : ∃ k : ℕ, (k : ℤ) = b3 - a2 := ⟨(b3 - a2).toNat, by omega⟩
  obtain ⟨A, hA⟩ : ∃ k : ℕ, (k : ℤ) = a2 - a1 := ⟨(a2 - a1).toNat, by omega⟩
  obtain ⟨B, hB⟩ : ∃ k : ℕ, (k : ℤ) = a2 - a4 := ⟨(a2 - a4).toNat, by omega⟩
  obtain ⟨C, hC⟩ : ∃ k : ℕ, (k : ℤ) = b1 - a2 := ⟨(b1 - a2).toNat, by omega⟩
  rw [show (z1 : ℤ) - a1 = ((r - 1 - K1 : ℕ) : ℤ) by omega,
    show (z1 : ℤ) - (a2 + δ) = ((0 : ℕ) : ℤ) by omega,
    show (z1 : ℤ) - (a3 + δ) = ((E : ℕ) : ℤ) by omega,
    show (z1 : ℤ) - a4 = ((r - 1 - K2 : ℕ) : ℤ) by omega,
    show b1 - (z1 : ℤ) = ((M : ℕ) : ℤ) by omega,
    show b2 + δ - (z1 : ℤ) = ((0 : ℕ) : ℤ) by omega,
    show b3 + δ - (z1 : ℤ) = ((F : ℕ) : ℤ) by omega,
    show (z0 : ℤ) - a1 = ((A : ℕ) : ℤ) by omega,
    show (z0 : ℤ) - a2 = ((0 : ℕ) : ℤ) by omega,
    show (z0 : ℤ) - a3 = ((E : ℕ) : ℤ) by omega,
    show (z0 : ℤ) - a4 = ((B : ℕ) : ℤ) by omega,
    show b1 - (z0 : ℤ) = ((C : ℕ) : ℤ) by omega,
    show b2 - (z0 : ℤ) = ((0 : ℕ) : ℤ) by omega,
    show b3 - (z0 : ℤ) = ((F : ℕ) : ℤ) by omega]
  simp only [invQFact_nat]
  rw [inv_qfact_reflect hr (by omega), inv_qfact_reflect hr (by omega)]
  unfold regFac
  rw [show (b2 - a1).toNat = A by omega, show (b3 - a4).toNat = K1 by omega,
    show (b1 - a3).toNat = z1 + 1 - r by omega, show (b2 - a4).toNat = B by omega,
    show (b3 - a1).toNat = K2 by omega, show (b1 - a2).toNat = C by omega,
    show (a2 - r + 1).toNat = z0 + 1 - r by omega, show (a3 - r + 1).toNat = M by omega]
  have q : ∀ n : ℕ, n < r → qfact r n ≠ 0 := fun n hn => qfact_ne_zero hr hn
  have := q A (by omega); have := q B (by omega); have := q C (by omega); have := q E (by omega)
  have := q F (by omega); have := q M (by omega); have := q K1 (by omega); have := q K2 (by omega)
  have := q (r - 1) (by omega); have := q (z0 + 1 - r) (by omega); have := q (z1 + 1 - r) (by omega)
  have q0 : qfact r 0 = 1 := by simp [qfact]
  simp only [q0, inv_one, mul_one]
  field_simp

/-! ## The degenerate base: `a = d`, `b = c`, `p = 2` -/

lemma invQFact_one {r : ℕ} (hr : 2 ≤ r) : invQFact r 1 = 1 := by
  have := invQFact_nat r 1
  simp only [Nat.cast_one] at this
  rw [this]; simp [qfact, qnum_one hr]

lemma invQFact_zero (r : ℕ) : invQFact r 0 = 1 := by
  have := invQFact_nat r 0
  simp only [Nat.cast_zero] at this
  rw [this]; simp [qfact]

/-- A box inside `{z₀, z₀ + 1}` (`α₂ = α₃ = z₀`, `β₂ = β₃ = z₀ + 1`): the sum in closed form, a common
factor times the bracket `[z₀+1-α₁][z₀+1-α₄] - [z₀+2][β₁-z₀]`. -/
lemma SRg_pair {r : ℕ} (hr : 2 ≤ r) (a1 a4 b1 : ℤ) (z0 : ℕ) (hz : (r : ℤ) - 1 ≤ z0)
    (h1 : (z0 : ℤ) - a1 ≤ (r : ℤ) - 2) (h4 : (z0 : ℤ) - a4 ≤ (r : ℤ) - 2)
    (hb : b1 - z0 - 1 ≤ (r : ℤ) - 2) :
    SRg r a1 z0 z0 a4 b1 ((z0 : ℤ) + 1) ((z0 : ℤ) + 1) =
      (-1) ^ z0 * PnReg r ((z0 : ℤ) + 1) *
        (invQFact r ((z0 : ℤ) + 1 - a1) * invQFact r ((z0 : ℤ) + 1 - a4) * invQFact r (b1 - z0)) *
        (qZ r ((z0 : ℤ) + 1 - a1) * qZ r ((z0 : ℤ) + 1 - a4) - qZ r ((z0 : ℤ) + 2) * qZ r (b1 - z0)) := by
  have hsum : SRg r a1 z0 z0 a4 b1 ((z0 : ℤ) + 1) ((z0 : ℤ) + 1) =
      regTerm r a1 z0 z0 a4 b1 ((z0 : ℤ) + 1) ((z0 : ℤ) + 1) z0 +
        regTerm r a1 z0 z0 a4 b1 ((z0 : ℤ) + 1) ((z0 : ℤ) + 1) (z0 + 1) := by
    unfold SRg
    refine sum_eq_add z0 (z0 + 1) (by omega) (fun c _ hc => ?_) (fun h => ?_) (fun h => ?_)
    · rcases lt_or_gt_of_ne hc.1 with h | h
      · exact regTerm_zero_of_lt (by omega)
      · exact regTerm_zero_of_gt (by omega)
    · exact regTerm_zero_of_gt (by simp only [mem_range] at h; omega)
    · exact regTerm_zero_of_gt (by simp only [mem_range] at h; omega)
  rw [hsum]
  unfold regTerm
  push_cast
  rw [show (z0 : ℤ) - z0 = 0 by ring, show (z0 : ℤ) + 1 - z0 = 1 by ring,
    show (z0 : ℤ) + 1 - ((z0 : ℤ) + 1) = 0 by ring, invQFact_zero, invQFact_one hr,
    show (z0 : ℤ) + 1 + 1 = (z0 : ℤ) + 1 + 1 from rfl,
    PnReg_step ((z0 : ℤ) + 1) (by omega) (by omega),
    invQFact_step hr ((z0 : ℤ) - a1) h1, invQFact_step hr ((z0 : ℤ) - a4) h4,
    invQFact_step hr (b1 - ((z0 : ℤ) + 1)) (by omega)]
  rw [show (z0 : ℤ) - a1 + 1 = (z0 : ℤ) + 1 - a1 by ring, show (z0 : ℤ) - a4 + 1 = (z0 : ℤ) + 1 - a4 by ring,
    show b1 - ((z0 : ℤ) + 1) + 1 = b1 - z0 by ring, show (z0 : ℤ) + 1 + 1 = (z0 : ℤ) + 2 by ring]
  ring

/-- The bracket of `SRg_pair` is invariant: `[m₁][n₁] - [m₂][n₂]` depends on `m₁ - n₁`, `m₂ + n₂`, and
on `m₁ + n₁`, `m₂ - n₂` only through `cos`, which is unchanged under `y ↦ 2r - y`. -/
lemma bracket_reflect {r : ℕ} (hr : 2 ≤ r) (m1 n1 m2 n2 m1' n1' m2' n2' : ℤ)
    (h1 : m1 - n1 = m1' - n1') (h2 : m2 + n2 = m2' + n2') (h3 : m1 + n1 + (m2' - n2') = 2 * r)
    (h4 : m2 - n2 + (m1' + n1') = 2 * r) :
    qZ r m1 * qZ r n1 - qZ r m2 * qZ r n2 = qZ r m1' * qZ r n1' - qZ r m2' * qZ r n2' := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have key : ∀ m n : ℤ, qZ r m * qZ r n =
      (cos (((m - n : ℤ) : ℝ) * π / r) - cos (((m + n : ℤ) : ℝ) * π / r)) / 2 / sin (π / r) ^ 2 := by
    intro m n
    unfold qZ
    rw [div_mul_div_comm, sin_mul_sin', ← sq]
    push_cast
    ring_nf
  have refl : ∀ y : ℤ, cos ((((2 * r - y : ℤ)) : ℝ) * π / r) = cos ((y : ℝ) * π / r) := by
    intro y
    push_cast
    rw [show (2 * (r : ℝ) - y) * π / r = -((y : ℝ) * π / r) + 2 * π by field_simp; ring,
      cos_add_two_pi, cos_neg]
  rw [key, key, key, key, h1, h2, show m1 + n1 = 2 * r - (m2' - n2') by omega,
    show m1' + n1' = 2 * r - (m2 - n2) by omega, refl, refl]
  ring

/-- The common factor of `SRg_pair` under the reflection. -/
lemma pair_prefactor {r : ℕ} (hr : 2 ≤ r) {a1 a4 b1 : ℤ} {z0 z1 : ℕ}
    (hbal : b1 = a1 + a4 - 2) (hz1 : (z1 : ℤ) = r - 1 - (2 * z0 - b1) + z0)
    (hlo1 : a1 ≤ (r : ℤ) - 2) (hlo4 : a4 ≤ (r : ℤ) - 2) (hi : (r : ℤ) - 1 ≤ z0)
    (hA1 : a1 ≤ (z0 : ℤ) + 1) (hA4 : a4 ≤ (z0 : ℤ) + 1) (hB : (z0 : ℤ) ≤ b1) :
    (-1) ^ z1 * PnReg r ((z1 : ℤ) + 1) *
        (invQFact r ((z1 : ℤ) + 1 - a1) * invQFact r ((z1 : ℤ) + 1 - a4) * invQFact r (b1 - z1)) =
      regFac r a1 z0 z0 a4 b1 ((z0 : ℤ) + 1) ((z0 : ℤ) + 1) *
        ((-1) ^ z0 * PnReg r ((z0 : ℤ) + 1) *
          (invQFact r ((z0 : ℤ) + 1 - a1) * invQFact r ((z0 : ℤ) + 1 - a4) * invQFact r (b1 - z0))) := by
  rw [sign_PnReg hr (by omega), sign_PnReg hr (by omega)]
  obtain ⟨P1, hP1⟩ : ∃ k : ℕ, (k : ℤ) = z0 + 1 - a1 := ⟨((z0 : ℤ) + 1 - a1).toNat, by omega⟩
  obtain ⟨P4, hP4⟩ : ∃ k : ℕ, (k : ℤ) = z0 + 1 - a4 := ⟨((z0 : ℤ) + 1 - a4).toNat, by omega⟩
  obtain ⟨C, hC⟩ : ∃ k : ℕ, (k : ℤ) = b1 - z0 := ⟨(b1 - z0).toNat, by omega⟩
  obtain ⟨G, hG⟩ : ∃ k : ℕ, (k : ℤ) = z0 + 1 - r := ⟨((z0 : ℤ) + 1 - r).toNat, by omega⟩
  rw [show (z1 : ℤ) + 1 - a1 = ((r - 1 - P4 : ℕ) : ℤ) by omega,
    show (z1 : ℤ) + 1 - a4 = ((r - 1 - P1 : ℕ) : ℤ) by omega,
    show b1 - (z1 : ℤ) = ((G : ℕ) : ℤ) by omega, show (z0 : ℤ) + 1 - a1 = ((P1 : ℕ) : ℤ) by omega,
    show (z0 : ℤ) + 1 - a4 = ((P4 : ℕ) : ℤ) by omega, show b1 - (z0 : ℤ) = ((C : ℕ) : ℤ) by omega]
  simp only [invQFact_nat]
  rw [inv_qfact_reflect hr (by omega), inv_qfact_reflect hr (by omega)]
  unfold regFac
  rw [show ((z0 : ℤ) + 1 - a1).toNat = P1 by omega, show ((z0 : ℤ) + 1 - a4).toNat = P4 by omega,
    show (b1 - (z0 : ℤ)).toNat = C by omega, show ((z0 : ℤ) - r + 1).toNat = G by omega,
    show z1 + 1 - r = C by omega, show z0 + 1 - r = G by omega]
  have q : ∀ n : ℕ, n < r → qfact r n ≠ 0 := fun n hn => qfact_ne_zero hr hn
  have := q P1 (by omega); have := q P4 (by omega); have := q C (by omega); have := q G (by omega)
  have := q (r - 1) (by omega)
  field_simp

/-- **Degenerate base**: all four lower slacks equal `1` (the case `a = d`, `b = c`, `p = 2`, where the
recurrence in `p` from `p = 0` is singular). -/
lemma reflAt_pair {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 : ℤ}
    (H : ReflHyp r a1 a2 a3 a4 b1 b2 b3) (h2 : b2 = a2 + 1) (h3 : b3 = a3 + 1) (h23 : a2 = a3) :
    ReflAt r a1 a2 a3 a4 b1 b2 b3 := by
  obtain ⟨hbal, h11, h12, h13, h14, h21, h22, h23', h24, h31, h32, h33, h34, lo1, lo4, hi2, hi3⟩ := H
  unfold ReflAt
  set δ := rd r a2 a3 b1 with hδ
  unfold rd at hδ
  obtain ⟨z0, hz0⟩ : ∃ z0 : ℕ, (z0 : ℤ) = a2 := ⟨a2.toNat, by omega⟩
  obtain ⟨z1, hz1⟩ : ∃ z1 : ℕ, (z1 : ℤ) = a2 + δ := ⟨(a2 + δ).toNat, by omega⟩
  subst h2 h3 h23
  rw [show a2 + 1 + δ = (z1 : ℤ) + 1 by omega, show a2 + δ = (z1 : ℤ) by omega,
    show a2 + 1 = (z0 : ℤ) + 1 by omega, ← hz0]
  rw [SRg_pair hr a1 a4 b1 z1 (by omega) (by omega) (by omega) (by omega),
    SRg_pair hr a1 a4 b1 z0 (by omega) (by omega) (by omega) (by omega)]
  have hP := pair_prefactor hr (a1 := a1) (a4 := a4) (b1 := b1) (z0 := z0) (z1 := z1) (by omega)
    (by omega) lo1 lo4 (by omega) (by omega) (by omega) (by omega)
  have hK := bracket_reflect hr ((z0 : ℤ) + 1 - a1) ((z0 : ℤ) + 1 - a4) ((z0 : ℤ) + 2) (b1 - z0)
    ((z1 : ℤ) + 1 - a1) ((z1 : ℤ) + 1 - a4) ((z1 : ℤ) + 2) (b1 - z1) (by ring) (by ring) (by omega)
    (by omega)
  rw [hP, ← hK]
  ring

/-! ## The reflection for every tuple, by the recurrence in `p` -/

lemma not_dvd_of_pos_lt {r : ℕ} {m : ℤ} (h0 : 0 < m) (h1 : m < r) : ¬ (r : ℤ) ∣ m := by
  intro h; have := Int.le_of_dvd h0 h; omega

lemma mono_pinv (r : ℕ) (a b : ℤ) : uC r * (uC r ^ a)⁻¹ * uC r ^ b = uC r ^ (1 - a + b) := by
  have hu := uC_ne_zero r
  rw [show (1 - a + b : ℤ) = 1 + (-a) + b by ring, zpow_add₀ hu, zpow_add₀ hu, zpow_neg, zpow_one]

lemma rcR_fNa_ne {r : ℕ} (hr : 2 ≤ r) (a1 a2 a3 a4 b2 b3 : ℤ)
    (h : ∀ m ∈ ({1 - a3 + b3, 1 - a2 + b2, 1 - a3 + b2, 1 - a2 + b3} : Finset ℤ), 0 < m ∧ m < r) :
    rcR r a1 a2 a3 a4 b2 b3 fNa ≠ 0 := by
  have hu := uC_ne_zero r
  have z : ∀ n : ℤ, uC r ^ n ≠ 0 := fun n => zpow_ne_zero _ hu
  unfold rcR recCoef
  rw [eval_fNa hu (z _) (z _) (z _) (z _) (z _) (z _) one_ne_zero]
  simp only [mono_pinv]
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, i⟩⟩ := h
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
    exact bk_uC_ne hr (not_dvd_of_pos_lt (by assumption) (by assumption))

lemma regFac_shift (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 t : ℤ) :
    regFac r (a1 - t) a2 a3 (a4 - t) b1 (b2 - t) (b3 - t) = regFac r a1 a2 a3 a4 b1 b2 b3 := by
  unfold regFac
  rw [show b2 - t - (a1 - t) = b2 - a1 by ring, show b3 - t - (a4 - t) = b3 - a4 by ring,
    show b2 - t - (a4 - t) = b2 - a4 by ring, show b3 - t - (a1 - t) = b3 - a1 by ring]

/-- **The reflection of the regularised q-Racah sum**, for every tuple satisfying `ReflHyp`: by strong
induction on the smallest lower slack `n` (the distance `(p - p_min)/2` of the third-column colour
from its least value), the recurrence of `reg_recurrence` in `p` having the same coefficients for
`x` and `2r - 2 - x`. -/
theorem reflAt_of_slack {r : ℕ} (hr : 2 ≤ r) : ∀ (n : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ),
    ReflHyp r a1 a2 a3 a4 b1 b2 b3 →
    ((n : ℤ) ≤ b2 - a2 ∧ (n : ℤ) ≤ b3 - a3 ∧ (n : ℤ) ≤ b2 - a3 ∧ (n : ℤ) ≤ b3 - a2) →
    (b2 - a2 = n ∨ b3 - a3 = n ∨ b2 - a3 = n ∨ b3 - a2 = n) →
    ReflAt r a1 a2 a3 a4 b1 b2 b3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a1 a2 a3 a4 b1 b2 b3 H hn hn'
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.cast_zero, sub_eq_zero] at hn'
    rcases hn' with h | h | h | h
    · exact reflAt_base hr H h
    · exact ReflAt_swapb (ReflAt_swap23 (reflAt_base hr H.swapb.swap23 h))
    · exact ReflAt_swap23 (reflAt_base hr H.swap23 h)
    · exact ReflAt_swapb (reflAt_base hr H.swapb h)
  by_cases hdeg : b2 = a2 + 1 ∧ b3 = a3 + 1 ∧ a2 = a3
  · exact reflAt_pair hr H hdeg.1 hdeg.2.1 hdeg.2.2
  have H' := H
  obtain ⟨hbal, h11, h12, h13, h14, h21, h22, h23, h24, h31, h32, h33, h34, lo1, lo4, hi2, hi3⟩ := H'
  obtain ⟨s1, s2, s3, s4⟩ := hn
  have hp3 : 3 ≤ a1 + a4 - b1 := by omega
  have hrd : rd r a2 a3 b1 = (r : ℤ) - 1 - (a2 + a3 - b1) := rfl
  set δ := rd r a2 a3 b1 with hδ
  unfold rd at hδ
  -- the centre `p - 2` and the point `p - 4`
  have Hc : ReflHyp r (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) := by constructor <;> omega
  have IHc := ih (n - 1) (by omega) _ _ _ _ _ _ _ Hc (by omega) (by omega)
  have IHm : ReflAt r (a1 - 2) a2 a3 (a4 - 2) b1 (b2 - 2) (b3 - 2) := by
    by_cases hn2 : 2 ≤ n
    · exact ih (n - 2) (by omega) _ _ _ _ _ _ _ (by constructor <;> omega) (by omega) (by omega)
    · unfold ReflAt
      rw [SRg_eq_zero, SRg_eq_zero, mul_zero]
      · rcases hn' with h | h | h | h
        · exact ⟨a2, by simp, b2 - 2, by simp, by omega⟩
        · exact ⟨a3, by simp, b3 - 2, by simp, by omega⟩
        · exact ⟨a3, by simp, b2 - 2, by simp, by omega⟩
        · exact ⟨a2, by simp, b3 - 2, by simp, by omega⟩
      · rcases hn' with h | h | h | h
        · exact ⟨a2 + rd r a2 a3 b1, by simp, b2 - 2 + rd r a2 a3 b1, by simp, by omega⟩
        · exact ⟨a3 + rd r a2 a3 b1, by simp, b3 - 2 + rd r a2 a3 b1, by simp, by omega⟩
        · exact ⟨a3 + rd r a2 a3 b1, by simp, b2 - 2 + rd r a2 a3 b1, by simp, by omega⟩
        · exact ⟨a2 + rd r a2 a3 b1, by simp, b3 - 2 + rd r a2 a3 b1, by simp, by omega⟩
  unfold ReflAt at IHc IHm ⊢
  rw [show rd r a2 a3 b1 = δ from rfl] at IHc IHm ⊢
  rw [regFac_shift r a1 a2 a3 a4 b1 b2 b3 1] at IHc
  rw [regFac_shift r a1 a2 a3 a4 b1 b2 b3 2] at IHm
  -- the start of the box for both tuples
  obtain ⟨L, hL⟩ : ∃ L : ℕ, ((L : ℤ) = a2 ∨ (L : ℤ) = a3) ∧ a2 ≤ L ∧ a3 ≤ L := by
    rcases le_total a2 a3 with h | h
    · exact ⟨a3.toNat, by omega, by omega, by omega⟩
    · exact ⟨a2.toNat, by omega, by omega, by omega⟩
  obtain ⟨L', hL'⟩ : ∃ L : ℕ, ((L : ℤ) = a2 + δ ∨ (L : ℤ) = a3 + δ) ∧ a2 + δ ≤ L ∧ a3 + δ ≤ L := by
    rcases le_total a2 a3 with h | h
    · exact ⟨(a3 + δ).toNat, by omega, by omega, by omega⟩
    · exact ⟨(a2 + δ).toNat, by omega, by omega, by omega⟩
  have hD : ∀ k : ℤ, 0 ≤ k → k ≤ 2 → ¬ (r : ℤ) ∣ (b2 - 1) + (b3 - 1) - a2 - a3 + k :=
    fun k h0 h2 => not_dvd_of_pos_lt (by omega) (by omega)
  have hD' : ∀ k : ℤ, 0 ≤ k → k ≤ 2 →
      ¬ (r : ℤ) ∣ (b2 - 1 + δ) + (b3 - 1 + δ) - (a2 + δ) - (a3 + δ) + k :=
    fun k h0 h2 => not_dvd_of_pos_lt (by omega) (by omega)
  have recS := reg_recurrence hr (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) (by omega) L
    (by omega) (by omega) hL.1 hL.2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hD
  have recT := reg_recurrence hr (a1 - 1) (a2 + δ) (a3 + δ) (a4 - 1) b1 (b2 - 1 + δ) (b3 - 1 + δ)
    (by omega) L' (by omega) (by omega) hL'.1 hL'.2 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hD'
  have cs : ∀ P : Poly, (P = fNa ∨ P = fNc ∨ P = fbn ∨ P = fQ0 ∨ P = fQ1 ∨ P = fQ2) →
      rcR r (a1 - 1) (a2 + δ) (a3 + δ) (a4 - 1) (b2 - 1 + δ) (b3 - 1 + δ) P =
        rcR r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) P :=
    fun P hP => rcR_shift r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) δ P hP
  rw [cs fNa (by simp), cs fNc (by simp), cs fbn (by simp), cs fQ0 (by simp), cs fQ1 (by simp),
    cs fQ2 (by simp), rcR_shift_fCq hr (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) δ (by omega)] at recT
  simp only [sub_add_cancel] at recS recT
  rw [show b2 - 1 + δ + 1 = b2 + δ by ring, show b3 - 1 + δ + 1 = b3 + δ by ring,
    show a1 - 1 - 1 = a1 - 2 by ring, show a4 - 1 - 1 = a4 - 2 by ring,
    show b2 - 1 + δ - 1 = b2 - 2 + δ by ring, show b3 - 1 + δ - 1 = b3 - 2 + δ by ring] at recT
  rw [show a1 - 1 - 1 = a1 - 2 by ring, show a4 - 1 - 1 = a4 - 2 by ring,
    show b2 - 1 - 1 = b2 - 2 by ring, show b3 - 1 - 1 = b3 - 2 by ring] at recS
  rw [show b2 - 1 + δ = b2 + δ - 1 by ring, show b3 - 1 + δ = b3 + δ - 1 by ring] at recT
  rw [show b2 - 2 + δ = b2 + δ - 2 by ring, show b3 - 2 + δ = b3 + δ - 2 by ring] at recT
  rw [show b2 - 1 + δ = b2 + δ - 1 by ring, show b3 - 1 + δ = b3 + δ - 1 by ring] at IHc
  rw [show b2 - 2 + δ = b2 + δ - 2 by ring, show b3 - 2 + δ = b3 + δ - 2 by ring] at IHm
  rw [IHc, IHm] at recT
  have hc : 2 * (rcR r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) fNa / 2 /
      (rcR r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) fQ1 *
        rcR r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) fQ2)) ≠ 0 := by
    obtain ⟨_, hQ1, hQ2, _⟩ := nonvanishing_root hr (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) hD
    have hNa := rcR_fNa_ne hr (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) (by
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]; omega)
    unfold rcR at hNa ⊢
    exact mul_ne_zero two_ne_zero (div_ne_zero (div_ne_zero hNa two_ne_zero) (mul_ne_zero hQ1 hQ2))
  have key := mul_eq_zero.mp (show (2 * (rcR r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) fNa / 2 /
      (rcR r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) fQ1 *
        rcR r (a1 - 1) a2 a3 (a4 - 1) (b2 - 1) (b3 - 1) fQ2))) *
      ((SRg r a1 (a2 + δ) (a3 + δ) a4 b1 (b2 + δ) (b3 + δ) : ℂ) -
        (regFac r a1 a2 a3 a4 b1 b2 b3 : ℂ) * (SRg r a1 a2 a3 a4 b1 b2 b3 : ℂ)) = 0 by
    push_cast at recT
    linear_combination recT - (regFac r a1 a2 a3 a4 b1 b2 b3 : ℂ) * recS)
  rcases key with h | h
  · exact absurd h hc
  · exact_mod_cast sub_eq_zero.mp h

/-- **The reflection symmetry of the regularised q-Racah sum.** Under `ReflHyp` (the four triads
of `{a b x; c d p}` are triangles, those through `p` within the level and those through `x` above
it), replacing `x` by `2r - 2 - x` (the shift `δ` of `α₂, α₃, β₂, β₃`) multiplies `SRg` by
`regFac`. -/
theorem SRg_reflect {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 : ℤ}
    (H : ReflHyp r a1 a2 a3 a4 b1 b2 b3) : ReflAt r a1 a2 a3 a4 b1 b2 b3 := by
  have H' := H
  obtain ⟨_, _, _, _, _, _, h22, h23, _, _, h32, h33, _, _, _, _, _⟩ := H'
  rcases le_total (b2 - a2) (b3 - a3) with h | h <;> rcases le_total (b2 - a3) (b3 - a2) with h' | h'
  · rcases le_total (b2 - a2) (b2 - a3) with g | g
    · exact reflAt_of_slack hr (b2 - a2).toNat _ _ _ _ _ _ _ H (by omega) (by omega)
    · exact reflAt_of_slack hr (b2 - a3).toNat _ _ _ _ _ _ _ H (by omega) (by omega)
  · rcases le_total (b2 - a2) (b3 - a2) with g | g
    · exact reflAt_of_slack hr (b2 - a2).toNat _ _ _ _ _ _ _ H (by omega) (by omega)
    · exact reflAt_of_slack hr (b3 - a2).toNat _ _ _ _ _ _ _ H (by omega) (by omega)
  · rcases le_total (b3 - a3) (b2 - a3) with g | g
    · exact reflAt_of_slack hr (b3 - a3).toNat _ _ _ _ _ _ _ H (by omega) (by omega)
    · exact reflAt_of_slack hr (b2 - a3).toNat _ _ _ _ _ _ _ H (by omega) (by omega)
  · rcases le_total (b3 - a3) (b3 - a2) with g | g
    · exact reflAt_of_slack hr (b3 - a3).toNat _ _ _ _ _ _ _ H (by omega) (by omega)
    · exact reflAt_of_slack hr (b3 - a2).toNat _ _ _ _ _ _ _ H (by omega) (by omega)

end Lightlike.TV.Refl

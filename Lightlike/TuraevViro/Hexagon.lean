import Lightlike.TuraevViro.FMatrix

/-!
# The hexagon equation for the spin-1/2 F-matrix

Row G3-201 (QU3), first piece of the hexagon.  At `q = e^{iπ/r}`, `r ≥ 4`, the three quantum 6j symbols of four spin-1/2
lines are `{1 1 0; 1 1 0} = -1/[2]`, `{1 1 0; 1 1 2} = {1 1 2; 1 1 0} = 1/[2]`, `{1 1 2; 1 1 2} = 1/([2][3])` (doubled spins),
so the F-matrix `F^{1 1 1}_1` of `fMat` is `[[-1/[2], √[3]/[2]], [√[3]/[2], 1/[2]]]` on the channels `0, 2`.
-/

namespace Lightlike.TV

open Real Finset Lightlike.Pentagon

lemma qfact_zero' (r : ℕ) : qfact r 0 = 1 := by simp [qfact]
lemma qfact_one' {r : ℕ} (hr : 2 ≤ r) : qfact r 1 = 1 := by
  simp [qfact, qnum, (sin_pi_div_pos hr).ne']
lemma qfact_two' {r : ℕ} (hr : 2 ≤ r) : qfact r 2 = qnum r 2 := by
  have : qfact r 2 = qnum r 1 * qnum r 2 := by simp [qfact, Finset.prod_range_succ]
  rw [this, qnum_one hr, one_mul]

/-- The quantum 6j symbol `{1 1 0; 1 1 0} = -1/[2]` (doubled spins). -/
lemma sixJ_half_00 {r : ℕ} (hr : 4 ≤ r) : qSixJ r 1 1 0 1 1 0 = -1 / qnum r 2 := by
  have h2 : 2 ≤ r := by omega
  have hadm : qAdm r 1 1 0 := by
    unfold qAdm Tri; omega
  unfold qSixJ
  rw [if_pos ⟨hadm, hadm, hadm, hadm⟩]
  simp [qDelta, qRacahSum, qRacahTerm, invQFact, Finset.sum_range_succ, qfact_zero', qfact_one' h2, qfact_two' h2]
  have hq : 0 < qnum r 2 := qnum_pos (by omega) (by omega) (by omega)
  have hs : √(qnum r 2) * √(qnum r 2) = qnum r 2 := Real.mul_self_sqrt hq.le
  have hs0 : √(qnum r 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  field_simp
  nlinarith [hs]

lemma qfact_three' {r : ℕ} (hr : 2 ≤ r) : qfact r 3 = qnum r 2 * qnum r 3 := by
  have : qfact r 3 = qnum r 1 * qnum r 2 * qnum r 3 := by simp [qfact, Finset.prod_range_succ]
  rw [this, qnum_one hr, one_mul]

/-- The quantum 6j symbol `{1 1 0; 1 1 2} = 1/[2]` (doubled spins). -/
lemma sixJ_half_02 {r : ℕ} (hr : 4 ≤ r) : qSixJ r 1 1 0 1 1 2 = 1 / qnum r 2 := by
  have h2 : 2 ≤ r := by omega
  have hadm0 : qAdm r 1 1 0 := by unfold qAdm Tri; omega
  have hadm2 : qAdm r 1 1 2 := by unfold qAdm Tri; omega
  unfold qSixJ
  rw [if_pos ⟨hadm0, hadm2, hadm2, hadm0⟩]
  simp [qDelta, qRacahSum, qRacahTerm, invQFact, Finset.sum_range_succ, qfact_zero', qfact_one' h2, qfact_two' h2, qfact_three' h2]
  have hq2 : 0 < qnum r 2 := qnum_pos (by omega) (by omega) (by omega)
  have hq3 : 0 < qnum r 3 := qnum_pos (by omega) (by omega) (by omega)
  have hX : 0 ≤ (qnum r 3)⁻¹ * (qnum r 2)⁻¹ := by positivity
  have hsX : √((qnum r 3)⁻¹ * (qnum r 2)⁻¹) * √((qnum r 3)⁻¹ * (qnum r 2)⁻¹) = (qnum r 3)⁻¹ * (qnum r 2)⁻¹ :=
    Real.mul_self_sqrt hX
  have hs2 : (√(qnum r 2))⁻¹ * (√(qnum r 2))⁻¹ = (qnum r 2)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hq2.le]
  calc _ = ((√(qnum r 2))⁻¹ * (√(qnum r 2))⁻¹) * (√((qnum r 3)⁻¹ * (qnum r 2)⁻¹) * √((qnum r 3)⁻¹ * (qnum r 2)⁻¹)) *
        (qnum r 2 * qnum r 3) := by ring
    _ = _ := by rw [hs2, hsX]; field_simp

/-- The quantum 6j symbol `{1 1 2; 1 1 2} = 1/([2][3])` (doubled spins). -/
lemma sixJ_half_22 {r : ℕ} (hr : 4 ≤ r) : qSixJ r 1 1 2 1 1 2 = 1 / (qnum r 2 * qnum r 3) := by
  have h2 : 2 ≤ r := by omega
  have hadm2 : qAdm r 1 1 2 := by unfold qAdm Tri; omega
  unfold qSixJ
  rw [if_pos ⟨hadm2, hadm2, hadm2, hadm2⟩]
  simp [qDelta, qRacahSum, qRacahTerm, invQFact, Finset.sum_range_succ, qfact_zero', qfact_one' h2, qfact_two' h2, qfact_three' h2]
  have hq2 : 0 < qnum r 2 := qnum_pos (by omega) (by omega) (by omega)
  have hq3 : 0 < qnum r 3 := qnum_pos (by omega) (by omega) (by omega)
  have hX : 0 ≤ (qnum r 3)⁻¹ * (qnum r 2)⁻¹ := by positivity
  have hsX : √((qnum r 3)⁻¹ * (qnum r 2)⁻¹) * √((qnum r 3)⁻¹ * (qnum r 2)⁻¹) = (qnum r 3)⁻¹ * (qnum r 2)⁻¹ :=
    Real.mul_self_sqrt hX
  have hs2 : (√(qnum r 2))⁻¹ * (√(qnum r 2))⁻¹ = (qnum r 2)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hq2.le]
  calc _ = (√((qnum r 3)⁻¹ * (qnum r 2)⁻¹) * √((qnum r 3)⁻¹ * (qnum r 2)⁻¹)) *
        (√((qnum r 3)⁻¹ * (qnum r 2)⁻¹) * √((qnum r 3)⁻¹ * (qnum r 2)⁻¹)) * (qnum r 2 * qnum r 3) := by ring
    _ = _ := by rw [hsX]; field_simp


lemma sixJ_half_20 {r : ℕ} (hr : 4 ≤ r) : qSixJ r 1 1 2 1 1 0 = 1 / qnum r 2 := by
  have h2 : 2 ≤ r := by omega
  have hadm0 : qAdm r 1 1 0 := by unfold qAdm Tri; omega
  have hadm2 : qAdm r 1 1 2 := by unfold qAdm Tri; omega
  unfold qSixJ
  rw [if_pos ⟨hadm2, hadm0, hadm0, hadm2⟩]
  simp [qDelta, qRacahSum, qRacahTerm, invQFact, Finset.sum_range_succ, qfact_zero', qfact_one' h2, qfact_two' h2, qfact_three' h2]
  have hq2 : 0 < qnum r 2 := qnum_pos (by omega) (by omega) (by omega)
  have hq3 : 0 < qnum r 3 := qnum_pos (by omega) (by omega) (by omega)
  have hX : 0 ≤ (qnum r 3)⁻¹ * (qnum r 2)⁻¹ := by positivity
  have hsX : √((qnum r 3)⁻¹ * (qnum r 2)⁻¹) * √((qnum r 3)⁻¹ * (qnum r 2)⁻¹) = (qnum r 3)⁻¹ * (qnum r 2)⁻¹ :=
    Real.mul_self_sqrt hX
  have hs2 : (√(qnum r 2))⁻¹ * (√(qnum r 2))⁻¹ = (qnum r 2)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hq2.le]
  calc _ = ((√(qnum r 2))⁻¹ * (√(qnum r 2))⁻¹) * (√((qnum r 3)⁻¹ * (qnum r 2)⁻¹) * √((qnum r 3)⁻¹ * (qnum r 2)⁻¹)) *
        (qnum r 2 * qnum r 3) := by ring
    _ = _ := by rw [hs2, hsX]; field_simp

lemma qnum_two {r : ℕ} (hr : 2 ≤ r) : qnum r 2 = 2 * cos (π / r) := by
  have h := (sin_pi_div_pos hr).ne'
  unfold qnum
  rw [show ((2 : ℕ) : ℝ) * π / r = 2 * (π / r) by push_cast; ring, sin_two_mul]
  field_simp

lemma qnum_three {r : ℕ} (hr : 2 ≤ r) : qnum r 3 = qnum r 2 ^ 2 - 1 := by
  have h := (sin_pi_div_pos hr).ne'
  rw [qnum_two hr]
  unfold qnum
  rw [show ((3 : ℕ) : ℝ) * π / r = 3 * (π / r) by push_cast; ring, sin_three_mul]
  have := sin_sq_add_cos_sq (π / r)
  field_simp
  nlinarith [this]

/-- The spin-1/2 F-matrix entry `F^{111}_1[0,0] = -1/[2]`. -/
lemma fMat_half_00 {r : ℕ} (hr : 4 ≤ r) : fMat r 1 1 1 1 0 0 = -1 / qnum r 2 := by
  have h2 : 2 ≤ r := by omega
  unfold fMat
  rw [sixJ_half_00 hr]
  simp [qnum_one h2]

/-- The spin-1/2 F-matrix entry `F^{111}_1[0,2] = √[3]/[2]`. -/
lemma fMat_half_02 {r : ℕ} (hr : 4 ≤ r) : fMat r 1 1 1 1 0 2 = √(qnum r 3) / qnum r 2 := by
  have h2 : 2 ≤ r := by omega
  unfold fMat
  rw [sixJ_half_02 hr]
  simp [qnum_one h2]
  ring

/-- The spin-1/2 F-matrix entry `F^{111}_1[2,0] = √[3]/[2]`. -/
lemma fMat_half_20 {r : ℕ} (hr : 4 ≤ r) : fMat r 1 1 1 1 2 0 = √(qnum r 3) / qnum r 2 := by
  have h2 : 2 ≤ r := by omega
  unfold fMat
  rw [sixJ_half_20 hr]
  simp [qnum_one h2]
  ring

/-- The spin-1/2 F-matrix entry `F^{111}_1[2,2] = 1/[2]`. -/
lemma fMat_half_22 {r : ℕ} (hr : 4 ≤ r) : fMat r 1 1 1 1 2 2 = 1 / qnum r 2 := by
  have h2 : 2 ≤ r := by omega
  have hq2 : 0 < qnum r 2 := qnum_pos h2 (by omega) (by omega)
  have hq3 : 0 < qnum r 3 := qnum_pos h2 (by omega) (by omega)
  unfold fMat
  rw [sixJ_half_22 hr]
  simp
  rw [Real.sqrt_mul_self hq3.le]
  field_simp

/-- **The braiding eigenvalue** `R^{ab}_c = (-1)^((a+b-c)/2) q^{(c(c+2) - a(a+2) - b(b+2))/4}` of `U_q(sl₂)` at
`q = e^{iπ/r}` (doubled spins), with the fourth power of `q` in the exponent kept as an integer. -/
noncomputable def Rbr (r a b c : ℕ) : ℂ :=
  (-1 : ℂ) ^ ((a + b - c) / 2) *
    Complex.exp (Complex.I * π * (((c * (c + 2) : ℕ) : ℤ) - ((a * (a + 2) : ℕ) : ℤ) - ((b * (b + 2) : ℕ) : ℤ)) / (4 * r))

/-- `m = q^{1/2} = e^{iπ/(2r)}`. -/
noncomputable def qHalf (r : ℕ) : ℂ := Complex.exp (Complex.I * π / (2 * r))

lemma qHalf_ne_zero (r : ℕ) : qHalf r ≠ 0 := Complex.exp_ne_zero _

lemma Rbr_110 {r : ℕ} (hr : 2 ≤ r) : Rbr r 1 1 0 = -((qHalf r) ^ 3)⁻¹ := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  unfold Rbr qHalf
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, pow_one]
  congr 2
  push_cast
  field_simp
  ring

lemma Rbr_112 {r : ℕ} (hr : 2 ≤ r) : Rbr r 1 1 2 = qHalf r := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  unfold Rbr qHalf
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, pow_zero, one_mul]
  congr 1
  push_cast
  field_simp
  ring

lemma Rbr_101 {r : ℕ} (hr : 2 ≤ r) : Rbr r 1 0 1 = 1 := by
  unfold Rbr
  simp

lemma Rbr_121 {r : ℕ} (hr : 2 ≤ r) : Rbr r 1 2 1 = -((qHalf r) ^ 4)⁻¹ := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  unfold Rbr qHalf
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, pow_one]
  congr 2
  push_cast
  field_simp
  ring

/-- `[2] = (m⁴ + 1)/m²` for `m = q^{1/2}`. -/
lemma qnum_two_qHalf {r : ℕ} (hr : 2 ≤ r) : (qnum r 2 : ℂ) = ((qHalf r) ^ 4 + 1) / (qHalf r) ^ 2 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  rw [qnum_two hr]
  have h4 : (qHalf r) ^ 4 = Complex.exp (2 * (Complex.I * π / r)) := by
    unfold qHalf; rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp; ring
  have h2 : (qHalf r) ^ 2 = Complex.exp (Complex.I * π / r) := by
    unfold qHalf; rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [h4, h2, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  rw [show Complex.exp (2 * (Complex.I * π / r)) = Complex.exp (Complex.I * π / r) * Complex.exp (Complex.I * π / r) by
    rw [← Complex.exp_add]; congr 1; ring]
  have hne := Complex.exp_ne_zero (Complex.I * π / r)
  have : Complex.exp (-(π / r : ℂ) * Complex.I) = (Complex.exp (Complex.I * π / r))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; ring
  rw [show ((π : ℂ) / r * Complex.I) = Complex.I * π / r by ring, this]
  field_simp

/-- The algebra of the spin-1/2 hexagon, entry `(0,0)`. -/
lemma hexAlg_00 (m s t : ℂ) (hm : m ≠ 0) (ht : t = (m ^ 4 + 1) / m ^ 2) (hs : s * s = t ^ 2 - 1)
    (h4 : m ^ 4 + 1 ≠ 0) :
    (-(m ^ 3)⁻¹) * (-1 / t) * (-(m ^ 3)⁻¹) = (-1 / t) * 1 * (-1 / t) + (s / t) * (-(m ^ 4)⁻¹) * (s / t) := by
  have ht0 : t ≠ 0 := by rw [ht]; exact div_ne_zero h4 (pow_ne_zero 2 hm)
  have key : (s / t) * (-(m ^ 4)⁻¹) * (s / t) = (s * s) * (-(m ^ 4)⁻¹) / t ^ 2 := by field_simp
  rw [key, hs, ht]
  field_simp
  ring

/-- The algebra of the spin-1/2 hexagon, entries `(0,2)` and `(2,0)`. -/
lemma hexAlg_02 (m s t : ℂ) (hm : m ≠ 0) (ht : t = (m ^ 4 + 1) / m ^ 2) (h4 : m ^ 4 + 1 ≠ 0) :
    (-(m ^ 3)⁻¹) * (s / t) * m = (-1 / t) * 1 * (s / t) + (s / t) * (-(m ^ 4)⁻¹) * (1 / t) := by
  rw [ht]
  field_simp
  ring

/-- The algebra of the spin-1/2 hexagon, entry `(2,2)`. -/
lemma hexAlg_22 (m s t : ℂ) (hm : m ≠ 0) (ht : t = (m ^ 4 + 1) / m ^ 2) (hs : s * s = t ^ 2 - 1)
    (h4 : m ^ 4 + 1 ≠ 0) :
    m * (1 / t) * m = (s / t) * 1 * (s / t) + (1 / t) * (-(m ^ 4)⁻¹) * (1 / t) := by
  have ht0 : t ≠ 0 := by rw [ht]; exact div_ne_zero h4 (pow_ne_zero 2 hm)
  have key : (s / t) * 1 * (s / t) = (s * s) / t ^ 2 := by field_simp
  rw [key, hs, ht]
  field_simp
  ring

/-- **The hexagon equation for four spin-1/2 lines.** With the braiding eigenvalues `Rbr` and the F-matrix `fMat` of
the associator, `R^{11}_e F^{111}_1[e,g] R^{11}_g = Σ_h F^{111}_1[e,h] R^{1h}_1 F^{111}_1[h,g]` on the channels
`e, g ∈ {0, 2}`, for `q = e^{iπ/r}`, `r ≥ 4`. -/
theorem hexagon_half {r : ℕ} (hr : 4 ≤ r) {e g : ℕ} (he : e = 0 ∨ e = 2) (hg : g = 0 ∨ g = 2) :
    Rbr r 1 1 e * (fMat r 1 1 1 1 e g : ℂ) * Rbr r 1 1 g =
      ∑ h ∈ ({0, 2} : Finset ℕ), (fMat r 1 1 1 1 e h : ℂ) * Rbr r 1 h 1 * (fMat r 1 1 1 1 h g : ℂ) := by
  have h2 : 2 ≤ r := by omega
  have hq2 : 0 < qnum r 2 := qnum_pos h2 (by omega) (by omega)
  have hq3 : 0 < qnum r 3 := qnum_pos h2 (by omega) (by omega)
  have hm0 : qHalf r ≠ 0 := qHalf_ne_zero r
  have ht : (qnum r 2 : ℂ) = ((qHalf r) ^ 4 + 1) / (qHalf r) ^ 2 := qnum_two_qHalf h2
  have htne : (qnum r 2 : ℂ) ≠ 0 := by exact_mod_cast hq2.ne'
  have h4 : (qHalf r) ^ 4 + 1 ≠ 0 := by
    intro h; rw [h, zero_div] at ht; exact htne ht
  have hs : ((√(qnum r 3) : ℝ) : ℂ) * ((√(qnum r 3) : ℝ) : ℂ) = (qnum r 2 : ℂ) ^ 2 - 1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hq3.le, qnum_three h2]
    push_cast
    ring
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 2)]
  rcases he with rfl | rfl <;> rcases hg with rfl | rfl <;>
    simp only [fMat_half_00 hr, fMat_half_02 hr, fMat_half_20 hr, fMat_half_22 hr, Rbr_110 h2, Rbr_112 h2,
      Rbr_101 h2, Rbr_121 h2] <;> push_cast
  · exact hexAlg_00 _ _ _ hm0 ht hs h4
  · linear_combination hexAlg_02 (qHalf r) ((√(qnum r 3) : ℝ) : ℂ) (qnum r 2 : ℂ) hm0 ht h4
  · linear_combination hexAlg_02 (qHalf r) ((√(qnum r 3) : ℝ) : ℂ) (qnum r 2 : ℂ) hm0 ht h4
  · exact hexAlg_22 _ _ _ hm0 ht hs h4

end Lightlike.TV

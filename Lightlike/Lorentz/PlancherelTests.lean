module

public import Lightlike.Lorentz.Plancherel
public import Lightlike.Lorentz.LimitFormulaTests

/-!
# Trust checks for the Plancherel formula of SL(2,ℂ) (milestone HA2)

Checks of `plancherel_trace` and `plancherel` from `Lightlike.Lorentz.Plancherel`, with the
test function `testLF X = b(Σᵢⱼ |X_ij|²)` of `LimitFormulaTests` (`b` a bump equal to `1` near
`2`, so `testLF 1 = 1`).

1. **Non-vacuity.** `testLF` meets the hypotheses of both theorems. The trace form gives the
   nonzero value `16π⁴` (`testLF_plancherel_trace`), and the Hilbert–Schmidt form has
   `∫ |f|² dg > 0` for `f = testLF|_{SL(2,ℂ)}` (`testLF_plancherel`).
2. **The flat sum is a different quantity.** Without the density, the sum of the traces is the
   orbital integral at the identity, `Σ_n ∫ tr π_{n,ρ}(F) dρ = 2π³ ∫ F♮([[1, x], [0, 1]]) d²x`
   (`hasSum_trace_flat`), not a multiple of `F(1)`. This is Fourier inversion of the orbital
   integral at the identity, the step that the density `n² + 4ρ²` (a Laplacian) turns into the
   value `F(1)`.
3. **Wrong inputs give different answers.** With the density `n² + 4ρ² + 1` the formula fails for
   `testLF` (`testLF_wrong_density`), because the flat sum adds `2π³ ∫ b(2 + |x|²) d²x > 0`. With
   the constant `16π³` of the orbital form `hasSum_density_orbInt` in place of `16π⁴` it fails too
   (`testLF_wrong_constant`): the trace `tr π_{n,ρ}(F) = π T_{F♮}(n, ρ)` carries a factor `π`.
4. **The constant of Perez–Rovelli.** In their variables (`plancherel_trace_perezRovelli`) the
   constant `1/(8π⁴)` of their eqs. (A11) and (A16) gives `4 F(1)`, not `F(1)`
   (`testLF_perezRovelli_constant`); the correct constant there is `1/(32π⁴)`.
5. **Non-vacuity beyond `n = 0`.** `testLF` is bi-SU(2)-invariant, so it only exercises the term
   `n = 0`. The odd test function `testOdd X = X₀₀ · testLF X` (`testOdd (-X) = -testOdd X`, and
   not bi-SU(2)-invariant since `-1 ∈ SU(2)` and `testOdd 1 = 1`) has kernels of parity
   `(-1)^(n+1)` (`psKernel_odd`), so every even-`n` term of `plancherel` vanishes; since the
   total `16π⁴ ∫ |f|²` is positive, some odd `n` gives a nonzero term (`testOdd_plancherel`).

The numerical cross-check `scripts/lorentz/plancherel_check.py` evaluates both sides of the full
formula for a conjugation-invariant Gaussian test function by quadrature, with wrong densities as
controls.
-/

@[expose] public section

open MeasureTheory Complex Metric
open scoped ContDiff FourierTransform

local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-- `∫ 𝓕c(ρ/π) dρ = π c(0)` for `c` smooth with compact support. -/
lemma integral_fourier_div_pi {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c) :
    Integrable (fun ρ : ℝ => 𝓕 c (ρ / Real.pi)) ∧
      ∫ ρ : ℝ, 𝓕 c (ρ / Real.pi) = Real.pi * c 0 := by
  have hi := integrable_fourier_of_hasCompactSupport hc hcs
  refine ⟨hi.comp_div Real.pi_ne_zero, ?_⟩
  rw [Measure.integral_comp_div (𝓕 c), abs_of_pos Real.pi_pos, integral_fourier_eq hc hcs,
    Complex.real_smul]

/-- **The trace as a Fourier transform**: `tr π_{n,ρ}(F) = 2π² 𝓕c_n(ρ/π)`, with `c_n` the angular
Fourier coefficients of the orbital integral of the `SU(2)` average `F♮`. -/
lemma trace_eq_fourier {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) (n : ℤ)
    (ρ : ℝ) :
    ∫ z, psKernel n ρ (fun g => F (toArr g)) z z =
      2 * (Real.pi : ℂ) ^ 2 * 𝓕 (orbCoeff (su2Avg F) n) (ρ / Real.pi) := by
  rw [integral_psKernel_diag hF.continuous hs n ρ,
    integral_mult_orbInt (contDiff_su2Avg hF) (hasCompactSupport_su2Avg hs) n ρ]
  ring

/-- **The flat-density sum.** Without the Plancherel density, the traces are integrable and their
sum is the orbital integral at the identity:
`Σ_{n ∈ ℤ} ∫ tr π_{n,ρ}(F) dρ = 2π³ Φ_{F♮}(1)`, `Φ_{F♮}(1) = ∫ F♮([[1, x], [0, 1]]) d²x`. -/
theorem hasSum_trace_flat {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    (∀ n : ℤ, Integrable fun ρ : ℝ => ∫ z, psKernel n ρ (fun g => F (toArr g)) z z) ∧
    HasSum (fun n : ℤ => ∫ ρ : ℝ, ∫ z, psKernel n ρ (fun g => F (toArr g)) z z)
      (2 * (Real.pi : ℂ) ^ 3 * orbInt (su2Avg F) 1) := by
  have hA := contDiff_su2Avg hF
  have hAs := hasCompactSupport_su2Avg hs
  have hD := fun n : ℤ =>
    integral_fourier_div_pi (contDiff_orbCoeff hA hAs n) (hasCompactSupport_orbCoeff hAs n)
  have hD2 : ∀ n : ℤ, ∫ ρ : ℝ, 𝓕 (orbCoeff (su2Avg F) n) (ρ / Real.pi) =
      Real.pi * orbCoeff (su2Avg F) n 0 := fun n => (hD n).2
  simp_rw [trace_eq_fourier hF hs]
  refine ⟨fun n => (hD n).1.const_mul _, ?_⟩
  simp_rw [integral_const_mul, hD2]
  convert (hasSum_fourierCoeffOn (contDiff_orbExp_right hA hAs 0)
    (orbExp_periodic _ 0)).mul_left (2 * (Real.pi : ℂ) ^ 3) using 1
  · funext n
    rw [orbCoeff]
    ring
  · simp [orbExp]

/-- `testLF` is smooth of every order. -/
lemma contDiff_testLF_top : ContDiff ℝ ∞ testLF :=
  contDiff_testF.comp contDiff_hsNormSq

/-- On the orbit of the identity, `Σᵢⱼ |X_ij|² = 2 + |x|²` for `X = [[1, x], [0, 1]]`. -/
lemma hsNormSq_triMat_one (x : ℂ) : hsNormSq (triMat 1 x) = 2 + ‖x‖ ^ 2 := by
  simp [hsNormSq, triMat, mat2, Fin.sum_univ_two]
  ring

/-- The orbital integral of `testLF` at the identity is positive:
`Φ(1) = ∫ b(2 + |x|²) d²x > 0`. -/
theorem orbInt_testLF_one :
    orbInt testLF 1 = ((∫ x : ℂ, testBump (2 + ‖x‖ ^ 2) : ℝ) : ℂ) ∧
      0 < ∫ x : ℂ, testBump (2 + ‖x‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · rw [orbInt, ← integral_complex_ofReal]
    simp_rw [testLF, hsNormSq_triMat_one, testF]
  have hc : Continuous fun x : ℂ => testBump (2 + ‖x‖ ^ 2) :=
    testBump.continuous.comp (continuous_const.add (continuous_norm.pow 2))
  have hcs : HasCompactSupport fun x : ℂ => testBump (2 + ‖x‖ ^ 2) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) fun x hx => ?_
    have h1 : 1 < ‖x‖ := by simpa using hx
    refine testBump.zero_of_le_dist ?_
    have hr : testBump.rOut = 1 := rfl
    rw [hr, Real.dist_eq, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    nlinarith
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun x => testBump.nonneg)
    (x := 0) ?_
  rw [norm_zero, zero_pow two_ne_zero, add_zero,
    testBump.one_of_mem_closedBall (mem_closedBall_self testBump.rIn_pos.le)]
  exact one_ne_zero

/-- **Non-vacuity of `plancherel_trace`**: `testLF` meets its hypotheses, and the right side is
`16π⁴ ≠ 0`. -/
theorem testLF_plancherel_trace :
    HasSum (fun n : ℤ => ∫ ρ : ℝ, ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) *
      ∫ z, psKernel n ρ (fun g => testLF (toArr g)) z z) (16 * (Real.pi : ℂ) ^ 4) ∧
      (16 * (Real.pi : ℂ) ^ 4) ≠ 0 := by
  have h := (plancherel_trace contDiff_testLF_top hasCompactSupport_testLF).2
  rw [testLF_one, mul_one] at h
  exact ⟨h, mul_ne_zero (by norm_num) (pow_ne_zero _ (ofReal_ne_zero.2 Real.pi_ne_zero))⟩

/-- **Non-vacuity of `plancherel`**: `f = testLF|_{SL(2,ℂ)}` meets its hypotheses, and
`∫ |f|² dg > 0`. -/
theorem testLF_plancherel :
    HasSum (fun n : ℤ => ∫ ρ : ℝ, ((n : ℝ) ^ 2 + 4 * ρ ^ 2) *
      ∫ z, ∫ z', ‖psKernel n ρ (fun g => testLF (toArr g)) z' z‖ ^ 2)
      (16 * Real.pi ^ 4 * ∫ g, ‖testLF (toArr g)‖ ^ 2 ∂haarC) ∧
      0 < ∫ g, ‖testLF (toArr g)‖ ^ 2 ∂haarC := by
  refine ⟨(plancherel (f := fun g => testLF (toArr g)) contDiff_testLF_top
    hasCompactSupport_testLF fun _ => rfl).2.2.2, ?_⟩
  have hc : Continuous fun g : SL2C => ‖testLF (toArr g)‖ ^ 2 :=
    ((contDiff_testLF_top.continuous.comp isClosedEmbedding_toArr.continuous).norm).pow 2
  have hcs : HasCompactSupport fun g : SL2C => ‖testLF (toArr g)‖ ^ 2 :=
    (hasCompactSupport_restrict hasCompactSupport_testLF).comp_left
      (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun g => by positivity)
    (x := 1) ?_
  rw [toArr_one, testLF_one]
  norm_num

/-- **Wrong density**: with `n² + 4ρ² + 1` in place of `n² + 4ρ²` the trace form of the Plancherel
formula is false for `testLF`. -/
theorem testLF_wrong_density :
    ¬ HasSum (fun n : ℤ => ∫ ρ : ℝ, ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2 + 1) *
      ∫ z, psKernel n ρ (fun g => testLF (toArr g)) z z)
      (16 * (Real.pi : ℂ) ^ 4 * testLF (mat2 1 0 0 1)) := by
  intro h
  obtain ⟨hi1, hs1⟩ := plancherel_trace contDiff_testLF_top hasCompactSupport_testLF
  obtain ⟨hi2, hs2⟩ := hasSum_trace_flat contDiff_testLF_top hasCompactSupport_testLF
  have hsplit : (fun n : ℤ => ∫ ρ : ℝ, ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2 + 1) *
      ∫ z, psKernel n ρ (fun g => testLF (toArr g)) z z) = fun n : ℤ =>
      (∫ ρ : ℝ, ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) *
        ∫ z, psKernel n ρ (fun g => testLF (toArr g)) z z) +
      ∫ ρ : ℝ, ∫ z, psKernel n ρ (fun g => testLF (toArr g)) z z := by
    funext n
    rw [← integral_add (hi1 n) (hi2 n)]
    congr 1
    funext ρ
    ring
  rw [hsplit] at h
  have he := h.unique (hs1.add hs2)
  rw [su2Avg_eq_self isSU2ConjInvariant_testLF, orbInt_testLF_one.1] at he
  have h0 : ((2 * Real.pi ^ 3 * ∫ x : ℂ, testBump (2 + ‖x‖ ^ 2) : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination -he
  exact (mul_pos (by positivity) orbInt_testLF_one.2).ne' (ofReal_eq_zero.1 h0)

/-- **Wrong constant**: with the constant `16π³` of the orbital form in place of `16π⁴` the trace
form of the Plancherel formula is false for `testLF`. -/
theorem testLF_wrong_constant :
    ¬ HasSum (fun n : ℤ => ∫ ρ : ℝ, ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) *
      ∫ z, psKernel n ρ (fun g => testLF (toArr g)) z z)
      (16 * (Real.pi : ℂ) ^ 3 * testLF (mat2 1 0 0 1)) := by
  intro h
  have he := h.unique testLF_plancherel_trace.1
  rw [testLF_one, mul_one] at he
  have h0 : ((16 * Real.pi ^ 3 * (Real.pi - 1) : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination -he
  have hpi : 1 < Real.pi := by linarith [Real.pi_gt_three]
  exact (mul_pos (by positivity) (sub_pos.2 hpi)).ne' (ofReal_eq_zero.1 h0)

/-- **The constant of Perez–Rovelli fails**: in their variables (`plancherel_trace_perezRovelli`)
the constant `1/(8π⁴)` of their (A11) and (A16) gives `4 F(1)` in place of `F(1)` for `testLF`,
whose value at the identity is `1`. -/
theorem testLF_perezRovelli_constant :
    (8 * (Real.pi : ℂ) ^ 4)⁻¹ * ∑' n : ℤ, ∫ σ : ℝ, ((n : ℂ) ^ 2 + (σ : ℂ) ^ 2) *
      ∫ z, prKernel n σ (fun g => testLF (toArr g)) z z = 4 * testLF (mat2 1 0 0 1) ∧
    4 * testLF (mat2 1 0 0 1) ≠ testLF (mat2 1 0 0 1) := by
  have h := (plancherel_trace_perezRovelli contDiff_testLF_top hasCompactSupport_testLF).2.1
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [h.tsum_eq, testLF_one]
  refine ⟨?_, by norm_num⟩
  field_simp
  ring

/-! ## Non-vacuity beyond `n = 0`: an odd test function -/

/-- `m(-λ) = (-1)ⁿ m(λ)`. -/
lemma mult_neg (n : ℤ) (ρ : ℂ) (w : ℂ) : mult n ρ (-w) = (-1) ^ n * mult n ρ w := by
  simp only [mult, norm_neg, neg_div]
  rw [neg_eq_neg_one_mul (w / _), mul_zpow]
  ring

/-- `g_z(-b, w, -λ) = -g_z(b, w, λ)` as arrays, off the null set `λ = 0`. -/
lemma toArr_chartPt_neg (z w : ℂ) {q : ℂ × ℂ} (hq : q.2 ≠ 0) :
    toArr (chartPt z w (-q)) = -toArr (chartPt z w q) := by
  have h1 : (![(-q).1, w, (-q).2] : Fin 3 → ℂ) 2 ≠ 0 := by simpa using hq
  have h2 : (![q.1, w, q.2] : Fin 3 → ℂ) 2 ≠ 0 := by simpa using hq
  funext i j
  rw [show (-toArr (chartPt z w q)) i j = -(toArr (chartPt z w q) i j) from rfl]
  simp only [toArr, chartPt]
  rw [fixChart_apply z h1, fixChart_apply z h2]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **Parity of the kernel**: if `F(-X) = -F(X)`, then `K_f = -(-1)ⁿ K_f` for
`f = F|_{SL(2,ℂ)}`, because `q ↦ -q` maps `g_z(q)` to `-g_z(q)` and `m(-λ) = (-1)ⁿ m(λ)`. -/
lemma psKernel_odd {F : P2 → ℂ} (hF : ∀ X, F (-X) = -F X) (n : ℤ) (ρ : ℝ) (z w : ℂ) :
    psKernel n ρ (fun g => F (toArr g)) z w =
      -((-1 : ℂ) ^ n) * psKernel n ρ (fun g => F (toArr g)) z w := by
  have hm : MeasurePreserving (fun q : ℂ × ℂ => -q) volume volume :=
    (Measure.measurePreserving_neg (volume : Measure ℂ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℂ))
  unfold psKernel
  rw [← integral_const_mul]
  refine (hm.integral_comp measurableEmbedding_neg _).symm.trans (integral_congr_ae ?_)
  filter_upwards [ae_snd_ne_zero] with q hq
  show F (toArr (chartPt z w (-q))) * mult n ρ (-q).2 =
    -((-1 : ℂ) ^ n) * (F (toArr (chartPt z w q)) * mult n ρ q.2)
  rw [toArr_chartPt_neg z w hq, hF, Prod.snd_neg, mult_neg]
  ring

/-- For odd `F` the kernels of even `n` vanish. -/
lemma psKernel_eq_zero_of_even {F : P2 → ℂ} (hF : ∀ X, F (-X) = -F X) {n : ℤ} (hn : Even n)
    (ρ : ℝ) (z w : ℂ) : psKernel n ρ (fun g => F (toArr g)) z w = 0 := by
  have h := psKernel_odd hF n ρ z w
  rw [hn.neg_one_zpow] at h
  linear_combination h / 2

/-- The odd test function `testOdd X = X₀₀ · testLF X`. -/
noncomputable def testOdd (X : P2) : ℂ := X 0 0 * testLF X

lemma contDiff_testOdd : ContDiff ℝ ∞ testOdd := by
  have h0 : ContDiff ℝ ∞ fun X : P2 => X 0 := contDiff_pi.1 contDiff_id 0
  have h00 : ContDiff ℝ ∞ fun X : P2 => X 0 0 := contDiff_pi.1 h0 0
  exact h00.mul contDiff_testLF_top

lemma hasCompactSupport_testOdd : HasCompactSupport testOdd :=
  hasCompactSupport_testLF.mono fun _ hX =>
    Function.mem_support.2 (right_ne_zero_of_mul (Function.mem_support.1 hX))

/-- `testOdd` is odd. -/
lemma testOdd_neg (X : P2) : testOdd (-X) = -testOdd X := by
  simp [testOdd, testLF, hsNormSq]

/-- `testOdd 1 = 1`. -/
lemma testOdd_one : testOdd (mat2 1 0 0 1) = 1 := by
  rw [testOdd, testLF_one, mat2_apply_zero_zero, mul_one]

/-- **Non-vacuity of `plancherel` beyond `n = 0`**: for `f = testOdd|_{SL(2,ℂ)}`, which is not
bi-SU(2)-invariant (`f(-g) = -f(g)` with `-1 ∈ SU(2)`, and `f(1) = 1`), all kernels with even
`n` vanish, `∫ |f|² dg > 0`, and so some odd `n` has a nonzero term in `plancherel`. -/
theorem testOdd_plancherel :
    (∀ n : ℤ, Even n → ∀ (ρ : ℝ) (z' z : ℂ),
      psKernel n ρ (fun g => testOdd (toArr g)) z' z = 0) ∧
    0 < ∫ g, ‖testOdd (toArr g)‖ ^ 2 ∂haarC ∧
    ∃ n : ℤ, Odd n ∧ ∫ ρ : ℝ, ((n : ℝ) ^ 2 + 4 * ρ ^ 2) *
      ∫ z, ∫ z', ‖psKernel n ρ (fun g => testOdd (toArr g)) z' z‖ ^ 2 ≠ 0 := by
  have heven : ∀ n : ℤ, Even n → ∀ (ρ : ℝ) (z' z : ℂ),
      psKernel n ρ (fun g => testOdd (toArr g)) z' z = 0 :=
    fun n hn ρ z' z => psKernel_eq_zero_of_even testOdd_neg hn ρ z' z
  have hpos : 0 < ∫ g, ‖testOdd (toArr g)‖ ^ 2 ∂haarC := by
    have hc : Continuous fun g : SL2C => ‖testOdd (toArr g)‖ ^ 2 :=
      ((contDiff_testOdd.continuous.comp isClosedEmbedding_toArr.continuous).norm).pow 2
    have hcs : HasCompactSupport fun g : SL2C => ‖testOdd (toArr g)‖ ^ 2 :=
      (hasCompactSupport_restrict hasCompactSupport_testOdd).comp_left
        (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun g => by positivity)
      (x := 1) ?_
    rw [toArr_one, testOdd_one]
    norm_num
  refine ⟨heven, hpos, ?_⟩
  have hsum := (plancherel (f := fun g => testOdd (toArr g)) contDiff_testOdd
    hasCompactSupport_testOdd fun _ => rfl).2.2.2
  by_contra hno
  simp only [not_exists, not_and, ne_eq, not_not] at hno
  have h0 : HasSum (fun n : ℤ => ∫ ρ : ℝ, ((n : ℝ) ^ 2 + 4 * ρ ^ 2) *
      ∫ z, ∫ z', ‖psKernel n ρ (fun g => testOdd (toArr g)) z' z‖ ^ 2) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0) with n
    rcases Int.even_or_odd n with h | h
    · simp [heven n h]
    · exact hno n h
  exact (mul_pos (by positivity) hpos).ne' (hsum.unique h0)

end Lightlike.Lorentz

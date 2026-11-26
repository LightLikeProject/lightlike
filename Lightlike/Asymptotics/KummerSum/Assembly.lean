import Lightlike.Asymptotics.KummerSum.Laplace
import Lightlike.Asymptotics.KummerSum.Sides
import Lightlike.Asymptotics.SaddleRay

/-!
# The saddle-point asymptotics of Kummer's sum

The contour method of `Lightlike.Asymptotics`, run on Kummer's sum
`K(m) = Σ_{t ≤ m} (−1)^t C(m,t)²` (`kummerSum`), whose value is known independently
(`kummer_alternating`, not used here).  With `N = m + 1`:

1. `K(m) = −Im(Φ(m + ½) − Φ(−½))/π` for a primitive `Φ` of the kernel `f`
   (`kummerSum_eq_im_primitive`);
2. `Φ(m + ½) − Φ(−½)` is the integral of `f` up `Re z = −½`, across `Im z = N/2` and down
   `Re z = m + ½` (`sub_eq_integral_line`);
3. on the vertical sides `‖f‖ ≤ (q_N²/N) e^{N/2 + 3/(2N)}` (`KummerSum/Sides.lean`);
4. across, `f(z(s)) N = −q_N² (2i)^N e^{N φ(s)} A(z(s))` with the saddle `α₀ = (1 + i)/2`,
   `e^{N ψ(α₀)} = (2i)^N` (`kummerKernel_eq`, `kummerPhase_saddle`), `A = 1 + O(1/N)`
   (`norm_kummerAmp_sub_one_le`), and Laplace's method gives `∫ e^{Nφ} = (π/(2N))^{1/2} + O(1/N)`
   (`norm_integral_kummerPhase_sub_le`).

So (`kummerSum_saddle_bound`) there is `C` with, for `m ≥ 5`,

  `|K(m) − q_N² L(m)| ≤ (q_N²/π) (C 2^N / N + e^{N/2 + 3/(2N)})`,

where `L(m) = 2^N Im(i^N) √(π/(2N))/π` (`kummerLead`) is the saddle-point leading term: `2^N i^N`
from `e^{Nψ(α₀)}`, `√(π/(2N)) = √(2π/(N |ψ''(α₀)|))` from `ψ''(α₀) = −4`, and `−Im(−·)/π` from the
contour identity.  Since `q_N → 1` and `e^{N/2} = o(2^N/√N)`, `K(2n)/L(2n) → 1`
(`tendsto_kummerSum_div_kummerLead`).  The closed form `(−1)^n C(2n, n)` has the same asymptotics
by the real Stirling formula (`tendsto_centralBinom_div_kummerLead`), and
`kummerSum_saddle_matches_closed_form` states both sides.
-/

open Complex Set MeasureTheory intervalIntegral Filter Topology Finset
open scoped Real Nat

namespace Lightlike.Asymptotics

/-- Kummer's sum `Σ_{t ≤ m} (−1)^t C(m,t)²`. -/
noncomputable def kummerSum (m : ℕ) : ℝ := ∑ t ∈ range (m + 1), (-1 : ℝ) ^ t * (m.choose t : ℝ) ^ 2

/-- The saddle-point leading term `L(m) = 2^N Im(i^N) √(π/(2N)) / π`, `N = m + 1`. -/
noncomputable def kummerLead (m : ℕ) : ℝ :=
  2 ^ (m + 1) * (I ^ (m + 1)).im * √(π / (2 * (m + 1))) / π

/-- The fundamental theorem of calculus along a line segment `t ↦ a + t v`, `t ∈ [p, q]`. -/
theorem sub_eq_integral_line {Φ f : ℂ → ℂ} (a v : ℂ) {p q : ℝ} (hpq : p ≤ q)
    (hd : ∀ t ∈ Icc p q, HasDerivAt Φ (f (a + t * v)) (a + t * v))
    (hc : ContinuousOn (fun t : ℝ => f (a + t * v)) (Icc p q)) :
    Φ (a + q * v) - Φ (a + p * v) = ∫ t in p..q, f (a + t * v) * v := by
  symm
  apply integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hpq] at ht
    have hγ : HasDerivAt (fun w : ℂ => a + w * v) v (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const v).const_add a
    exact ((hd t ht).comp (t : ℂ) hγ).comp_ofReal
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpq]
    exact (hc.mul continuousOn_const).integrableOn_Icc

/-- Kummer's kernel is continuous off the integers. -/
lemma continuousAt_kummerKernel (m : ℕ) {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) :
    ContinuousAt (kummerKernel m) z :=
  ((continuous_const.mul (differentiable_kummerT m).continuous).continuousAt).div
    (by fun_prop) (sin_pi_mul_ne_zero hz)

lemma ne_intCast_of_re {z : ℂ} {r : ℝ} (hr : z.re = r) (h : ∀ n : ℤ, (n : ℝ) ≠ r) :
    ∀ n : ℤ, z ≠ n := fun n hn => h n (by rw [← hr, hn]; simp)

lemma intCast_ne_half_sub (k : ℤ) (n : ℤ) : (n : ℝ) ≠ k - 1 / 2 := by
  intro h
  have : (2 : ℝ) * (n - k) = -1 := by linarith
  have h2 : (2 * (n - k) : ℤ) = -1 := by exact_mod_cast this
  omega

/-- **The saddle-point bound for Kummer's sum.** -/
theorem kummerSum_saddle_bound :
    ∃ C : ℝ, ∀ m : ℕ, 5 ≤ m →
      |kummerSum m - stirQ (m + 1) ^ 2 * kummerLead m| ≤
        stirQ (m + 1) ^ 2 / π * (2 ^ (m + 1) * C / (m + 1) +
          Real.exp (((m + 1 : ℕ) : ℝ) / 2 + 3 / (2 * ((m + 1 : ℕ) : ℝ)))) := by
  obtain ⟨C, hC⟩ := norm_integral_kummerPhase_sub_le
  refine ⟨C + 26, fun m hm => ?_⟩
  set N : ℝ := ((m + 1 : ℕ) : ℝ) with hNdef
  have hNm : N = (m : ℝ) + 1 := by rw [hNdef]; push_cast; ring
  have hN6 : 6 ≤ N := by
    have : (5 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hNm]; linarith
  have hN0 : 0 < N := by linarith
  have hm1 : 1 ≤ m := by omega
  set q := stirQ (m + 1)
  set B := q ^ 2 / N * Real.exp (N / 2 + 3 / (2 * N)) with hB
  -- the contour identity
  obtain ⟨Φ, hΦ, -, -, hS⟩ := kummerSum_eq_im_primitive m (x₁ := -1 / 2) (x₂ := m + 1 / 2)
    (by norm_num) (by linarith)
  have hΦd : ∀ z : ℂ, 0 ≤ z.im → (∀ n : ℤ, z ≠ n) →
      HasDerivAt Φ (kummerKernel m z) z := hΦ
  -- the left side
  have hL : ∀ t : ℝ, ∀ n : ℤ, (-1 / 2 : ℂ) + t * I ≠ n :=
    fun t => ne_intCast_of_re (r := -1 / 2) (by simp) (fun n h => intCast_ne_half_sub 0 n (by rw [h]; push_cast; ring))
  have hR : ∀ t : ℝ, ∀ n : ℤ, ((m : ℂ) + 1 / 2) + t * I ≠ n :=
    fun t => ne_intCast_of_re (r := m + 1 / 2) (by simp) (fun n => by
      intro h; have := intCast_ne_half_sub (m + 1) n; push_cast at this; apply this; linarith)
  have h1 := sub_eq_integral_line (Φ := Φ) (f := kummerKernel m) (-1 / 2) I (p := 0) (q := N / 2)
    (by linarith) (fun t ht => hΦd _ (by simp [ht.1]) (hL t))
    (fun t _ => by
      have : ContinuousAt (fun t : ℝ => kummerKernel m (-1 / 2 + t * I)) t :=
        ContinuousAt.comp (f := fun t : ℝ => (-1 / 2 : ℂ) + t * I)
          (continuousAt_kummerKernel m (hL t)) (by fun_prop)
      exact this.continuousWithinAt)
  have h3 := sub_eq_integral_line (Φ := Φ) (f := kummerKernel m) ((m : ℂ) + 1 / 2) I (p := 0)
    (q := N / 2) (by linarith) (fun t ht => hΦd _ (by simp [ht.1]) (hR t))
    (fun t _ => by
      have : ContinuousAt (fun t : ℝ => kummerKernel m ((m : ℂ) + 1 / 2 + t * I)) t :=
        ContinuousAt.comp (f := fun t : ℝ => (m : ℂ) + 1 / 2 + t * I)
          (continuousAt_kummerKernel m (hR t)) (by fun_prop)
      exact this.continuousWithinAt)
  -- across, through the saddle
  have hlineeq : ∀ s : ℝ, kummerLinePt N s = ((N : ℂ) * kummerSaddle - 1 / 2) + s * N := by
    intro s; simp only [kummerLinePt]; ring
  have hP : ∀ s : ℝ, 0 < (kummerLinePt N s).im := fun s => by rw [kummerLinePt_im]; linarith
  have h2 := sub_eq_integral_line (Φ := Φ) (f := kummerKernel m)
    ((N : ℂ) * kummerSaddle - 1 / 2) (N : ℂ) (p := -(1 / 2)) (q := 1 / 2) (by norm_num)
    (fun t _ => by rw [← hlineeq]; exact hΦd _ (hP t).le (ne_intCast_of_im_pos (hP t)))
    (fun t _ => by
      have : ContinuousAt (fun t : ℝ => kummerKernel m (kummerLinePt N t)) t :=
        (continuousAt_kummerKernel m (ne_intCast_of_im_pos (hP t))).comp
          (by unfold kummerLinePt; fun_prop)
      simp only [← hlineeq]; exact this.continuousWithinAt)
  simp only [← hlineeq] at h2
  -- the end points match
  have eA : (-1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * I = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have eB : ((m : ℂ) + 1 / 2) + ((0 : ℝ) : ℂ) * I = ((m + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have eC : kummerLinePt N (-(1 / 2)) = (-1 / 2 : ℂ) + ((N / 2 : ℝ) : ℂ) * I := by
    simp only [kummerLinePt, kummerSaddle]; push_cast; ring
  have eD : kummerLinePt N (1 / 2) = ((m : ℂ) + 1 / 2) + ((N / 2 : ℝ) : ℂ) * I := by
    simp only [kummerLinePt, kummerSaddle]; rw [hNm]; push_cast; ring
  rw [eA] at h1; rw [eB] at h3; rw [eC, eD] at h2
  set I1 := ∫ t in (0 : ℝ)..N / 2, kummerKernel m (-1 / 2 + t * I) * I
  set I3 := ∫ t in (0 : ℝ)..N / 2, kummerKernel m ((m : ℂ) + 1 / 2 + t * I) * I
  set I2 := ∫ t in (-(1 / 2) : ℝ)..1 / 2, kummerKernel m (kummerLinePt N t) * N
  have hD : Φ ((m + 1 / 2 : ℝ) : ℂ) - Φ ((-1 / 2 : ℝ) : ℂ) = I1 + I2 - I3 := by
    rw [← h1, ← h2, ← h3]; ring
  -- bounds on the vertical sides
  have hside : ∀ g : ℝ → ℂ, (∀ t, |t| ≤ N / 2 → ‖g t‖ ≤ B) →
      ‖∫ t in (0 : ℝ)..N / 2, g t * I‖ ≤ B * (N / 2) := by
    intro g hg
    have := norm_integral_le_of_norm_le_const (a := 0) (b := N / 2) (C := B)
      (f := fun t => g t * I) (fun t ht => by
        rw [uIoc_of_le (by linarith)] at ht
        rw [norm_mul, norm_I, mul_one]
        exact hg t (by rw [abs_of_pos ht.1]; exact ht.2))
    rwa [sub_zero, abs_of_pos (by linarith)] at this
  have hI1 : ‖I1‖ ≤ B * (N / 2) := hside _ fun t ht => norm_kummerKernel_left_le hm1 ht
  have hI3 : ‖I3‖ ≤ B * (N / 2) := hside _ fun t ht => norm_kummerKernel_right_le hm1 ht
  -- the kernel across, in Stirling form
  have hNc : ((m : ℂ) + 1) = (N : ℂ) := by rw [hNm]; push_cast; ring
  have hexp0 : cexp ((N : ℂ) * kummerPhase kummerSaddle) = (2 * I) ^ (m + 1) := by
    rw [kummerPhase_saddle, hNdef, ofReal_natCast, exp_nat_mul, exp_add, ← ofReal_exp,
      Real.exp_log (by norm_num), exp_pi_div_two_mul_I]
    push_cast; ring
  have hK2 : ∀ s : ℝ, kummerKernel m (kummerLinePt N s) * N =
      -(q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * (cexp (N * kummerPhi s) * kummerAmp m (kummerLinePt N s)) := by
    intro s
    rw [kummerKernel_eq m (hP s), hNc]
    have hα : (kummerLinePt N s + 1 / 2) / (N : ℂ) = kummerSaddle + s := by
      rw [kummerLinePt]; field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast hN0.ne']; ring
    rw [hα, show (N : ℂ) * kummerPhase (kummerSaddle + s) =
      N * kummerPhase kummerSaddle + N * kummerPhi s by rw [kummerPhi]; ring, exp_add, hexp0]
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast hN0.ne']
    ring
  have hcont : Continuous fun s : ℝ => cexp (N * kummerPhi s) :=
    (continuous_const.mul continuous_kummerPhi).cexp
  have hampc : ContinuousOn (fun s : ℝ => kummerAmp m (kummerLinePt N s)) (Icc (-(1 / 2)) (1 / 2)) := by
    have hcI : ∀ s : ℝ, ContinuousAt (fun s : ℝ => kummerKernel m (kummerLinePt N s) * N) s :=
      fun s => ((continuousAt_kummerKernel m (ne_intCast_of_im_pos (hP s))).comp
        (by unfold kummerLinePt; fun_prop)).mul continuousAt_const
    intro s _
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (stirQ_pos (m + 1)).ne'
    have e : (fun s : ℝ => kummerAmp m (kummerLinePt N s)) = fun s =>
        (kummerKernel m (kummerLinePt N s) * N) /
          (-(q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * cexp (N * kummerPhi s)) := by
      funext s; rw [hK2 s]; field_simp
    rw [e]
    exact ((hcI s).div (continuousAt_const.mul hcont.continuousAt)
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ hq0))
        (pow_ne_zero _ (mul_ne_zero two_ne_zero I_ne_zero))) (exp_ne_zero _))).continuousWithinAt
  set L : ℂ := ((π : ℂ) / (N * 4 / 2)) ^ (1 / 2 : ℂ)
  set J0 := ∫ s in (-(1 / 2) : ℝ)..1 / 2, cexp (N * kummerPhi s)
  set J1 := ∫ s in (-(1 / 2) : ℝ)..1 / 2, cexp (N * kummerPhi s) * (kummerAmp m (kummerLinePt N s) - 1)
  have hint0 : IntervalIntegrable (fun s : ℝ => cexp (N * kummerPhi s)) volume (-(1 / 2)) (1 / 2) :=
    hcont.intervalIntegrable _ _
  have hint1 : IntervalIntegrable (fun s : ℝ => cexp (N * kummerPhi s) *
      (kummerAmp m (kummerLinePt N s) - 1)) volume (-(1 / 2)) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact (hcont.continuousOn.mul (hampc.sub continuousOn_const)).integrableOn_Icc
  have hI2 : I2 = -(q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * (J0 + J1) := by
    simp only [I2, hK2]
    rw [intervalIntegral.integral_const_mul, ← integral_add hint0 hint1]
    congr 1
    refine integral_congr fun s _ => by ring
  have hJ0 : ‖J0 - L‖ ≤ C / N := hC N hN0
  have hJ1 : ‖J1‖ ≤ 26 / N := by
    have := norm_integral_le_of_norm_le_const (a := -(1 / 2)) (b := 1 / 2) (C := 26 / N)
      (f := fun s => cexp (N * kummerPhi s) * (kummerAmp m (kummerLinePt N s) - 1))
      (fun s hs => by
        rw [uIoc_of_le (by norm_num)] at hs
        have hs' : |s| ≤ 1 / 2 := abs_le.2 ⟨hs.1.le, hs.2⟩
        rw [norm_mul, norm_exp]
        have hre : (↑N * kummerPhi s).re ≤ 0 := by
          rw [re_ofReal_mul]; nlinarith [re_kummerPhi_le hs', sq_nonneg s]
        have ha := norm_kummerAmp_sub_one_le hm hs'
        rw [show ((m : ℝ) + 1) = N from hNm.symm] at ha
        calc Real.exp (↑N * kummerPhi s).re * ‖kummerAmp m (kummerLinePt N s) - 1‖
            ≤ 1 * (26 / N) := by
              gcongr
              exact Real.exp_le_one_iff.2 hre
          _ = 26 / N := one_mul _)
    rwa [show |(1 / 2 : ℝ) - -(1 / 2)| = 1 by norm_num, mul_one] at this
  -- the leading term
  have hLreal : L = ((√(π / (2 * N)) : ℝ) : ℂ) := by
    simp only [L]
    rw [show (π : ℂ) / (N * 4 / 2) = ((π / (2 * N) : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  -- combine
  have hsum : kummerSum m = -(I1 + I2 - I3).im / π := by
    rw [kummerSum, hS, hD]
  set E := (J0 - L) + J1
  have hE : ‖E‖ ≤ (C + 26) / N := by
    calc ‖E‖ ≤ ‖J0 - L‖ + ‖J1‖ := norm_add_le _ _
      _ ≤ C / N + 26 / N := add_le_add hJ0 hJ1
      _ = (C + 26) / N := by ring
  have hJ : J0 + J1 = L + E := by simp only [E]; ring
  have hlead : (-(-(q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * L)).im / π = q ^ 2 * kummerLead m := by
    rw [hLreal, kummerLead, mul_pow, neg_mul, neg_mul, neg_neg]
    rw [show (q : ℂ) ^ 2 * ((2 : ℂ) ^ (m + 1) * I ^ (m + 1)) * ((√(π / (2 * N)) : ℝ) : ℂ) =
      ((q ^ 2 * 2 ^ (m + 1) * √(π / (2 * N)) : ℝ) : ℂ) * I ^ (m + 1) by push_cast; ring,
      im_ofReal_mul, hNm]
    ring
  have key : kummerSum m - q ^ 2 * kummerLead m =
      ((-(I1 - I3)).im + ((q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * E).im) / π := by
    rw [hsum, hI2, hJ, ← hlead, show I1 + -(q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * (L + E) - I3 =
      (I1 - I3) + (-(q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * L) +
        (-((q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * E)) by ring]
    simp only [add_im, neg_im]; ring
  rw [key]
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hnorm2 : ‖((q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * E)‖ ≤ q ^ 2 * 2 ^ (m + 1) * ((C + 26) / N) := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_mul, norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (stirQ_pos _)]
    simp only [norm_ofNat, mul_one]
    gcongr
  have hnorm1 : ‖-(I1 - I3)‖ ≤ q ^ 2 * Real.exp (N / 2 + 3 / (2 * N)) := by
    rw [norm_neg]
    calc ‖I1 - I3‖ ≤ ‖I1‖ + ‖I3‖ := norm_sub_le _ _
      _ ≤ B * (N / 2) + B * (N / 2) := add_le_add hI1 hI3
      _ = q ^ 2 * Real.exp (N / 2 + 3 / (2 * N)) := by
        rw [hB]; field_simp; ring
  calc |(-(I1 - I3)).im + ((q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * E).im|
      ≤ ‖-(I1 - I3)‖ + ‖((q : ℂ) ^ 2 * (2 * I) ^ (m + 1) * E)‖ :=
        (abs_add_le _ _).trans (add_le_add (abs_im_le_norm _) (abs_im_le_norm _))
    _ ≤ q ^ 2 * Real.exp (N / 2 + 3 / (2 * N)) + q ^ 2 * 2 ^ (m + 1) * ((C + 26) / N) :=
        add_le_add hnorm1 hnorm2
    _ = q ^ 2 / π * (2 ^ (m + 1) * (C + 26) / (m + 1) + Real.exp (N / 2 + 3 / (2 * N))) * π := by
        rw [← hNm]; field_simp; ring

end Lightlike.Asymptotics

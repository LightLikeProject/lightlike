import Lightlike.Asymptotics.ContourIdentity
import Lightlike.Asymptotics.RacahSaddles.KnownSum

/-!
# The contour identity for Kummer's alternating sum

A second run of the contour method of `Lightlike.Asymptotics` on a sum whose value is known
independently: Kummer's sum `Σ_t (−1)^t C(m,t)²` (`m = 2n`), whose value `(−1)^n C(2n,n)` is
`kummer_alternating`.  Its kernel is
  `f(z) = π T(z) / sin(π z)`,  `T(z) = (m! / (Γ(z+1) Γ(m−z+1)))²`
(`kummerKernel`, `kummerT`): `T` is entire, real on the real axis, `(−1)^t T(t) = (−1)^t C(m,t)²`
for `0 ≤ t ≤ m` and `0` at all other integers (a double zero of `1/Γ`).  So the residues of `f` are
the terms of the sum, and `exists_primitive_im_sub` (the generic principal-part argument of
`ContourIdentity.lean`) gives a primitive `Φ` of `f` on the closed upper half-plane minus the
integers with `Σ_t (−1)^t C(m,t)² = −Im (Φ(x₂) − Φ(x₁)) / π` for `x₁ < 0` and `m < x₂`
(`kummerSum_eq_im_primitive`).  This is the analogue of `racahSum_eq_im_primitive`; the pattern of
Gamma functions is different (no numerator Gamma, two pairs of inverse Gammas), so the Racah
kernel is not an instance.
-/

open Complex Set Filter Topology Finset
open scoped Real

namespace Lightlike.Asymptotics

/-- The entire factor of Kummer's kernel, `(m! / (Γ(z+1) Γ(m−z+1)))²`. -/
noncomputable def kummerT (m : ℕ) (z : ℂ) : ℂ :=
  ((m.factorial : ℂ) * (Complex.Gamma (z + 1))⁻¹ * (Complex.Gamma (m - z + 1))⁻¹) ^ 2

/-- Kummer's kernel `π T(z) / sin(π z)`; its residue at `t` is `(−1)^t T(t)`. -/
noncomputable def kummerKernel (m : ℕ) (z : ℂ) : ℂ :=
  π * kummerT m z / Complex.sin (π * z)

/-- `T` is entire. -/
lemma differentiable_kummerT (m : ℕ) : Differentiable ℂ (kummerT m) := by
  intro z
  have hG : ∀ w : ℂ → ℂ, Differentiable ℂ w →
      DifferentiableAt ℂ (fun z => (Complex.Gamma (w z))⁻¹) z :=
    fun w hw => (Complex.differentiable_one_div_Gamma (w z)).comp z (hw z)
  have h1 := hG (fun z => z + 1) (by fun_prop)
  have h2 := hG (fun z => (m : ℂ) - z + 1) (by fun_prop)
  exact (((differentiableAt_const _).mul h1).mul h2).pow 2

/-- `T` is real on the real axis. -/
lemma kummerT_ofReal (m : ℕ) (x : ℝ) :
    kummerT m x = ((((m.factorial : ℝ) * (Real.Gamma (x + 1))⁻¹ * (Real.Gamma (m - x + 1))⁻¹) ^ 2
      : ℝ) : ℂ) := by
  simp only [kummerT, ofReal_pow, ofReal_mul, ofReal_inv, ← Complex.Gamma_ofReal, ofReal_add,
    ofReal_sub, ofReal_natCast, ofReal_one]

/-- Kummer's kernel is real on the real axis. -/
lemma kummerKernel_ofReal_im (m : ℕ) (x : ℝ) : (kummerKernel m x).im = 0 := by
  rw [kummerKernel, kummerT_ofReal, show (π : ℂ) * x = ((π * x : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_sin, ← ofReal_mul, ← ofReal_div, ofReal_im]

/-- `T` at an integer `n`: `(m! · invFact n · invFact (m − n))²`. -/
lemma kummerT_intCast (m : ℕ) (n : ℤ) :
    kummerT m n = (((m.factorial : ℝ) * PhyslibAlpha.Sl2.invFact n *
      PhyslibAlpha.Sl2.invFact ((m : ℤ) - n)) ^ 2 : ℝ) := by
  have h2 : ((m : ℂ) - n + 1) = (((m : ℤ) - n : ℤ) : ℂ) + 1 := by push_cast; ring
  simp only [kummerT, h2, inv_Gamma_intCast_add_one]
  push_cast
  ring

/-- `T` vanishes at integers outside `[0, m]`. -/
lemma kummerT_intCast_of_not_mem (m : ℕ) {n : ℤ} (hn : n < 0 ∨ (m : ℤ) < n) :
    kummerT m n = 0 := by
  rw [kummerT_intCast]
  rcases hn with h | h
  · rw [PhyslibAlpha.Sl2.invFact_of_neg h]; simp
  · rw [PhyslibAlpha.Sl2.invFact_of_neg (by omega : (m : ℤ) - n < 0)]; simp

/-- `T` at a natural `t ≤ m` is `C(m,t)²`. -/
lemma kummerT_natCast (m t : ℕ) (ht : t ≤ m) : kummerT m t = ((m.choose t : ℝ) ^ 2 : ℝ) := by
  have h := kummerT_intCast m (t : ℤ)
  rw [Int.cast_natCast] at h
  rw [h]
  have hm : ((m : ℤ) - t) = ((m - t : ℕ) : ℤ) := by omega
  have h3 : (m.choose t : ℝ) * t.factorial * (m - t).factorial = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ht
  have hpos1 : (t.factorial : ℝ) ≠ 0 := by positivity
  have hpos2 : ((m - t).factorial : ℝ) ≠ 0 := by positivity
  have key : (m.factorial : ℝ) * PhyslibAlpha.Sl2.invFact t *
      PhyslibAlpha.Sl2.invFact ((m - t : ℕ) : ℤ) = m.choose t := by
    rw [PhyslibAlpha.Sl2.invFact_natCast, PhyslibAlpha.Sl2.invFact_natCast, ← h3]
    field_simp
  rw [hm, key]

/-- **The residues of Kummer's kernel**: `(z − n) f(z) → (−1)ⁿ T(n)` at every integer `n`. -/
theorem tendsto_mul_kummerKernel (m : ℕ) (n : ℤ) :
    Tendsto (fun z => (z - n) * kummerKernel m z) (𝓝[≠] (n : ℂ))
      (𝓝 ((-1) ^ n * kummerT m n)) := by
  have hs : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * n) * (π * 1)) n :=
    ((hasDerivAt_id' (n : ℂ)).const_mul (π : ℂ)).csin
  have hcos := cos_pi_mul_intCast n
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : Complex.cos (π * n) * (π * 1) ≠ 0 := by
    rw [hcos, mul_one]
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hπ
  have hT : Tendsto (fun z => (π : ℂ) * kummerT m z) (𝓝[≠] (n : ℂ)) (𝓝 (π * kummerT m n)) :=
    ((continuous_const.mul (differentiable_kummerT m).continuous).tendsto _).mono_left
      nhdsWithin_le_nhds
  have hlim := hT.mul ((hasDerivAt_iff_tendsto_slope.mp hs).inv₀ hne)
  have hval : (π : ℂ) * kummerT m n * (Complex.cos (π * n) * (π * 1))⁻¹ =
      (-1) ^ n * kummerT m n := by
    have h1 : ((-1 : ℂ) ^ n)⁻¹ = (-1) ^ n := by rw [← inv_zpow, inv_neg, inv_one]
    rw [hcos, mul_one, mul_inv, h1]
    field_simp
  rw [hval] at hlim
  refine hlim.congr fun z => ?_
  rw [slope_def_field, sin_pi_mul_intCast, sub_zero, inv_div, kummerKernel]
  ring

/-- **The contour identity for Kummer's sum.** For real `x₁ < 0` and `m < x₂`, Kummer's kernel has a
primitive `Φ` on the closed upper half-plane minus the integers, continuous at `x₁` and `x₂`, with
`Σ_{t ≤ m} (−1)^t C(m,t)² = −Im (Φ(x₂) − Φ(x₁)) / π`. -/
theorem kummerSum_eq_im_primitive (m : ℕ) {x₁ x₂ : ℝ} (h₁ : x₁ < 0) (h₂ : (m : ℝ) < x₂) :
    ∃ Φ : ℂ → ℂ, (∀ z : ℂ, 0 ≤ z.im → (∀ n : ℤ, z ≠ n) →
        HasDerivAt Φ (kummerKernel m z) z) ∧
      ContinuousAt Φ x₁ ∧ ContinuousAt Φ x₂ ∧
      ∑ t ∈ range (m + 1), (-1 : ℝ) ^ t * (m.choose t : ℝ) ^ 2 = -(Φ x₂ - Φ x₁).im / π := by
  classical
  set M : Finset ℤ := (range (m + 1)).map Nat.castEmbedding with hM
  have hMz : ∀ n, n ∉ M → (-1 : ℂ) ^ n * kummerT m n = 0 := by
    intro n hn
    have : n < 0 ∨ (m : ℤ) < n := by
      by_contra hc
      push Not at hc
      apply hn
      obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hc.1
      simp only [hM, Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply]
      exact ⟨t, by omega, rfl⟩
    rw [kummerT_intCast_of_not_mem m this, mul_zero]
  have hc : ∀ n : ℤ, ((-1 : ℂ) ^ n * kummerT m n).im = 0 := by
    intro n
    rw [kummerT_intCast, show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_zpow,
      ← ofReal_mul, ofReal_im]
  have h1 : ∀ n ∈ M, x₁ < n := by
    intro n hn
    simp only [hM, Finset.mem_map, Nat.castEmbedding_apply] at hn
    obtain ⟨t, -, rfl⟩ := hn
    push_cast
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith
  have h2 : ∀ n ∈ M, (n : ℝ) < x₂ := by
    intro n hn
    simp only [hM, Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    push_cast
    have : (t : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp ht
    linarith
  have hdk : ∀ z : ℂ, (∀ n : ℤ, z ≠ n) → DifferentiableAt ℂ (kummerKernel m) z := fun z hz =>
    ((differentiable_kummerT m z).const_mul _).div (by fun_prop) (sin_pi_mul_ne_zero hz)
  obtain ⟨Φ, hΦ, hΦc, him⟩ := exists_primitive_im_sub (c := fun n => (-1) ^ n * kummerT m n)
    (M := M) hdk (tendsto_mul_kummerKernel m) hMz hc (fun x _ => kummerKernel_ofReal_im m x) h1 h2
  refine ⟨Φ, hΦ, hΦc _ (by simp) fun n hn e => (h1 n hn).ne (by exact_mod_cast e),
    hΦc _ (by simp) fun n hn e => (h2 n hn).ne' (by exact_mod_cast e), ?_⟩
  rw [him, neg_mul, neg_neg, mul_div_cancel_left₀ _ Real.pi_ne_zero, hM, sum_map]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htm : t ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  simp only [Nat.castEmbedding_apply, Int.cast_natCast]
  rw [kummerT_natCast m t htm, zpow_natCast,
    show ((-1 : ℂ)) ^ t = (((-1 : ℝ) ^ t : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul, ofReal_re]

end Lightlike.Asymptotics

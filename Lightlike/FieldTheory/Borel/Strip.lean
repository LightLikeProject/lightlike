import Lightlike.FieldTheory.Borel.Transform

/-!
# The strip, the derivatives `b_m` and the local Borel transforms `B_x`

Definitions for the rest of the Nevanlinna–Sokal theorem (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2,
Theorem 1, pp. 5-6, and its proof, Appendix B, pp. 24-25):

* `sokalStrip ρ`, the strip `{t ∈ ℂ | dist(t, ℝ₊) < ρ}` to which the Borel transform continues;
* `taylorRem f a q z = f(z) - ∑_{k<q} a_k z^k`, the rest term `R_q(z)` of eq. (2.4);
* `borelDeriv f a m x c`, the function `b_m(x)` of eq. (B.6) along the line `Re w = c` (the circle
  `Re z⁻¹ = c` in the source's variable `z = w⁻¹`); `b_0` is `borelZero` (`borelDeriv_zero`);
* `borelLocal f a x c t = ∑_m b_m(x) (t - x)^m/m!`, the local Borel transform `B_x(t)` of eq. (B.7).

`sokalHyp_const` is an example of the hypotheses: the constant function `1`.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

/-- **The strip of the Nevanlinna–Sokal theorem**, `{t ∈ ℂ | dist(t, [0, ∞)) < ρ}`. -/
def sokalStrip (ρ : ℝ) : Set ℂ := {t | ∃ x : ℝ, 0 ≤ x ∧ ‖t - x‖ < ρ}

/-- **The rest term** `R_q(z) = f(z) - ∑_{k<q} a_k z^k` of the asymptotic expansion (BGKL eq. (2.4)). -/
noncomputable def taylorRem (f : ℂ → ℂ) (a : ℕ → ℂ) (q : ℕ) (z : ℂ) : ℂ := f z - ∑ k ∈ range q, a k * z ^ k

/-- **The function `b_m`** of BGKL eq. (B.6) along the line `Re w = c`:
`b_m(x) = a_m + (1/2π) ∫ e^{x(c+iy)} (c+iy)^{m-1} R_{m+1}((c+iy)⁻¹) dy`, the source's
`a_m + (1/2πi) ∮ dz e^{x/z} z^{-m-1} R_{m+1}(z)` over the circle `Re z⁻¹ = c`, in `w = z⁻¹`. -/
noncomputable def borelDeriv (f : ℂ → ℂ) (a : ℕ → ℂ) (m : ℕ) (x c : ℝ) : ℂ :=
  a m + ((2 * π : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, cexp (x * ((c : ℂ) + y * I)) * ((c : ℂ) + y * I) ^ ((m : ℤ) - 1) *
    taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹

/-- **The local Borel transform** `B_x(t) = ∑_m b_m(x) (t - x)^m/m!` of BGKL eq. (B.7). -/
noncomputable def borelLocal (f : ℂ → ℂ) (a : ℕ → ℂ) (x c : ℝ) (t : ℂ) : ℂ :=
  ∑' m, borelDeriv f a m x c * (t - x) ^ m / (m ! : ℂ)

/-- `b_0` is the function `borelZero` of eq. (B.3). -/
lemma borelDeriv_zero (f : ℂ → ℂ) (a : ℕ → ℂ) (x c : ℝ) : borelDeriv f a 0 x c = borelZero f (a 0) x c := by
  unfold borelDeriv borelZero borelIntegrand taylorRem
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Nat.cast_zero, zero_sub, zpow_neg_one, zero_add, range_one, sum_singleton, pow_zero, mul_one]
  ring

lemma mem_sokalStrip_of_nonneg {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 ≤ x) : (x : ℂ) ∈ sokalStrip ρ :=
  ⟨x, hx, by simpa using hρ⟩

/-- **The hypotheses are not vacuous**: the constant function `1`, with `a = (1, 0, 0, …)`, satisfies them for
every `R, ρ > 0` with `K = 1`. -/
theorem sokalHyp_const {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) :
    SokalHyp (fun _ => (1 : ℂ)) (Pi.single 0 1) R 1 ρ where
  R_pos := hR
  K_nonneg := zero_le_one
  ρ_pos := hρ
  analytic := differentiableOn_const 1
  rem := by
    intro q z _
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have hs : ∑ k ∈ range q, (Pi.single 0 1 : ℕ → ℂ) k * z ^ k = 1 := by
        rw [Finset.sum_eq_single_of_mem 0 (mem_range.2 hq) fun k _ hk => by simp [hk]]
        simp
      rw [hs, sub_self, norm_zero]
      positivity

end Lightlike.FieldTheory.Borel

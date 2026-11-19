import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Integrals over a union of unit windows

If `0 ≤ f ≤ c k` on the window `(p + k, p + k + 1]`, then
`∫_{(p, p + n]} f dμ ≤ ∑_{k<n} c k · μ (p + k, p + k + 1]` (`setIntegral_Ioc_le_sum`).
-/

open MeasureTheory Set

noncomputable section

namespace Lightlike.Tauberian

theorem setIntegral_Ioc_le_sum (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] {f : ℝ → ℝ} (p : ℝ)
    (c : ℕ → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hint : ∀ n : ℕ, IntegrableOn f (Ioc p (p + n)) μ)
    (hc : ∀ k : ℕ, ∀ x ∈ Ioc (p + k) (p + k + 1), f x ≤ c k) (n : ℕ) :
    ∫ x in Ioc p (p + n), f x ∂μ ≤ ∑ k ∈ Finset.range n, c k * μ.real (Ioc (p + k) (p + k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : Ioc p (p + ((n + 1 : ℕ) : ℝ)) = Ioc p (p + n) ∪ Ioc (p + n) (p + n + 1) := by
      rw [Ioc_union_Ioc_eq_Ioc (by simp [Nat.cast_nonneg]) (by simp)]
      push_cast; ring_nf
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint n) ((hint (n + 1)).mono_set (by
        intro x hx
        exact ⟨by linarith [hx.1, (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)], by push_cast; linarith [hx.2]⟩)),
      Finset.sum_range_succ]
    have h2 : ∫ x in Ioc (p + n) (p + n + 1), f x ∂μ ≤ c n * μ.real (Ioc (p + n) (p + n + 1)) := by
      calc ∫ x in Ioc (p + n) (p + n + 1), f x ∂μ ≤ ∫ x in Ioc (p + n) (p + n + 1), c n ∂μ :=
            setIntegral_mono_on ((hint (n + 1)).mono_set (by
              intro x hx
              exact ⟨by linarith [hx.1, (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)], by push_cast; linarith [hx.2]⟩))
              (integrableOn_const (measure_Ioc_lt_top).ne) measurableSet_Ioc (hc n)
        _ = c n * μ.real (Ioc (p + n) (p + n + 1)) := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
    linarith

end Lightlike.Tauberian

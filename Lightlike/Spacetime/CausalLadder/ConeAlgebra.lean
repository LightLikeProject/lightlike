import Lightlike.Spacetime.Causal.ConeConvex

/-!
# The orthogonal complement of a timelike vector is spacelike

For a Lorentzian form `B`, a causal vector `w` (`B w w ≤ 0`) that is `B`-orthogonal to a timelike
vector `X` is zero. This is the algebraic fact behind the compactness argument of the chart cone
estimate for causal curves (`Lightlike.Causal`): a limit of unit causal vectors that is orthogonal
to the time orientation would be a nonzero causal vector orthogonal to a timelike one.

Supporting lemma, textbook-standard (Wald 1984, Section 8.1 for the cone of timelike vectors); no
catalogue entry.
-/

namespace Lightlike

open Finset

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **A causal vector orthogonal to a timelike vector vanishes**: for a Lorentzian form `B`,
`B X X < 0`, `B w X = 0` and `B w w ≤ 0` give `w = 0`. -/
theorem IsLorentzianForm.eq_zero_of_orthogonal_timelike (h : IsLorentzianForm n B) {X w : V}
    (hX : B X X < 0) (hwX : B w X = 0) (hw : B w w ≤ 0) : w = 0 := by
  obtain ⟨e, he⟩ := h
  rcases n with _ | m
  · rw [IsLorentzianForm.apply_eq_sum e he] at hX
    simp at hX
  · rw [IsLorentzianForm.apply_eq_succ e he] at hX hwX hw
    have hsX : ∑ i : Fin m, e.repr X i.succ ^ 2 < e.repr X 0 ^ 2 := by
      simpa [sq] using (by linarith : ∑ i : Fin m, e.repr X i.succ * e.repr X i.succ <
        e.repr X 0 * e.repr X 0)
    have hsw : ∑ i : Fin m, e.repr w i.succ ^ 2 ≤ e.repr w 0 ^ 2 := by
      simpa [sq] using (by linarith : ∑ i : Fin m, e.repr w i.succ * e.repr w i.succ ≤
        e.repr w 0 * e.repr w 0)
    have hcs : (∑ i : Fin m, e.repr w i.succ * e.repr X i.succ) ^ 2 ≤
        (∑ i : Fin m, e.repr w i.succ ^ 2) * ∑ i : Fin m, e.repr X i.succ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hnn : 0 ≤ ∑ i : Fin m, e.repr X i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hnw : 0 ≤ ∑ i : Fin m, e.repr w i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hdot : ∑ i : Fin m, e.repr w i.succ * e.repr X i.succ = e.repr w 0 * e.repr X 0 := by
      linarith
    have hw0 : e.repr w 0 = 0 := by
      have h1 : (e.repr w 0 * e.repr X 0) ^ 2 ≤ e.repr w 0 ^ 2 * ∑ i : Fin m, e.repr X i.succ ^ 2 := by
        rw [← hdot]
        calc _ ≤ _ := hcs
          _ ≤ _ := mul_le_mul_of_nonneg_right hsw hnn
      by_contra hne
      have hpos : 0 < e.repr w 0 ^ 2 := by positivity
      nlinarith
    have hws : ∀ i : Fin m, e.repr w i.succ = 0 := by
      intro i
      have : ∑ i : Fin m, e.repr w i.succ ^ 2 ≤ 0 := by rw [hw0] at hsw; simpa using hsw
      have h0 : ∑ i : Fin m, e.repr w i.succ ^ 2 = 0 := le_antisymm this hnw
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (e.repr w i.succ)).1 h0 i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    refine e.ext_elem fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hw0
    · simpa using hws j

end Lightlike

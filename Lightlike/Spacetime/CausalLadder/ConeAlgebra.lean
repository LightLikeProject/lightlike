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

namespace Lightlike

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **Two future causal vectors have nonpositive product**: for a Lorentzian form with `B X X < 0`,
`B u u ≤ 0`, `B w w ≤ 0`, `B u X < 0` and `B w X < 0` give `B u w ≤ 0`. The proof perturbs `u` and
`w` by `t X` to future timelike vectors (`IsLorentzianForm.neg_of_futureTimelike`) and lets
`t → 0`. -/
theorem IsLorentzianForm.nonpos_of_futureCausal (h : IsLorentzianForm n B) {u w X : V}
    (hX : B X X < 0) (hu : B u u ≤ 0) (hw : B w w ≤ 0) (hu' : B u X < 0) (hw' : B w X < 0) :
    B u w ≤ 0 := by
  have hsymm := h.symm
  have key : ∀ t : ℝ, 0 < t → B u w + t * (B u X + B X w) + t ^ 2 * B X X < 0 := by
    intro t ht
    have tim : ∀ v : V, B v v ≤ 0 → B v X < 0 → B (v + t • X) (v + t • X) < 0 ∧
        B (v + t • X) X < 0 := by
      intro v hv hvX
      refine ⟨?_, ?_⟩
      · simp only [map_add, map_smul, add_apply, smul_apply,
          smul_eq_mul]
        rw [hsymm X v]
        nlinarith [mul_neg_of_pos_of_neg ht hvX, mul_neg_of_pos_of_neg (mul_pos ht ht) hX]
      · simp only [map_add, map_smul, add_apply, smul_apply,
          smul_eq_mul]
        nlinarith [mul_neg_of_pos_of_neg ht hX]
    obtain ⟨a1, a2⟩ := tim u hu hu'
    obtain ⟨b1, b2⟩ := tim w hw hw'
    have := h.neg_of_futureTimelike hX a1 b1 a2 b2
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul] at this
    nlinarith [this]
  by_contra hpos
  push Not at hpos
  -- choose `t` small so that the perturbation is below `B u w`
  set A : ℝ := B u X + B X w with hA
  set D : ℝ := B X X with hD
  set m : ℝ := |A| + |D| + 1 with hm
  have hmpos : 0 < m := by positivity
  set t : ℝ := min 1 (B u w / (2 * m)) with ht
  have htpos : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ B u w / (2 * m) := min_le_right _ _
  have hk := key t htpos
  have h1 : -(t * A) ≤ t * |A| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs A) htpos.le
    linarith
  have h2 : -(t ^ 2 * D) ≤ t * |D| := by
    have h3 := mul_le_mul_of_nonneg_left (neg_le_abs D) (sq_nonneg t)
    have h4 : t ^ 2 * |D| ≤ t * |D| := by
      have : t ^ 2 ≤ t := by nlinarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg D)
    linarith
  have h3 : t * m ≤ B u w / 2 := by
    have := mul_le_mul_of_nonneg_right ht2 hmpos.le
    have e : B u w / (2 * m) * m = B u w / 2 := by field_simp
    linarith
  have h4 : t * |A| + t * |D| ≤ t * m := by
    have : 0 ≤ t := htpos.le
    nlinarith [abs_nonneg A, abs_nonneg D]
  linarith

/-- **The future causal cone is its own dual.** If `B X X < 0` and `D` has `B u D ≤ 0` for every
future timelike `u` (`B u u < 0`, `B u X < 0`), then `B D D ≤ 0` and `B D X ≤ 0`: `D` lies in the
closure of the future timelike cone. -/
theorem IsLorentzianForm.futureCausal_of_forall_nonpos (h : IsLorentzianForm n B) {X D : V}
    (hX : B X X < 0) (hD : ∀ u : V, B u u < 0 → B u X < 0 → B u D ≤ 0) :
    B D D ≤ 0 ∧ B D X ≤ 0 := by
  have hsymm := h.symm
  have hXD : B X D ≤ 0 := hD X hX hX
  refine ⟨?_, by rw [hsymm D X]; exact hXD⟩
  by_contra hpos
  push Not at hpos
  set a : ℝ := B X X with ha
  set b : ℝ := B X D with hb
  set c : ℝ := B D D with hc
  have hq : 0 < b ^ 2 - a * c := by nlinarith [sq_nonneg b, mul_neg_of_neg_of_pos hX hpos]
  set q : ℝ := b ^ 2 - a * c with hqdef
  set δ : ℝ := q / (c ^ 2 + q) with hδ
  have hδpos : 0 < δ := by positivity
  have hδsq : δ ^ 2 * c ^ 2 < q := by
    have hd : 0 < c ^ 2 + q := by positivity
    rw [hδ, div_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg c, sq_nonneg q, mul_pos hpos hpos, mul_pos (mul_pos hpos hpos) hq]
  set s : ℝ := -b / c + δ with hs
  have hspos : 0 < s := by
    have : 0 ≤ -b / c := div_nonneg (by linarith) hpos.le
    linarith
  have hcs : b + c * s = c * δ := by rw [hs]; field_simp; ring
  refine absurd (hD (X + s • D) ?_ ?_) (not_le.2 ?_)
  · simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [hsymm D X]
    -- `a + 2 b s + c s² = a - b²/c + c δ²`
    have e : a + s * b + s * (b + s * c) = a - b ^ 2 / c + c * δ ^ 2 := by
      rw [hs]; field_simp; ring
    have h5 : c * δ ^ 2 < b ^ 2 / c - a := by
      rw [show b ^ 2 / c - a = (b ^ 2 - a * c) / c by field_simp, lt_div_iff₀ hpos]
      nlinarith [hδsq]
    linarith [e, h5]
  · simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [hsymm D X]
    nlinarith [mul_nonneg hspos.le (neg_nonneg.2 hXD)]
  · simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    nlinarith [mul_pos hpos hδpos]

end Lightlike

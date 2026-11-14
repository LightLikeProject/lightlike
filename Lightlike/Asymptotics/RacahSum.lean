import PhyslibAlpha.QuantumMechanics.AngularMomentum.Wigner3j
import Mathlib

/-!
# Racah's alternating sum and a contiguous relation

Racah's single-sum formula writes the 6j symbol as a prefactor times

  `Σ_t (−1)^t (t+1)! / (∏ᵢ (t − Aᵢ)! ∏ₖ (Bₖ − t)!)`,

with `A₀ … A₃` the four face sums and `B₀ B₁ B₂` the three sums of four edges avoiding an
opposite pair. Here the sum is defined for arbitrary integer data (`rsum`), with `1/n! = 0` for
`n < 0` (Physlib's `invFact`), so that shifted sums need no case distinctions.

The main result is a **contiguous relation** (`rsum_contiguous`): for balanced data
(`Σ Aᵢ = Σ Bₖ`),

  `(B₀ + B₁ − A₀ − A₂ + 1)(B₂ − A₂) S = (B₀ − A₀ + 1)(B₁ − A₀ + 1) S₊ − (A₁ + 1)(A₃ + 1) S₋`,

where `S₊` lowers `A₀` and `B₂` by one, and `S₋` lowers every `A` except `A₂` and every `B` by
one. It is proven by telescoping: with `M(t)` a common factor, the three summands combine to
`G(t+1) − G(t)` for `G(t) = (−1)^t t! / ((t−A₀)! ∏_{i≥1} (t−Aᵢ−1)! ∏ₖ (Bₖ−t)!)`, which vanishes
at both ends. This is the relation that the Biedenharn–Elliott identity with one spin `½`
imposes on the 6j symbol, and it drives the proof of Racah's formula.

The other results: the sum does not depend on the summation range once the range passes some
`Bₖ` (`sum_range_rterm_eq_rsum`), it is invariant under permutations of the `A` and of the `B`
(`rsum_comp`), and it vanishes when some `Bₖ < Aᵢ` (`rsum_eq_zero_of_lt`).
-/

open Finset PhyslibAlpha.Sl2

namespace Lightlike.Asymptotics

/-- `n · (1/n!) = 1/(n−1)!` for every integer `n`; both sides vanish for `n ≤ 0`. -/
lemma intCast_mul_invFact (n : ℤ) : (n : ℝ) * invFact n = invFact (n - 1) := by
  rcases lt_or_ge n 1 with h | h
  · rw [invFact_of_neg (by omega : n - 1 < 0)]
    rcases lt_or_ge n 0 with h' | h'
    · rw [invFact_of_neg h', mul_zero]
    · obtain rfl : n = 0 := by omega
      simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨(n - 1).toNat, by omega⟩
    rw [show ((m : ℤ) + 1 - 1) = m by ring, invFact_natCast,
      show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, invFact_natCast,
      Nat.factorial_succ]
    push_cast
    field_simp

/-- `1/(m−1)! = m · (1/m!)`, in the form used for rewriting. -/
lemma invFact_eq_mul {n : ℤ} (m : ℤ) (h : n = m - 1) : invFact n = (m : ℝ) * invFact m := by
  rw [h, intCast_mul_invFact]

/-- The summand `(−1)^t (t+1)! / (∏ᵢ (t − Aᵢ)! ∏ₖ (Bₖ − t)!)` of Racah's sum. -/
noncomputable def rterm (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (t : ℕ) : ℝ :=
  (-1 : ℝ) ^ t * ((t + 1).factorial : ℝ) *
    ((∏ i, invFact ((t : ℤ) - A i)) * ∏ k, invFact (B k - t))

/-- **Racah's alternating sum** with face sums `A` and quad sums `B`. The range `t ≤ Σₖ Bₖ`
contains every nonzero term when the `Bₖ` are nonnegative. -/
noncomputable def rsum (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) : ℝ :=
  ∑ t ∈ range ((∑ k, B k).toNat + 1), rterm A B t

lemma rterm_eq_zero_of_gt {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} {t : ℕ} (k : Fin 3) (h : B k < t) :
    rterm A B t = 0 := by
  rw [rterm, prod_eq_zero (mem_univ k) (invFact_of_neg (by omega)), mul_zero, mul_zero]

lemma rterm_eq_zero_of_lt {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} {t : ℕ} (i : Fin 4) (h : (t : ℤ) < A i) :
    rterm A B t = 0 := by
  rw [rterm, prod_eq_zero (mem_univ i) (invFact_of_neg (by omega)), zero_mul, mul_zero]

/-- Extending the summation range past some `Bₖ` adds only zero terms. -/
lemma sum_range_rterm_eq {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} {M N : ℕ} (hMN : M ≤ N) (k : Fin 3)
    (hk : B k < M) : ∑ t ∈ range N, rterm A B t = ∑ t ∈ range M, rterm A B t := by
  refine (sum_subset (range_subset_range.mpr hMN) fun t _ ht => ?_).symm
  exact rterm_eq_zero_of_gt k (by simp only [mem_range, not_lt] at ht; omega)

/-- Any summation range that passes some `Bₖ` gives `rsum`. -/
lemma sum_range_rterm_eq_rsum {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} (hB : ∀ k, 0 ≤ B k) {N : ℕ}
    (k : Fin 3) (hk : B k < N) : ∑ t ∈ range N, rterm A B t = rsum A B := by
  have hle : B k ≤ ∑ k, B k :=
    single_le_sum (f := B) (fun k _ => hB k) (mem_univ k)
  have hk' : B k < ((∑ k, B k).toNat + 1 : ℕ) := by omega
  have hm : B k < ((min N ((∑ k, B k).toNat + 1) : ℕ) : ℤ) := by
    rw [Nat.cast_min]; exact lt_min hk hk'
  rw [rsum, sum_range_rterm_eq (min_le_left N _) k hm, sum_range_rterm_eq (min_le_right N _) k hm]

/-- `rsum` vanishes when some `Bₖ < Aᵢ`: every term then has a negative factorial argument. -/
lemma rsum_eq_zero_of_lt {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} (i : Fin 4) (k : Fin 3) (h : B k < A i) :
    rsum A B = 0 := by
  refine sum_eq_zero fun t _ => ?_
  rcases lt_or_ge (t : ℤ) (A i) with ht | ht
  · exact rterm_eq_zero_of_lt i ht
  · exact rterm_eq_zero_of_gt k (by omega)

/-- `rsum` is invariant under permutations of the face sums and of the quad sums. -/
lemma rsum_comp (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 4)) (τ : Equiv.Perm (Fin 3)) :
    rsum (A ∘ σ) (B ∘ τ) = rsum A B := by
  have hB : ∑ k, (B ∘ τ) k = ∑ k, B k := Equiv.sum_comp τ B
  rw [rsum, rsum, hB]
  refine sum_congr rfl fun t _ => ?_
  simp only [rterm, Function.comp_apply]
  rw [Equiv.prod_comp σ (fun i => invFact ((t : ℤ) - A i)),
    Equiv.prod_comp τ (fun k => invFact (B k - t))]

/-! ## The contiguous relation -/

/-- The summand of the sum with every `A` except `A₂` and every `B` lowered by one, shifted to
`u = t + 1`; it vanishes at `u = 0` when `A₂ ≥ 0`. -/
noncomputable def rtermLow (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (u : ℕ) : ℝ :=
  -((-1 : ℝ) ^ u * (u.factorial : ℝ) *
    (invFact ((u : ℤ) - A 0) * invFact ((u : ℤ) - A 1) * invFact ((u : ℤ) - 1 - A 2) *
      invFact ((u : ℤ) - A 3)) * ∏ k, invFact (B k - u))

/-- The telescoping certificate `G(t) = (−1)^t t! / ((t−A₀)! ∏_{i≥1} (t−Aᵢ−1)! ∏ₖ (Bₖ−t)!)`. -/
noncomputable def rcert (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (t : ℕ) : ℝ :=
  (-1 : ℝ) ^ t * (t.factorial : ℝ) *
    (invFact ((t : ℤ) - A 0) * invFact ((t : ℤ) - A 1 - 1) * invFact ((t : ℤ) - A 2 - 1) *
      invFact ((t : ℤ) - A 3 - 1)) * ∏ k, invFact (B k - t)

lemma sum_range_rterm_low (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (hA2 : 0 ≤ A 2) (N : ℕ) :
    ∑ t ∈ range N, rterm ![A 0 - 1, A 1 - 1, A 2, A 3 - 1] ![B 0 - 1, B 1 - 1, B 2 - 1] t =
      ∑ u ∈ range (N + 1), rtermLow A B u := by
  rw [sum_range_succ']
  have h0 : rtermLow A B 0 = 0 := by
    rw [rtermLow, invFact_of_neg (by omega : ((0 : ℕ) : ℤ) - 1 - A 2 < 0)]
    simp
  rw [h0, add_zero]
  refine sum_congr rfl fun t _ => ?_
  simp only [rterm, rtermLow, Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [show (t : ℤ) - (A 0 - 1) = ((t + 1 : ℕ) : ℤ) - A 0 by push_cast; ring,
    show (t : ℤ) - (A 1 - 1) = ((t + 1 : ℕ) : ℤ) - A 1 by push_cast; ring,
    show (t : ℤ) - A 2 = ((t + 1 : ℕ) : ℤ) - 1 - A 2 by push_cast; ring,
    show (t : ℤ) - (A 3 - 1) = ((t + 1 : ℕ) : ℤ) - A 3 by push_cast; ring,
    show B 0 - 1 - (t : ℤ) = B 0 - ((t + 1 : ℕ) : ℤ) by push_cast; ring,
    show B 1 - 1 - (t : ℤ) = B 1 - ((t + 1 : ℕ) : ℤ) by push_cast; ring,
    show B 2 - 1 - (t : ℤ) = B 2 - ((t + 1 : ℕ) : ℤ) by push_cast; ring, pow_succ]
  ring

/-- The three summands of the contiguous relation telescope: `C₀ T − C₊ T₊ + C₋ T₋ = G(t+1) − G(t)`. -/
lemma contiguous_term (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (hbal : ∑ i, A i = ∑ k, B k) (t : ℕ) :
    (((B 0 + B 1 - A 0 - A 2 + 1) * (B 2 - A 2) : ℤ) : ℝ) * rterm A B t -
      (((B 0 - A 0 + 1) * (B 1 - A 0 + 1) : ℤ) : ℝ) *
        rterm ![A 0 - 1, A 1, A 2, A 3] ![B 0, B 1, B 2 - 1] t +
      (((A 1 + 1) * (A 3 + 1) : ℤ) : ℝ) * rtermLow A B t =
      rcert A B (t + 1) - rcert A B t := by
  simp only [rterm, rtermLow, rcert, Fin.prod_univ_four, Fin.prod_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have e0 : invFact ((t : ℤ) - A 0) = ((t : ℝ) - A 0 + 1) * invFact ((t : ℤ) - A 0 + 1) := by
    rw [invFact_eq_mul ((t : ℤ) - A 0 + 1) (by ring)]; push_cast; ring
  have e0' : invFact ((t : ℤ) - (A 0 - 1)) = invFact ((t : ℤ) - A 0 + 1) := by
    congr 1; ring
  have e0'' : invFact (((t + 1 : ℕ) : ℤ) - A 0) = invFact ((t : ℤ) - A 0 + 1) := by
    congr 1; push_cast; ring
  have e1 : invFact ((t : ℤ) - A 1 - 1) = ((t : ℝ) - A 1) * invFact ((t : ℤ) - A 1) := by
    rw [invFact_eq_mul ((t : ℤ) - A 1) (by ring)]; push_cast; ring
  have e2 : invFact ((t : ℤ) - A 2 - 1) = ((t : ℝ) - A 2) * invFact ((t : ℤ) - A 2) := by
    rw [invFact_eq_mul ((t : ℤ) - A 2) (by ring)]; push_cast; ring
  have e2' : invFact ((t : ℤ) - 1 - A 2) = ((t : ℝ) - A 2) * invFact ((t : ℤ) - A 2) := by
    rw [invFact_eq_mul ((t : ℤ) - A 2) (by ring)]; push_cast; ring
  have e3 : invFact ((t : ℤ) - A 3 - 1) = ((t : ℝ) - A 3) * invFact ((t : ℤ) - A 3) := by
    rw [invFact_eq_mul ((t : ℤ) - A 3) (by ring)]; push_cast; ring
  have f1 : ∀ i : Fin 4, invFact (((t + 1 : ℕ) : ℤ) - A i - 1) = invFact ((t : ℤ) - A i) := by
    intro i; congr 1; push_cast; ring
  have g : ∀ k : Fin 3, invFact (B k - ((t + 1 : ℕ) : ℤ)) =
      ((B k : ℝ) - t) * invFact (B k - (t : ℤ)) := by
    intro k; rw [invFact_eq_mul (B k - (t : ℤ)) (by push_cast; ring)]; push_cast; ring
  have g2 : invFact (B 2 - 1 - (t : ℤ)) = ((B 2 : ℝ) - t) * invFact (B 2 - (t : ℤ)) := by
    rw [invFact_eq_mul (B 2 - (t : ℤ)) (by ring)]; push_cast; ring
  rw [e0, e0', e0'', e1, e2, e2', e3, f1 1, f1 2, f1 3, g 0, g 1, g 2, g2, Nat.factorial_succ,
    pow_succ]
  have hbal' : (A 0 : ℝ) + A 1 + A 2 + A 3 = B 0 + B 1 + B 2 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hbal
    simpa [Fin.sum_univ_four, Fin.sum_univ_three] using this
  push_cast
  linear_combination (-(((t : ℝ) - A 2) * ((t : ℝ) + 1) * ((t : ℝ) - A 0 + 1))) *
      ((-1 : ℝ) ^ t * (t.factorial : ℝ) * (invFact ((t : ℤ) - A 0 + 1) *
        invFact ((t : ℤ) - A 1) * invFact ((t : ℤ) - A 2) * invFact ((t : ℤ) - A 3)) *
        (invFact (B 0 - (t : ℤ)) * invFact (B 1 - (t : ℤ)) * invFact (B 2 - (t : ℤ)))) * hbal'

/-- **The contiguous relation of Racah's sum.** For balanced data (`Σ Aᵢ = Σ Bₖ`) with
`Aᵢ ≥ 0` and `Bₖ ≥ 1`,
`(B₀ + B₁ − A₀ − A₂ + 1)(B₂ − A₂) S = (B₀ − A₀ + 1)(B₁ − A₀ + 1) S₊ − (A₁ + 1)(A₃ + 1) S₋`,
with `S₊` lowering `A₀, B₂` and `S₋` lowering `A₀, A₁, A₃, B₀, B₁, B₂` by one. -/
theorem rsum_contiguous (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (hbal : ∑ i, A i = ∑ k, B k)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ k, 1 ≤ B k) :
    (((B 0 + B 1 - A 0 - A 2 + 1) * (B 2 - A 2) : ℤ) : ℝ) * rsum A B =
      (((B 0 - A 0 + 1) * (B 1 - A 0 + 1) : ℤ) : ℝ) *
          rsum ![A 0 - 1, A 1, A 2, A 3] ![B 0, B 1, B 2 - 1] -
        (((A 1 + 1) * (A 3 + 1) : ℤ) : ℝ) *
          rsum ![A 0 - 1, A 1 - 1, A 2, A 3 - 1] ![B 0 - 1, B 1 - 1, B 2 - 1] := by
  set N := (B 0).toNat + 1 with hN
  have hN0 : B 0 < (N + 1 : ℕ) := by omega
  have hBp : ∀ k, 0 ≤ (![B 0, B 1, B 2 - 1] : Fin 3 → ℤ) k := by
    intro k; fin_cases k <;> simp <;> linarith [hB 0, hB 1, hB 2]
  have hBm : ∀ k, 0 ≤ (![B 0 - 1, B 1 - 1, B 2 - 1] : Fin 3 → ℤ) k := by
    intro k; fin_cases k <;> simp <;> linarith [hB 0, hB 1, hB 2]
  have hterm : ∀ t ∈ range (N + 1),
      (((B 0 + B 1 - A 0 - A 2 + 1) * (B 2 - A 2) : ℤ) : ℝ) * rterm A B t -
        (((B 0 - A 0 + 1) * (B 1 - A 0 + 1) : ℤ) : ℝ) *
          rterm ![A 0 - 1, A 1, A 2, A 3] ![B 0, B 1, B 2 - 1] t +
        (((A 1 + 1) * (A 3 + 1) : ℤ) : ℝ) * rtermLow A B t =
      rcert A B (t + 1) - rcert A B t := fun t _ => contiguous_term A B hbal t
  have hG0 : rcert A B 0 = 0 := by
    rw [rcert, invFact_of_neg (by have := hA 1; omega : ((0 : ℕ) : ℤ) - A 1 - 1 < 0)]
    simp
  have hGN : rcert A B (N + 1) = 0 := by
    rw [rcert, prod_eq_zero (mem_univ (0 : Fin 3)) (invFact_of_neg (by omega)), mul_zero]
  have key := sum_congr rfl hterm
  rw [sum_range_sub (rcert A B), hG0, hGN, sub_zero, sum_add_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum] at key
  rw [← sum_range_rterm_eq_rsum (B := B) (fun k => by linarith [hB k]) 0 hN0,
    ← sum_range_rterm_eq_rsum hBp 0 (N := N + 1) (by simp; omega),
    ← sum_range_rterm_eq_rsum hBm 0 (N := N) (by simp; omega), sum_range_rterm_low A B (hA 2)]
  linarith

end Lightlike.Asymptotics

import Lightlike.SpinFoam.EPRLStateSum.NodeCoefThree

/-!
# Mixed-parity node coefficients: the obstruction to a positional Ooguri identity

A tetrahedron with sorted spins `t₀ t₁ t₂ t₃` sits at the node `a` of a 4-simplex with the rotation
`r = a mod 4` (`NodeBasis`). The EPRL label `i` of that node is the coupling label of the legs
`(t_r t_{r+1})`, so its parity is `t_r + t_{r+1}`. This file proves the parity support of
`nodeCoef` and its consequence: if `t₀ + t₂` is odd, the labels `i` allowed at an even rotation
and at an odd rotation have different parity, so the product `N_r(i,l) N_{r'}(i,l')` vanishes
identically for `r` even and `r'` odd. Hence the positional sum over the shared label `i` of a
tetrahedron seen at positions of different parity is `0`, while the Ooguri gluing is `δ_{ll'}`
(`sum_nodeCoef_one_mul` & co.).

* `nodeCoef_even_parity`, `nodeCoef_odd_parity`: parity of the support in `i`;
* `nodeCoef_mul_eq_zero_of_odd`: the vanishing of the mixed product;
* `sum_nodeCoef_even_odd_eq_zero`: the positional sum over `i` is zero.
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam.EPRLStateSum

/-- A nonzero rotation coefficient has the admissible triads `(j₀ j₃ k)` and `(k j₁ j₂)` in the
row label `k`. -/
lemma rot1Recoupling_support_row {j₀ j₁ j₂ j₃ k l : ℕ} (h : rot1Recoupling j₀ j₁ j₂ j₃ k l ≠ 0) :
    Pentagon.Tri j₀ j₃ k ∧ Pentagon.Tri k j₁ j₂ := by
  have h4 : fourRecoupling j₀ j₃ j₁ j₂ k l ≠ 0 := by
    intro h0
    apply h
    unfold rot1Recoupling
    rw [h0]
    ring
  obtain ⟨t1, t2, -, -⟩ := fourRecoupling_support h4
  exact ⟨t1, t2⟩

/-- Rotation `0`: a nonzero coefficient forces `t₀ + t₁ + i` even. -/
lemma nodeCoef_zero_parity {t₀ t₁ t₂ t₃ i l : ℕ} (h : nodeCoef t₀ t₁ t₂ t₃ 0 i l ≠ 0) :
    (t₀ + t₁ + i) % 2 = 0 := by
  have h' : fourRecoupling t₀ t₁ t₂ t₃ i l ≠ 0 := h
  obtain ⟨a, -, -, -⟩ := fourRecoupling_support h'
  exact a.1

/-- Rotation `2`: a nonzero coefficient forces `t₀ + t₁ + i` even. -/
lemma nodeCoef_two_parity {t₀ t₁ t₂ t₃ i l : ℕ} (h : nodeCoef t₀ t₁ t₂ t₃ 2 i l ≠ 0) :
    (t₀ + t₁ + i) % 2 = 0 := by
  have h' : fourRecoupling t₀ t₁ t₂ t₃ i l ≠ 0 := by
    intro h0
    apply h
    show (-1 : ℝ) ^ i * fourRecoupling t₀ t₁ t₂ t₃ i l = 0
    rw [h0, mul_zero]
  obtain ⟨a, -, -, -⟩ := fourRecoupling_support h'
  exact a.1

/-- Rotation `1`: a nonzero coefficient forces `t₁ + t₂ + i` even. -/
lemma nodeCoef_one_parity {t₀ t₁ t₂ t₃ i l : ℕ} (h : nodeCoef t₀ t₁ t₂ t₃ 1 i l ≠ 0) :
    (t₁ + t₂ + i) % 2 = 0 := by
  have h' : ∑ k ∈ range (t₀ + t₁ + 1),
      rot1Recoupling t₀ t₁ t₂ t₃ i k * fourRecoupling t₀ t₁ t₂ t₃ k l ≠ 0 := h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
  obtain ⟨-, a⟩ := rot1Recoupling_support_row (left_ne_zero_of_mul hk)
  have := a.1
  omega

/-- Rotation `3`: a nonzero coefficient forces `t₁ + t₂ + i` even. -/
lemma nodeCoef_three_parity {t₀ t₁ t₂ t₃ i l : ℕ} (h : nodeCoef t₀ t₁ t₂ t₃ 3 i l ≠ 0) :
    (t₁ + t₂ + i) % 2 = 0 := by
  have h' : ∑ k ∈ range (t₂ + t₃ + 1),
      rot1Recoupling t₂ t₃ t₀ t₁ i k * ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l) ≠ 0 := h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
  obtain ⟨a, -⟩ := rot1Recoupling_support_row (left_ne_zero_of_mul hk)
  have := a.1
  omega

/-- Even rotations: the support in `i` has parity `t₀ + t₁`. -/
lemma nodeCoef_even_parity {t₀ t₁ t₂ t₃ r i l : ℕ} (hr : r % 2 = 0)
    (h : nodeCoef t₀ t₁ t₂ t₃ r i l ≠ 0) : (t₀ + t₁ + i) % 2 = 0 := by
  have h4 : r % 4 = 0 ∨ r % 4 = 2 := by omega
  rcases h4 with h4 | h4
  · have e : nodeCoef t₀ t₁ t₂ t₃ r i l = nodeCoef t₀ t₁ t₂ t₃ 0 i l := by
      simp only [nodeCoef, h4]
    rw [e] at h
    exact nodeCoef_zero_parity h
  · have e : nodeCoef t₀ t₁ t₂ t₃ r i l = nodeCoef t₀ t₁ t₂ t₃ 2 i l := by
      simp only [nodeCoef, h4]
    rw [e] at h
    exact nodeCoef_two_parity h

/-- Odd rotations: the support in `i` has parity `t₁ + t₂`. -/
lemma nodeCoef_odd_parity {t₀ t₁ t₂ t₃ r i l : ℕ} (hr : r % 2 = 1)
    (h : nodeCoef t₀ t₁ t₂ t₃ r i l ≠ 0) : (t₁ + t₂ + i) % 2 = 0 := by
  have h4 : r % 4 = 1 ∨ r % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · have e : nodeCoef t₀ t₁ t₂ t₃ r i l = nodeCoef t₀ t₁ t₂ t₃ 1 i l := by
      simp only [nodeCoef, h4]
    rw [e] at h
    exact nodeCoef_one_parity h
  · have e : nodeCoef t₀ t₁ t₂ t₃ r i l = nodeCoef t₀ t₁ t₂ t₃ 3 i l := by
      simp only [nodeCoef, h4]
    rw [e] at h
    exact nodeCoef_three_parity h

/-- **Mixed parity vanishing**: if `t₀ + t₂` is odd, the node coefficients of an even rotation `r`
and an odd rotation `r'` have disjoint supports in the label `i`, so their product is `0`. -/
theorem nodeCoef_mul_eq_zero_of_odd {t₀ t₁ t₂ t₃ r r' : ℕ} (hr : r % 2 = 0) (hr' : r' % 2 = 1)
    (hodd : (t₀ + t₂) % 2 = 1) (i l l' : ℕ) :
    nodeCoef t₀ t₁ t₂ t₃ r i l * nodeCoef t₀ t₁ t₂ t₃ r' i l' = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  have a := nodeCoef_even_parity hr h1
  have b := nodeCoef_odd_parity hr' h2
  omega

/-- **The positional sum over a shared label vanishes** for a tetrahedron with `t₀ + t₂` odd seen
at rotations of different parity: for every range `S` of labels, `Σ_{i ∈ S} N_r(i,l) N_{r'}(i,l') = 0`,
whereas the intrinsic Ooguri gluing would give `δ_{ll'}`. -/
theorem sum_nodeCoef_even_odd_eq_zero {t₀ t₁ t₂ t₃ r r' : ℕ} (hr : r % 2 = 0) (hr' : r' % 2 = 1)
    (hodd : (t₀ + t₂) % 2 = 1) (S : Finset ℕ) (l l' : ℕ) :
    ∑ i ∈ S, nodeCoef t₀ t₁ t₂ t₃ r i l * nodeCoef t₀ t₁ t₂ t₃ r' i l' = 0 :=
  sum_eq_zero fun i _ => nodeCoef_mul_eq_zero_of_odd hr hr' hodd i l l'

end Lightlike.SpinFoam.EPRLStateSum

import Lightlike.SpinFoam.EPRLStateSum.NodeCoef

/-!
# Orthogonality of the node coefficients for the rotations `1` and `3`

`nodeCoef t₀ t₁ t₂ t₃ r i l` (`NodeCoef.lean`) is, for `r = 1, 3`, a product of two orthogonal
matrices (the rotation matrix `rot1Recoupling` and the recoupling matrix `fourRecoupling`, the
latter with the sign `(-1)^k` for `r = 3`). This file proves that the product is orthogonal in the
label `i`:

* `fourRecoupling_support`: a nonzero recoupling coefficient has four admissible triads;
* `rot1Recoupling_support`: the same for the rotation matrix;
* `sum_comp_orth`: composition of an orthogonal matrix with a row vector of coefficients supported
  on its admissible rows;
* `sum_nodeCoef_one_mul`, `sum_nodeCoef_three_mul`: `Σ_l N_r(i,l) N_r(i',l) = δ_{ii'}` on the
  admissible labels of the rotated legs.
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

/-- A nonzero recoupling coefficient `⟨ι^{(12)k} | ι^{(13)l}⟩` has the four admissible triads
`(j₁ j₂ k)`, `(k j₃ j₄)`, `(j₁ j₃ l)`, `(l j₂ j₄)`. -/
lemma fourRecoupling_support {j₁ j₂ j₃ j₄ k l : ℕ} (h : fourRecoupling j₁ j₂ j₃ j₄ k l ≠ 0) :
    Pentagon.Tri j₁ j₂ k ∧ Pentagon.Tri k j₃ j₄ ∧ Pentagon.Tri j₁ j₃ l ∧
      Pentagon.Tri l j₂ j₄ := by
  have h6 : sixJSym j₁ j₂ k j₄ j₃ l ≠ 0 := by
    intro h0
    apply h
    unfold fourRecoupling
    rw [h0, mul_zero]
  obtain ⟨t1, t2, t3, t4⟩ := Pentagon.tri_of_sixJSym_ne_zero h6
  unfold Pentagon.Tri at *
  omega

/-- A nonzero rotation coefficient has the admissible triads `(j₀ j₃ k)`, `(k j₁ j₂)`, `(j₀ j₁ l)`
and `(l j₃ j₂)`. -/
lemma rot1Recoupling_support {j₀ j₁ j₂ j₃ k l : ℕ} (h : rot1Recoupling j₀ j₁ j₂ j₃ k l ≠ 0) :
    Pentagon.Tri j₀ j₁ l ∧ Pentagon.Tri l j₂ j₃ := by
  have h4 : fourRecoupling j₀ j₃ j₁ j₂ k l ≠ 0 := by
    intro h0
    apply h
    unfold rot1Recoupling
    rw [h0]
    ring
  obtain ⟨-, -, t3, t4⟩ := fourRecoupling_support h4
  unfold Pentagon.Tri at *
  omega

/-- Composition of an orthogonal matrix `R` (rows `k`, admissible when `P k`) with coefficient
vectors supported on the admissible rows: `Σ_l (Σ_k a_k R_{kl}) (Σ_k a'_k R_{kl}) = Σ_k a_k a'_k`. -/
lemma sum_comp_orth {S T : Finset ℕ} (a a' : ℕ → ℝ) (R : ℕ → ℕ → ℝ) (P : ℕ → Prop)
    [DecidablePred P]
    (horth : ∀ k ∈ T, ∀ k' ∈ T, ∑ l ∈ S, R k l * R k' l = if k = k' ∧ P k then 1 else 0)
    (hsupp : ∀ k ∈ T, a k ≠ 0 → P k) :
    ∑ l ∈ S, (∑ k ∈ T, a k * R k l) * (∑ k' ∈ T, a' k' * R k' l) = ∑ k ∈ T, a k * a' k := by
  have h1 : ∀ l, (∑ k ∈ T, a k * R k l) * (∑ k' ∈ T, a' k' * R k' l) =
      ∑ k ∈ T, ∑ k' ∈ T, (a k * a' k') * (R k l * R k' l) := fun l => by
    rw [sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun k' _ => by ring
  simp only [h1]
  rw [sum_comm]
  have h2 : ∀ k ∈ T, ∑ l ∈ S, ∑ k' ∈ T, (a k * a' k') * (R k l * R k' l) =
      ∑ k' ∈ T, (a k * a' k') * (if k = k' ∧ P k then 1 else 0) := fun k hk => by
    rw [sum_comm]
    refine sum_congr rfl fun k' hk' => ?_
    rw [← mul_sum, horth k hk k' hk']
  rw [sum_congr rfl h2]
  refine sum_congr rfl fun k hk => ?_
  by_cases hP : P k
  · simp [hP, hk]
  · have : a k = 0 := by
      by_contra hne
      exact hP (hsupp k hk hne)
    simp [this]

/-- **Orthogonality for rotation `1`**: `Σ_l N₁(i,l) N₁(i',l) = δ_{ii'}` for the admissible
labels `i` of the legs `(t₁ t₂)(t₃ t₀)`. -/
theorem sum_nodeCoef_one_mul (t₀ t₁ t₂ t₃ i i' : ℕ) :
    ∑ l ∈ range (t₀ + t₂ + 1), nodeCoef t₀ t₁ t₂ t₃ 1 i l * nodeCoef t₀ t₁ t₂ t₃ 1 i' l =
      if i = i' ∧ Pentagon.Tri t₀ t₃ i ∧ Pentagon.Tri i t₁ t₂ then 1 else 0 := by
  have hN : ∀ j l, nodeCoef t₀ t₁ t₂ t₃ 1 j l = ∑ k ∈ range (t₀ + t₁ + 1),
      rot1Recoupling t₀ t₁ t₂ t₃ j k * fourRecoupling t₀ t₁ t₂ t₃ k l := fun j l => rfl
  simp only [hN]
  rw [sum_comp_orth (S := range (t₀ + t₂ + 1)) (T := range (t₀ + t₁ + 1))
    (fun k => rot1Recoupling t₀ t₁ t₂ t₃ i k) (fun k => rot1Recoupling t₀ t₁ t₂ t₃ i' k)
    (fun k l => fourRecoupling t₀ t₁ t₂ t₃ k l) (fun k => Pentagon.Tri t₀ t₁ k ∧ Pentagon.Tri k t₂ t₃)
    (fun k _ k' _ => sum_fourRecoupling_mul t₀ t₁ t₂ t₃ k k')
    (fun k _ hk => rot1Recoupling_support hk)]
  exact sum_rot1Recoupling_mul t₀ t₁ t₂ t₃ i i'

/-- **Orthogonality for rotation `3`**: `Σ_l N₃(i,l) N₃(i',l) = δ_{ii'}` for the admissible
labels `i` of the legs `(t₃ t₀)(t₁ t₂)`. -/
theorem sum_nodeCoef_three_mul (t₀ t₁ t₂ t₃ i i' : ℕ) :
    ∑ l ∈ range (t₀ + t₂ + 1), nodeCoef t₀ t₁ t₂ t₃ 3 i l * nodeCoef t₀ t₁ t₂ t₃ 3 i' l =
      if i = i' ∧ Pentagon.Tri t₂ t₁ i ∧ Pentagon.Tri i t₃ t₀ then 1 else 0 := by
  have hN : ∀ j l, nodeCoef t₀ t₁ t₂ t₃ 3 j l = ∑ k ∈ range (t₂ + t₃ + 1),
      rot1Recoupling t₂ t₃ t₀ t₁ j k * ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l) :=
    fun j l => rfl
  simp only [hN]
  rw [sum_comp_orth (S := range (t₀ + t₂ + 1)) (T := range (t₂ + t₃ + 1))
    (fun k => rot1Recoupling t₂ t₃ t₀ t₁ i k) (fun k => rot1Recoupling t₂ t₃ t₀ t₁ i' k)
    (fun k l => (-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l)
    (fun k => Pentagon.Tri t₀ t₁ k ∧ Pentagon.Tri k t₂ t₃)
    (fun k _ k' _ => by
      have h := sum_fourRecoupling_mul t₀ t₁ t₂ t₃ k k'
      have : ∀ l ∈ range (t₀ + t₂ + 1), ((-1 : ℝ) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l) *
          ((-1) ^ k' * fourRecoupling t₀ t₁ t₂ t₃ k' l) =
          ((-1) ^ k * (-1) ^ k') * (fourRecoupling t₀ t₁ t₂ t₃ k l *
            fourRecoupling t₀ t₁ t₂ t₃ k' l) := fun l _ => by ring
      rw [sum_congr rfl this, ← mul_sum, h]
      by_cases hkk : k = k'
      · subst hkk
        rw [negOnePow_mul_self]
        simp
      · simp [hkk])
    (fun k _ hk => by
      obtain ⟨t3, t4⟩ := rot1Recoupling_support hk
      unfold Pentagon.Tri at *
      exact ⟨by omega, by omega⟩)]
  exact sum_rot1Recoupling_mul t₂ t₃ t₀ t₁ i i'

end Lightlike.SpinFoam.EPRLStateSum

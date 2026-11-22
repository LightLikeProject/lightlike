module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!
# The 3j symbol with a zero spin, and sums over projections

Preparatory material for the orthogonality relations of the 3j and 6j symbols
(`ThreeJOrth.lean`) in Physlib's doubled-spin parametrisation `threeJ j₁ j₂ j₃ m₁ m₂ m₃`
(`jᵢ ∈ ℕ` twice the spin, `mᵢ ∈ ℤ` twice the projection).

## Main results

* `PhyslibAlpha.Sl2.threeJ_zero_left`: the closed form
  `(0 b c; m₁ m₂ m₃) = δ_{m₁,0} δ_{c,b} δ_{m₃,-m₂} (-1)^((b-m₂)/2) / √(b+1)`.
* `PhyslibAlpha.Sl2.sum_Icc_parity`: a sum over `μ ∈ [-j, j]` of a function that vanishes at the
  wrong parity is a sum over `α ∈ [0, j]` with `μ = j - 2α`.
* `PhyslibAlpha.Sl2.sum_Icc_neg`: the reflection `μ ↦ -μ` of a symmetric range.
-/

@[expose] public section

open Finset

namespace PhyslibAlpha.Sl2

/-- `sixSum 0 0 a 0 0 b` has the single term `z = 0`. -/
lemma sixSum_zero_zero (a b : ℤ) : sixSum 0 0 a 0 0 b = invFact (-a) * invFact b := by
  unfold sixSum
  rw [finsum_eq_single _ 0]
  · simp [sixTerm, invFact]
  · intro z hz
    unfold sixTerm
    rcases lt_or_gt_of_ne hz with h | h
    · rw [show invFact (z - 0) = 0 by simp [invFact]; omega]
      ring
    · rw [show invFact (0 - z) = 0 by simp [invFact]; omega]
      ring

/-- **The 3j symbol with a zero first spin** (doubled units):
`(0 b c; m₁ m₂ m₃) = δ_{m₁,0} δ_{c,b} δ_{m₃,-m₂} (-1)^((b-m₂)/2) / √(b+1)` for an admissible
`m₂`, and `0` otherwise. -/
lemma threeJ_zero_left (b c : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ 0 b c m₁ m₂ m₃ =
      if m₁ = 0 ∧ c = b ∧ m₃ = -m₂ ∧ -(b : ℤ) ≤ m₂ ∧ m₂ ≤ b ∧ ((b : ℤ) - m₂) % 2 = 0 then
        (-1) ^ ((((b : ℤ) - m₂) / 2).toNat) / Real.sqrt ((b : ℝ) + 1)
      else 0 := by
  unfold threeJ
  by_cases h : Adm3 0 b c m₁ m₂ m₃
  · obtain ⟨hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    have hm₁ : m₁ = 0 := by omega
    have hc : b = c := by omega
    have hm₃ : m₃ = -m₂ := by omega
    subst hm₁ hc hm₃
    rw [ite_eq_left ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩,
      ite_eq_left ⟨rfl, rfl, rfl, h3, h4, h8⟩]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((b : ℤ) - m₂) = 2 * k := ⟨(((b : ℤ) - m₂) / 2).toNat, by omega⟩
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, ((b : ℤ) + m₂) = 2 * k' := ⟨(((b : ℤ) + m₂) / 2).toNat, by omega⟩
    have hkk : k + k' = b := by omega
    have hR : reggeJ 0 b b 0 m₂ (-m₂) = ![![b, 0, 0], ![0, k, k'], ![0, k', k]] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [reggeJ] <;> omega
    have htk : (((b : ℤ) - m₂) / 2).toNat = k := by omega
    rw [threeJR, hR, htk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.prod_univ_three, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one,
      add_zero, zero_add, Nat.cast_zero, sub_zero]
    rw [sixSum_zero_zero, show -((k' : ℤ) - b) = (k : ℤ) by omega, invFact_natCast,
      invFact_natCast, Nat.factorial_succ]
    have hk0 : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hk'0 : (0 : ℝ) < k'.factorial := by exact_mod_cast Nat.factorial_pos k'
    have hb0 : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
    have hb1 : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have hsq : Real.sqrt ((b.factorial : ℝ) * ((k.factorial : ℝ) * (k'.factorial : ℝ)) *
        ((k'.factorial : ℝ) * (k.factorial : ℝ)) / (((b + 1) * b.factorial : ℕ) : ℝ)) =
        (k.factorial : ℝ) * k'.factorial / Real.sqrt ((b : ℝ) + 1) := by
      rw [show (b.factorial : ℝ) * ((k.factorial : ℝ) * (k'.factorial : ℝ)) *
          ((k'.factorial : ℝ) * (k.factorial : ℝ)) / (((b + 1) * b.factorial : ℕ) : ℝ) =
          ((k.factorial : ℝ) * k'.factorial) ^ 2 / ((b : ℝ) + 1) by
            rw [div_eq_div_iff (by positivity) (by positivity)]
            push_cast
            ring,
        Real.sqrt_div' _ hb1.le, Real.sqrt_sq (by positivity)]
    rw [hsq]
    field_simp
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨rfl, rfl, rfl, h1, h2, h3⟩
    exact h ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A sum over doubled projections `μ ∈ [-j, j]` of a function vanishing at the wrong parity is a
sum over `α ∈ [0, j]` with `μ = j - 2α`. -/
lemma sum_Icc_parity (j : ℕ) (F : ℤ → ℝ) (hF : ∀ μ, ((j : ℤ) - μ) % 2 ≠ 0 → F μ = 0) :
    ∑ μ ∈ Icc (-(j : ℤ)) j, F μ = ∑ α ∈ range (j + 1), F ((j : ℤ) - 2 * α) := by
  rw [← sum_image (s := range (j + 1)) (g := fun α : ℕ => (j : ℤ) - 2 * α) (f := F)]
  · symm
    apply sum_subset
    · intro μ hμ
      simp only [mem_image, mem_range] at hμ
      obtain ⟨α, hα, rfl⟩ := hμ
      simp only [mem_Icc]
      omega
    · intro μ hμ hn
      apply hF
      intro hp
      apply hn
      simp only [mem_Icc] at hμ
      simp only [mem_image, mem_range]
      exact ⟨(((j : ℤ) - μ) / 2).toNat, by omega, by omega⟩
  · intro α _ β _ h
    simp only at h
    omega

/-- Reflection `μ ↦ -μ` of a symmetric range. -/
lemma sum_Icc_neg (j : ℕ) (F : ℤ → ℝ) :
    ∑ μ ∈ Icc (-(j : ℤ)) j, F μ = ∑ μ ∈ Icc (-(j : ℤ)) j, F (-μ) := by
  refine sum_nbij' (fun μ => -μ) (fun μ => -μ) ?_ ?_ ?_ ?_ ?_ <;> intro μ hμ <;>
    simp only [mem_Icc, neg_neg] at hμ ⊢ <;> omega

end PhyslibAlpha.Sl2

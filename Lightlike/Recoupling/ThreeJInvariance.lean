import Lightlike.Recoupling.Invariant

/-!
# The 3j symbols are invariant tensors

Physlib constructs the Clebsch–Gordan coefficients as the components of the coupled vectors
`|J, M⟩ ∈ V(m) ⊗ V(n)`, which form a lowering string under the diagonal action of `sl₂`
(`PhyslibAlpha.Sl2.tensorF_coupledVec`). Taking components of `J₋ |J, M⟩` in the product basis,
with `J₊` adjoint to `J₋` for the invariant inner product (`tensorForm_tensorE`), gives the
lowering recursion of the Clebsch–Gordan coefficients (`cg_lower`). Converted to Physlib's general
3j symbol `threeJ` it is the recursion

`rc j₁ m₁ (m₁+2, m₂, m₃) + rc j₂ m₂ (m₁, m₂+2, m₃) + rc j₃ m₃ (m₁, m₂, m₃+2) = 0`

for all spins and projections (`threeJ_lower`; doubled units, `rc j m = √((j - m)(j + m + 2))`),
i.e. the total lowering operator annihilates the 3j tensor. With `m ↦ -m` the raising recursion
follows (`threeJ_raise`), and with them the invariance of the 3j symbol (`isInv_threeJT`).

## References

- A. R. Edmonds, *Angular Momentum in Quantum Mechanics* (Princeton, 1957), eq. (3.7.13): the
  recursion relations of the 3j symbols.
- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439, §5.3: Wigner's 3jm symbol.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon
open scoped TensorProduct

namespace Lightlike.Recoupling

/-- The raising operator on Physlib's normalised basis: `E u₀ = 0` and
`E u_a = √(a (n - a + 1)) u_{a-1}` for `1 ≤ a ≤ n`. -/
lemma rhoE_normVec (n a : ℕ) (ha : a ≤ n) :
    (ρE : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n a) =
      if a = 0 then 0 else Real.sqrt ((a : ℝ) * ((n : ℝ) - a + 1)) • normVec n (a - 1) := by
  rcases a with _ | a
  · simp [normVec, ρE_vNat_zero]
  · rw [ρE_normVec_succ (by omega), ite_eq_right (Nat.succ_ne_zero a)]
    simp only [Nat.add_sub_cancel]
    congr 2
    push_cast
    ring

variable {m n : ℕ}

/-- **The lowering recursion of the Clebsch–Gordan coefficients** in Physlib's parameters:
`√((l+1)(J-l)) ⟨a b | k, l+1⟩ = √(a(m-a+1)) ⟨a-1, b | k, l⟩ + √(b(n-b+1)) ⟨a, b-1 | k, l⟩`
with `J = m + n - 2k` (the terms with `a = 0` or `b = 0` absent). -/
lemma cg_lower (hmn : 0 < m + n) {k l a b : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (ha : a ≤ m) (hb : b ≤ n) :
    Real.sqrt (((l : ℝ) + 1) * (((m + n - 2 * k : ℕ) : ℝ) - l)) *
        cgCoefficient m n k (l + 1) a b =
      (if a = 0 then 0 else
        Real.sqrt ((a : ℝ) * ((m : ℝ) - a + 1)) * cgCoefficient m n k l (a - 1) b) +
      (if b = 0 then 0 else
        Real.sqrt ((b : ℝ) * ((n : ℝ) - b + 1)) * cgCoefficient m n k l a (b - 1)) := by
  have hF : tensorF m n (coupledVec m n k l) =
      Real.sqrt (((l : ℝ) + 1) * (((m + n - 2 * k : ℕ) : ℝ) - l)) • coupledVec m n k (l + 1) := by
    rcases lt_or_eq_of_le hl with hl' | hl'
    · exact tensorF_coupledVec hkm hkn hl'
    · subst hl'
      have h0 : stringVec (K := ℝ) m n k (m + n - 2 * k + 1) = 0 :=
        stringVec_eq_zero hmn hkm hkn (by omega)
      rw [coupledVec, map_smul, tensorF_stringVec, h0, smul_zero]
      simp
  have key := tensorForm_tensorE (normVec m a ⊗ₜ normVec n b) (coupledVec m n k l)
  rw [hF, map_smul, smul_eq_mul] at key
  unfold cgCoefficient
  rw [← key, tensorE, diagEnd_tmul, rhoE_normVec m a ha, rhoE_normVec n b hb]
  split_ifs <;>
    simp [map_add, LinearMap.add_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- `rc j (j - 2a) = 2 √(a (j - a + 1))`. -/
lemma rc_sub_two_mul (j a : ℕ) :
    rc j ((j : ℤ) - 2 * a) = 2 * Real.sqrt ((a : ℝ) * ((j : ℝ) - a + 1)) := by
  unfold rc
  rw [show ((((j : ℤ) - ((j : ℤ) - 2 * a)) * ((j : ℤ) + ((j : ℤ) - 2 * a) + 2) : ℤ) : ℝ) =
      4 * ((a : ℝ) * ((j : ℝ) - a + 1)) by push_cast; ring,
    Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `rc` vanishes outside the open ladder. -/
lemma rc_eq_zero_of {j : ℕ} {m : ℤ} (h : m ≤ -(j : ℤ) - 2 ∨ (j : ℤ) ≤ m) : rc j m = 0 := by
  unfold rc
  apply Real.sqrt_eq_zero'.mpr
  have : ((j : ℤ) - m) * ((j : ℤ) + m + 2) ≤ 0 := by
    rcases h with h | h
    · exact mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    · exact mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
  exact_mod_cast this

/-- The admissibility conditions of the lowering recursion's main case. -/
def LowerAdm (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) : Prop :=
  m₁ + m₂ + m₃ = -2 ∧ -(j₁ : ℤ) ≤ m₁ ∧ m₁ ≤ j₁ ∧ -(j₂ : ℤ) ≤ m₂ ∧ m₂ ≤ j₂ ∧
    -(j₃ : ℤ) ≤ m₃ ∧ m₃ ≤ j₃ ∧ ((j₁ : ℤ) - m₁) % 2 = 0 ∧ ((j₂ : ℤ) - m₂) % 2 = 0 ∧
      ((j₃ : ℤ) - m₃) % 2 = 0 ∧ j₃ ≤ j₁ + j₂ ∧ j₁ ≤ j₂ + j₃ ∧ j₂ ≤ j₁ + j₃ ∧
        (j₁ + j₂ + j₃) % 2 = 0

/-- **The lowering recursion of the 3j symbols** (doubled units, all spins and projections):
`rc j₁ m₁ (m₁+2, m₂, m₃) + rc j₂ m₂ (m₁, m₂+2, m₃) + rc j₃ m₃ (m₁, m₂, m₃+2) = 0`. -/
theorem threeJ_lower (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    rc j₁ m₁ * threeJ j₁ j₂ j₃ (m₁ + 2) m₂ m₃ + rc j₂ m₂ * threeJ j₁ j₂ j₃ m₁ (m₂ + 2) m₃ +
      rc j₃ m₃ * threeJ j₁ j₂ j₃ m₁ m₂ (m₃ + 2) = 0 := by
  by_cases H : LowerAdm j₁ j₂ j₃ m₁ m₂ m₃
  swap
  · -- every term vanishes
    have t1 : rc j₁ m₁ * threeJ j₁ j₂ j₃ (m₁ + 2) m₂ m₃ = 0 := by
      by_cases hA : Adm3 j₁ j₂ j₃ (m₁ + 2) m₂ m₃
      · rw [rc_eq_zero_of (by unfold LowerAdm at H; omega), zero_mul]
      · rw [threeJ_of_not hA, mul_zero]
    have t2 : rc j₂ m₂ * threeJ j₁ j₂ j₃ m₁ (m₂ + 2) m₃ = 0 := by
      by_cases hA : Adm3 j₁ j₂ j₃ m₁ (m₂ + 2) m₃
      · rw [rc_eq_zero_of (by unfold LowerAdm at H; omega), zero_mul]
      · rw [threeJ_of_not hA, mul_zero]
    have t3 : rc j₃ m₃ * threeJ j₁ j₂ j₃ m₁ m₂ (m₃ + 2) = 0 := by
      by_cases hA : Adm3 j₁ j₂ j₃ m₁ m₂ (m₃ + 2)
      · rw [rc_eq_zero_of (by unfold LowerAdm at H; omega), zero_mul]
      · rw [threeJ_of_not hA, mul_zero]
    rw [t1, t2, t3]
    ring
  obtain ⟨hs, h1, h2, h3, h4, h5, h6, p1, p2, p3, t1, t2, t3, tp⟩ := H
  -- Physlib's parameters
  obtain ⟨a, rfl, ha⟩ : ∃ a : ℕ, m₁ = (j₁ : ℤ) - 2 * a ∧ a ≤ j₁ :=
    ⟨(((j₁ : ℤ) - m₁) / 2).toNat, by omega, by omega⟩
  obtain ⟨b, rfl, hb⟩ : ∃ b : ℕ, m₂ = (j₂ : ℤ) - 2 * b ∧ b ≤ j₂ :=
    ⟨(((j₂ : ℤ) - m₂) / 2).toNat, by omega, by omega⟩
  obtain ⟨k, rfl, hk1, hk2⟩ : ∃ k : ℕ, j₃ = j₁ + j₂ - 2 * k ∧ k ≤ j₁ ∧ k ≤ j₂ :=
    ⟨(j₁ + j₂ - j₃) / 2, by omega, by omega, by omega⟩
  obtain ⟨l, rfl, hl⟩ : ∃ l : ℕ, m₃ = -(((j₁ + j₂ - 2 * k : ℕ) : ℤ) - 2 * l) ∧
      l ≤ j₁ + j₂ - 2 * k :=
    ⟨((((j₁ + j₂ - 2 * k : ℕ) : ℤ) + m₃) / 2).toNat, by omega, by omega⟩
  have hmn : 0 < j₁ + j₂ := by omega
  set J := j₁ + j₂ - 2 * k with hJ
  have hrec := cg_lower hmn hk1 hk2 hl ha hb
  -- the Clebsch–Gordan coefficients as 3j symbols
  set σ : ℝ := (-1) ^ (j₁ + k + l) * Real.sqrt ((J + 1 : ℕ) : ℝ) with hσ
  have hσ0 : σ ≠ 0 := by
    rw [hσ]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Real.sqrt_pos.mpr (by positivity)).ne'
  have cA : a ≠ 0 → cgCoefficient j₁ j₂ k l (a - 1) b =
      σ * threeJ j₁ j₂ J ((j₁ : ℤ) - 2 * a + 2) ((j₂ : ℤ) - 2 * b) (-((J : ℤ) - 2 * l)) := by
    intro ha0
    rw [cgCoefficient_eq_wigner3j hmn hk1 hk2 hl (by omega) hb,
      wigner3j_eq_threeJ hk1 hk2 hl (by omega) hb, hσ]
    congr 2
    push_cast [Nat.cast_sub (show 1 ≤ a by omega)]
    ring
  have cB : b ≠ 0 → cgCoefficient j₁ j₂ k l a (b - 1) =
      σ * threeJ j₁ j₂ J ((j₁ : ℤ) - 2 * a) ((j₂ : ℤ) - 2 * b + 2) (-((J : ℤ) - 2 * l)) := by
    intro hb0
    rw [cgCoefficient_eq_wigner3j hmn hk1 hk2 hl ha (by omega),
      wigner3j_eq_threeJ hk1 hk2 hl ha (by omega), hσ]
    congr 2
    push_cast [Nat.cast_sub (show 1 ≤ b by omega)]
    ring
  -- the third coefficient
  have hc3 : rc J (-((J : ℤ) - 2 * l)) =
      2 * Real.sqrt (((l : ℝ) + 1) * (((J : ℕ) : ℝ) - l)) := by
    have e : -((J : ℤ) - 2 * l) = (J : ℤ) - 2 * ((J - l : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hl]
      ring
    rw [e, rc_sub_two_mul]
    congr 2
    push_cast [Nat.cast_sub hl]
    ring
  rw [rc_sub_two_mul, rc_sub_two_mul, hc3]
  -- the three terms of the recursion
  have hA' : (if a = 0 then (0 : ℝ) else
      Real.sqrt ((a : ℝ) * ((j₁ : ℝ) - a + 1)) * cgCoefficient j₁ j₂ k l (a - 1) b) =
      σ * (Real.sqrt ((a : ℝ) * ((j₁ : ℝ) - a + 1)) *
        threeJ j₁ j₂ J ((j₁ : ℤ) - 2 * a + 2) ((j₂ : ℤ) - 2 * b) (-((J : ℤ) - 2 * l))) := by
    by_cases ha0 : a = 0
    · subst ha0; simp
    · rw [ite_eq_right ha0, cA ha0]; ring
  have hB' : (if b = 0 then (0 : ℝ) else
      Real.sqrt ((b : ℝ) * ((j₂ : ℝ) - b + 1)) * cgCoefficient j₁ j₂ k l a (b - 1)) =
      σ * (Real.sqrt ((b : ℝ) * ((j₂ : ℝ) - b + 1)) *
        threeJ j₁ j₂ J ((j₁ : ℤ) - 2 * a) ((j₂ : ℤ) - 2 * b + 2) (-((J : ℤ) - 2 * l))) := by
    by_cases hb0 : b = 0
    · subst hb0; simp
    · rw [ite_eq_right hb0, cB hb0]; ring
  have hL : Real.sqrt (((l : ℝ) + 1) * ((J : ℝ) - l)) * cgCoefficient j₁ j₂ k (l + 1) a b =
      -σ * (Real.sqrt (((l : ℝ) + 1) * ((J : ℝ) - l)) *
        threeJ j₁ j₂ J ((j₁ : ℤ) - 2 * a) ((j₂ : ℤ) - 2 * b) (-((J : ℤ) - 2 * l) + 2)) := by
    rcases lt_or_eq_of_le hl with hl' | hl'
    · rw [cgCoefficient_eq_wigner3j hmn hk1 hk2 (by omega) ha hb,
        wigner3j_eq_threeJ hk1 hk2 (by omega) ha hb, hσ,
        show j₁ + k + (l + 1) = (j₁ + k + l) + 1 by ring, pow_succ]
      simp only [← hJ]
      have e : -((J : ℤ) - 2 * ((l + 1 : ℕ) : ℤ)) = -((J : ℤ) - 2 * l) + 2 := by
        push_cast; ring
      rw [e]
      ring
    · rw [hl', sub_self, mul_zero, Real.sqrt_zero]
      ring
  have hrec' : Real.sqrt (((l : ℝ) + 1) * ((J : ℝ) - l)) * cgCoefficient j₁ j₂ k (l + 1) a b =
      _ := hrec
  rw [hL, hA', hB'] at hrec'
  apply mul_left_cancel₀ hσ0
  linear_combination (-2 : ℝ) * hrec'

/-- `(j₁ j₂ j₃; m₁ m₂ m₃) = (-1)^((j₁+j₂+j₃)/2) (j₁ j₂ j₃; -m₁ -m₂ -m₃)`. -/
lemma threeJ_eq_neg (j₁ j₂ j₃ : ℕ) (x y z : ℤ) :
    threeJ j₁ j₂ j₃ x y z = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₁ j₂ j₃ (-x) (-y) (-z) := by
  rw [threeJ_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **The raising recursion of the 3j symbols** (doubled units, all spins and projections):
`rc j₁ (m₁-2) (m₁-2, m₂, m₃) + rc j₂ (m₂-2) (m₁, m₂-2, m₃) + rc j₃ (m₃-2) (m₁, m₂, m₃-2) = 0`. -/
theorem threeJ_raise (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    rc j₁ (m₁ - 2) * threeJ j₁ j₂ j₃ (m₁ - 2) m₂ m₃ +
        rc j₂ (m₂ - 2) * threeJ j₁ j₂ j₃ m₁ (m₂ - 2) m₃ +
      rc j₃ (m₃ - 2) * threeJ j₁ j₂ j₃ m₁ m₂ (m₃ - 2) = 0 := by
  have h := threeJ_lower j₁ j₂ j₃ (-m₁) (-m₂) (-m₃)
  have hr : ∀ (j : ℕ) (x : ℤ), rc j (x - 2) = rc j (-x) := fun j x => by
    rw [← rc_neg_sub_two j (-x), neg_neg]
  rw [threeJ_eq_neg j₁ j₂ j₃ (m₁ - 2), threeJ_eq_neg j₁ j₂ j₃ m₁ (m₂ - 2),
    threeJ_eq_neg j₁ j₂ j₃ m₁ m₂ (m₃ - 2), hr, hr, hr]
  rw [show -(m₁ - 2) = -m₁ + 2 by ring, show -(m₂ - 2) = -m₂ + 2 by ring,
    show -(m₃ - 2) = -m₃ + 2 by ring]
  linear_combination (-1 : ℝ) ^ ((j₁ + j₂ + j₃) / 2) * h

/-- The 3j symbol `(j₁ j₂ j₃; m₀ m₁ m₂)` as a tensor with three legs. -/
noncomputable def threeJT (j₁ j₂ j₃ : ℕ) (m : Fin 3 → ℤ) : ℝ := threeJ j₁ j₂ j₃ (m 0) (m 1) (m 2)

/-- **The 3j symbol is an invariant tensor** with three incoming legs. -/
theorem isInv_threeJT (j₁ j₂ j₃ : ℕ) :
    IsInv ![j₁, j₂, j₃] ![false, false, false] (threeJT j₁ j₂ j₃) where
  supp m h i := by
    have := adm3_of_threeJ_ne_zero h
    fin_cases i <;> simp [AdmProj] <;> omega
  weight m h := by
    have := adm3_of_threeJ_ne_zero h
    simp [Fin.sum_univ_three]
    omega
  raise m := by
    have := threeJ_raise j₁ j₂ j₃ (m 0) (m 1) (m 2)
    simp only [Fin.sum_univ_three, raiseAt, threeJT]
    simp
    linarith
  lower m := by
    have := threeJ_lower j₁ j₂ j₃ (m 0) (m 1) (m 2)
    simp only [Fin.sum_univ_three, raiseAt, threeJT]
    simp
    linarith

end Lightlike.Recoupling

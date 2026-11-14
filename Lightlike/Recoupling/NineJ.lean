import Lightlike.Recoupling.Ladder
import PhyslibAlpha.QuantumMechanics.AngularMomentum.NineJ

/-!
# The 9j symbol as a sum over projections

Physlib defines the 9j symbol through 6j symbols,
`{j₁₁ j₁₂ j₁₃; j₂₁ j₂₂ j₂₃; j₃₁ j₃₂ j₃₃} = Σ_x (-1)^x (x + 1) {6j} {6j} {6j}` in doubled spins
(`nineJSym`). This file proves its form as a sum over the projections of products of six 3j
symbols, one for each row and each column (DLMF 34.6.1):

`{9j} = Σ_{μ} (j₁₁ j₁₂ j₁₃; μ₁₁ μ₁₂ μ₁₃) (j₂₁ j₂₂ j₂₃; μ₂₁ μ₂₂ μ₂₃) (j₃₁ j₃₂ j₃₃; μ₃₁ μ₃₂ μ₃₃)
  (j₁₁ j₂₁ j₃₁; μ₁₁ μ₂₁ μ₃₁) (j₁₂ j₂₂ j₃₂; μ₁₂ μ₂₂ μ₃₂) (j₁₃ j₂₃ j₃₃; μ₁₃ μ₂₃ μ₃₃)`.

This is the form in which the 9j symbol arises from recoupling four angular momenta. The proof
evaluates the closed Möbius ladder of three rungs (`Lightlike/Recoupling/Ladder.lean`) in two ways:
as a sum of three 6j symbols (`mobius_eq`), which is the 9j symbol up to a sign, and term by term as
a sum of products of 3j symbols, which become the six row and column symbols after the 3j
symmetries.

## Main results

- `mobius_three_eq_nineJSym`: the Möbius ladder of three rungs is a 9j symbol.
- `nineJSym_eq_sum_threeJ`: the row/column form of the 9j symbol.
- `nineJSym_eq_zero_of_not_tri₃`: the 9j symbol vanishes unless its third column is an admissible
  triad.

## References

- DLMF, §34.6, eq. 34.6.1.
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton (1957), §6.4.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.Recoupling

/-- Powers of `-1` depend only on the parity of the exponent. -/
lemma neg_one_pow_congr_mod {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℝ) ^ m = (-1) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-- **The Möbius ladder of three rungs is a 9j symbol**: with rails `(a₀ a₁ a₂ b₀)`,
`(b₀ b₁ b₂ a₀)` and rungs `(c₀ c₁ c₂)`, it equals
`(-1)^{S/2 + b₀} {a₀ b₂ c₂; a₁ c₁ a₂; c₀ b₁ b₀}`, where `S` is the sum of the nine spins. -/
theorem mobius_three_eq_nineJSym (a b c : ℕ → ℕ) (ha : a 3 = b 0) (hb : b 3 = a 0) :
    mobius 3 a b c = (-1) ^ ((a 0 + a 1 + a 2 + b 0 + b 1 + b 2 + c 0 + c 1 + c 2) / 2 + b 0) *
      nineJSym (a 0) (b 2) (c 2) (a 1) (c 1) (a 2) (c 0) (b 1) (b 0) := by
  rw [mobius_eq 2 a b c ha hb, nineJSym, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [prod_range_succ, prod_range_zero, one_mul, rungFactor, ha, hb]
  have e1 : sixJSym (a 1) (b 1) x (b 2) (a 2) (c 1) =
      sixJSym (b 2) (c 1) (b 1) (a 1) x (a 2) := by
    rw [sixJSym_swap₂₃ (b 2) (b 1) (c 1) (a 1) (a 2) x,
      ← sixJSym_flip₁₂ (b 2) (b 1) (c 1) (a 1) (a 2) x,
      sixJSym_flip₂₃ (a 1) (a 2) (c 1) (b 2) (b 1) x]
  have e2 : sixJSym (a 2) (b 2) x (a 0) (b 0) (c 2) =
      sixJSym (c 2) (a 2) (b 0) x (a 0) (b 2) := by
    rw [sixJSym_swap₁₂ (a 2) (c 2) (b 0) (a 0) x (b 2),
      sixJSym_swap₂₃ (a 2) (b 0) (c 2) (a 0) (b 2) x,
      sixJSym_flip₂₃ (a 2) (b 2) x (a 0) (b 0) (c 2)]
  rw [sixJSym_flip₂₃ (a 0) (b 0) x (b 1) (a 1) (c 0), e1, e2]
  by_cases h₁ : sixJSym (a 0) (a 1) (c 0) (b 1) (b 0) x = 0
  · simp [h₁]
  by_cases h₂ : sixJSym (b 2) (c 1) (b 1) (a 1) x (a 2) = 0
  · simp [h₂]
  by_cases h₃ : sixJSym (c 2) (a 2) (b 0) x (a 0) (b 2) = 0
  · simp [h₃]
  obtain ⟨t₁, t₂, t₃, t₄⟩ := tri_of_sixJSym_ne_zero h₁
  obtain ⟨t₅, t₆, -, -⟩ := tri_of_sixJSym_ne_zero h₂
  obtain ⟨t₇, t₈, -, -⟩ := tri_of_sixJSym_ne_zero h₃
  have key : (-1 : ℝ) ^ ((a 0 + b 0 + x) / 2) * (-1) ^ (x + (a 1 + b 0 + c 0 + x) / 2) *
      (-1) ^ (x + (a 2 + b 1 + c 1 + x) / 2) * (-1) ^ (x + (b 0 + b 2 + c 2 + x) / 2) =
      (-1) ^ ((a 0 + a 1 + a 2 + b 0 + b 1 + b 2 + c 0 + c 1 + c 2) / 2 + b 0) * (-1) ^ x := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    apply neg_one_pow_congr_mod
    unfold Tri at *
    omega
  simp only [t₂, ↓reduceIte]
  linear_combination ((x : ℝ) + 1) * (sixJSym (a 0) (a 1) (c 0) (b 1) (b 0) x *
    sixJSym (b 2) (c 1) (b 1) (a 1) x (a 2) * sixJSym (c 2) (a 2) (b 0) x (a 0) (b 2)) * key

/-- The closed Möbius ladder of three rungs as an explicit sum over the nine projections. -/
lemma mobius_three_eq_sum (a b c : ℕ → ℕ) :
    mobius 3 a b c = ∑ p ∈ pairBox (a 0) (b 0), ∑ r ∈ pairBox (a 2) (b 2),
      ∑ m₂ ∈ Icc (-(c 2 : ℤ)) (c 2), ∑ q ∈ pairBox (a 1) (b 1), ∑ m₁ ∈ Icc (-(c 1 : ℤ)) (c 1),
        ∑ m₀ ∈ Icc (-(c 0 : ℤ)) (c 0),
          edgeSign (a 0) p.1 * edgeSign (b 0) p.2 *
            (edgeSign (c 0) m₀ * threeJ (a 0) (a 1) (c 0) (-p.1) q.1 m₀ *
              threeJ (b 0) (b 1) (c 0) (-p.2) q.2 (-m₀)) *
            (edgeSign (a 1) q.1 * edgeSign (b 1) q.2) *
            (edgeSign (c 1) m₁ * threeJ (a 1) (a 2) (c 1) (-q.1) r.1 m₁ *
              threeJ (b 1) (b 2) (c 1) (-q.2) r.2 (-m₁)) *
            (edgeSign (a 2) r.1 * edgeSign (b 2) r.2) *
            (edgeSign (c 2) m₂ * threeJ (a 2) (a 3) (c 2) (-r.1) p.2 m₂ *
              threeJ (b 2) (b 3) (c 2) (-r.2) p.1 (-m₂)) := by
  unfold mobius
  refine sum_congr rfl fun p hp => ?_
  have hd : ∀ q, ∑ x ∈ pairBox (a 0) (b 0), pairDelta p x *
      (edgeSign (a 0) x.1 * edgeSign (b 0) x.2) * rungKernel (a 0) (a 1) (b 0) (b 1) (c 0) x q =
      edgeSign (a 0) p.1 * edgeSign (b 0) p.2 * rungKernel (a 0) (a 1) (b 0) (b 1) (c 0) p q := by
    intro q
    simp only [pairDelta, ite_mul, one_mul, zero_mul, sum_ite_eq', hp, ↓reduceIte]
  simp only [ladder, rung]
  simp only [hd]
  simp only [rungKernel, sum_mul, mul_sum]

/-- One term of the three-rung Möbius ladder, with the rails `(j₁₁ j₂₁ j₂₃ j₃₃)` and
`(j₃₃ j₃₂ j₁₂ j₁₁)` and the rungs `(j₃₁ j₂₂ j₁₃)`, as one term of the row/column form of the 9j
symbol. -/
lemma mobius_term_eq (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℕ) (p₁ p₂ q₁ q₂ r₁ r₂ m₀ m₁ m₂ : ℤ) :
    (-1 : ℝ) ^ ((j₁₁ + j₂₁ + j₂₃ + j₃₃ + j₃₂ + j₁₂ + j₃₁ + j₂₂ + j₁₃) / 2 + j₃₃) *
      (edgeSign j₁₁ p₁ * edgeSign j₃₃ p₂ *
        (edgeSign j₃₁ m₀ * threeJ j₁₁ j₂₁ j₃₁ (-p₁) q₁ m₀ * threeJ j₃₃ j₃₂ j₃₁ (-p₂) q₂ (-m₀)) *
        (edgeSign j₂₁ q₁ * edgeSign j₃₂ q₂) *
        (edgeSign j₂₂ m₁ * threeJ j₂₁ j₂₃ j₂₂ (-q₁) r₁ m₁ * threeJ j₃₂ j₁₂ j₂₂ (-q₂) r₂ (-m₁)) *
        (edgeSign j₂₃ r₁ * edgeSign j₁₂ r₂) *
        (edgeSign j₁₃ m₂ * threeJ j₂₃ j₃₃ j₁₃ (-r₁) p₂ m₂ * threeJ j₁₂ j₁₁ j₁₃ (-r₂) p₁ (-m₂))) =
    threeJ j₁₁ j₁₂ j₁₃ (-p₁) r₂ m₂ * threeJ j₂₁ j₂₂ j₂₃ q₁ (-m₁) (-r₁) *
      threeJ j₃₁ j₃₂ j₃₃ m₀ (-q₂) p₂ * (threeJ j₁₁ j₂₁ j₃₁ (-p₁) q₁ m₀ *
        threeJ j₁₂ j₂₂ j₃₂ r₂ (-m₁) (-q₂) * threeJ j₁₃ j₂₃ j₃₃ m₂ (-r₁) p₂) := by
  have e₃ := threeJ_neg j₃₃ j₃₂ j₃₁ p₂ (-q₂) m₀
  have e₂ := threeJ_neg j₂₁ j₂₃ j₂₂ q₁ (-r₁) (-m₁)
  have e₁ := threeJ_neg j₁₂ j₁₁ j₁₃ r₂ (-p₁) m₂
  simp only [neg_neg] at e₁ e₂ e₃
  rw [e₁, e₂, e₃, threeJ_swap₁₃ j₃₁ j₃₂ j₃₃ m₀ (-q₂) p₂, threeJ_swap₂₃ j₂₁ j₂₂ j₂₃ q₁ (-m₁) (-r₁),
    threeJ_swap j₁₁ j₁₂ j₁₃ (-p₁) r₂ m₂, ← threeJ_cycle j₃₂ j₁₂ j₂₂ (-q₂) r₂ (-m₁),
    threeJ_cycle j₁₃ j₂₃ j₃₃ m₂ (-r₁) p₂]
  by_cases h₁ : threeJ j₁₁ j₁₂ j₁₃ (-p₁) r₂ m₂ = 0
  · simp [h₁]
  by_cases h₂ : threeJ j₂₁ j₂₂ j₂₃ q₁ (-m₁) (-r₁) = 0
  · simp [h₂]
  by_cases h₃ : threeJ j₃₁ j₃₂ j₃₃ m₀ (-q₂) p₂ = 0
  · simp [h₃]
  by_cases h₄ : threeJ j₁₁ j₂₁ j₃₁ (-p₁) q₁ m₀ = 0
  · simp [h₄]
  by_cases h₅ : threeJ j₁₂ j₂₂ j₃₂ r₂ (-m₁) (-q₂) = 0
  · simp [h₅]
  by_cases h₆ : threeJ j₁₃ j₂₃ j₃₃ m₂ (-r₁) p₂ = 0
  · simp [h₆]
  obtain ⟨s₁, -, -, -, -, -, -, a₁, a₂, a₃, -, -, -, t₁⟩ := adm3_of_threeJ_ne_zero h₁
  obtain ⟨s₂, -, -, -, -, -, -, a₄, a₅, a₆, -, -, -, t₂⟩ := adm3_of_threeJ_ne_zero h₂
  obtain ⟨s₃, -, -, -, -, -, -, a₇, a₈, a₉, -, -, -, t₃⟩ := adm3_of_threeJ_ne_zero h₃
  obtain ⟨s₄, -⟩ := adm3_of_threeJ_ne_zero h₄
  obtain ⟨s₅, -⟩ := adm3_of_threeJ_ne_zero h₅
  obtain ⟨s₆, -⟩ := adm3_of_threeJ_ne_zero h₆
  have hn : (-1 : ℝ) ≠ 0 := by norm_num
  have key : (-1 : ℝ) ^ ((j₁₁ + j₂₁ + j₂₃ + j₃₃ + j₃₂ + j₁₂ + j₃₁ + j₂₂ + j₁₃) / 2 + j₃₃) *
      (edgeSign j₁₁ p₁ * edgeSign j₃₃ p₂ * edgeSign j₃₁ m₀ * edgeSign j₂₁ q₁ * edgeSign j₃₂ q₂ *
        edgeSign j₂₂ m₁ * edgeSign j₂₃ r₁ * edgeSign j₁₂ r₂ * edgeSign j₁₃ m₂) *
      ((-1) ^ ((j₃₃ + j₃₂ + j₃₁) / 2) * (-1) ^ ((j₃₁ + j₃₂ + j₃₃) / 2) *
        (-1) ^ ((j₂₁ + j₂₃ + j₂₂) / 2) * (-1) ^ ((j₂₁ + j₂₂ + j₂₃) / 2) *
        (-1) ^ ((j₁₂ + j₁₁ + j₁₃) / 2) * (-1) ^ ((j₁₁ + j₁₂ + j₁₃) / 2)) = 1 := by
    unfold edgeSign
    simp only [← zpow_natCast, ← zpow_add₀ hn]
    rw [neg_one_zpow_congr (q := 0) (by push_cast; omega), zpow_zero]
  linear_combination (threeJ j₁₁ j₁₂ j₁₃ (-p₁) r₂ m₂ * threeJ j₂₁ j₂₂ j₂₃ q₁ (-m₁) (-r₁) *
      threeJ j₃₁ j₃₂ j₃₃ m₀ (-q₂) p₂ * (threeJ j₁₁ j₂₁ j₃₁ (-p₁) q₁ m₀ *
        threeJ j₁₂ j₂₂ j₃₂ r₂ (-m₁) (-q₂) * threeJ j₁₃ j₂₃ j₃₃ m₂ (-r₁) p₂)) * key

/-- The 9j symbol as a sum over the projections of products of six 3j symbols, one for each row
and each column (DLMF 34.6.1, in doubled spins). -/
theorem nineJSym_eq_sum_threeJ (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℕ) :
    nineJSym j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      ∑ μ₁₁ ∈ Icc (-(j₁₁ : ℤ)) j₁₁, ∑ μ₁₂ ∈ Icc (-(j₁₂ : ℤ)) j₁₂, ∑ μ₁₃ ∈ Icc (-(j₁₃ : ℤ)) j₁₃,
      ∑ μ₂₁ ∈ Icc (-(j₂₁ : ℤ)) j₂₁, ∑ μ₂₂ ∈ Icc (-(j₂₂ : ℤ)) j₂₂, ∑ μ₂₃ ∈ Icc (-(j₂₃ : ℤ)) j₂₃,
      ∑ μ₃₁ ∈ Icc (-(j₃₁ : ℤ)) j₃₁, ∑ μ₃₂ ∈ Icc (-(j₃₂ : ℤ)) j₃₂, ∑ μ₃₃ ∈ Icc (-(j₃₃ : ℤ)) j₃₃,
        threeJ j₁₁ j₁₂ j₁₃ μ₁₁ μ₁₂ μ₁₃ * threeJ j₂₁ j₂₂ j₂₃ μ₂₁ μ₂₂ μ₂₃ *
          threeJ j₃₁ j₃₂ j₃₃ μ₃₁ μ₃₂ μ₃₃ * (threeJ j₁₁ j₂₁ j₃₁ μ₁₁ μ₂₁ μ₃₁ *
            threeJ j₁₂ j₂₂ j₃₂ μ₁₂ μ₂₂ μ₃₂ * threeJ j₁₃ j₂₃ j₃₃ μ₁₃ μ₂₃ μ₃₃) := by
  set a : ℕ → ℕ := fun n => match n with | 0 => j₁₁ | 1 => j₂₁ | 2 => j₂₃ | _ => j₃₃ with ha
  set b : ℕ → ℕ := fun n => match n with | 0 => j₃₃ | 1 => j₃₂ | 2 => j₁₂ | _ => j₁₁ with hb
  set c : ℕ → ℕ := fun n => match n with | 0 => j₃₁ | 1 => j₂₂ | _ => j₁₃ with hc
  have hm := mobius_three_eq_nineJSym a b c rfl rfl
  rw [mobius_three_eq_sum] at hm
  simp only [ha, hb, hc] at hm
  have hS : (-1 : ℝ) ^ ((j₁₁ + j₂₁ + j₂₃ + j₃₃ + j₃₂ + j₁₂ + j₃₁ + j₂₂ + j₁₃) / 2 + j₃₃) *
      (-1) ^ ((j₁₁ + j₂₁ + j₂₃ + j₃₃ + j₃₂ + j₁₂ + j₃₁ + j₂₂ + j₁₃) / 2 + j₃₃) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [← one_mul (nineJSym _ _ _ _ _ _ _ _ _), ← hS, mul_assoc, ← hm]
  simp only [mul_sum]
  simp only [← sum_product']
  refine sum_nbij' (fun x => (-x.1.1, x.2.1.2, x.2.2.1, x.2.2.2.1.1, -x.2.2.2.2.1, -x.2.1.1,
      x.2.2.2.2.2, -x.2.2.2.1.2, x.1.2))
    (fun μ => ((-μ.1, μ.2.2.2.2.2.2.2.2), (-μ.2.2.2.2.2.1, μ.2.1), μ.2.2.1,
      (μ.2.2.2.1, -μ.2.2.2.2.2.2.2.1), -μ.2.2.2.2.1, μ.2.2.2.2.2.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨p₁, p₂⟩, ⟨r₁, r₂⟩, m₂, ⟨q₁, q₂⟩, m₁, m₀⟩ h
    simp only [pairBox, mem_product, mem_Icc] at h ⊢
    omega
  · rintro ⟨μ₁₁, μ₁₂, μ₁₃, μ₂₁, μ₂₂, μ₂₃, μ₃₁, μ₃₂, μ₃₃⟩ h
    simp only [pairBox, mem_product, mem_Icc] at h ⊢
    omega
  · rintro ⟨⟨p₁, p₂⟩, ⟨r₁, r₂⟩, m₂, ⟨q₁, q₂⟩, m₁, m₀⟩ -
    simp
  · rintro ⟨μ₁₁, μ₁₂, μ₁₃, μ₂₁, μ₂₂, μ₂₃, μ₃₁, μ₃₂, μ₃₃⟩ -
    simp
  · rintro ⟨⟨p₁, p₂⟩, ⟨r₁, r₂⟩, m₂, ⟨q₁, q₂⟩, m₁, m₀⟩ -
    exact mobius_term_eq j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ p₁ p₂ q₁ q₂ r₁ r₂ m₀ m₁ m₂

/-- **Selection rule of the 9j symbol**: it vanishes unless its third column `(j₁₃ j₂₃ j₃₃)` is an
admissible triad. -/
theorem nineJSym_eq_zero_of_not_tri₃ (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℕ)
    (h : ¬ Tri j₁₃ j₂₃ j₃₃) : nineJSym j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ = 0 := by
  have h0 : ∀ μ₁ μ₂ μ₃ : ℤ, threeJ j₁₃ j₂₃ j₃₃ μ₁ μ₂ μ₃ = 0 := fun μ₁ μ₂ μ₃ => by
    by_contra hne
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h₁, h₂, h₃, h₄⟩ := adm3_of_threeJ_ne_zero hne
    exact h ⟨h₄, h₁, h₂, h₃⟩
  rw [nineJSym_eq_sum_threeJ]
  simp [h0]

end Lightlike.Recoupling

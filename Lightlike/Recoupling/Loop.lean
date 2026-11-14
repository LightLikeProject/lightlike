import Lightlike.Recoupling.Span

/-!
# The projector of an internal tetrahedron and the loop of an internal triangle

Two identities used when a spin foam is cut open along internal faces.

* `fourJ_neg`: **reversal of all projections** changes an intertwiner by the sign
  `(-1)^((j₁+j₂+j₃+j₄)/2)`. Equivalently, the invariant bilinear form applied to all four legs
  leaves it unchanged (`fourJ_twist`).
* `sum_fourJT_mul_perm`: **the sum `Σ_k ι^{(k)} ⊗ ι^{(k)}` does not depend on the order of the
  legs** used to define the basis, since both orders give orthonormal bases of the same invariant
  space (`eq_sum_fourJ`).
* `loop_fourJ`: **the loop identity**
  `Σ_j (2j+1) Σ_x Σ_μ ι^{(x)}_{h μ} ι^{(x)}_{h' μ} = δ_{h h'}` for intertwiners of `(a b c j)` in the
  channel `(a b)(c j)`: a strand of spin `j` closing on itself through the projector of a
  tetrahedron, summed over `j` with the dimension, is the identity on the other three legs. It is
  the completeness of the 3j symbols, used twice.

## References

- A. R. Edmonds, *Angular Momentum in Quantum Mechanics* (Princeton, 1957), §3.7,
  eqs. (3.7.7), (3.7.8): the orthogonality and completeness of the 3j symbols.
- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439, §5.4: orthonormal bases of the
  invariant space of four spins.
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.Recoupling

/-- **Reversal of the projections**:
`ι^{(k)}_{-m₁ -m₂ -m₃ -m₄} = (-1)^((j₁+j₂+j₃+j₄)/2) ι^{(k)}_{m₁ m₂ m₃ m₄}` (doubled units). -/
theorem fourJ_neg (j₁ j₂ j₃ j₄ k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ j₁ j₂ j₃ j₄ k (-m₁) (-m₂) (-m₃) (-m₄) =
      (-1) ^ ((j₁ + j₂ + j₃ + j₄) / 2) * fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ := by
  unfold fourJ
  rw [sum_Icc_neg]
  simp only [Finset.mul_sum]
  refine sum_congr rfl fun μ _ => ?_
  rw [neg_neg, threeJ_neg]
  rw [show threeJ k j₃ j₄ μ (-m₃) (-m₄) = threeJ k j₃ j₄ (-(-μ)) (-m₃) (-m₄) by rw [neg_neg],
    threeJ_neg]
  by_cases h1 : Tri j₁ j₂ k ∧ AdmProj k μ
  · by_cases h2 : Tri k j₃ j₄
    · obtain ⟨⟨t1, t2, t3, t4⟩, -, -, p⟩ := h1
      obtain ⟨u1, u2, u3, u4⟩ := h2
      have hs : ((k : ℤ) - -μ) / 2 = ((k : ℤ) - μ) / 2 + μ := by omega
      have e1 : (-1 : ℝ) ^ μ = (-1) ^ k := by
        rw [← zpow_natCast]; exact neg_one_zpow_congr (by omega)
      have e2 : (-1 : ℝ) ^ ((j₁ + j₂ + k) / 2) * (-1) ^ ((k + j₃ + j₄) / 2) =
          (-1) ^ ((j₁ + j₂ + j₃ + j₄) / 2) * (-1) ^ k := by
        rw [← pow_add, ← pow_add]
        exact Lightlike.PR.neg_one_pow_congr (by omega)
      have e3 : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
      rw [hs, zpow_add₀ (by norm_num), e1]
      linear_combination (Real.sqrt ((k : ℝ) + 1) * (-1) ^ (((k : ℤ) - μ) / 2) *
        threeJ j₁ j₂ k m₁ m₂ μ * threeJ k j₃ j₄ (-μ) m₃ m₄ * (-1) ^ k) * e2 +
        (Real.sqrt ((k : ℝ) + 1) * (-1) ^ (((k : ℤ) - μ) / 2) *
        threeJ j₁ j₂ k m₁ m₂ μ * threeJ k j₃ j₄ (-μ) m₃ m₄ * (-1) ^ ((j₁ + j₂ + j₃ + j₄) / 2)) * e3
    · have h0 : threeJ k j₃ j₄ (-μ) m₃ m₄ = 0 := by
        by_contra h
        exact h2 (by
          have := adm3_of_threeJ_ne_zero h
          unfold Tri; omega)
      rw [h0]; ring
  · rw [threeJ_eq_zero_of_not h1]; ring

/-- `Σ_{j ≤ N} (j + 1) Σ_μ (x c j; ξ h μ)(x c j; ξ' h' μ) = δ_{ξξ'} δ_{hh'}` for admissible
`ξ, h` and any `N ≥ x + c`: the completeness of the 3j symbols over a longer range of `j`. -/
lemma sum_threeJ_complete_le (x c N : ℕ) (hN : x + c ≤ N) {ξ h : ℤ} (hξ : AdmProj x ξ)
    (hh : AdmProj c h) (ξ' h' : ℤ) :
    ∑ j ∈ range (N + 1), ∑ μ ∈ Icc (-(j : ℤ)) j,
      ((j : ℝ) + 1) * (threeJ x c j ξ h μ * threeJ x c j ξ' h' μ) =
      if ξ = ξ' ∧ h = h' then 1 else 0 := by
  rw [← sum_threeJ_complete x c hξ hh ξ' h']
  symm
  apply sum_subset (range_subset_range.mpr (by omega))
  intro j _ hj
  refine sum_eq_zero fun μ _ => ?_
  rw [threeJ_eq_zero_of_not (fun h => hj (mem_range.mpr (by unfold Tri at h; omega)))]
  ring

/-- **The loop identity.** For the intertwiners of `(a b c j)` in the channel `(a b)(c j)`,
`Σ_j (j + 1) Σ_x Σ_μ ι^{(x)}_{h₀ h₁ h₂ μ} ι^{(x)}_{h₀' h₁' h₂' μ} = δ_{hh'}` (doubled units, `h`
admissible): closing the strand of spin `j` of a tetrahedron's projector and summing over `j` with
the dimension gives the identity on the other three legs. -/
theorem loop_fourJ (a b c : ℕ) {h₀ h₁ h₂ : ℤ} (ha : AdmProj a h₀) (hb : AdmProj b h₁)
    (hc : AdmProj c h₂) (h₀' h₁' h₂' : ℤ) :
    ∑ j ∈ range (a + b + c + 1), ((j : ℝ) + 1) * ∑ x ∈ range (a + b + 1), ∑ μ ∈ Icc (-(j : ℤ)) j,
      fourJ a b c j x h₀ h₁ h₂ μ * fourJ a b c j x h₀' h₁' h₂' μ =
      if h₀ = h₀' ∧ h₁ = h₁' ∧ h₂ = h₂' then 1 else 0 := by
  -- expand the intertwiners
  have hexp : ∀ j x : ℕ, ∑ μ ∈ Icc (-(j : ℤ)) j,
      fourJ a b c j x h₀ h₁ h₂ μ * fourJ a b c j x h₀' h₁' h₂' μ =
      ((x : ℝ) + 1) * ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ ξ' ∈ Icc (-(x : ℤ)) x,
        (-1) ^ (((x : ℤ) - ξ) / 2) * (-1) ^ (((x : ℤ) - ξ') / 2) *
          (threeJ a b x h₀ h₁ ξ * threeJ a b x h₀' h₁' ξ') *
          ∑ μ ∈ Icc (-(j : ℤ)) j, threeJ x c j (-ξ) h₂ μ * threeJ x c j (-ξ') h₂' μ := by
    intro j x
    have hs : Real.sqrt ((x : ℝ) + 1) * Real.sqrt ((x : ℝ) + 1) = (x : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hprod : ∀ μ : ℤ, fourJ a b c j x h₀ h₁ h₂ μ * fourJ a b c j x h₀' h₁' h₂' μ =
        ((x : ℝ) + 1) * ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ ξ' ∈ Icc (-(x : ℤ)) x,
          ((-1) ^ (((x : ℤ) - ξ) / 2) * threeJ a b x h₀ h₁ ξ * threeJ x c j (-ξ) h₂ μ) *
          ((-1) ^ (((x : ℤ) - ξ') / 2) * threeJ a b x h₀' h₁' ξ' * threeJ x c j (-ξ') h₂' μ) := by
      intro μ
      unfold fourJ
      rw [mul_mul_mul_comm, hs, sum_mul_sum]
    simp only [hprod]
    rw [← Finset.mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun ξ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun ξ' _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun μ _ => ?_
    ring
  simp only [hexp]
  simp only [Finset.mul_sum]
  rw [sum_comm]
  -- for each `x`, the sum over `j` is the completeness of the 3j symbols `(x c j)`
  have hx : ∀ x ∈ range (a + b + 1), ∑ j ∈ range (a + b + c + 1),
      ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ ξ' ∈ Icc (-(x : ℤ)) x, ∑ μ ∈ Icc (-(j : ℤ)) j,
        ((j : ℝ) + 1) * (((x : ℝ) + 1) *
          ((-1) ^ (((x : ℤ) - ξ) / 2) * (-1) ^ (((x : ℤ) - ξ') / 2) *
            (threeJ a b x h₀ h₁ ξ * threeJ a b x h₀' h₁' ξ') *
            (threeJ x c j (-ξ) h₂ μ * threeJ x c j (-ξ') h₂' μ))) =
      ∑ ξ ∈ Icc (-(x : ℤ)) x, ((x : ℝ) + 1) *
        (threeJ a b x h₀ h₁ ξ * threeJ a b x h₀' h₁' ξ) * (if h₂ = h₂' then 1 else 0) := by
    intro x hxr
    have hle : x + c ≤ a + b + c := by have := mem_range.mp hxr; omega
    rw [sum_comm]
    refine sum_congr rfl fun ξ hξ => ?_
    rw [sum_comm]
    by_cases hadm : AdmProj x ξ
    · have hneg : AdmProj x (-ξ) := admProj_neg.mpr hadm
      have hj : ∀ ξ' : ℤ, ∑ j ∈ range (a + b + c + 1), ∑ μ ∈ Icc (-(j : ℤ)) j,
          ((j : ℝ) + 1) * (((x : ℝ) + 1) *
            ((-1) ^ (((x : ℤ) - ξ) / 2) * (-1) ^ (((x : ℤ) - ξ') / 2) *
              (threeJ a b x h₀ h₁ ξ * threeJ a b x h₀' h₁' ξ') *
              (threeJ x c j (-ξ) h₂ μ * threeJ x c j (-ξ') h₂' μ))) =
          ((x : ℝ) + 1) * ((-1) ^ (((x : ℤ) - ξ) / 2) * (-1) ^ (((x : ℤ) - ξ') / 2) *
            (threeJ a b x h₀ h₁ ξ * threeJ a b x h₀' h₁' ξ')) *
          (if -ξ = -ξ' ∧ h₂ = h₂' then 1 else 0) := by
        intro ξ'
        have hc0 := sum_threeJ_complete_le x c (a + b + c) hle hneg hc (-ξ') h₂'
        rw [← hc0, Finset.mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun μ _ => ?_
        ring
      rw [sum_congr rfl fun ξ' _ => hj ξ']
      have hξI : ξ ∈ Icc (-(x : ℤ)) x := hξ
      rw [sum_eq_single ξ (fun ξ' _ hne => by
        rw [ite_eq_right (fun h => hne (by omega)), mul_zero]) (fun h => absurd hξI h)]
      have hsq : (-1 : ℝ) ^ (((x : ℤ) - ξ) / 2) * (-1) ^ (((x : ℤ) - ξ) / 2) = 1 :=
        neg_one_zpow_mul_self _
      by_cases h2 : h₂ = h₂'
      · rw [ite_eq_left ⟨rfl, h2⟩, ite_eq_left h2, hsq]; ring
      · rw [ite_eq_right (fun h => h2 h.2), ite_eq_right h2]; ring
    · have h0 : threeJ a b x h₀ h₁ ξ = 0 := threeJ_eq_zero_of_not fun h => hadm h.2
      simp [h0]
  rw [sum_congr rfl hx]
  have hfac : (∑ x ∈ range (a + b + 1), ∑ ξ ∈ Icc (-(x : ℤ)) x, ((x : ℝ) + 1) *
      (threeJ a b x h₀ h₁ ξ * threeJ a b x h₀' h₁' ξ) * (if h₂ = h₂' then (1 : ℝ) else 0)) =
      (∑ x ∈ range (a + b + 1), ∑ ξ ∈ Icc (-(x : ℤ)) x, ((x : ℝ) + 1) *
      (threeJ a b x h₀ h₁ ξ * threeJ a b x h₀' h₁' ξ)) * (if h₂ = h₂' then (1 : ℝ) else 0) := by
    simp only [Finset.sum_mul]
  rw [hfac, sum_threeJ_complete a b ha hb h₀' h₁']
  by_cases e1 : h₀ = h₀' ∧ h₁ = h₁' <;> by_cases e2 : h₂ = h₂' <;> simp [e1, e2]

/-! ## Independence of the leg order -/

/-- The intertwiner with its legs read in the order `π`: `fourJ` of the spins
`j (π 0), …, j (π 3)` at the projections `m ∘ π`. -/
noncomputable def fourJP (j : Fin 4 → ℕ) (π : Equiv.Perm (Fin 4)) (x : ℕ) (m : Fin 4 → ℤ) : ℝ :=
  fourJT (j (π 0)) (j (π 1)) (j (π 2)) (j (π 3)) x (m ∘ π)

lemma vec_fin4 {α : Type*} (f : Fin 4 → α) : ![f 0, f 1, f 2, f 3] = f := by
  funext i; fin_cases i <;> rfl

lemma box4_eq (j : Fin 4 → ℕ) :
    box4 (j 0) (j 1) (j 2) (j 3) = Fintype.piFinset fun i => Icc (-(j i : ℤ)) (j i) := by
  unfold box4; rw [vec_fin4 j]

/-- The intertwiners in any leg order are invariant tensors of the original legs. -/
lemma isInv_fourJP (j : Fin 4 → ℕ) (π : Equiv.Perm (Fin 4)) (x : ℕ) :
    IsInv j ![false, false, false, false] (fourJP j π x) := by
  have h := (isInv_fourJT (j (π 0)) (j (π 1)) (j (π 2)) (j (π 3)) x).reindex π.symm
  have e1 : ![j (π 0), j (π 1), j (π 2), j (π 3)] ∘ π.symm = j := by
    rw [vec_fin4 (fun i => j (π i))]; funext i; simp
  have hc : (![false, false, false, false] : Fin 4 → Bool) = fun _ => false := by
    funext i; fin_cases i <;> rfl
  have e2 : (![false, false, false, false] : Fin 4 → Bool) ∘ π.symm = ![false, false, false, false] := by
    rw [hc]; rfl
  rw [e1, e2] at h
  exact h.congr fun m => rfl

/-- Sums over the box of projections of four legs can be read in any leg order. -/
lemma sum_box4_perm (j : Fin 4 → ℕ) (π : Equiv.Perm (Fin 4)) (F : (Fin 4 → ℤ) → ℝ) :
    ∑ n ∈ box4 (j 0) (j 1) (j 2) (j 3), F n =
      ∑ n ∈ box4 (j (π 0)) (j (π 1)) (j (π 2)) (j (π 3)), F (n ∘ π.symm) := by
  rw [box4_eq, box4_eq (fun i => j (π i))]
  apply sum_nbij' (fun n => n ∘ π) (fun n => n ∘ π.symm)
  · intro n hn
    simp only [Fintype.mem_piFinset] at hn ⊢
    intro i; exact hn (π i)
  · intro n hn
    simp only [Fintype.mem_piFinset] at hn ⊢
    intro i
    have := hn (π.symm i)
    simpa using this
  · intro n _; funext i; simp
  · intro n _; funext i; simp
  · intro n _; congr 1; funext i; simp

/-- **The projector of a tetrahedron does not depend on the leg order** of its intertwiner basis:
`Σ_k ι^{(k)}_m ι^{(k)}_{m'}` is the same for the orders `(0 1 2 3)` and `π`. -/
theorem sum_fourJT_mul_perm (j : Fin 4 → ℕ) (π : Equiv.Perm (Fin 4)) (m m' : Fin 4 → ℤ) :
    ∑ k ∈ range (j 0 + j 1 + 1), fourJT (j 0) (j 1) (j 2) (j 3) k m *
        fourJT (j 0) (j 1) (j 2) (j 3) k m' =
      ∑ x ∈ range (j (π 0) + j (π 1) + 1), fourJP j π x m * fourJP j π x m' := by
  have hj : ![j 0, j 1, j 2, j 3] = j := vec_fin4 j
  -- the permuted intertwiners in the original basis
  have hτ : ∀ x n, fourJP j π x n = ∑ k ∈ range (j 0 + j 1 + 1),
      (∑ p ∈ box4 (j 0) (j 1) (j 2) (j 3), fourJT (j 0) (j 1) (j 2) (j 3) k p * fourJP j π x p) *
        fourJT (j 0) (j 1) (j 2) (j 3) k n := by
    intro x n
    have h : IsInv ![j 0, j 1, j 2, j 3] ![false, false, false, false] (fourJP j π x) := by
      rw [hj]; exact isInv_fourJP j π x
    exact eq_sum_fourJ h n
  -- the original intertwiners in the permuted basis
  have hι : ∀ k n, fourJT (j 0) (j 1) (j 2) (j 3) k n = ∑ x ∈ range (j (π 0) + j (π 1) + 1),
      (∑ p ∈ box4 (j 0) (j 1) (j 2) (j 3), fourJP j π x p * fourJT (j 0) (j 1) (j 2) (j 3) k p) *
        fourJP j π x n := by
    intro k n
    have h := (isInv_fourJT (j 0) (j 1) (j 2) (j 3) k).reindex π
    have e1 : ![j 0, j 1, j 2, j 3] ∘ π = ![j (π 0), j (π 1), j (π 2), j (π 3)] := by
      rw [hj, vec_fin4 (fun i => j (π i))]; rfl
    have hc : (![false, false, false, false] : Fin 4 → Bool) = fun _ => false := by
      funext i; fin_cases i <;> rfl
    have e2 : (![false, false, false, false] : Fin 4 → Bool) ∘ π =
        ![false, false, false, false] := by
      rw [hc]; rfl
    rw [e1, e2] at h
    have e := eq_sum_fourJ h (n ∘ π)
    have hl : (n ∘ π) ∘ π.symm = n := by funext i; simp
    simp only [hl] at e
    rw [e]
    refine sum_congr rfl fun x _ => ?_
    have hin : ∑ p ∈ box4 (j (π 0)) (j (π 1)) (j (π 2)) (j (π 3)),
        fourJT (j (π 0)) (j (π 1)) (j (π 2)) (j (π 3)) x p *
          fourJT (j 0) (j 1) (j 2) (j 3) k (p ∘ π.symm) =
        ∑ p ∈ box4 (j 0) (j 1) (j 2) (j 3), fourJP j π x p *
          fourJT (j 0) (j 1) (j 2) (j 3) k p := by
      rw [sum_box4_perm j π]
      refine sum_congr rfl fun p _ => ?_
      have hp : (p ∘ π.symm) ∘ π = p := by funext i; simp
      unfold fourJP
      rw [hp]
    rw [hin]
    rfl
  -- combine
  calc ∑ k ∈ range (j 0 + j 1 + 1), fourJT (j 0) (j 1) (j 2) (j 3) k m *
        fourJT (j 0) (j 1) (j 2) (j 3) k m'
      = ∑ k ∈ range (j 0 + j 1 + 1), fourJT (j 0) (j 1) (j 2) (j 3) k m *
          ∑ x ∈ range (j (π 0) + j (π 1) + 1), (∑ p ∈ box4 (j 0) (j 1) (j 2) (j 3),
            fourJP j π x p * fourJT (j 0) (j 1) (j 2) (j 3) k p) * fourJP j π x m' := by
        refine sum_congr rfl fun k _ => by rw [← hι k m']
    _ = ∑ x ∈ range (j (π 0) + j (π 1) + 1), (∑ k ∈ range (j 0 + j 1 + 1),
          (∑ p ∈ box4 (j 0) (j 1) (j 2) (j 3), fourJT (j 0) (j 1) (j 2) (j 3) k p *
            fourJP j π x p) * fourJT (j 0) (j 1) (j 2) (j 3) k m) * fourJP j π x m' := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun x _ => sum_congr rfl fun k _ => ?_
        refine sum_congr rfl fun p _ => ?_
        ring
    _ = ∑ x ∈ range (j (π 0) + j (π 1) + 1), fourJP j π x m * fourJP j π x m' := by
        refine sum_congr rfl fun x _ => by rw [← hτ x m]

end Lightlike.Recoupling

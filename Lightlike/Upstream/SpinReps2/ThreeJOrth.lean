module

public import Lightlike.Upstream.SpinReps2.ThreeJZero

/-!
# Orthogonality of the 3j symbols in the general parametrisation

Physlib proves the orthogonality of the Wigner 3j symbols in the parametrisation of its
Clebsch–Gordan construction (`sum_wigner3j_mul_wigner3j`: spins `m, n`, a coupled spin `m + n - 2k`
and projections given by counters `l, α, β`). Physlib's general 3j symbol `threeJ j₁ j₂ j₃ m₁ m₂ m₃`
uses doubled spins `jᵢ ∈ ℕ` and doubled projections `mᵢ ∈ ℤ`. This file states the orthogonality
relation for `threeJ`, for all spins:

`Σ_{m₁ m₂} (j₁ j₂ J; m₁ m₂ μ) (j₁ j₂ J'; m₁ m₂ μ') = δ_{JJ'} δ_{μμ'} / (2J + 1)`

for an admissible pair `(J, μ)` (`J` in the triangle range of `j₁, j₂` with even perimeter,
`|μ| ≤ J`, `J - μ` even), and `0` otherwise. In doubled units the factor `1 / (2J + 1)` is
`1 / (J + 1)`. The sums run over the full ranges `|mᵢ| ≤ jᵢ`; the terms of the wrong parity vanish.

## Main definitions

* `PhyslibAlpha.Sl2.Triad j₁ j₂ j₃`: the triangle condition with even perimeter, in doubled units.
* `PhyslibAlpha.Sl2.AdmProj J μ`: `μ` is an admissible projection of the doubled spin `J`.

## Main results

* `PhyslibAlpha.Sl2.sum_threeJ_mul_threeJ`: orthogonality of the 3j symbols.
* `PhyslibAlpha.Sl2.sum_range_triad`: a sum over the third spin reduces to Physlib's
  parametrisation `x = a + b - 2k`.

## References

* [Edmonds, *Angular Momentum in Quantum Mechanics*, Ch. 3][edmonds-1957]
-/

@[expose] public section

open Finset

namespace PhyslibAlpha.Sl2

/-- The triangle condition with even perimeter for the doubled spins `x, y, z`. -/
def Triad (x y z : ℕ) : Prop := (x + y + z) % 2 = 0 ∧ z ≤ x + y ∧ x ≤ y + z ∧ y ≤ x + z

instance (x y z : ℕ) : Decidable (Triad x y z) := by unfold Triad; infer_instance

/-- An admissible projection `μ` of a doubled spin `J`: `|μ| ≤ J` and `J - μ` even. -/
def AdmProj (J : ℕ) (μ : ℤ) : Prop := -(J : ℤ) ≤ μ ∧ μ ≤ J ∧ ((J : ℤ) - μ) % 2 = 0

instance (J : ℕ) (μ : ℤ) : Decidable (AdmProj J μ) := by unfold AdmProj; infer_instance

/-- A nonzero 3j symbol has an admissible triad and an admissible third projection. -/
lemma triad_admProj_of_threeJ_ne_zero {j₁ j₂ J : ℕ} {m₁ m₂ μ : ℤ}
    (h : threeJ j₁ j₂ J m₁ m₂ μ ≠ 0) : Triad j₁ j₂ J ∧ AdmProj J μ := by
  obtain ⟨-, -, -, -, -, h5, h6, -, -, h9, h10, h11, h12, h13⟩ := adm3_of_threeJ_ne_zero h
  exact ⟨⟨h13, h10, h11, h12⟩, h5, h6, h9⟩

/-- A 3j symbol vanishes unless its triad and its third projection are admissible. -/
lemma threeJ_eq_zero_of_not_triad_admProj {j₁ j₂ J : ℕ} {m₁ m₂ μ : ℤ}
    (h : ¬(Triad j₁ j₂ J ∧ AdmProj J μ)) : threeJ j₁ j₂ J m₁ m₂ μ = 0 := by
  by_contra h'
  exact h (triad_admProj_of_threeJ_ne_zero h')

/-- A sum over the third spin `x ≤ j₁ + j₂` of a function vanishing outside the triangle range is a
sum over `k ≤ min j₁ j₂` with `x = j₁ + j₂ - 2k` (Physlib's parametrisation). -/
lemma sum_range_triad (a b : ℕ) (G : ℕ → ℝ) (hG : ∀ x, ¬Triad a b x → G x = 0) :
    ∑ x ∈ range (a + b + 1), G x = ∑ k ∈ range (min a b + 1), G (a + b - 2 * k) := by
  rw [← sum_image (s := range (min a b + 1)) (g := fun k => a + b - 2 * k) (f := G)]
  · symm
    apply sum_subset
    · intro x hx
      simp only [mem_image, mem_range] at hx ⊢
      omega
    · intro x hx hn
      apply hG
      intro ht
      apply hn
      simp only [mem_image, mem_range]
      unfold Triad at ht
      refine ⟨(a + b - x) / 2, ?_, by omega⟩
      have : (a + b - x) / 2 ≤ min a b := le_min (by omega) (by omega)
      omega
  · intro k₁ hk₁ k₂ hk₂ h
    simp only [coe_range, Set.mem_Iio] at hk₁ hk₂
    have h1 : k₁ ≤ a ∧ k₁ ≤ b := le_min_iff.mp (Nat.lt_succ_iff.mp hk₁)
    have h2 : k₂ ≤ a ∧ k₂ ≤ b := le_min_iff.mp (Nat.lt_succ_iff.mp hk₂)
    simp only at h
    omega

/-- **Orthogonality of the 3j symbols** (doubled units, all spins):
`Σ_{m₁ m₂} (j₁ j₂ J; m₁ m₂ μ) (j₁ j₂ J'; m₁ m₂ μ') = δ_{JJ'} δ_{μμ'} / (J + 1)` when `(j₁ j₂ J)` is
an admissible triad and `μ` an admissible projection of `J`, and `0` otherwise. -/
theorem sum_threeJ_mul_threeJ (j₁ j₂ J J' : ℕ) (μ μ' : ℤ) :
    ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂,
      threeJ j₁ j₂ J m₁ m₂ μ * threeJ j₁ j₂ J' m₁ m₂ μ' =
      if J = J' ∧ μ = μ' ∧ Triad j₁ j₂ J ∧ AdmProj J μ then 1 / ((J : ℝ) + 1) else 0 := by
  -- an inadmissible `(J, μ)` or `(J', μ')` kills every term
  by_cases hA : Triad j₁ j₂ J ∧ AdmProj J μ
  swap
  · rw [ite_eq_right (fun h => hA h.2.2)]
    refine sum_eq_zero fun m₁ _ => sum_eq_zero fun m₂ _ => ?_
    rw [threeJ_eq_zero_of_not_triad_admProj hA, zero_mul]
  by_cases hA' : Triad j₁ j₂ J' ∧ AdmProj J' μ'
  swap
  · rw [ite_eq_right (fun h => hA' (by obtain ⟨rfl, rfl, h'⟩ := h; exact h'))]
    refine sum_eq_zero fun m₁ _ => sum_eq_zero fun m₂ _ => ?_
    rw [threeJ_eq_zero_of_not_triad_admProj hA', mul_zero]
  obtain ⟨⟨hp, hT1, hT2, hT3⟩, hμ1, hμ2, hμ3⟩ := hA
  obtain ⟨⟨hp', hT1', hT2', hT3'⟩, hμ1', hμ2', hμ3'⟩ := hA'
  -- all spins zero
  by_cases h0 : j₁ + j₂ = 0
  · have h1 : j₁ = 0 := by omega
    have h2 : j₂ = 0 := by omega
    have hJ : J = 0 := by omega
    have hJ' : J' = 0 := by omega
    have hμ : μ = 0 := by omega
    have hμ' : μ' = 0 := by omega
    subst h1 h2 hJ hJ' hμ hμ'
    simp [threeJ_zero_left, AdmProj, Triad]
  -- reindex `m₁ = j₁ - 2α`, `m₂ = j₂ - 2β` and use Physlib's orthogonality
  rw [sum_Icc_parity j₁ _ (fun ν hν => sum_eq_zero fun m₂ _ => by
    rw [threeJ_of_not (fun h => by obtain ⟨_, -, -, -, -, -, -, h8, -⟩ := h; omega)]; ring)]
  rw [sum_congr rfl fun (α : ℕ) _ => sum_Icc_parity j₂
    (fun m₂ => threeJ j₁ j₂ J ((j₁ : ℤ) - 2 * (α : ℤ)) m₂ μ *
      threeJ j₁ j₂ J' ((j₁ : ℤ) - 2 * (α : ℤ)) m₂ μ')
    (fun ν hν => by
      rw [threeJ_of_not (fun h => by obtain ⟨_, -, -, -, -, -, -, -, h9, -⟩ := h; omega)]
      ring)]
  obtain ⟨k, hJ, hk1, hk2⟩ : ∃ k, j₁ + j₂ - 2 * k = J ∧ k ≤ j₁ ∧ k ≤ j₂ :=
    ⟨(j₁ + j₂ - J) / 2, by omega, by omega, by omega⟩
  obtain ⟨k', hJ', hk1', hk2'⟩ : ∃ k', j₁ + j₂ - 2 * k' = J' ∧ k' ≤ j₁ ∧ k' ≤ j₂ :=
    ⟨(j₁ + j₂ - J') / 2, by omega, by omega, by omega⟩
  obtain ⟨l, hμ, hlJ⟩ : ∃ l : ℕ, -((J : ℤ) - 2 * (l : ℤ)) = μ ∧ l ≤ J :=
    ⟨((J + μ) / 2).toNat, by omega, by omega⟩
  obtain ⟨l', hμ', hlJ'⟩ : ∃ l' : ℕ, -((J' : ℤ) - 2 * (l' : ℤ)) = μ' ∧ l' ≤ J' :=
    ⟨((J' + μ') / 2).toNat, by omega, by omega⟩
  have hw := sum_wigner3j_mul_wigner3j (m := j₁) (n := j₂) (by omega) (k := k) (k' := k')
    (l := l) (l' := l') hk1 hk2 hk1' hk2' (by omega) (by omega)
  have hterm : ∀ α ∈ range (j₁ + 1), ∀ β ∈ range (j₂ + 1),
      threeJ j₁ j₂ J ((j₁ : ℤ) - 2 * (α : ℤ)) ((j₂ : ℤ) - 2 * (β : ℤ)) μ *
        threeJ j₁ j₂ J' ((j₁ : ℤ) - 2 * (α : ℤ)) ((j₂ : ℤ) - 2 * (β : ℤ)) μ' =
      wigner3j j₁ j₂ k l α β * wigner3j j₁ j₂ k' l' α β := by
    intro α hα β hβ
    simp only [mem_range] at hα hβ
    rw [wigner3j_eq_threeJ (m := j₁) (n := j₂) (k := k) (l := l) (α := α) (β := β) hk1 hk2
        (by omega) (by omega) (by omega),
      wigner3j_eq_threeJ (m := j₁) (n := j₂) (k := k') (l := l') (α := α) (β := β) hk1' hk2'
        (by omega) (by omega) (by omega), hJ, hJ', hμ, hμ']
  rw [sum_congr rfl fun α hα => sum_congr rfl fun β hβ => hterm α hα β hβ, hw]
  have hiff : (k = k' ∧ l = l') ↔ (J = J' ∧ μ = μ' ∧ Triad j₁ j₂ J ∧ AdmProj J μ) := by
    constructor
    · rintro ⟨h1, h2⟩
      subst h1 h2
      exact ⟨by omega, by omega, ⟨hp, hT1, hT2, hT3⟩, hμ1, hμ2, hμ3⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨by omega, by omega⟩
  by_cases hc : k = k' ∧ l = l'
  · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc), show j₁ + j₂ - 2 * k + 1 = J + 1 by omega]
    push_cast
    ring
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.mpr h))]

end PhyslibAlpha.Sl2

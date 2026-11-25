import Lightlike.Spin4.CGBridge
import Lightlike.Recoupling.Intertwiner

/-!
# The 6j symbols as recoupling coefficients of the spin representations of SU(2)

Physlib defines the Clebsch–Gordan coefficients (`PhyslibAlpha.Sl2.cgCoefficient`) and the 3j and
6j symbols (`threeJ`, `sixJSym`) for the Lie algebra `sl₂`; `Lightlike/Spin4/CGBridge.lean` shows
that the Clebsch–Gordan matrices `cgMatrix` intertwine the group representations `SU2.spinMat`.
This file closes the circle for three spins: the two ways of coupling `a ⊗ b ⊗ c` to a total spin
`J` (doubled units throughout) are SU(2)-equivariant maps, and the 6j symbol is their overlap.

* `coupleLeft a b c k₁ k₂`: couple `a ⊗ b → e = a + b - 2k₁`, then `e ⊗ c → J = e + c - 2k₂`;
* `coupleRight a b c k₁ k₂`: couple `b ⊗ c → f = b + c - 2k₁`, then `a ⊗ f → J = a + f - 2k₂`;
* `coupleLeft_equivariant`, `coupleRight_equivariant`: both intertwine
  `spinMat a g ⊗ spinMat b g ⊗ spinMat c g` with `spinMat J g` for every `g ∈ SU(2)`;
* `coupleLeft_apply`, `coupleRight_apply`: their entries are the sums of Clebsch–Gordan
  coefficients in `sum_cg_overlap`;
* `sum_cg_overlap`: the Hilbert–Schmidt inner product of `coupleLeft` and `coupleRight` is
  `(J + 1) (-1)^(…) √((e + 1)(f + 1)) {a b e; c J f}` (the Racah recoupling coefficient).

## Differences from the sources

The overlap is stated as the sum over all entries (the Hilbert–Schmidt inner product), not as the
matrix identity `coupleLeftᴴ coupleRight = λ · 1`, which follows from Schur's lemma for `spinRep`
(not used here). The sign is the product of the signs of the phases of the Clebsch–Gordan
coefficients (Condon–Shortley, as in Physlib) and of the 3j symmetries; it is not simplified to the
textbook `(-1)^{a+b+c+J}`, and has not been compared with a source (comparison pending). This
is **weaker** than the matrix form; whether it meets the milestone's done-when is an owner
decision, and the item stays open until then.

## References

* A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton (1957), Ch. 6 (Racah
  coefficients and 6j symbols).
* D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*
  (1988), Ch. 9 (6j symbols and Racah coefficients).
-/

open Finset PhyslibAlpha.Sl2

namespace Lightlike.SU2

open Lightlike.Spin4 Lightlike.Recoupling

/-- Clebsch–Gordan coefficient in `ℕ`-indexed form. -/
theorem cgCoefficient_eq_threeJ' {n m k : ℕ} (hk : k ≤ n) (hk' : k ≤ m) {a b l : ℕ}
    (ha : a ≤ n) (hb : b ≤ m) (hl : l ≤ n + m - 2 * k) :
    cgCoefficient n m k l a b = (-1 : ℝ) ^ (n + k + l) *
      Real.sqrt ((n + m - 2 * k + 1 : ℕ) : ℝ) *
      threeJ n m (n + m - 2 * k) ((n : ℤ) - 2 * a) ((m : ℤ) - 2 * b)
        (-(((n + m - 2 * k : ℕ) : ℤ) - 2 * l)) := by
  have := cgMatrix_eq_threeJ hk hk' (⟨a, Nat.lt_succ_of_le ha⟩, ⟨b, Nat.lt_succ_of_le hb⟩)
    ⟨l, Nat.lt_succ_of_le hl⟩
  rw [cgMatrix_apply] at this
  exact_mod_cast this


/-- The sum over `μ ∈ [-k, k]` of a function vanishing for `k - μ` odd is the sum over
`μ = 2l - k`, `l = 0, …, k`. -/
lemma sum_Icc_eq_sum_range (k : ℕ) (F : ℤ → ℝ) (hF : ∀ μ, ((k : ℤ) - μ) % 2 ≠ 0 → F μ = 0) :
    ∑ μ ∈ Icc (-(k : ℤ)) k, F μ = ∑ l ∈ range (k + 1), F (2 * (l : ℤ) - k) := by
  have hinj : Set.InjOn (fun l : ℕ => 2 * (l : ℤ) - k) (range (k + 1) : Finset ℕ) := by
    intro x _ y _ h; simp only at h; omega
  rw [← Finset.sum_image (f := F) (g := fun l : ℕ => 2 * (l : ℤ) - k) hinj]
  symm
  apply Finset.sum_subset
  · intro μ hμ
    simp only [mem_image, mem_range] at hμ
    obtain ⟨l, hl, rfl⟩ := hμ
    simp only [mem_Icc]; omega
  · intro μ hμ hn
    apply hF
    intro h
    apply hn
    simp only [mem_Icc] at hμ
    simp only [mem_image, mem_range]
    exact ⟨((k + μ) / 2).toNat, by omega, by omega⟩


lemma sign_aux (x y l n : ℕ) :
    (-1 : ℝ) ^ (x + l) * (-1) ^ (l + n + y) =
      (-1) ^ (x + y) * (-1 : ℝ) ^ ((((l + n : ℕ) : ℤ) - (2 * (l : ℤ) - ((l + n : ℕ) : ℤ))) / 2) := by
  have : ((((l + n : ℕ) : ℤ) - (2 * (l : ℤ) - ((l + n : ℕ) : ℤ))) / 2) = (n : ℤ) := by
    push_cast; omega
  rw [this, zpow_natCast]
  have h2 : (-1 : ℝ) ^ (l + l) = 1 := by rw [← two_mul, pow_mul]; simp
  calc (-1 : ℝ) ^ (x + l) * (-1) ^ (l + n + y)
      = (-1) ^ (x + y) * (-1) ^ n * (-1) ^ (l + l) := by
        rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
    _ = _ := by rw [h2, mul_one]


/-- Coupling `a ⊗ b → e` and then `e ⊗ c → J` with Physlib's Clebsch–Gordan coefficients is, up
to a sign and `√(J+1)`, the 4-valent intertwiner `fourJ a b c J e`. -/
theorem sum_cg_left {a b c k₁ k₂ α β γ δ : ℕ} (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b)
    (hk₂e : k₂ ≤ a + b - 2 * k₁) (hk₂c : k₂ ≤ c) (hα : α ≤ a) (hβ : β ≤ b) (hγ : γ ≤ c)
    (hδ : δ ≤ a + b - 2 * k₁ + c - 2 * k₂) :
    ∑ l ∈ range (a + b - 2 * k₁ + 1),
        cgCoefficient a b k₁ l α β * cgCoefficient (a + b - 2 * k₁) c k₂ δ l γ =
      (-1 : ℝ) ^ (a + k₁ + k₂ + δ) * Real.sqrt (((a + b - 2 * k₁ + c - 2 * k₂ : ℕ) : ℝ) + 1) *
        fourJ a b c (a + b - 2 * k₁ + c - 2 * k₂) (a + b - 2 * k₁)
          ((a : ℤ) - 2 * α) ((b : ℤ) - 2 * β) ((c : ℤ) - 2 * γ)
          (-(((a + b - 2 * k₁ + c - 2 * k₂ : ℕ) : ℤ) - 2 * δ)) := by
  rw [fourJ, sum_Icc_eq_sum_range]
  swap
  · intro μ hμ
    rw [threeJ_of_not (by intro h; exact hμ (by have := h.2.2.2.2.2.2.2.2.2.2.1; omega))]
    simp
  have hterm : ∀ l ∈ range (a + b - 2 * k₁ + 1),
      cgCoefficient a b k₁ l α β * cgCoefficient (a + b - 2 * k₁) c k₂ δ l γ =
      (-1 : ℝ) ^ (a + k₁ + k₂ + δ) * Real.sqrt (((a + b - 2 * k₁ + c - 2 * k₂ : ℕ) : ℝ) + 1) *
        (Real.sqrt (((a + b - 2 * k₁ : ℕ) : ℝ) + 1) *
          ((-1 : ℝ) ^ ((((a + b - 2 * k₁ : ℕ) : ℤ) - (2 * (l : ℤ) - ((a + b - 2 * k₁ : ℕ) : ℤ))) / 2) *
            threeJ a b (a + b - 2 * k₁) ((a : ℤ) - 2 * α) ((b : ℤ) - 2 * β)
              (2 * (l : ℤ) - ((a + b - 2 * k₁ : ℕ) : ℤ)) *
            threeJ (a + b - 2 * k₁) c (a + b - 2 * k₁ + c - 2 * k₂)
              (-(2 * (l : ℤ) - ((a + b - 2 * k₁ : ℕ) : ℤ))) ((c : ℤ) - 2 * γ)
              (-(((a + b - 2 * k₁ + c - 2 * k₂ : ℕ) : ℤ) - 2 * δ)))) := by
    intro l hl
    have hl' : l ≤ a + b - 2 * k₁ := Nat.lt_succ_iff.mp (mem_range.mp hl)
    rw [cgCoefficient_eq_threeJ' hk₁a hk₁b hα hβ hl', cgCoefficient_eq_threeJ' hk₂e hk₂c
      hl' hγ hδ]
    have h1 : -(2 * (l : ℤ) - ((a + b - 2 * k₁ : ℕ) : ℤ)) = ((a + b - 2 * k₁ : ℕ) : ℤ) - 2 * l := by
      ring
    have h2 : -(((a + b - 2 * k₁ : ℕ) : ℤ) - 2 * l) = 2 * (l : ℤ) - ((a + b - 2 * k₁ : ℕ) : ℤ) := by
      ring
    rw [h1, h2]
    obtain ⟨n, hn⟩ : ∃ n, a + b - 2 * k₁ = l + n := ⟨a + b - 2 * k₁ - l, by omega⟩
    have hs := sign_aux (a + k₁) (k₂ + δ) l n
    rw [hn]
    have key : (-1 : ℝ) ^ (a + k₁ + l) * (-1) ^ (l + n + k₂ + δ) =
        (-1) ^ (a + k₁ + k₂ + δ) * (-1 : ℝ) ^ ((((l + n : ℕ) : ℤ) - (2 * (l : ℤ) - ((l + n : ℕ) : ℤ))) / 2) := by
      rw [show a + k₁ + k₂ + δ = a + k₁ + (k₂ + δ) by ring,
        show l + n + k₂ + δ = l + n + (k₂ + δ) by ring]; exact hs
    generalize (-1 : ℝ) ^ ((((l + n : ℕ) : ℤ) - (2 * (l : ℤ) - ((l + n : ℕ) : ℤ))) / 2) = S at key ⊢
    simp only [Nat.cast_add_one]
    linear_combination (Real.sqrt (((l + n : ℕ) : ℝ) + 1) * Real.sqrt (((l + n + c - 2 * k₂ : ℕ) : ℝ) + 1) *
      threeJ a b (l + n) ((a : ℤ) - 2 * α) ((b : ℤ) - 2 * β) (2 * (l : ℤ) - ((l + n : ℕ) : ℤ)) *
      threeJ (l + n) c (l + n + c - 2 * k₂) (((l + n : ℕ) : ℤ) - 2 * l) ((c : ℤ) - 2 * γ)
        (-(((l + n + c - 2 * k₂ : ℕ) : ℤ) - 2 * δ))) * key
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]


lemma neg_one_pow_eq_of_mod {x y : ℕ} (h : x % 2 = y % 2) : (-1 : ℝ) ^ x = (-1) ^ y := by
  have key : ∀ z : ℕ, (-1 : ℝ) ^ z = (-1) ^ (z % 2) := fun z => by
    conv_lhs => rw [← Nat.mod_add_div z 2, pow_add, pow_mul]
    simp
  rw [key x, key y, h]

lemma threeJ_swap' (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₂ j₁ j₃ m₂ m₁ m₃ := by
  rw [threeJ_swap j₂ j₁ j₃ m₂ m₁ m₃, add_comm j₂ j₁]

/-- Coupling `b ⊗ c → f` and then `a ⊗ f → J` is, up to a sign and `√(J+1)`, the 4-valent
intertwiner `fourJ b c a J f`. -/
theorem sum_cg_right {a b c k₁ k₂ α β γ δ : ℕ} (hk₁b : k₁ ≤ b) (hk₁c : k₁ ≤ c)
    (hk₂a : k₂ ≤ a) (hk₂f : k₂ ≤ b + c - 2 * k₁) (hα : α ≤ a) (hβ : β ≤ b) (hγ : γ ≤ c)
    (hδ : δ ≤ a + (b + c - 2 * k₁) - 2 * k₂) :
    ∑ l ∈ range (b + c - 2 * k₁ + 1),
        cgCoefficient b c k₁ l β γ * cgCoefficient a (b + c - 2 * k₁) k₂ δ α l =
      (-1 : ℝ) ^ (b + k₁ + δ) * Real.sqrt (((a + (b + c - 2 * k₁) - 2 * k₂ : ℕ) : ℝ) + 1) *
        fourJ b c a (a + (b + c - 2 * k₁) - 2 * k₂) (b + c - 2 * k₁)
          ((b : ℤ) - 2 * β) ((c : ℤ) - 2 * γ) ((a : ℤ) - 2 * α)
          (-(((a + (b + c - 2 * k₁) - 2 * k₂ : ℕ) : ℤ) - 2 * δ)) := by
  rw [fourJ, sum_Icc_eq_sum_range]
  swap
  · intro μ hμ
    rw [threeJ_of_not (by intro h; exact hμ (by have := h.2.2.2.2.2.2.2.2.2.2.1; omega))]
    simp
  have hterm : ∀ l ∈ range (b + c - 2 * k₁ + 1),
      cgCoefficient b c k₁ l β γ * cgCoefficient a (b + c - 2 * k₁) k₂ δ α l =
      (-1 : ℝ) ^ (b + k₁ + δ) * Real.sqrt (((a + (b + c - 2 * k₁) - 2 * k₂ : ℕ) : ℝ) + 1) *
        (Real.sqrt (((b + c - 2 * k₁ : ℕ) : ℝ) + 1) *
          ((-1 : ℝ) ^ ((((b + c - 2 * k₁ : ℕ) : ℤ) - (2 * (l : ℤ) - ((b + c - 2 * k₁ : ℕ) : ℤ))) / 2) *
            threeJ b c (b + c - 2 * k₁) ((b : ℤ) - 2 * β) ((c : ℤ) - 2 * γ)
              (2 * (l : ℤ) - ((b + c - 2 * k₁ : ℕ) : ℤ)) *
            threeJ (b + c - 2 * k₁) a (a + (b + c - 2 * k₁) - 2 * k₂)
              (-(2 * (l : ℤ) - ((b + c - 2 * k₁ : ℕ) : ℤ))) ((a : ℤ) - 2 * α)
              (-(((a + (b + c - 2 * k₁) - 2 * k₂ : ℕ) : ℤ) - 2 * δ)))) := by
    intro l hl
    have hl' : l ≤ b + c - 2 * k₁ := Nat.lt_succ_iff.mp (mem_range.mp hl)
    rw [cgCoefficient_eq_threeJ' hk₁b hk₁c hβ hγ hl', cgCoefficient_eq_threeJ' hk₂a hk₂f
      hα hl' hδ]
    have h1 : -(2 * (l : ℤ) - ((b + c - 2 * k₁ : ℕ) : ℤ)) = ((b + c - 2 * k₁ : ℕ) : ℤ) - 2 * l := by
      ring
    have h2 : -(((b + c - 2 * k₁ : ℕ) : ℤ) - 2 * l) = 2 * (l : ℤ) - ((b + c - 2 * k₁ : ℕ) : ℤ) := by
      ring
    rw [h1, h2, threeJ_swap' a (b + c - 2 * k₁)]
    have hS : (-1 : ℝ) ^ ((((b + c - 2 * k₁ : ℕ) : ℤ) - (2 * (l : ℤ) - ((b + c - 2 * k₁ : ℕ) : ℤ))) / 2)
        = (-1 : ℝ) ^ (b + c - 2 * k₁ - l) := by
      rw [← zpow_natCast]; congr 1; push_cast [Nat.cast_sub hl']; omega
    rw [hS]
    have hsg : (-1 : ℝ) ^ (b + k₁ + l) * (-1) ^ (a + k₂ + δ) *
        (-1) ^ ((a + (b + c - 2 * k₁) + (a + (b + c - 2 * k₁) - 2 * k₂)) / 2) =
        (-1) ^ (b + k₁ + δ) * (-1) ^ (b + c - 2 * k₁ - l) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      apply neg_one_pow_eq_of_mod
      omega
    generalize (-1 : ℝ) ^ (b + c - 2 * k₁ - l) = S at hsg ⊢
    simp only [Nat.cast_add_one]
    linear_combination (Real.sqrt (((b + c - 2 * k₁ : ℕ) : ℝ) + 1) *
      Real.sqrt (((a + (b + c - 2 * k₁) - 2 * k₂ : ℕ) : ℝ) + 1) *
      threeJ b c (b + c - 2 * k₁) ((b : ℤ) - 2 * β) ((c : ℤ) - 2 * γ)
        (2 * (l : ℤ) - ((b + c - 2 * k₁ : ℕ) : ℤ)) *
      threeJ (b + c - 2 * k₁) a (a + (b + c - 2 * k₁) - 2 * k₂)
        (((b + c - 2 * k₁ : ℕ) : ℤ) - 2 * l) ((a : ℤ) - 2 * α)
        (-(((a + (b + c - 2 * k₁) - 2 * k₂ : ℕ) : ℤ) - 2 * δ))) * hsg
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]


lemma sum_Icc_eq_sum_range_rev (k : ℕ) (F : ℤ → ℝ) (hF : ∀ μ, ((k : ℤ) - μ) % 2 ≠ 0 → F μ = 0) :
    ∑ μ ∈ Icc (-(k : ℤ)) k, F μ = ∑ l ∈ range (k + 1), F ((k : ℤ) - 2 * l) := by
  rw [sum_Icc_eq_sum_range k F hF, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  have := mem_range.mp hl
  congr 1
  push_cast [Nat.cast_sub (show l ≤ k from by omega)]
  omega

lemma fourJ_zero₁ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₁ : ℤ) - m₁) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  rw [fourJ]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun μ _ => ?_)
  rw [threeJ_of_not (fun hh => h hh.2.2.2.2.2.2.2.1)]; simp

lemma fourJ_zero₂ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₂ : ℤ) - m₂) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  rw [fourJ]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun μ _ => ?_)
  rw [threeJ_of_not (fun hh => h hh.2.2.2.2.2.2.2.2.1)]; simp

lemma fourJ_zero₃ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₃ : ℤ) - m₃) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  rw [fourJ]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun μ _ => ?_)
  rw [threeJ_of_not (fun hh => h hh.2.2.2.2.2.2.2.2.1)]; simp

lemma fourJ_zero₄ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₄ : ℤ) - m₄) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  rw [fourJ]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun μ _ => ?_)
  rw [threeJ_of_not (fun hh => h hh.2.2.2.2.2.2.2.2.2.1)]; simp

lemma fourJ_swap₁₂ (a b c d k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ b a c d k m₂ m₁ m₃ m₄ = (-1) ^ ((a + b + k) / 2) * fourJ a b c d k m₁ m₂ m₃ m₄ := by
  rw [fourJ, fourJ, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [threeJ_swap a b k m₁ m₂ μ]; ring


/-- A sum over the projections `m ∈ [-j, j]` of four legs, of a summand vanishing on the wrong
parities, is the sum over the indices `m = j - 2α` (last leg: `m = 2δ - j`). -/
lemma sum4_Icc_eq (j₁ j₂ j₃ j₄ : ℕ) (G : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h₁ : ∀ m₁ m₂ m₃ m₄, ((j₁ : ℤ) - m₁) % 2 ≠ 0 → G m₁ m₂ m₃ m₄ = 0)
    (h₂ : ∀ m₁ m₂ m₃ m₄, ((j₂ : ℤ) - m₂) % 2 ≠ 0 → G m₁ m₂ m₃ m₄ = 0)
    (h₃ : ∀ m₁ m₂ m₃ m₄, ((j₃ : ℤ) - m₃) % 2 ≠ 0 → G m₁ m₂ m₃ m₄ = 0)
    (h₄ : ∀ m₁ m₂ m₃ m₄, ((j₄ : ℤ) - m₄) % 2 ≠ 0 → G m₁ m₂ m₃ m₄ = 0) :
    ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃,
      ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄, G m₁ m₂ m₃ m₄ =
    ∑ α₁ ∈ range (j₁ + 1), ∑ α₂ ∈ range (j₂ + 1), ∑ α₃ ∈ range (j₃ + 1),
      ∑ α₄ ∈ range (j₄ + 1), G ((j₁ : ℤ) - 2 * α₁) ((j₂ : ℤ) - 2 * α₂) ((j₃ : ℤ) - 2 * α₃)
        (2 * (α₄ : ℤ) - j₄) := by
  rw [sum_Icc_eq_sum_range_rev j₁ _ (fun m₁ h => Finset.sum_eq_zero fun m₂ _ =>
    Finset.sum_eq_zero fun m₃ _ => Finset.sum_eq_zero fun m₄ _ => h₁ _ _ _ _ h)]
  refine Finset.sum_congr rfl fun α₁ _ => ?_
  rw [sum_Icc_eq_sum_range_rev j₂ _ (fun m₂ h => Finset.sum_eq_zero fun m₃ _ =>
    Finset.sum_eq_zero fun m₄ _ => h₂ _ _ _ _ h)]
  refine Finset.sum_congr rfl fun α₂ _ => ?_
  rw [sum_Icc_eq_sum_range_rev j₃ _ (fun m₃ h => Finset.sum_eq_zero fun m₄ _ => h₃ _ _ _ _ h)]
  refine Finset.sum_congr rfl fun α₃ _ => ?_
  rw [sum_Icc_eq_sum_range j₄ _ (fun m₄ h => h₄ _ _ _ _ h)]


lemma fourJ_swap₁₂' (a b c d k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ a b c d k m₁ m₂ m₃ m₄ = (-1) ^ ((a + b + k) / 2) * fourJ b a c d k m₂ m₁ m₃ m₄ := by
  rw [fourJ_swap₁₂ a b c d k m₁ m₂ m₃ m₄, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-- **The 6j symbol is the overlap of the two couplings of `a ⊗ b ⊗ c` to spin `J`.** Couple
`a ⊗ b → e` and then `e ⊗ c → J`, or `b ⊗ c → f` and then `a ⊗ f → J`, with the Clebsch–Gordan
matrices `cgMatrix` (which intertwine the representations `spinMat`, `Spin4.cgMatrix_equivariant`).
The Hilbert–Schmidt inner product of the two intertwiners `ℂ^{J+1} → ℂ^{a+1} ⊗ ℂ^{b+1} ⊗ ℂ^{c+1}`
is `(J+1) (-1)^(...) √((e+1)(f+1)) {a b e; c J f}` (doubled units). -/
theorem sum_cg_overlap {a b c k₁ k₂ k₁' k₂' : ℕ} (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b)
    (hk₂e : k₂ ≤ a + b - 2 * k₁) (hk₂c : k₂ ≤ c) (hk₁'b : k₁' ≤ b) (hk₁'c : k₁' ≤ c)
    (hk₂'a : k₂' ≤ a) (hk₂'f : k₂' ≤ b + c - 2 * k₁')
    (hJ : a + b - 2 * k₁ + c - 2 * k₂ = a + (b + c - 2 * k₁') - 2 * k₂') :
    ∑ α ∈ range (a + 1), ∑ β ∈ range (b + 1), ∑ γ ∈ range (c + 1),
      ∑ δ ∈ range (a + b - 2 * k₁ + c - 2 * k₂ + 1),
        (∑ l ∈ range (a + b - 2 * k₁ + 1),
          cgCoefficient a b k₁ l α β * cgCoefficient (a + b - 2 * k₁) c k₂ δ l γ) *
        (∑ l ∈ range (b + c - 2 * k₁' + 1),
          cgCoefficient b c k₁' l β γ * cgCoefficient a (b + c - 2 * k₁') k₂' δ α l) =
      ((a + b - 2 * k₁ + c - 2 * k₂ : ℕ) + 1 : ℝ) *
        ((-1 : ℝ) ^ (a + k₁ + k₂ + b + k₁') *
          (-1) ^ ((a + b + (a + b - 2 * k₁)) / 2) *
          (-1) ^ ((a + c + (a + b - 2 * k₁) + (b + c - 2 * k₁')) / 2)) *
        Real.sqrt ((((a + b - 2 * k₁ : ℕ) : ℝ) + 1) * (((b + c - 2 * k₁' : ℕ) : ℝ) + 1)) *
        sixJSym a b (a + b - 2 * k₁) c (a + b - 2 * k₁ + c - 2 * k₂) (b + c - 2 * k₁') := by
  set J := a + b - 2 * k₁ + c - 2 * k₂ with hJdef
  set e := a + b - 2 * k₁ with he
  set f := b + c - 2 * k₁' with hf
  have hpt : ∀ α ∈ range (a + 1), ∀ β ∈ range (b + 1), ∀ γ ∈ range (c + 1),
      ∀ δ ∈ range (J + 1),
      (∑ l ∈ range (e + 1),
          cgCoefficient a b k₁ l α β * cgCoefficient e c k₂ δ l γ) *
        (∑ l ∈ range (f + 1),
          cgCoefficient b c k₁' l β γ * cgCoefficient a f k₂' δ α l) =
      ((J : ℝ) + 1) * ((-1 : ℝ) ^ (a + k₁ + k₂ + b + k₁') *
          (-1) ^ ((a + b + e) / 2)) *
        (fourJ b a c J e ((b : ℤ) - 2 * β) ((a : ℤ) - 2 * α) ((c : ℤ) - 2 * γ)
            (2 * (δ : ℤ) - J) *
          fourJ b c a J f ((b : ℤ) - 2 * β) ((c : ℤ) - 2 * γ) ((a : ℤ) - 2 * α)
            (2 * (δ : ℤ) - J)) := by
    intro α hα β hβ γ hγ δ hδ
    have hα' := Nat.lt_succ_iff.mp (mem_range.mp hα)
    have hβ' := Nat.lt_succ_iff.mp (mem_range.mp hβ)
    have hγ' := Nat.lt_succ_iff.mp (mem_range.mp hγ)
    have hδ' := Nat.lt_succ_iff.mp (mem_range.mp hδ)
    have hL := sum_cg_left hk₁a hk₁b hk₂e hk₂c hα' hβ' hγ' hδ'
    have hR := sum_cg_right (a := a) (b := b) (c := c) (k₁ := k₁') (k₂ := k₂') (α := α) (β := β)
      (γ := γ) (δ := δ) hk₁'b hk₁'c hk₂'a hk₂'f hα' hβ' hγ' (by omega)
    rw [← hJ] at hR
    rw [hL, hR, show -((J : ℤ) - 2 * δ) = 2 * (δ : ℤ) - J by ring,
      fourJ_swap₁₂' a b c J e]
    have hsq : Real.sqrt ((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 1) = (J : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hsg : (-1 : ℝ) ^ (a + k₁ + k₂ + δ) * (-1) ^ (b + k₁' + δ) =
        (-1) ^ (a + k₁ + k₂ + b + k₁') := by
      rw [← pow_add]; apply neg_one_pow_eq_of_mod; omega
    linear_combination (fourJ b a c J e ((b : ℤ) - 2 * β) ((a : ℤ) - 2 * α) ((c : ℤ) - 2 * γ)
        (2 * (δ : ℤ) - J) * fourJ b c a J f ((b : ℤ) - 2 * β) ((c : ℤ) - 2 * γ)
          ((a : ℤ) - 2 * α) (2 * (δ : ℤ) - J) * (-1 : ℝ) ^ ((a + b + e) / 2)) *
      (Real.sqrt ((J : ℝ) + 1) * Real.sqrt ((J : ℝ) + 1) * hsg + (-1 : ℝ) ^ (a + k₁ + k₂ + b + k₁') * hsq)
  have h4 : ∀ α ∈ range (a + 1), ∀ β ∈ range (b + 1), ∀ γ ∈ range (c + 1),
      ∑ δ ∈ range (J + 1), (∑ l ∈ range (e + 1),
          cgCoefficient a b k₁ l α β * cgCoefficient e c k₂ δ l γ) *
        (∑ l ∈ range (f + 1),
          cgCoefficient b c k₁' l β γ * cgCoefficient a f k₂' δ α l) =
      ∑ δ ∈ range (J + 1), ((J : ℝ) + 1) * ((-1 : ℝ) ^ (a + k₁ + k₂ + b + k₁') *
          (-1) ^ ((a + b + e) / 2)) *
        (fourJ b a c J e ((b : ℤ) - 2 * β) ((a : ℤ) - 2 * α) ((c : ℤ) - 2 * γ)
            (2 * (δ : ℤ) - J) *
          fourJ b c a J f ((b : ℤ) - 2 * β) ((c : ℤ) - 2 * γ) ((a : ℤ) - 2 * α)
            (2 * (δ : ℤ) - J)) :=
    fun α hα β hβ γ hγ => Finset.sum_congr rfl (hpt α hα β hβ γ hγ)
  rw [Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β hβ =>
    Finset.sum_congr rfl (h4 α hα β hβ)]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsw := sum_fourJ_mul_fourJ_swap b a c J e f
  rw [sum4_Icc_eq b a c J _
    (fun m₁ m₂ m₃ m₄ h => by rw [fourJ_zero₁ h, zero_mul])
    (fun m₁ m₂ m₃ m₄ h => by rw [fourJ_zero₂ h, zero_mul])
    (fun m₁ m₂ m₃ m₄ h => by rw [fourJ_zero₃ h, zero_mul])
    (fun m₁ m₂ m₃ m₄ h => by rw [fourJ_zero₄ h, zero_mul])] at hsw
  rw [hsw, sixJSym_swap₁₂]
  ring


open Matrix
open scoped Kronecker

/-- The intertwiner `ℂ^{J+1} → ℂ^{a+1} ⊗ ℂ^{b+1} ⊗ ℂ^{c+1}` coupling `a ⊗ b → e = a+b-2k₁` first and
then `e ⊗ c → J = e+c-2k₂`. -/
noncomputable def coupleLeft (a b c k₁ k₂ : ℕ) :
    Matrix (Idx a b × Fin (c + 1)) (Fin (a + b - 2 * k₁ + c - 2 * k₂ + 1)) ℂ :=
  (cgMatrix a b k₁ ⊗ₖ (1 : Matrix (Fin (c + 1)) (Fin (c + 1)) ℂ)) *
    cgMatrix (a + b - 2 * k₁) c k₂

/-- The intertwiner coupling `b ⊗ c → f = b+c-2k₁` first and then `a ⊗ f → J = a+f-2k₂`. -/
noncomputable def coupleRight (a b c k₁ k₂ : ℕ) :
    Matrix (Fin (a + 1) × Idx b c) (Fin (a + (b + c - 2 * k₁) - 2 * k₂ + 1)) ℂ :=
  ((1 : Matrix (Fin (a + 1)) (Fin (a + 1)) ℂ) ⊗ₖ cgMatrix b c k₁) *
    cgMatrix a (b + c - 2 * k₁) k₂

/-- The matrix `coupleLeft` intertwines `spinMat a ⊗ spinMat b ⊗ spinMat c` with `spinMat J`. -/
theorem coupleLeft_equivariant {a b c k₁ k₂ : ℕ} (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b)
    (hk₂e : k₂ ≤ a + b - 2 * k₁) (hk₂c : k₂ ≤ c) (g : SU2) :
    ((spinMat a g ⊗ₖ spinMat b g) ⊗ₖ spinMat c g) * coupleLeft a b c k₁ k₂ =
      coupleLeft a b c k₁ k₂ * spinMat (a + b - 2 * k₁ + c - 2 * k₂) g := by
  have h1 := cgMatrix_equivariant hk₁a hk₁b g
  have h2 := cgMatrix_equivariant hk₂e hk₂c g
  unfold coupleLeft
  calc _ = (((spinMat a g ⊗ₖ spinMat b g) ⊗ₖ spinMat c g) *
          (cgMatrix a b k₁ ⊗ₖ (1 : Matrix (Fin (c + 1)) (Fin (c + 1)) ℂ))) *
          cgMatrix (a + b - 2 * k₁) c k₂ := by rw [Matrix.mul_assoc]
    _ = ((cgMatrix a b k₁ ⊗ₖ (1 : Matrix (Fin (c + 1)) (Fin (c + 1)) ℂ)) *
          (spinMat (a + b - 2 * k₁) g ⊗ₖ spinMat c g)) * cgMatrix (a + b - 2 * k₁) c k₂ := by
        rw [← Matrix.mul_kronecker_mul, h1, Matrix.mul_one, ← Matrix.mul_kronecker_mul,
          Matrix.one_mul]
    _ = (cgMatrix a b k₁ ⊗ₖ (1 : Matrix (Fin (c + 1)) (Fin (c + 1)) ℂ)) *
          (cgMatrix (a + b - 2 * k₁) c k₂ * spinMat (a + b - 2 * k₁ + c - 2 * k₂) g) := by
        rw [Matrix.mul_assoc, h2]
    _ = _ := by rw [Matrix.mul_assoc]

/-- The matrix `coupleRight` intertwines `spinMat a ⊗ spinMat b ⊗ spinMat c` with `spinMat J`. -/
theorem coupleRight_equivariant {a b c k₁ k₂ : ℕ} (hk₁b : k₁ ≤ b) (hk₁c : k₁ ≤ c)
    (hk₂a : k₂ ≤ a) (hk₂f : k₂ ≤ b + c - 2 * k₁) (g : SU2) :
    (spinMat a g ⊗ₖ (spinMat b g ⊗ₖ spinMat c g)) * coupleRight a b c k₁ k₂ =
      coupleRight a b c k₁ k₂ * spinMat (a + (b + c - 2 * k₁) - 2 * k₂) g := by
  have h1 := cgMatrix_equivariant hk₁b hk₁c g
  have h2 := cgMatrix_equivariant hk₂a hk₂f g
  unfold coupleRight
  calc _ = ((spinMat a g ⊗ₖ (spinMat b g ⊗ₖ spinMat c g)) *
          ((1 : Matrix (Fin (a + 1)) (Fin (a + 1)) ℂ) ⊗ₖ cgMatrix b c k₁)) *
          cgMatrix a (b + c - 2 * k₁) k₂ := by rw [Matrix.mul_assoc]
    _ = (((1 : Matrix (Fin (a + 1)) (Fin (a + 1)) ℂ) ⊗ₖ cgMatrix b c k₁) *
          (spinMat a g ⊗ₖ spinMat (b + c - 2 * k₁) g)) * cgMatrix a (b + c - 2 * k₁) k₂ := by
        rw [← Matrix.mul_kronecker_mul, h1, Matrix.mul_one, ← Matrix.mul_kronecker_mul,
          Matrix.one_mul]
    _ = ((1 : Matrix (Fin (a + 1)) (Fin (a + 1)) ℂ) ⊗ₖ cgMatrix b c k₁) *
          (cgMatrix a (b + c - 2 * k₁) k₂ *
            spinMat (a + (b + c - 2 * k₁) - 2 * k₂) g) := by
        rw [Matrix.mul_assoc, h2]
    _ = _ := by rw [Matrix.mul_assoc]

/-- The entries of `coupleLeft`: the sums of Clebsch–Gordan coefficients of `sum_cg_overlap`. -/
theorem coupleLeft_apply (a b c k₁ k₂ : ℕ) (α : Fin (a + 1)) (β : Fin (b + 1)) (γ : Fin (c + 1))
    (δ : Fin (a + b - 2 * k₁ + c - 2 * k₂ + 1)) :
    coupleLeft a b c k₁ k₂ ((α, β), γ) δ =
      ((∑ l ∈ range (a + b - 2 * k₁ + 1),
        cgCoefficient a b k₁ l α β * cgCoefficient (a + b - 2 * k₁) c k₂ δ l γ : ℝ) : ℂ) := by
  unfold coupleLeft
  rw [Matrix.mul_apply, Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range
    (fun l => cgCoefficient a b k₁ l α β * cgCoefficient (a + b - 2 * k₁) c k₂ δ l γ)]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single γ]
  · simp [Matrix.kroneckerMap_apply, cgMatrix_apply]
  · intro γ' _ hne
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hne)]
  · simp

/-- The entries of `coupleRight`. -/
theorem coupleRight_apply (a b c k₁ k₂ : ℕ) (α : Fin (a + 1)) (β : Fin (b + 1)) (γ : Fin (c + 1))
    (δ : Fin (a + (b + c - 2 * k₁) - 2 * k₂ + 1)) :
    coupleRight a b c k₁ k₂ (α, (β, γ)) δ =
      ((∑ l ∈ range (b + c - 2 * k₁ + 1),
        cgCoefficient b c k₁ l β γ * cgCoefficient a (b + c - 2 * k₁) k₂ δ α l : ℝ) : ℂ) := by
  unfold coupleRight
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single α]
  · rw [← Fin.sum_univ_eq_sum_range
      (fun l => cgCoefficient b c k₁ l β γ * cgCoefficient a (b + c - 2 * k₁) k₂ δ α l)]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Matrix.kroneckerMap_apply, cgMatrix_apply, mul_comm]
  · intro α' _ hne
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hne)]
  · simp


/-! ## Non-vacuity -/

/-- The hypotheses of `sum_cg_overlap` hold, for three spins `1/2` coupled to `J = 3/2`. -/
example : (0 : ℕ) ≤ 1 ∧ (0 : ℕ) ≤ 1 ∧ (0 : ℕ) ≤ 1 + 1 - 2 * 0 ∧ (0 : ℕ) ≤ 1 ∧
    1 + 1 - 2 * 0 + 1 - 2 * 0 = 1 + (1 + 1 - 2 * 0) - 2 * 0 := by omega

/-- The overlap theorem applied to three spins `1/2` coupled to `3/2`. -/
example := sum_cg_overlap (a := 1) (b := 1) (c := 1) (k₁ := 0) (k₂ := 0) (k₁' := 0) (k₂' := 0)
  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  (by omega)

end Lightlike.SU2

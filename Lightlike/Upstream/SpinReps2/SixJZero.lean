module

public import Lightlike.Upstream.SpinReps2.ThreeJOrth

/-!
# 3j and 6j symbols with a zero spin; the total square sum of a 3j symbol

Preparatory material for the orthogonality of the 6j symbols for all spins (`SixJOrth.lean`), in
Physlib's doubled-spin parametrisation (`jᵢ ∈ ℕ` twice the spin, `mᵢ ∈ ℤ` twice the projection).

## Main results

* `PhyslibAlpha.Sl2.sum_threeJ_sq`: `Σ_{m₁ m₂ m₃} (j₁ j₂ j₃; m₁ m₂ m₃)² = 1` for an admissible
  triad `(j₁ j₂ j₃)` and `0` otherwise.
* `PhyslibAlpha.Sl2.sixJSym_zero_left`: the closed form of the 6j symbol with a zero spin,
  `{0 j₂ j₃; j₄ j₅ j₆} = δ_{j₂ j₃} δ_{j₅ j₆} [(j₂ j₅ j₄) admissible] (-1)^{(j₂+j₅+j₄)/2} /
  √((j₂+1)(j₅+1))`.
-/

@[expose] public section

open Finset

namespace PhyslibAlpha.Sl2

/-- **3j orthogonality, summed over all projections**: `Σ_{m₁ m₂ m₃} (j₁ j₂ j₃; m₁ m₂ m₃)² = 1` for
an admissible triad, `0` otherwise. -/
lemma sum_threeJ_sq (j₁ j₂ j₃ : ℕ) :
    ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃,
      threeJ j₁ j₂ j₃ m₁ m₂ m₃ ^ 2 = if Triad j₁ j₂ j₃ then 1 else 0 := by
  by_cases ht : Triad j₁ j₂ j₃
  · rw [ite_eq_left ht]
    obtain ⟨hpar, hA, hB, hC⟩ := ht
    by_cases h0 : j₁ + j₂ = 0
    · have h1 : j₁ = 0 := by omega
      have h2 : j₂ = 0 := by omega
      have h3 : j₃ = 0 := by omega
      subst h1 h2 h3
      simp [threeJ_zero_left]
    -- bring `m₃` outside and reindex all three projections
    rw [sum_congr rfl fun m₁ _ => sum_comm, sum_comm, sum_Icc_neg j₃]
    rw [sum_Icc_parity j₃ _ (fun μ hμ => by
      refine sum_eq_zero fun m₁ _ => sum_eq_zero fun m₂ _ => ?_
      rw [threeJ_of_not (fun h => by obtain ⟨_, -, -, -, -, -, -, -, -, h10, -⟩ := h; omega)]
      ring)]
    set k := (j₁ + j₂ - j₃) / 2 with hk
    have hJ : j₁ + j₂ - 2 * k = j₃ := by omega
    have hterm : ∀ l ∈ range (j₃ + 1),
        ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂,
          threeJ j₁ j₂ j₃ m₁ m₂ (-((j₃ : ℤ) - 2 * l)) ^ 2 = 1 / ((j₃ + 1 : ℕ) : ℝ) := by
      intro l hl
      simp only [mem_range] at hl
      rw [sum_Icc_parity j₁ _ (fun μ hμ => sum_eq_zero fun m₂ _ => by
        rw [threeJ_of_not (fun h => by obtain ⟨_, -, -, -, -, -, -, h8, -⟩ := h; omega)]; ring)]
      rw [sum_congr rfl fun (α : ℕ) _ => sum_Icc_parity j₂
        (fun m₂ => threeJ j₁ j₂ j₃ ((j₁ : ℤ) - 2 * (α : ℤ)) m₂ (-((j₃ : ℤ) - 2 * (l : ℤ))) ^ 2)
        (fun μ hμ => by
          rw [threeJ_of_not (fun h => by obtain ⟨_, -, -, -, -, -, -, -, h9, -⟩ := h; omega)]
          ring)]
      have hw := sum_wigner3j_mul_wigner3j (m := j₁) (n := j₂) (by omega) (k := k) (k' := k)
        (l := l) (l' := l) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [ite_eq_left ⟨rfl, rfl⟩, show j₁ + j₂ - 2 * k + 1 = j₃ + 1 by omega] at hw
      rw [← hw]
      refine sum_congr rfl fun α hα => sum_congr rfl fun β hβ => ?_
      simp only [mem_range] at hα hβ
      rw [wigner3j_eq_threeJ (by omega) (by omega) (by omega) (by omega) (by omega), hJ, sq]
    rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
    field_simp
  · rw [ite_eq_right ht]
    refine sum_eq_zero fun m₁ _ => sum_eq_zero fun m₂ _ => sum_eq_zero fun m₃ _ => ?_
    rw [threeJ_of_not (fun h => ht (by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, h10, h11, h12, h13⟩ := h
      exact ⟨h13, h10, h11, h12⟩))]
    ring

/-- `(-1)^m = (-1)^n` for natural exponents of the same parity. -/
lemma neg_one_pow_congr_mod {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℝ) ^ m = (-1) ^ n := by
  rw [← Nat.mod_add_div m 2, ← Nat.mod_add_div n 2, pow_add, pow_add, pow_mul, pow_mul, h]
  simp

/-- The summand of `sixJSym 0 j₂ j₂ j₄ j₅ j₅` on the support `(0, m₁, -m₁, m₃, m₄, m₄)`: a constant
times a squared 3j symbol. -/
lemma sixJTerm_zero_support (j₂ j₄ j₅ : ℕ) (m₁ m₃ m₄ : ℤ) :
    sixJTerm 0 j₂ j₂ j₄ j₅ j₅ ![0, m₁, -m₁, m₃, m₄, m₄] =
      (-1) ^ ((j₂ + j₅ + j₄) / 2) / (Real.sqrt ((j₂ : ℝ) + 1) * Real.sqrt ((j₅ : ℝ) + 1)) *
        threeJ j₄ j₂ j₅ m₃ m₁ (-m₄) ^ 2 := by
  unfold sixJTerm
  simp only [show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 0 = 0 from rfl,
    show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 1 = m₁ from rfl,
    show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 2 = -m₁ from rfl,
    show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 3 = m₃ from rfl,
    show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 4 = m₄ from rfl,
    show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 5 = m₄ from rfl]
  by_cases hT : threeJ j₄ j₂ j₅ m₃ m₁ (-m₄) = 0
  · rw [hT]; ring
  have hA : Adm3 j₄ j₂ j₅ m₃ m₁ (-m₄) := by
    by_contra h
    exact hT (threeJ_of_not h)
  obtain ⟨hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hA
  -- the fourth 3j symbol equals the third
  have h4th : threeJ j₄ j₅ j₂ (-m₃) m₄ (-m₁) = threeJ j₄ j₂ j₅ m₃ m₁ (-m₄) := by
    have hn := threeJ_neg j₄ j₂ j₅ m₃ m₁ (-m₄)
    rw [neg_neg] at hn
    rw [threeJ_swap₂₃ j₄ j₂ j₅ (-m₃) (-m₁) m₄, hn, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [h4th, threeJ_zero_left, threeJ_zero_left,
    ite_eq_left ⟨by omega, rfl, by omega, by omega, by omega, by omega⟩,
    ite_eq_left ⟨rfl, rfl, by omega, by omega, by omega, by omega⟩]
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℕ, (j₂ : ℤ) + m₁ = 2 * k := ⟨(((j₂ : ℤ) + m₁) / 2).toNat, by omega⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℕ, (j₅ : ℤ) + m₄ = 2 * k := ⟨(((j₅ : ℤ) + m₄) / 2).toNat, by omega⟩
  obtain ⟨k₃, hk₃⟩ : ∃ k : ℕ, (j₄ : ℤ) - m₃ = 2 * k := ⟨(((j₄ : ℤ) - m₃) / 2).toNat, by omega⟩
  have hE : 0 ≤ ((((0 : ℕ) : ℤ) - 0 + ((j₂ : ℤ) - m₁) + ((j₂ : ℤ) - -m₁) + ((j₄ : ℤ) - m₃) +
      ((j₅ : ℤ) - m₄) + ((j₅ : ℤ) - m₄)) / 2) := by omega
  have eE : ((((0 : ℕ) : ℤ) - 0 + ((j₂ : ℤ) - m₁) + ((j₂ : ℤ) - -m₁) + ((j₄ : ℤ) - m₃) +
      ((j₅ : ℤ) - m₄) + ((j₅ : ℤ) - m₄)) / 2).toNat = j₂ + k₃ + 2 * j₅ - 2 * k₂ := by omega
  have e1 : (((j₂ : ℤ) - -m₁) / 2).toNat = k₁ := by omega
  have e2 : (((j₅ : ℤ) - -m₄) / 2).toNat = k₂ := by omega
  rw [← Int.toNat_of_nonneg hE, zpow_natCast, eE, e1, e2]
  clear h7 h8 h9 h10 h13 hE eE e1 e2
  have hsign : (-1 : ℝ) ^ (j₂ + k₃ + 2 * j₅ - 2 * k₂) * ((-1) ^ k₁ * (-1) ^ k₂) =
      (-1) ^ ((j₂ + j₅ + j₄) / 2) := by
    rw [← pow_add, ← pow_add]
    exact neg_one_pow_congr_mod (by omega)
  rw [← hsign]
  ring

/-- **The 6j symbol with a zero spin** (doubled units):
`{0 j₂ j₃; j₄ j₅ j₆} = δ_{j₂ j₃} δ_{j₅ j₆} [(j₂ j₅ j₄) admissible] (-1)^{(j₂+j₅+j₄)/2} /
√((j₂+1)(j₅+1))`. -/
theorem sixJSym_zero_left (j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym 0 j₂ j₃ j₄ j₅ j₆ =
      if j₃ = j₂ ∧ j₆ = j₅ ∧ Triad j₂ j₅ j₄ then
        (-1) ^ ((j₂ + j₅ + j₄) / 2) / (Real.sqrt ((j₂ : ℝ) + 1) * Real.sqrt ((j₅ : ℝ) + 1))
      else 0 := by
  by_cases h23 : j₃ = j₂
  swap
  · rw [ite_eq_right (fun h => h23 h.1)]
    refine sum_eq_zero fun m _ => ?_
    rw [sixJTerm, threeJ_zero_left, ite_eq_right (fun h => h23 h.2.1)]
    ring
  by_cases h56 : j₆ = j₅
  swap
  · rw [ite_eq_right (fun h => h56 h.2.1)]
    refine sum_eq_zero fun m _ => ?_
    rw [sixJTerm, threeJ_zero_left j₅ j₆ (m 0) (-m 4) (m 5), ite_eq_right (fun h => h56 h.2.1)]
    ring
  subst j₃ j₆
  unfold sixJSym
  set g : (ℤ × ℤ) × ℤ → (Fin 6 → ℤ) := fun x => ![0, x.1.1, -x.1.1, x.1.2, x.2, x.2] with hg
  set P := (Icc (-(j₂ : ℤ)) j₂ ×ˢ Icc (-(j₄ : ℤ)) j₄) ×ˢ Icc (-(j₅ : ℤ)) j₅ with hP
  have hsub : P.image g ⊆ sixJBox 0 j₂ j₂ j₄ j₅ j₅ := by
    intro m hm
    simp only [hP, mem_image, mem_product, mem_Icc] at hm
    obtain ⟨⟨⟨m₁, m₃⟩, m₄⟩, ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩, rfl⟩ := hm
    dsimp only at h1 h2 h3 h4 h5 h6
    rw [mem_sixJBox]
    simp only [hg, show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 0 = 0 from rfl,
      show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 1 = m₁ from rfl,
      show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 2 = -m₁ from rfl,
      show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 3 = m₃ from rfl,
      show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 4 = m₄ from rfl,
      show (![0, m₁, -m₁, m₃, m₄, m₄] : Fin 6 → ℤ) 5 = m₄ from rfl]
    omega
  have hzero : ∀ m ∈ sixJBox 0 j₂ j₂ j₄ j₅ j₅, m ∉ P.image g →
      sixJTerm 0 j₂ j₂ j₄ j₅ j₅ m = 0 := by
    intro m hm hnot
    by_contra hne
    apply hnot
    have hprod := right_ne_zero_of_mul hne
    have hA := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hprod))
    have hB := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hprod))
    rw [threeJ_zero_left] at hA
    rw [threeJ_zero_left] at hB
    split_ifs at hA with cA
    swap
    · exact absurd rfl hA
    split_ifs at hB with cB
    swap
    · exact absurd rfl hB
    rw [mem_sixJBox] at hm
    simp only [hP, mem_image, mem_product, mem_Icc]
    refine ⟨((m 1, m 3), m 4), ⟨⟨⟨by dsimp only; omega, by dsimp only; omega⟩, by dsimp only; omega,
      by dsimp only; omega⟩, by dsimp only; omega, by dsimp only; omega⟩, ?_⟩
    funext i
    fin_cases i <;> simp [hg] <;> omega
  rw [← sum_subset hsub hzero, sum_image]
  · rw [sum_congr rfl fun x _ => sixJTerm_zero_support j₂ j₄ j₅ x.1.1 x.1.2 x.2,
      ← mul_sum, hP, sum_product, sum_product, sum_comm]
    rw [sum_congr rfl fun m₃ _ => sum_congr rfl fun m₁ _ =>
      sum_Icc_neg j₅ (fun m₄ => threeJ j₄ j₂ j₅ m₃ m₁ (-m₄) ^ 2)]
    simp only [neg_neg]
    rw [sum_threeJ_sq]
    by_cases ht : Triad j₂ j₅ j₄
    · have ht' : Triad j₄ j₂ j₅ := by unfold Triad at ht ⊢; omega
      rw [ite_eq_left ht', ite_eq_left ⟨trivial, trivial, ht⟩, mul_one]
    · have ht' : ¬ Triad j₄ j₂ j₅ := fun h => ht (by unfold Triad at h ⊢; omega)
      rw [ite_eq_right ht', ite_eq_right (fun h => ht h.2.2), mul_zero]
  · intro x _ y _ hxy
    have h1 := congrFun hxy 1
    have h3 := congrFun hxy 3
    have h4 := congrFun hxy 4
    simp only [hg] at h1 h3 h4
    exact Prod.ext (Prod.ext h1 h3) h4

end PhyslibAlpha.Sl2

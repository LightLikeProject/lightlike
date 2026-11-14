module

public import Lightlike.PonzanoRegge.BEPositive

/-!
# Biedenharn–Elliott with a zero spin (stage 6 of the pentagon route), and the full identity

The file ends with `biedenharnElliott`: the identity for **all** spins.

Step 1: closed forms of 3j and 6j symbols with a zero spin, from Physlib's definitions.

* `threeJ_zero_left`: `(0 b c; m₁ m₂ m₃) = δ_{m₁,0} δ_{c,b} δ_{m₃,-m₂} (-1)^{(b-m₂)/2} / √(b+1)`
  (doubled units). With a zero spin the Regge square has zero entries, and Physlib's alternating
  factorial sum `sixSum` has a single term.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace Lightlike.Pentagon

instance (x y z : ℕ) : Decidable (Tri x y z) := by unfold Tri; infer_instance

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

/-- **The 3j symbol with a zero first spin.** -/
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

/-- **3j orthogonality, summed over all projections**: `Σ_{m₁ m₂ m₃} (j₁ j₂ j₃; m₁ m₂ m₃)² = 1` for an
admissible triad, `0` otherwise. -/
lemma sum_threeJ_sq (j₁ j₂ j₃ : ℕ) :
    ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃,
      threeJ j₁ j₂ j₃ m₁ m₂ m₃ ^ 2 = if Tri j₁ j₂ j₃ then 1 else 0 := by
  by_cases ht : Tri j₁ j₂ j₃
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
    exact neg_one_pow_eq_of_mod (by omega)
  rw [← hsign]
  ring

/-- **The 6j symbol with a zero spin** (doubled units):
`{0 j₂ j₃; j₄ j₅ j₆} = δ_{j₂ j₃} δ_{j₅ j₆} [(j₂ j₅ j₄) admissible] (-1)^{(j₂+j₅+j₄)/2} / √((j₂+1)(j₅+1))`.
Checked numerically in `scripts/sixj_zero_check.py`. -/
theorem sixJSym_zero_left (j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym 0 j₂ j₃ j₄ j₅ j₆ =
      if j₃ = j₂ ∧ j₆ = j₅ ∧ Tri j₂ j₅ j₄ then
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
    by_cases ht : Tri j₂ j₅ j₄
    · have ht' : Tri j₄ j₂ j₅ := by unfold Tri at ht ⊢; omega
      rw [ite_eq_left ht', ite_eq_left ⟨trivial, trivial, ht⟩, mul_one]
    · have ht' : ¬ Tri j₄ j₂ j₅ := fun h => ht (by unfold Tri at h ⊢; omega)
      rw [ite_eq_right ht', ite_eq_right (fun h => ht h.2.2), mul_zero]
  · intro x _ y _ hxy
    have h1 := congrFun hxy 1
    have h3 := congrFun hxy 3
    have h4 := congrFun hxy 4
    simp only [hg] at h1 h3 h4
    exact Prod.ext (Prod.ext h1 h3) h4

/-! ## Step 2: symmetries of the Biedenharn–Elliott identity -/

lemma sj_swap12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₂ j₁ j₃ j₅ j₄ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![0, 2, 1, 3] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_flip12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₄ j₅ j₃ j₁ j₂ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![3, 2, 1, 0] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_swap23 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₃ j₂ j₄ j₆ j₅ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![0, 1, 3, 2] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_flipswap (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₅ j₄ j₃ j₂ j₁ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![3, 1, 2, 0] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_swap13 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₃ j₂ j₁ j₆ j₅ j₄ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![0, 3, 2, 1] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- One term of `beLHS`. -/
noncomputable def beTerm (a b c d e f p q r x : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) * ((x : ℝ) + 1) *
    (sixJSym a b x c d p * sixJSym c d x e f q * sixJSym e f x b a r)

/-- `beLHS` may be summed over any range containing `[0, a + b]` (larger `x` violate the triangle
rule in `(a b x)`). -/
lemma beLHS_eq_sum (a b c d e f p q r N : ℕ) (hN : a + b ≤ N) :
    beLHS a b c d e f p q r = ∑ x ∈ range (N + 1), beTerm a b c d e f p q r x := by
  unfold beLHS
  apply sum_subset
  · intro x hx; simp only [mem_range] at hx ⊢; omega
  · intro x _ hx
    simp only [mem_range, not_lt] at hx
    rw [sixJSym_vanishes_beyond_range (show a + b < x by omega)]
    ring

/-- Symmetry `D ↔ E` of the 2-3 configuration. -/
theorem be_swapDE (a b c d e f p q r : ℕ) :
    beLHS b a d c f e p q r = beLHS a b c d e f p q r ∧
      beRHS b a d c f e p q r = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_swap12 a b x c d p, sj_swap12 c d x e f q, sj_swap12 e f x b a r,
      show b + a + d + c + f + e + p + q + r + x = a + b + c + d + e + f + p + q + r + x by ring]
  · rw [beRHS, beRHS, mul_comm]

/-- Symmetry `A ↔ B` of the 2-3 configuration. -/
theorem be_swapAB (a b c d e f p q r : ℕ) :
    beLHS d c b a e f p r q = beLHS a b c d e f p q r ∧
      beRHS d c b a e f p r q = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_flipswap a b x c d p, sj_flip12 e f x b a r, sj_flip12 c d x e f q,
      show d + c + b + a + e + f + p + r + q + x = a + b + c + d + e + f + p + q + r + x by ring]
    ring
  · rw [beRHS, beRHS, sj_swap23 p q r e a d, sj_swap23 p q r f b c]

/-- Symmetry `A ↔ C` of the 2-3 configuration. -/
theorem be_swapAC (a b c d e f p q r : ℕ) :
    beLHS e f c d a b q p r = beLHS a b c d e f p q r ∧
      beRHS e f c d a b q p r = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_flip12 c d x e f q, sj_flip12 a b x c d p, sj_flipswap e f x b a r,
      show e + f + c + d + a + b + q + p + r + x = a + b + c + d + e + f + p + q + r + x by ring]
    ring
  · rw [beRHS, beRHS, sj_swap12 p q r e a d, sj_swap12 p q r f b c]

/-- Symmetry `B ↔ C` of the 2-3 configuration. -/
theorem be_swapBC (a b c d e f p q r : ℕ) :
    beLHS a b f e d c r q p = beLHS a b c d e f p q r ∧
      beRHS a b f e d c r q p = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_flipswap e f x b a r, sj_flipswap c d x e f q, sj_flipswap a b x c d p,
      show a + b + f + e + d + c + r + q + p + x = a + b + c + d + e + f + p + q + r + x by ring]
    ring
  · rw [beRHS, beRHS, sj_swap13 p q r e a d, sj_swap13 p q r f b c, mul_comm]

/-! ## Step 3: the case `a = 0` -/

lemma sj_M1 (b c d e f q : ℕ) : sixJSym d q e f b c = sixJSym c d b e f q := by
  have := sixJSym_perm (permOf ![2, 0, 1, 3] (by decide)) c d b e f q
  simpa [permOf, edgeM] using this

/-- **Biedenharn–Elliott with `a = 0`** (all other spins arbitrary): the `x`-sum collapses to
`x = b` and three of the 6j symbols take the zero-spin closed form. -/
theorem be_a_zero (b c d e f p q r : ℕ) : beLHS 0 b c d e f p q r = beRHS 0 b c d e f p q r := by
  unfold beLHS beRHS
  rw [sj_flipswap 0 e r q p d, sum_eq_single b]
  · rw [sj_flipswap 0 b b f e r, sixJSym_zero_left b b c d p, sixJSym_zero_left b b f e r,
      sixJSym_zero_left e r q p d]
    by_cases hpd : p = d
    swap
    · rw [ite_eq_right (show ¬(b = b ∧ p = d ∧ Tri b d c) from fun h => hpd h.2.1),
        ite_eq_right (show ¬(r = e ∧ d = p ∧ Tri e p q) from fun h => hpd h.2.1.symm)]
      ring
    by_cases hre : r = e
    swap
    · rw [ite_eq_right (show ¬(b = b ∧ r = e ∧ Tri b e f) from fun h => hre h.2.1),
        ite_eq_right (show ¬(r = e ∧ d = p ∧ Tri e p q) from fun h => hre h.1)]
      ring
    subst p r
    rw [sj_M1 b c d e f q]
    by_cases hM : sixJSym c d b e f q = 0
    · rw [hM]; ring
    obtain ⟨T1, T2, T3, T4⟩ := tri_of_sixJSym_ne_zero hM
    have h1 : Tri b d c := by unfold Tri at *; omega
    have h2 : Tri b e f := by unfold Tri at *; omega
    rw [ite_eq_left ⟨rfl, rfl, h1⟩, ite_eq_left ⟨rfl, rfl, h2⟩, ite_eq_left ⟨rfl, rfl, T3⟩]
    have hb0 : 0 < Real.sqrt ((b : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hd0 : 0 < Real.sqrt ((d : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have he0 : 0 < Real.sqrt ((e : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsign : (-1 : ℝ) ^ ((0 + b + c + d + e + f + d + q + e + b) / 2) *
        (-1) ^ ((b + d + c) / 2) * (-1) ^ ((b + e + f) / 2) = (-1) ^ ((e + d + q) / 2) := by
      rw [← pow_add, ← pow_add]
      exact neg_one_pow_eq_of_mod (by unfold Tri at *; omega)
    rw [← hsign]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  · intro x _ hx
    rw [sixJSym_zero_left, ite_eq_right (fun h => hx h.1)]
    ring
  · intro h
    simp at h

/-! ## Step 4: 6j orthogonality in `sixJSym` form, and the case `p = 0` -/

/-- **6j orthogonality** (doubled units), translated from Physlib's `sum_sixJ_mul_sixJ`:
`Σ_x (x+1)(q+1) {B A x; E F q}{B A x; E F r} = δ_{qr} [(A E q), (B q F) admissible]`, for
`B, E > 0`. Checked numerically on 2,304 cases. -/
theorem sixJSym_orth {B A E F q r : ℕ} (hB : 0 < B) (hE : 0 < E) :
    ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym B A x E F q * sixJSym B A x E F r) =
      if q = r ∧ Tri A E q ∧ Tri B q F then 1 else 0 := by
  have hBA : 0 < B + A := by omega
  have hAE : 0 < A + E := by omega
  -- if `q` is not an admissible label, every term vanishes
  by_cases hq : Tri A E q ∧ Tri B q F
  swap
  · rw [ite_eq_right (fun h => hq ⟨h.2.1, h.2.2⟩)]
    refine sum_eq_zero fun x _ => ?_
    have h0 : sixJSym B A x E F q = 0 := by
      by_contra h
      obtain ⟨-, T2, T3, -⟩ := tri_of_sixJSym_ne_zero h
      exact hq ⟨by unfold Tri at *; omega, by unfold Tri at *; omega⟩
    rw [h0]; ring
  by_cases hr : Tri A E r ∧ Tri B r F
  swap
  · rw [ite_eq_right (show ¬(q = r ∧ Tri A E q ∧ Tri B q F) from fun h => by
      obtain ⟨rfl, h1, h2⟩ := h
      exact hr ⟨h1, h2⟩)]
    refine sum_eq_zero fun x _ => ?_
    have h0 : sixJSym B A x E F r = 0 := by
      by_contra h
      obtain ⟨-, T2, T3, -⟩ := tri_of_sixJSym_ne_zero h
      exact hr ⟨by unfold Tri at *; omega, by unfold Tri at *; omega⟩
    rw [h0]; ring
  obtain ⟨⟨q0, q1, q2, q3⟩, ⟨q4, q5, q6, q7⟩⟩ := hq
  obtain ⟨⟨r0, r1, r2, r3⟩, ⟨r4, r5, r6, r7⟩⟩ := hr
  have hPhys := sum_sixJ_mul_sixJ (a := B) (b := A) (c := E) hBA hAE hB hE
    (K := (B + A + E - F) / 2)
    (k₃ := ⟨(A + E - q) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩)
    (k₃' := ⟨(A + E - r) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩)
    (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega)
    (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega)
  have hrhs : (if (⟨(A + E - q) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩ :
      Fin (min A E + 1)) = ⟨(A + E - r) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr
        ⟨by omega, by omega⟩)⟩ then (1 : ℝ) else 0) =
      if q = r ∧ Tri A E q ∧ Tri B q F then 1 else 0 := by
    by_cases hqr : q = r
    · subst hqr
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, ⟨q0, q1, q2, q3⟩, ⟨q4, q5, q6, q7⟩⟩]
    · rw [ite_eq_right (fun h => hqr (by have := congrArg Fin.val h; simp only at this; omega)),
        ite_eq_right (fun h => hqr h.1)]
  rw [← hrhs, ← hPhys, sum_range_eq_sum_fin B A]
  · refine sum_congr rfl fun k₁ _ => ?_
    have hk₁ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁.isLt)
    by_cases hA : ValidA B A E ((B + A + E - F) / 2) k₁
    · rw [sixJ_eq_sixJSym hBA hAE hB hE hA (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;>
          omega),
        sixJ_eq_sixJSym hBA hAE hB hE hA (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;>
          omega)]
      simp only
      obtain ⟨a1, a2, a3⟩ := hA
      rw [show B + A + E - 2 * ((B + A + E - F) / 2) = F by omega,
        show A + E - 2 * ((A + E - q) / 2) = q by omega,
        show A + E - 2 * ((A + E - r) / 2) = r by omega]
      push_cast
      ring
    · rw [show sixJSym B A (B + A - 2 * (k₁ : ℕ)) E F q = 0 by
        by_contra h
        obtain ⟨-, -, -, T4⟩ := tri_of_sixJSym_ne_zero h
        exact hA (by unfold Tri at T4; unfold ValidA; refine ⟨?_, ?_, ?_⟩ <;> omega)]
      unfold sixJ
      rw [ite_eq_right (fun h => hA h.1)]
      ring
  · intro x hx
    have h0 : sixJSym B A x E F q = 0 := by
      by_contra h
      exact hx (tri_of_sixJSym_ne_zero h).1
    rw [h0]; ring

/-- One term of the `p = 0` case: a constant times the orthogonality summand. -/
lemma be_p_zero_term {a b e f q r x : ℕ} :
    (-1 : ℝ) ^ ((a + b + b + a + e + f + 0 + q + r + x) / 2) * ((x : ℝ) + 1) *
        ((if a = a ∧ b = b ∧ Tri a b x then
            (-1) ^ ((a + b + x) / 2) / (Real.sqrt ((a : ℝ) + 1) * Real.sqrt ((b : ℝ) + 1)) else 0) *
          sixJSym b a x e f q * sixJSym e f x b a r) =
      (-1) ^ ((a + b + e + f + q + r) / 2) /
          (((q : ℝ) + 1) * (Real.sqrt ((a : ℝ) + 1) * Real.sqrt ((b : ℝ) + 1))) *
        (((x : ℝ) + 1) * ((q : ℝ) + 1) * (sixJSym b a x e f q * sixJSym b a x e f r)) := by
  rw [sj_flip12 b a x e f r]
  by_cases hq : sixJSym b a x e f q = 0
  · rw [hq]; ring
  by_cases hr : sixJSym b a x e f r = 0
  · rw [hr]; ring
  obtain ⟨⟨p1, -, -, -⟩, ⟨p2, -, -, -⟩, -, ⟨p4, -, -, -⟩⟩ := tri_of_sixJSym_ne_zero hq
  obtain ⟨T1, ⟨p5, -, -, -⟩, -, -⟩ := tri_of_sixJSym_ne_zero hr
  have hab : Tri a b x := by unfold Tri at T1 ⊢; omega
  rw [ite_eq_left ⟨rfl, rfl, hab⟩]
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have ha0 : 0 < Real.sqrt ((a : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hb0 : 0 < Real.sqrt ((b : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsign : (-1 : ℝ) ^ ((a + b + b + a + e + f + 0 + q + r + x) / 2) * (-1) ^ ((a + b + x) / 2) =
      (-1) ^ ((a + b + e + f + q + r) / 2) := by
    rw [← pow_add]
    exact neg_one_pow_eq_of_mod (by omega)
  rw [← hsign]
  field_simp

/-- **Biedenharn–Elliott with `p = 0`**, for `b, e > 0` (through 6j orthogonality). -/
theorem be_p_zero {a b c d e f q r : ℕ} (hb : 0 < b) (he : 0 < e) :
    beLHS a b c d e f 0 q r = beRHS a b c d e f 0 q r := by
  unfold beLHS beRHS
  rw [sixJSym_zero_left q r e a d, sixJSym_zero_left q r f b c]
  have hz : ∀ x, sixJSym a b x c d 0 = sixJSym 0 d a x b c := fun x =>
    (sj_swap13 a b x c d 0).symm.trans (sj_flip12 x b a 0 d c).symm
  simp only [hz, sixJSym_zero_left d a _ b c]
  by_cases hda : d = a
  swap
  · rw [ite_eq_right (show ¬(r = q ∧ d = a ∧ Tri q a e) from fun h => hda h.2.1), zero_mul]
    refine sum_eq_zero fun x _ => ?_
    rw [ite_eq_right (show ¬(a = d ∧ c = b ∧ Tri d b x) from fun h => hda h.1.symm)]
    ring
  by_cases hcb : c = b
  swap
  · rw [ite_eq_right (show ¬(r = q ∧ c = b ∧ Tri q b f) from fun h => hcb h.2.1), mul_zero]
    refine sum_eq_zero fun x _ => ?_
    rw [ite_eq_right (show ¬(a = d ∧ c = b ∧ Tri d b x) from fun h => hcb h.2.1)]
    ring
  subst d c
  rw [sum_congr rfl fun x _ => be_p_zero_term, ← mul_sum, add_comm a b, sixJSym_orth hb he]
  by_cases hc : q = r ∧ Tri a e q ∧ Tri b q f
  · obtain ⟨rfl, h1, h2⟩ := hc
    rw [ite_eq_left ⟨rfl, h1, h2⟩,
      ite_eq_left ⟨rfl, rfl, by unfold Tri at h1 ⊢; omega⟩, ite_eq_left ⟨rfl, rfl, by unfold Tri at h2 ⊢; omega⟩]
    have hq0 : 0 < Real.sqrt ((q : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have ha0 : 0 < Real.sqrt ((a : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hb0 : 0 < Real.sqrt ((b : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsign : (-1 : ℝ) ^ ((b + a + e + f + q + q) / 2) =
        (-1) ^ ((q + a + e) / 2) * (-1) ^ ((q + b + f) / 2) := by
      rw [← pow_add]
      exact neg_one_pow_eq_of_mod (by unfold Tri at h1 h2; omega)
    rw [hsign]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  · rw [ite_eq_right hc, mul_zero]
    by_cases hqr : r = q
    · subst hqr
      by_cases h1 : Tri r a e
      · rw [ite_eq_left ⟨rfl, rfl, h1⟩, ite_eq_right (fun h => hc ⟨rfl, by unfold Tri at h1 ⊢; omega,
          by obtain ⟨-, -, h2⟩ := h; unfold Tri at h2 ⊢; omega⟩), mul_zero]
      · rw [ite_eq_right (fun h => h1 h.2.2), zero_mul]
    · rw [ite_eq_right (fun h => hqr h.1), zero_mul]

/-! ## Step 5: the Biedenharn–Elliott identity for all spins -/

/-- Transfer an identity along a symmetry of both sides. -/
lemma be_of_symm {L L' R R' : ℝ} (hL : L' = L) (hR : R' = R) (h : L' = R') : L = R := by
  rw [← hL, ← hR, h]

/-- **The Biedenharn–Elliott identity**, for all spins (doubled units). Proof:
* an apex zero (`a, b, c, d, e, f`) is moved to `a` by the vertex symmetries and handled by
  `be_a_zero`;
* with every apex spin positive, a zero in `p` (or in `r`, after `B ↔ C`) is `be_p_zero`;
* otherwise all of `a, b, c, e, p, r` are positive and `biedenharnElliott_pos` (the recoupling
  pentagon) applies. -/
theorem biedenharnElliott : BiedenharnElliott := by
  intro a b c d e f p q r
  by_cases ha : a = 0
  · subst ha; exact be_a_zero b c d e f p q r
  by_cases hb : b = 0
  · subst hb
    obtain ⟨hL, hR⟩ := be_swapDE a 0 c d e f p q r
    exact be_of_symm hL hR (be_a_zero a d c f e p q r)
  by_cases hc : c = 0
  · subst hc
    obtain ⟨h1L, h1R⟩ := be_swapAB a b 0 d e f p q r
    obtain ⟨h2L, h2R⟩ := be_swapDE d 0 b a e f p r q
    exact be_of_symm h1L h1R (be_of_symm h2L h2R (be_a_zero d a b f e p r q))
  by_cases hd : d = 0
  · subst hd
    obtain ⟨hL, hR⟩ := be_swapAB a b c 0 e f p q r
    exact be_of_symm hL hR (be_a_zero c b a e f p r q)
  by_cases he : e = 0
  · subst he
    obtain ⟨hL, hR⟩ := be_swapAC a b c d 0 f p q r
    exact be_of_symm hL hR (be_a_zero f c d a b q p r)
  by_cases hf : f = 0
  · subst hf
    obtain ⟨h1L, h1R⟩ := be_swapAC a b c d e 0 p q r
    obtain ⟨h2L, h2R⟩ := be_swapDE e 0 c d a b q p r
    exact be_of_symm h1L h1R (be_of_symm h2L h2R (be_a_zero e d c b a q p r))
  by_cases hp : p = 0
  · subst hp
    exact be_p_zero (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero he)
  by_cases hr : r = 0
  · subst hr
    obtain ⟨hL, hR⟩ := be_swapBC a b c d e f p q 0
    exact be_of_symm hL hR (be_p_zero (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hd))
  exact biedenharnElliott_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
    (Nat.pos_of_ne_zero hc) (Nat.pos_of_ne_zero he) (Nat.pos_of_ne_zero hp) (Nat.pos_of_ne_zero hr)

end Lightlike.Pentagon

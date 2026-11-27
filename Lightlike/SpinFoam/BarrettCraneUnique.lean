import Lightlike.SpinFoam.BarrettCrane
import Lightlike.Asymptotics.Racah
import Lightlike.Recoupling.Span

/-!
# Uniqueness of the Barrett–Crane intertwiner

`bcNode_unique` (Reisenberger 1999, §3): a Spin(4)-invariant tensor of four simple representations
`(j k, j k)` whose components are diagonal in the `(01)(23)` and `(02)(13)` trivalent tree bases is a
multiple of the Barrett–Crane node `bcNode j`: the four-valent case of Reisenberger's theorem. `bcNode_hyp`: the node satisfies these hypotheses.

The argument: the two diagonal matrices are related by the orthogonal recoupling matrix
(`sum_basisB_mul_basisA`), whose column at the extreme channel is a stretched, hence nonzero,
6j symbol (`sixJSym_extreme_ne_zero`, from Racah's formula `sixJSym_eq_racahW`).

## References

* `reisenberger-1999`, Definition 1 (§2) and Theorem (§3).
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon Lightlike.Asymptotics

namespace Lightlike.SpinFoam.BC

/-- A term of Racah's sum whose index lies between every face sum and every quad sum is nonzero. -/
lemma rterm_ne_zero_of {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} {t : ℕ} (hA : ∀ i, A i ≤ t)
    (hB : ∀ k, (t : ℤ) ≤ B k) : rterm A B t ≠ 0 := by
  rw [rterm_eq_of (fun i => ((t : ℤ) - A i).toNat) (fun k => (B k - t).toNat)
    (fun i => by have := hA i; omega) (fun k => by have := hB k; omega)]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) (by positivity)

/-- **A stretched 6j symbol is nonzero**: an admissible symbol in which a face sum equals a quad sum
(a degenerate configuration) has a one-term Racah sum. -/
theorem racahW_ne_zero_of_stretched {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (hA : Adm6 j₁ j₂ j₃ j₄ j₅ j₆)
    (i : Fin 4) (k : Fin 3) (hik : faceD j₁ j₂ j₃ j₄ j₅ j₆ i = quadD j₁ j₂ j₃ j₄ j₅ j₆ k) :
    racahW j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0 := by
  have hle : ∀ i' k', faceD j₁ j₂ j₃ j₄ j₅ j₆ i' ≤ quadD j₁ j₂ j₃ j₄ j₅ j₆ k' := by
    unfold Adm6 Tri at hA
    intro i' k'
    fin_cases i' <;> fin_cases k' <;> simp [faceD, quadD] <;> omega
  have hnn : ∀ k', 0 ≤ quadD j₁ j₂ j₃ j₄ j₅ j₆ k' := fun k' =>
    (faceD_nonneg j₁ j₂ j₃ j₄ j₅ j₆ i).trans (hle i k')
  set t := (faceD j₁ j₂ j₃ j₄ j₅ j₆ i).toNat
  have ht : faceD j₁ j₂ j₃ j₄ j₅ j₆ i = t := by
    rw [Int.toNat_of_nonneg (faceD_nonneg _ _ _ _ _ _ i)]
  rw [racahW_of_adm hA, rsum_eq_single t i k ht (hik ▸ ht) hnn]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · exact (Real.sqrt_pos.2 (triSq_pos _ _ _)).ne'
  · exact (Real.sqrt_pos.2 (triSq_pos _ _ _)).ne'
  · exact (Real.sqrt_pos.2 (triSq_pos _ _ _)).ne'
  · exact (Real.sqrt_pos.2 (triSq_pos _ _ _)).ne'
  · refine rterm_ne_zero_of (fun i' => ?_) (fun k' => ?_)
    · rw [← ht, hik]; exact hle i' k
    · rw [← ht]; exact hle i k'

/-- **The recoupling coefficient at the extreme channel is nonzero**: for admissible `k`, the
coefficient of the `(j₁ j₃)(j₂ j₄)` intertwiner with the largest channel `l₀ = min(j₁+j₃, j₂+j₄)`
in the `(j₁ j₂)(j₃ j₄)` intertwiner of channel `k` does not vanish. -/
theorem sixJSym_extreme_ne_zero {j₁ j₂ j₃ j₄ k l₀ : ℕ} (hk₁ : Tri j₁ j₂ k) (hk₂ : Tri k j₃ j₄)
    (hl₁ : Tri j₁ j₃ l₀) (hl₂ : Tri l₀ j₂ j₄) (hl : l₀ = j₁ + j₃ ∨ l₀ = j₂ + j₄) :
    sixJSym j₁ j₂ k j₄ j₃ l₀ ≠ 0 := by
  rw [sixJSym_eq_racahW]
  have hA : Adm6 j₁ j₂ k j₄ j₃ l₀ := by unfold Adm6 Tri at *; omega
  rcases hl with h | h
  · exact racahW_ne_zero_of_stretched hA 2 0 (by simp [faceD, quadD]; unfold Tri at *; omega)
  · exact racahW_ne_zero_of_stretched hA 1 0 (by simp [faceD, quadD]; unfold Tri at *; omega)

/-! ## The two pairing bases -/

open Lightlike.Recoupling Lightlike.Spin4

/-- The intertwiner of the pairing `(01)(23)` with channel `k`, as a tensor. -/
noncomputable abbrev basisA (j : Fin 4 → ℕ) (k : ℕ) : (Fin 4 → ℤ) → ℝ :=
  fourJT (j 0) (j 1) (j 2) (j 3) k

/-- The intertwiner of the pairing `(02)(13)` with channel `l`, as a tensor. -/
noncomputable def basisB (j : Fin 4 → ℕ) (l : ℕ) (m : Fin 4 → ℤ) : ℝ :=
  fourJ (j 0) (j 2) (j 1) (j 3) l (m 0) (m 2) (m 1) (m 3)

/-- The box of projections of the four legs. -/
abbrev boxJ (j : Fin 4 → ℕ) : Finset (Fin 4 → ℤ) := box4 (j 0) (j 1) (j 2) (j 3)

/-- The recoupling coefficient vanishes at a channel `l` that is not admissible for `(02)(13)`. -/
lemma fourRecoupling_eq_zero_of_not {j₁ j₂ j₃ j₄ k l : ℕ} (h : ¬(Tri j₁ j₃ l ∧ Tri l j₂ j₄)) :
    fourRecoupling j₁ j₂ j₃ j₄ k l = 0 := by
  have : sixJSym j₁ j₂ k j₄ j₃ l = 0 := by
    by_contra h'
    obtain ⟨-, t2, t3, -⟩ := tri_of_sixJSym_ne_zero h'
    exact h ⟨t2, by unfold Tri at *; omega⟩
  rw [fourRecoupling, this, mul_zero]

/-- **The overlap of the two bases is the recoupling coefficient**:
`⟨ι^{(02)l}, ι^{(01)k}⟩ = R_{kl}`. -/
theorem sum_basisB_mul_basisA (j : Fin 4 → ℕ) (k l : ℕ) :
    ∑ n ∈ boxJ j, basisB j l n * basisA j k n = fourRecoupling (j 0) (j 1) (j 2) (j 3) k l := by
  have hA : ∀ n, basisA j k n =
      ∑ l' ∈ range (j 0 + j 2 + 1), fourRecoupling (j 0) (j 1) (j 2) (j 3) k l' * basisB j l' n :=
    fun n => fourJ_eq_sum_fourRecoupling _ _ _ _ _ _ _ _ _
  have hB : ∀ l l' : ℕ, ∑ n ∈ boxJ j, basisB j l n * basisB j l' n =
      if l = l' ∧ Tri (j 0) (j 2) l ∧ Tri l (j 1) (j 3) then 1 else 0 := by
    intro l l'
    rw [boxJ, box4, sum_piFinset_four]
    simp only [basisB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    rw [← sum_fourJ_mul_fourJ (j 0) (j 2) (j 1) (j 3) l l']
    exact sum_congr rfl fun a _ => sum_comm
  simp only [hA, mul_sum]
  rw [sum_comm]
  simp only [mul_left_comm (basisB j l _), ← mul_sum, hB]
  by_cases ht : Tri (j 0) (j 2) l ∧ Tri l (j 1) (j 3)
  · have hl : l ∈ range (j 0 + j 2 + 1) := by rw [mem_range]; unfold Tri at ht; omega
    rw [sum_eq_single l (fun l' _ hl' => by rw [ite_eq_right (fun h => hl' h.1.symm), mul_zero])
      (fun h => absurd hl h), ite_eq_left ⟨rfl, ht⟩, mul_one]
  · rw [fourRecoupling_eq_zero_of_not ht]
    exact sum_eq_zero fun l' _ => by
      rw [ite_eq_right (fun h : l = l' ∧ Tri (j 0) (j 2) l ∧ Tri l (j 1) (j 3) => ht h.2), mul_zero]

/-! ## The uniqueness theorem -/

/-- Pairing a tensor `Σ_k x_k a_k ⊗ b_k` with `f ⊗ g`. -/
lemma double_sum_eq (S : Finset (Fin 4 → ℤ)) (K : Finset ℕ) (f g : (Fin 4 → ℤ) → ℝ)
    (a b : ℕ → (Fin 4 → ℤ) → ℝ) (x : ℕ → ℝ) :
    ∑ μ ∈ S, ∑ ν ∈ S, f μ * g ν * ∑ k ∈ K, x k * (a k μ * b k ν) =
      ∑ k ∈ K, x k * ((∑ μ ∈ S, f μ * a k μ) * (∑ ν ∈ S, g ν * b k ν)) := by
  have h : ∀ k, x k * ((∑ μ ∈ S, f μ * a k μ) * (∑ ν ∈ S, g ν * b k ν)) =
      ∑ μ ∈ S, ∑ ν ∈ S, f μ * g ν * (x k * (a k μ * b k ν)) := fun k => by
    rw [sum_mul_sum, mul_sum]
    exact sum_congr rfl fun μ _ => by rw [mul_sum]; exact sum_congr rfl fun ν _ => by ring
  rw [sum_congr rfl fun k _ => h k]
  simp only [mul_sum]
  calc _ = ∑ μ ∈ S, ∑ k ∈ K, ∑ ν ∈ S, f μ * g ν * (x k * (a k μ * b k ν)) :=
        sum_congr rfl fun μ _ => sum_comm
    _ = _ := sum_comm

/-- The components `⟨ι^{(01)k} ⊗ ι^{(01)k'}, Φ⟩` of a tensor `Φ(μ, ν)` in the `(01)(23)` basis. -/
noncomputable def coefA (j : Fin 4 → ℕ) (Φ : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ) (k k' : ℕ) : ℝ :=
  ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, basisA j k μ * basisA j k' ν * Φ μ ν

/-- The components `⟨ι^{(02)l} ⊗ ι^{(02)l'}, Φ⟩` of a tensor `Φ(μ, ν)` in the `(02)(13)` basis. -/
noncomputable def coefB (j : Fin 4 → ℕ) (Φ : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ) (l l' : ℕ) : ℝ :=
  ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, basisB j l μ * basisB j l' ν * Φ μ ν

/-- The four spins `j` with four incoming legs, as `IsInv` takes them. -/
abbrev legs (j : Fin 4 → ℕ) : Fin 4 → ℕ := ![j 0, j 1, j 2, j 3]

/-- **Expansion in the `(01)(23)` basis**: a tensor invariant in each factor is
`Φ = Σ_{k k'} ⟨ι_k ⊗ ι_{k'}, Φ⟩ ι_k ⊗ ι_{k'}`. -/
theorem eq_sum_coefA {j : Fin 4 → ℕ} {Φ : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ}
    (hμ : ∀ ν, IsInv (legs j) ![false, false, false, false] fun μ => Φ μ ν)
    (hν : ∀ μ, IsInv (legs j) ![false, false, false, false] (Φ μ)) (μ ν : Fin 4 → ℤ) :
    Φ μ ν = ∑ k ∈ range (j 0 + j 1 + 1), ∑ k' ∈ range (j 0 + j 1 + 1),
      coefA j Φ k k' * basisA j k μ * basisA j k' ν := by
  rw [eq_sum_fourJ (hμ ν) μ]
  refine sum_congr rfl fun k _ => ?_
  have h2 : ∀ n, Φ n ν = ∑ k' ∈ range (j 0 + j 1 + 1),
      (∑ n' ∈ boxJ j, basisA j k' n' * Φ n n') * basisA j k' ν := fun n => eq_sum_fourJ (hν n) ν
  simp only [h2, mul_sum, coefA, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k' _ => sum_congr rfl fun n _ => sum_congr rfl fun n' _ => by ring

/-- **Reisenberger's uniqueness theorem, real form**: a tensor `Φ(μ, ν)` on four legs with spins
`j`, invariant in `μ` and in `ν`, whose components are diagonal in the `(01)(23)` basis and in the
`(02)(13)` basis, is a multiple of `Σ_k ι_k ⊗ ι_k`. -/
theorem eq_smul_sum_basisA {j : Fin 4 → ℕ} {Φ : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ}
    (hμ : ∀ ν, IsInv (legs j) ![false, false, false, false] fun μ => Φ μ ν)
    (hν : ∀ μ, IsInv (legs j) ![false, false, false, false] (Φ μ))
    (hA : ∀ k k', k ≠ k' → coefA j Φ k k' = 0) (hB : ∀ l l', l ≠ l' → coefB j Φ l l' = 0) :
    ∃ c : ℝ, ∀ μ ν, Φ μ ν =
      c * ∑ k ∈ channel (j 0) (j 1) (j 2) (j 3), basisA j k μ * basisA j k ν := by
  set K := range (j 0 + j 1 + 1)
  set x : ℕ → ℝ := fun k => coefA j Φ k k
  -- the diagonal expansion
  have hD : ∀ μ ν, Φ μ ν = ∑ k ∈ K, x k * (basisA j k μ * basisA j k ν) := by
    intro μ ν
    rw [eq_sum_coefA hμ hν μ ν]
    refine sum_congr rfl fun k hk => ?_
    rw [sum_eq_single k (fun k' _ hk' => by rw [hA k k' (Ne.symm hk'), zero_mul, zero_mul])
      (fun h => absurd hk h)]
    ring
  -- the `(02)(13)` components through the recoupling matrix
  set R := fourRecoupling (j 0) (j 1) (j 2) (j 3)
  have hM : ∀ l l', coefB j Φ l l' = ∑ k ∈ K, x k * (R k l * R k l') := by
    intro l l'
    simp only [coefB, hD, double_sum_eq, sum_basisB_mul_basisA, R]
  -- the extreme channel of `(02)(13)`
  set l₀ := min (j 0 + j 2) (j 1 + j 3)
  by_cases hne : ∃ k, Tri (j 0) (j 1) k ∧ Tri k (j 2) (j 3)
  swap
  · refine ⟨0, fun μ ν => ?_⟩
    rw [hD, zero_mul]
    refine sum_eq_zero fun k _ => ?_
    rw [show basisA j k μ = 0 from fourJ_eq_zero_of_not_adm (fun h => hne ⟨k, h⟩) _ _ _ _,
      zero_mul, mul_zero]
  obtain ⟨k₁, hk₁, hk₂⟩ := hne
  have hl₀ : l₀ ∈ range (j 0 + j 2 + 1) := by rw [mem_range]; omega
  refine ⟨coefB j Φ l₀ l₀, fun μ ν => ?_⟩
  -- `x_k R_{k l₀} = R_{k l₀} M_{l₀ l₀}` for admissible `k`
  have hx : ∀ k, Tri (j 0) (j 1) k → Tri k (j 2) (j 3) → x k = coefB j Φ l₀ l₀ := by
    intro k t1 t2
    have hkK : k ∈ K := by rw [mem_range]; unfold Tri at t1; omega
    have hsum : ∑ l ∈ range (j 0 + j 2 + 1), R k l * coefB j Φ l l₀ = x k * R k l₀ := by
      simp only [hM, mul_sum]
      rw [sum_comm]
      have : ∀ k' ∈ K, ∑ l ∈ range (j 0 + j 2 + 1), R k l * (x k' * (R k' l * R k' l₀)) =
          x k' * R k' l₀ * (if k = k' ∧ Tri (j 0) (j 1) k ∧ Tri k (j 2) (j 3) then 1 else 0) := by
        intro k' _
        rw [← sum_fourRecoupling_mul, mul_sum]
        exact sum_congr rfl fun l _ => by ring
      rw [sum_congr rfl this, sum_eq_single k (fun k' _ hk' => by
        rw [ite_eq_right (fun h => hk' h.1.symm), mul_zero]) (fun h => absurd hkK h),
        ite_eq_left ⟨rfl, t1, t2⟩, mul_one]
    rw [sum_eq_single l₀ (fun l _ hl => by rw [hB l l₀ hl, mul_zero]) (fun h => absurd hl₀ h)]
      at hsum
    have hR : R k l₀ ≠ 0 := by
      have h6 := sixJSym_extreme_ne_zero (j₁ := j 0) (j₂ := j 1) (j₃ := j 2) (j₄ := j 3)
        (l₀ := l₀) t1 t2 (by unfold Tri at *; omega) (by unfold Tri at *; omega) (by omega)
      simp only [R, fourRecoupling]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) h6
      exact (Real.sqrt_pos.2 (by positivity)).ne'
    exact (mul_right_cancel₀ hR (by rw [← hsum]; ring)).symm.trans rfl |>.symm
  rw [hD, mul_sum, channel, sum_filter]
  refine sum_congr rfl fun k _ => ?_
  by_cases ht : Tri (j 0) (j 1) k ∧ Tri (j 2) (j 3) k
  · rw [ite_eq_left ht, hx k ht.1 (by unfold Tri at *; omega)]
  · rw [ite_eq_right ht, show basisA j k μ = 0 from fourJ_eq_zero_of_not_adm
      (fun h => ht ⟨h.1, by unfold Tri at *; omega⟩) _ _ _ _, zero_mul, mul_zero]

/-! ## The Barrett–Crane node satisfies the hypotheses -/

/-- The real Barrett–Crane node `Σ_k ι_k ⊗ ι_k`, whose complexification is `bcNode`. -/
noncomputable def bcNodeR (j : Fin 4 → ℕ) (μ ν : Fin 4 → ℤ) : ℝ :=
  ∑ k ∈ channel (j 0) (j 1) (j 2) (j 3), basisA j k μ * basisA j k ν

lemma bcNode_eq_ofReal (j : Fin 4 → ℕ) (μ ν : Fin 4 → ℤ) : bcNode j μ ν = (bcNodeR j μ ν : ℂ) := by
  simp only [bcNode, bcNodeR, fourJNode, basisA, fourJT]
  push_cast
  rfl

/-- The recoupling matrix read backwards: `R^{(01)}_{kl} = R^{(02)}_{lk}`. -/
lemma fourRecoupling_symm (j₁ j₂ j₃ j₄ k l : ℕ) :
    fourRecoupling j₁ j₂ j₃ j₄ k l = fourRecoupling j₁ j₃ j₂ j₄ l k := by
  rw [fourRecoupling, fourRecoupling, sixJSym_flip₂₃,
    show j₂ + j₃ + k + l = j₃ + j₂ + l + k by ring, mul_comm ((k : ℝ) + 1)]

/-- The columns of the recoupling matrix are orthonormal. -/
lemma sum_fourRecoupling_mul_col (j₁ j₂ j₃ j₄ l l' : ℕ) :
    ∑ k ∈ range (j₁ + j₂ + 1), fourRecoupling j₁ j₂ j₃ j₄ k l * fourRecoupling j₁ j₂ j₃ j₄ k l' =
      if l = l' ∧ Tri j₁ j₃ l ∧ Tri l j₂ j₄ then 1 else 0 := by
  simp only [fourRecoupling_symm j₁ j₂ j₃ j₄]
  exact sum_fourRecoupling_mul j₁ j₃ j₂ j₄ l l'

/-- **The Barrett–Crane node is invariant in each factor.** -/
theorem isInv_bcNodeR_left (j : Fin 4 → ℕ) (ν : Fin 4 → ℤ) :
    IsInv (legs j) ![false, false, false, false] fun μ => bcNodeR j μ ν := by
  refine (IsInv.sum (channel (j 0) (j 1) (j 2) (j 3))
    (fun k _ => (isInv_fourJT (j 0) (j 1) (j 2) (j 3) k).smul (basisA j k ν))).congr fun μ => ?_
  simp only [bcNodeR]
  exact sum_congr rfl fun k _ => mul_comm _ _

theorem isInv_bcNodeR_right (j : Fin 4 → ℕ) (μ : Fin 4 → ℤ) :
    IsInv (legs j) ![false, false, false, false] (bcNodeR j μ) := by
  refine (IsInv.sum (channel (j 0) (j 1) (j 2) (j 3))
    (fun k _ => (isInv_fourJT (j 0) (j 1) (j 2) (j 3) k).smul (basisA j k μ))).congr fun ν => ?_
  rfl

/-- The `(01)(23)` components of the Barrett–Crane node are diagonal. -/
theorem coefA_bcNodeR (j : Fin 4 → ℕ) {k₁ k₂ : ℕ} (h : k₁ ≠ k₂) : coefA j (bcNodeR j) k₁ k₂ = 0 := by
  have e : ∀ μ ν, bcNodeR j μ ν =
      ∑ k ∈ channel (j 0) (j 1) (j 2) (j 3), (1 : ℝ) * (basisA j k μ * basisA j k ν) :=
    fun μ ν => by simp [bcNodeR]
  simp only [coefA, e, double_sum_eq, basisA, boxJ, sum_box4_fourJT]
  refine sum_eq_zero fun k _ => ?_
  by_cases h1 : k₁ = k
  · rw [ite_eq_right (fun h2 : k₂ = k ∧ _ => h (h1.trans h2.1.symm)), mul_zero, mul_zero]
  · rw [ite_eq_right (fun h2 : k₁ = k ∧ _ => h1 h2.1), zero_mul, mul_zero]

/-- The `(02)(13)` components of the Barrett–Crane node are diagonal. -/
theorem coefB_bcNodeR (j : Fin 4 → ℕ) {l₁ l₂ : ℕ} (h : l₁ ≠ l₂) : coefB j (bcNodeR j) l₁ l₂ = 0 := by
  have e : ∀ μ ν, bcNodeR j μ ν =
      ∑ k ∈ channel (j 0) (j 1) (j 2) (j 3), (1 : ℝ) * (basisA j k μ * basisA j k ν) :=
    fun μ ν => by simp [bcNodeR]
  simp only [coefB, e, double_sum_eq, sum_basisB_mul_basisA]
  simp only [one_mul]
  have hz : ∀ k ∈ range (j 0 + j 1 + 1), k ∉ channel (j 0) (j 1) (j 2) (j 3) →
      fourRecoupling (j 0) (j 1) (j 2) (j 3) k l₁ * fourRecoupling (j 0) (j 1) (j 2) (j 3) k l₂ = 0 := by
    intro k hk hc
    rw [fourRecoupling_symm, fourRecoupling_eq_zero_of_not, zero_mul]
    intro ht
    exact hc (mem_filter.2 ⟨hk, ht.1, by unfold Tri at *; omega⟩)
  have hs : channel (j 0) (j 1) (j 2) (j 3) ⊆ range (j 0 + j 1 + 1) := filter_subset _ _
  rw [sum_subset hs hz,
    sum_fourRecoupling_mul_col,
    ite_eq_right (fun h' => h h'.1)]

/-! ## The Barrett–Crane intertwiner is unique -/

/-- **The Barrett–Crane intertwiner is unique**: the four-valent case of Reisenberger's theorem
(Reisenberger 1999, §3, Theorem). Every Spin(4)-invariant tensor `Φ(μ, ν)` of four simple representations `(j k, j k)` satisfying the
hypotheses of Reisenberger's theorem is a multiple `c · bcNode j` (with `c = 0` allowed).

Here `μ` are the projections of the self-dual and `ν` those of the anti-self-dual factor, and
Spin(4) = SU(2) × SU(2) acts on them separately.

**The hypotheses.** Reisenberger, Definition 1 (§2), asks:
1. "On each edge the left handed spin, j_L, and the right handed spin, j_R, are equal." This is
   built in: leg `k` carries `(j k, j k)`.
2. "In any expansion of an n-valent vertex into a sum of trivalent trees only trivalent trees with
   j_L=j_R on each of the internal (virtual) edges appear." For a four-valent vertex there are
   three trees (§3: "There are three (unoriented) trivalent trees matching the four incident
   edges"). The hypothesis says that the components of `Φ` in the tree basis `ι_k ⊗ ι_{k'}` vanish
   for `k ≠ k'`.

Invariance (`hμ`, `hν`) is SU(2)-invariance of the real and imaginary parts in each factor.

**Difference from the source (stronger result).** We assume condition 2 for two of the three trees
only: `(01)(23)` (`hA`) and `(02)(13)` (`hB`). Reisenberger assumes it for all three (§3, after
eq. (7): X "commutes with G_12^2, G_13^2, and G_14^2"), although his proof, eqs. (8)–(16), uses
only `G₁₂²` and `G₁₃²`. The proof here is different. The two diagonal matrices are related by the
orthogonal recoupling matrix (`sum_basisB_mul_basisA`). Its column at the extreme channel
`l₀ = min(j₀ + j₂, j₁ + j₃)` is a stretched 6j symbol, nonzero for every admissible `k`
(`sixJSym_extreme_ne_zero`). Hence all diagonal entries are equal. -/
theorem bcNode_unique {j : Fin 4 → ℕ} {Φ : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ}
    (hμ : ∀ ν, IsInv (legs j) ![false, false, false, false] (fun μ => (Φ μ ν).re) ∧
      IsInv (legs j) ![false, false, false, false] (fun μ => (Φ μ ν).im))
    (hν : ∀ μ, IsInv (legs j) ![false, false, false, false] (fun ν => (Φ μ ν).re) ∧
      IsInv (legs j) ![false, false, false, false] (fun ν => (Φ μ ν).im))
    (hA : ∀ k k', k ≠ k' →
      ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, ((basisA j k μ * basisA j k' ν : ℝ) : ℂ) * Φ μ ν = 0)
    (hB : ∀ l l', l ≠ l' →
      ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, ((basisB j l μ * basisB j l' ν : ℝ) : ℂ) * Φ μ ν = 0) :
    ∃ c : ℂ, ∀ μ ν, Φ μ ν = c * bcNode j μ ν := by
  have re_sum : ∀ (F : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ),
      (∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, ((F μ ν : ℝ) : ℂ) * Φ μ ν).re =
        ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, F μ ν * (Φ μ ν).re := fun F => by
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have im_sum : ∀ (F : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ),
      (∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, ((F μ ν : ℝ) : ℂ) * Φ μ ν).im =
        ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, F μ ν * (Φ μ ν).im := fun F => by
    simp only [Complex.im_sum, Complex.im_ofReal_mul]
  obtain ⟨c₁, h₁⟩ := eq_smul_sum_basisA (Φ := fun μ ν => (Φ μ ν).re) (fun ν => (hμ ν).1)
    (fun μ => (hν μ).1)
    (fun k k' h => by have := congrArg Complex.re (hA k k' h); rwa [re_sum, Complex.zero_re] at this)
    (fun l l' h => by have := congrArg Complex.re (hB l l' h); rwa [re_sum, Complex.zero_re] at this)
  obtain ⟨c₂, h₂⟩ := eq_smul_sum_basisA (Φ := fun μ ν => (Φ μ ν).im) (fun ν => (hμ ν).2)
    (fun μ => (hν μ).2)
    (fun k k' h => by have := congrArg Complex.im (hA k k' h); rwa [im_sum, Complex.zero_im] at this)
    (fun l l' h => by have := congrArg Complex.im (hB l l' h); rwa [im_sum, Complex.zero_im] at this)
  refine ⟨⟨c₁, c₂⟩, fun μ ν => ?_⟩
  rw [bcNode_eq_ofReal]
  apply Complex.ext
  · rw [Complex.re_mul_ofReal]; exact h₁ μ ν
  · rw [Complex.im_mul_ofReal]; exact h₂ μ ν

/-- **Non-vacuity**: the Barrett–Crane node itself satisfies every hypothesis of `bcNode_unique`. -/
theorem bcNode_hyp (j : Fin 4 → ℕ) :
    (∀ ν, IsInv (legs j) ![false, false, false, false] (fun μ => (bcNode j μ ν).re) ∧
      IsInv (legs j) ![false, false, false, false] (fun μ => (bcNode j μ ν).im)) ∧
    (∀ μ, IsInv (legs j) ![false, false, false, false] (fun ν => (bcNode j μ ν).re) ∧
      IsInv (legs j) ![false, false, false, false] (fun ν => (bcNode j μ ν).im)) ∧
    (∀ k k', k ≠ k' → ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j,
      ((basisA j k μ * basisA j k' ν : ℝ) : ℂ) * bcNode j μ ν = 0) ∧
    (∀ l l', l ≠ l' → ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j,
      ((basisB j l μ * basisB j l' ν : ℝ) : ℂ) * bcNode j μ ν = 0) := by
  simp only [bcNode_eq_ofReal, Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_eq_zero]
  exact ⟨fun ν => ⟨isInv_bcNodeR_left j ν, isInv_zero⟩, fun μ => ⟨isInv_bcNodeR_right j μ, isInv_zero⟩,
    fun k k' h => coefA_bcNodeR j h, fun l l' h => coefB_bcNodeR j h⟩

/-- The diagonal components of the Barrett–Crane node are `1` on the channels. -/
theorem coefA_bcNodeR_self (j : Fin 4 → ℕ) {k : ℕ} (hk : k ∈ channel (j 0) (j 1) (j 2) (j 3)) :
    coefA j (bcNodeR j) k k = 1 := by
  have e : ∀ μ ν, bcNodeR j μ ν = ∑ k ∈ channel (j 0) (j 1) (j 2) (j 3),
      (1 : ℝ) * (basisA j k μ * basisA j k ν) :=
    fun μ ν => by simp [bcNodeR]
  obtain ⟨-, t1, t2⟩ := mem_filter.1 hk
  simp only [coefA, e, double_sum_eq, basisA, boxJ, sum_box4_fourJT]
  rw [sum_eq_single k (fun k' _ hk' => by rw [ite_eq_right (fun h : k = k' ∧ _ => hk' h.1.symm),
    zero_mul, mul_zero]) (fun h => absurd hk h)]
  rw [ite_eq_left ⟨rfl, t1, by unfold Tri at *; omega⟩, one_mul, one_mul]

/-- **The conclusion is not trivial**: the Barrett–Crane node of four spin-½ legs (doubled spins
`1`) is nonzero; its channel `0` gives `⟨ι_0 ⊗ ι_0, bcNode⟩ = 1`. -/
theorem coefA_bcNodeR_half : coefA (fun _ => 1) (bcNodeR fun _ => 1) 0 0 = 1 :=
  coefA_bcNodeR_self _ (by decide)

namespace Tests

/-- The tensor `ι_0 ⊗ ι_0` of four spin-½ legs. -/
noncomputable def single0 (μ ν : Fin 4 → ℤ) : ℝ :=
  basisA (fun _ => 1) 0 μ * basisA (fun _ => 1) 0 ν

/-- **The second pairing is needed** (wrong-model check): on four spin-½ legs, `ι_0 ⊗ ι_0` is
invariant in each factor and diagonal in the `(01)(23)` basis, but it is not a multiple of the
Barrett–Crane node (whose channels are `0` and `2`). So diagonality in one tree basis alone does
not give the conclusion of `bcNode_unique`. -/
theorem single0_counterexample :
    (∀ ν, IsInv (legs fun _ => 1) ![false, false, false, false] fun μ => single0 μ ν) ∧
    (∀ μ, IsInv (legs fun _ => 1) ![false, false, false, false] (single0 μ)) ∧
    (∀ k k', k ≠ k' → coefA (fun _ => 1) single0 k k' = 0) ∧
    ¬ ∃ c : ℝ, ∀ μ ν, single0 μ ν = c * bcNodeR (fun _ => 1) μ ν := by
  have e : ∀ μ ν, single0 μ ν = ∑ k ∈ ({0} : Finset ℕ),
      (1 : ℝ) * (basisA (fun _ => 1) k μ * basisA (fun _ => 1) k ν) :=
    fun μ ν => by simp [single0]
  have hc : ∀ k k', coefA (fun _ => 1) single0 k k' =
      (if k = 0 ∧ Tri 1 1 k ∧ Tri k 1 1 then 1 else 0) *
        (if k' = 0 ∧ Tri 1 1 k' ∧ Tri k' 1 1 then 1 else 0) := by
    intro k k'
    simp only [coefA, e, double_sum_eq, basisA, boxJ, sum_box4_fourJT]
    simp only [sum_singleton, one_mul]
  refine ⟨fun ν => ?_, fun μ => ?_, fun k k' h => ?_, fun ⟨c, hcΦ⟩ => ?_⟩
  · exact ((isInv_fourJT 1 1 1 1 0).smul (basisA (fun _ => 1) 0 ν)).congr fun μ => mul_comm _ _
  · exact (isInv_fourJT 1 1 1 1 0).smul (basisA (fun _ => 1) 0 μ)
  · rw [hc]
    by_cases h0 : k = 0
    · rw [ite_eq_right (fun h' : k' = 0 ∧ _ => h (h0.trans h'.1.symm)), mul_zero]
    · rw [ite_eq_right (fun h' : k = 0 ∧ _ => h0 h'.1), zero_mul]
  · have hlin : ∀ k, coefA (fun _ => 1) single0 k k = c * coefA (fun _ => 1) (bcNodeR fun _ => 1) k k := by
      intro k
      simp only [coefA, hcΦ, mul_sum]
      exact sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => by ring
    have h0 := hlin 0
    have h2 := hlin 2
    rw [coefA_bcNodeR_self _ (by decide), hc] at h0 h2
    rw [ite_eq_left ⟨rfl, by unfold Tri; omega, by unfold Tri; omega⟩] at h0
    rw [ite_eq_right (fun h : 2 = 0 ∧ _ => absurd h.1 (by norm_num))] at h2
    norm_num at h0 h2
    linarith

end Tests

end Lightlike.SpinFoam.BC

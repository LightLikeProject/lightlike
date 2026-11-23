module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!
# The recoupling pentagon, part 1: coupling trees in a four-fold product

This file is the first half of the proof of the Biedenharn–Elliott identity for Physlib's 6j symbol
`sixJSym` (see `Lightlike.Upstream.SpinReps2.BEPentagon2`). It builds the five coupling trees of
`V(a) ⊗ V(b) ⊗ V(c) ⊗ V(d)` and relates them by recoupling.

## Implementation notes

`stateB_eq_sum_stateA`: in `V(a) ⊗ V(b) ⊗ V(c)`,
`|j₁, (j₂ j₃) j₂₃; J M⟩ = Σ_{j₁₂} ⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩ |(j₁ j₂) j₁₂, j₃; J M⟩`.
It follows from Physlib's completeness of the first scheme (`eq_sum_vecA`), its selection rule
(`tripleForm_stateA_stateB_eq_zero`) and the definition of `recoupling`. The coefficient is
evaluated at the same `M` (`l`); Physlib's `recoupling_eq_recoupling_zero` makes it independent
of `M`, which lets the pentagon argument factor it out of the outer couplings.

The five trees (`T1 = ((12)3)4`, `T2 = (12)(34)`, `T3 = 1(2(34))`, `T4 = 1((23)4)`,
`T5 = (1(23))4`) are explicit vectors; the lemmas `T5_eq_sum_T1`, `T2_eq_sum_T1`, `T3_eq_sum_T4`,
`T4_eq_sum_T5`, `T3_eq_sum_T2` are the five recoupling moves.

## Main results

* `PhyslibAlpha.Sl2.Pentagon.stateB_eq_sum_stateA`: expansion of the second coupling scheme.
* `PhyslibAlpha.Sl2.Pentagon.T3_eq_sum_T2`, `T3_eq_sum_T4`, …: the five recoupling moves.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset
open scoped TensorProduct

namespace PhyslibAlpha.Sl2.Pentagon

variable {a b c : ℕ}

/-- **Expansion of the second coupling scheme in the first.** -/
theorem stateB_eq_sum_stateA (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K l : ℕ} {k₃ : Fin (min b c + 1)} (hB : ValidB a b c K k₃) (hl : l ≤ a + b + c - 2 * K) :
    stateB hbc k₃ (K - k₃) l = ∑ k₁ : Fin (min a b + 1),
      (if ValidA a b c K k₁ then recoupling hab hbc K l k₁ k₃ else 0) •
        stateA hab k₁ (K - k₁) l := by
  obtain ⟨hB1, hB2, hB3⟩ := hB
  conv_lhs => rw [eq_sum_vecA hab hc (stateB hbc k₃ (K - k₃) l)]
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun k₁ _ => ?_
  obtain ⟨hk₁a, hk₁b⟩ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁.isLt)
  rw [Fintype.sum_sigma]
  -- bounds carried by a string index `k₂`
  have hk₂ : ∀ k₂ : Fin (min (a + b - 2 * (k₁ : ℕ)) c + 1),
      (k₂ : ℕ) ≤ a + b - 2 * (k₁ : ℕ) ∧ (k₂ : ℕ) ≤ c :=
    fun k₂ => Nat.le_min.mp (Nat.lt_succ_iff.mp k₂.isLt)
  by_cases hA : ValidA a b c K k₁
  · obtain ⟨hA1, hA2, hA3⟩ := hA
    rw [ite_eq_left ⟨hA1, hA2, hA3⟩]
    have hk2 : K - (k₁ : ℕ) < min (a + b - 2 * (k₁ : ℕ)) c + 1 :=
      Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨hA2, hA3⟩)
    rw [sum_eq_single ⟨K - k₁, hk2⟩]
    · have hl' : l < a + b - 2 * (k₁ : ℕ) + c - 2 * (K - (k₁ : ℕ)) + 1 := by omega
      rw [sum_eq_single ⟨l, hl'⟩]
      · rfl
      · intro l' _ hl'ne
        rw [vecA, tripleForm_stateA_stateB_eq_zero hab hbc ha hc hA2 hA3 hB2 hB3
          (fun h => hl'ne (Fin.ext h.2)), zero_smul]
      · simp
    · intro k₂ _ hk₂ne
      refine sum_eq_zero fun l' _ => ?_
      obtain ⟨h1, h2⟩ := hk₂ k₂
      rw [vecA, tripleForm_stateA_stateB_eq_zero hab hbc ha hc h1 h2 hB2 hB3
        (fun h => hk₂ne (Fin.ext (by have := h.1; show (k₂ : ℕ) = K - k₁; omega))), zero_smul]
    · simp
  · rw [ite_eq_right hA, zero_smul]
    refine sum_eq_zero fun k₂ _ => sum_eq_zero fun l' _ => ?_
    obtain ⟨h1, h2⟩ := hk₂ k₂
    rw [vecA, tripleForm_stateA_stateB_eq_zero hab hbc ha hc h1 h2 hB2 hB3
      (fun h => hA (by have := h.1; exact ⟨by omega, by omega, by omega⟩)), zero_smul]

/-! ## The four-fold product and the coupling trees -/

variable {d : ℕ}

variable (a b c d) in
/-- `V(a) ⊗ V(b) ⊗ V(c) ⊗ V(d)`, bracketed `((V(a) ⊗ V(b)) ⊗ V(c)) ⊗ V(d)`. -/
abbrev Quad : Type := Triple a b c ⊗[ℝ] StandardSl2Module ℝ d

/-- Couple a family `v l` of triple-product vectors (spin `J/2`, `M = J/2 - l`) with `V(d)`:
`Σ_{l, δ} ⟨J/2, J/2 - l; d/2, d/2 - δ | (J + d)/2 - k, · - L⟩ · v l ⊗ u_δ`. -/
noncomputable def liftR (J : ℕ) (v : ℕ → Triple a b c) (k L : ℕ) : Quad a b c d :=
  ∑ l ∈ range (J + 1), ∑ δ ∈ range (d + 1), cgCoefficient J d k L l δ • (v l ⊗ₜ normVec d δ)

/-- `liftR` is linear in the family, for coefficients independent of `l`. -/
lemma liftR_eq_sum {ι : Type*} (s : Finset ι) (J : ℕ) {v : ℕ → Triple a b c} (r : ι → ℝ)
    (w : ι → ℕ → Triple a b c) (hv : ∀ l ∈ range (J + 1), v l = ∑ i ∈ s, r i • w i l) (k L : ℕ) :
    liftR (d := d) J v k L = ∑ i ∈ s, r i • liftR (d := d) J (w i) k L := by
  unfold liftR
  have h1 : ∀ l ∈ range (J + 1), ∀ δ ∈ range (d + 1),
      cgCoefficient J d k L l δ • (v l ⊗ₜ[ℝ] normVec d δ) =
        ∑ i ∈ s, r i • (cgCoefficient J d k L l δ • (w i l ⊗ₜ[ℝ] normVec d δ)) := by
    intro l hl δ _
    rw [hv l hl, TensorProduct.sum_tmul, smul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← TensorProduct.smul_tmul', smul_comm]
  rw [sum_congr rfl fun l hl => sum_congr rfl fun δ hδ => h1 l hl δ hδ]
  simp only [smul_sum]
  rw [sum_congr rfl fun l _ => sum_comm, sum_comm]

/-- **Tree `((12)3)4`**: `j₁₂ = (a+b)/2 - k₁₂`, `j₁₂₃ = j₁₂ + c/2 - k₁₂₃`, outer label `k₄`,
`M = J - L`. -/
noncomputable def T1 (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1)) (k₁₂₃ k₄ L : ℕ) : Quad a b c d :=
  liftR (a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃) (fun l => stateA hab k₁₂ k₁₂₃ l) k₄ L

/-- **Tree `(1(23))4`**: `j₂₃ = (b+c)/2 - k₂₃`, `j₁₂₃ = a/2 + j₂₃ - k₁`, outer label `k₄`. -/
noncomputable def T5 (hbc : 0 < b + c) (k₂₃ : Fin (min b c + 1)) (k₁ k₄ L : ℕ) : Quad a b c d :=
  liftR (a + (b + c - 2 * (k₂₃ : ℕ)) - 2 * k₁) (fun l => stateB hbc k₂₃ k₁ l) k₄ L

/-- **Relation R1** (recoupling of the inner `(1 2 3)` subtree): `T5 = Σ_{j₁₂} R_{abc} · T1`. -/
theorem T5_eq_sum_T1 (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c) {K : ℕ}
    {k₂₃ : Fin (min b c + 1)} (hB : ValidB a b c K k₂₃) (k₄ L : ℕ) :
    T5 (d := d) hbc k₂₃ (K - k₂₃) k₄ L = ∑ k₁₂ : Fin (min a b + 1),
      (if ValidA a b c K k₁₂ then recoupling hab hbc K 0 k₁₂ k₂₃ else 0) •
        T1 (d := d) hab k₁₂ (K - k₁₂) k₄ L := by
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hk₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂₃.isLt)
  have hJB : a + (b + c - 2 * (k₂₃ : ℕ)) - 2 * (K - k₂₃) = a + b + c - 2 * K := by omega
  rw [T5, hJB, liftR_eq_sum (univ : Finset (Fin (min a b + 1))) _
    (fun k₁₂ : Fin (min a b + 1) =>
      if ValidA a b c K k₁₂ then recoupling hab hbc K 0 k₁₂ k₂₃ else 0)
    (fun k₁₂ : Fin (min a b + 1) => fun l => stateA hab k₁₂ (K - k₁₂) l)]
  · refine sum_congr rfl fun k₁₂ _ => ?_
    split_ifs with hA
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      have hk₁₂ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁₂.isLt)
      rw [T1, show a + b - 2 * (k₁₂ : ℕ) + c - 2 * (K - k₁₂) = a + b + c - 2 * K by omega]
    · rw [zero_smul, zero_smul]
  · intro l hl
    have hl' : l ≤ a + b + c - 2 * K := by simp only [mem_range] at hl; omega
    rw [stateB_eq_sum_stateA hab hbc ha hc ⟨hB1, hB2, hB3⟩ hl']
    refine sum_congr rfl fun k₁₂ _ => ?_
    split_ifs with hA
    · rw [recoupling_eq_recoupling_zero hab hbc ha hA ⟨hB1, hB2, hB3⟩ hl']
    · rfl

/-- `E12 : V(j₁₂) ⊗ V(c) ⊗ V(d) → V(a) ⊗ V(b) ⊗ V(c) ⊗ V(d)`, through the `k₁₂`-th component of
`V(a) ⊗ V(b)`. -/
noncomputable def E12 (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1)) :
    Triple (a + b - 2 * (k₁₂ : ℕ)) c d →ₗ[ℝ] Quad a b c d :=
  ((embed hab k₁₂).rTensor (StandardSl2Module ℝ c)).rTensor (StandardSl2Module ℝ d)

/-- **Consistency C1**: `((12)3)4` is the `(j₁₂ c) d` first-scheme state, pushed in by `E12`. -/
lemma E12_stateA (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1))
    (h : 0 < a + b - 2 * (k₁₂ : ℕ) + c) (k₁ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1))
    (k₄ L : ℕ) :
    E12 (c := c) (d := d) hab k₁₂ (stateA h k₁ k₄ L) = T1 (d := d) hab k₁₂ k₁ k₄ L := by
  rw [stateA, coupledVec_eq_sum, T1, liftR]
  simp only [map_sum, map_smul, LinearMap.rTensor_tmul, embed_normVec, E12]
  rfl

/-- **Tree `(12)(34)`**: `j₁₂ = (a+b)/2 - k₁₂`, `j₃₄ = (c+d)/2 - k₃₄`, coupling label `k`. -/
noncomputable def T2 (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1)) (hcd : 0 < c + d)
    (k₃₄ : Fin (min c d + 1)) (k L : ℕ) : Quad a b c d :=
  E12 hab k₁₂ (stateB (a := a + b - 2 * (k₁₂ : ℕ)) hcd k₃₄ k L)

/-- **Relation R4** (recoupling of `(j₁₂ c d)`): `T2 = Σ_{j₁₂₃} R_{j₁₂ c d} · T1`. -/
theorem T2_eq_sum_T1 (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1))
    (h12c : 0 < a + b - 2 * (k₁₂ : ℕ) + c) (hcd : 0 < c + d) (h12 : 0 < a + b - 2 * (k₁₂ : ℕ))
    (hd : 0 < d) {K : ℕ} {k₃₄ : Fin (min c d + 1)}
    (hB : ValidB (a + b - 2 * (k₁₂ : ℕ)) c d K k₃₄) {L : ℕ}
    (hL : L ≤ a + b - 2 * (k₁₂ : ℕ) + c + d - 2 * K) :
    T2 hab k₁₂ hcd k₃₄ (K - k₃₄) L = ∑ k₁ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1),
      (if ValidA (a + b - 2 * (k₁₂ : ℕ)) c d K k₁ then recoupling h12c hcd K L k₁ k₃₄ else 0) •
        T1 (d := d) hab k₁₂ k₁ (K - k₁) L := by
  rw [T2, stateB_eq_sum_stateA h12c hcd h12 hd hB hL, map_sum]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [map_smul, E12_stateA]

variable (a b c d) in
/-- The associator `V(a) ⊗ ((V(b) ⊗ V(c)) ⊗ V(d)) ≃ ((V(a) ⊗ V(b)) ⊗ V(c)) ⊗ V(d)`. -/
noncomputable def assocL :
    StandardSl2Module ℝ a ⊗[ℝ] Triple b c d ≃ₗ[ℝ] Quad a b c d :=
  (TensorProduct.congr (LinearEquiv.refl ℝ _) (TensorProduct.assoc ℝ _ _ _)).trans
    ((TensorProduct.assoc ℝ _ _ _).symm.trans (TensorProduct.assoc ℝ _ _ _).symm)

lemma assocL_tmul (x : StandardSl2Module ℝ a) (y : StandardSl2Module ℝ b)
    (z : StandardSl2Module ℝ c) (w : StandardSl2Module ℝ d) :
    assocL a b c d (x ⊗ₜ ((y ⊗ₜ z) ⊗ₜ w)) = ((x ⊗ₜ y) ⊗ₜ z) ⊗ₜ w := rfl

/-- Couple `V(a)` with a family `w l` of `(b c d)`-triple vectors (spin `J/2`, `M = J/2 - l`):
`Σ_{α, l} ⟨a/2, a/2 - α; J/2, J/2 - l | (a + J)/2 - k, · - L⟩ · u_α ⊗ w l`. -/
noncomputable def liftL (J : ℕ) (w : ℕ → Triple b c d) (k L : ℕ) : Quad a b c d :=
  ∑ α ∈ range (a + 1), ∑ l ∈ range (J + 1),
    cgCoefficient a J k L α l • assocL a b c d (normVec a α ⊗ₜ w l)

/-- `liftL` is linear in the family, for coefficients independent of `l`. -/
lemma liftL_eq_sum {ι : Type*} (s : Finset ι) (J : ℕ) {v : ℕ → Triple b c d} (r : ι → ℝ)
    (w : ι → ℕ → Triple b c d) (hv : ∀ l ∈ range (J + 1), v l = ∑ i ∈ s, r i • w i l) (k L : ℕ) :
    liftL (a := a) J v k L = ∑ i ∈ s, r i • liftL (a := a) J (w i) k L := by
  unfold liftL
  have h1 : ∀ α ∈ range (a + 1), ∀ l ∈ range (J + 1),
      cgCoefficient a J k L α l • assocL a b c d (normVec a α ⊗ₜ[ℝ] v l) =
        ∑ i ∈ s, r i • (cgCoefficient a J k L α l • assocL a b c d (normVec a α ⊗ₜ[ℝ] w i l)) := by
    intro α _ l hl
    rw [hv l hl, TensorProduct.tmul_sum, map_sum, smul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, map_smul, smul_comm]
  rw [sum_congr rfl fun α hα => sum_congr rfl fun l hl => h1 α hα l hl]
  simp only [smul_sum]
  rw [sum_congr rfl fun α _ => sum_comm, sum_comm]

/-- **Tree `1((23)4)`**: `j₂₃ = (b+c)/2 - k₂₃`, `j₂₃₄ = j₂₃ + d/2 - k₂₃₄`, outer label `k₁`. -/
noncomputable def T4 (hbc : 0 < b + c) (k₂₃ : Fin (min b c + 1)) (k₂₃₄ k₁ L : ℕ) :
    Quad a b c d :=
  liftL (b + c - 2 * (k₂₃ : ℕ) + d - 2 * k₂₃₄) (fun l => stateA (c := d) hbc k₂₃ k₂₃₄ l) k₁ L

/-- **Tree `1(2(34))`**: `j₃₄ = (c+d)/2 - k₃₄`, `j₂₃₄ = b/2 + j₃₄ - k₂`, outer label `k₁`. -/
noncomputable def T3 (hcd : 0 < c + d) (k₃₄ : Fin (min c d + 1)) (k₂ k₁ L : ℕ) : Quad a b c d :=
  liftL (b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * k₂) (fun l => stateB (a := b) hcd k₃₄ k₂ l) k₁ L

/-- **Relation R3** (recoupling of the inner `(2 3 4)` subtree): `T3 = Σ_{j₂₃} R_{bcd} · T4`. -/
theorem T3_eq_sum_T4 (hbc : 0 < b + c) (hcd : 0 < c + d) (hb : 0 < b) (hd : 0 < d) {K : ℕ}
    {k₃₄ : Fin (min c d + 1)} (hB : ValidB b c d K k₃₄) (k₁ L : ℕ) :
    T3 (a := a) hcd k₃₄ (K - k₃₄) k₁ L = ∑ k₂₃ : Fin (min b c + 1),
      (if ValidA b c d K k₂₃ then recoupling hbc hcd K 0 k₂₃ k₃₄ else 0) •
        T4 (a := a) hbc k₂₃ (K - k₂₃) k₁ L := by
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hk₃₄ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₃₄.isLt)
  have hJB : b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (K - k₃₄) = b + c + d - 2 * K := by omega
  rw [T3, hJB, liftL_eq_sum (univ : Finset (Fin (min b c + 1))) _
    (fun k₂₃ : Fin (min b c + 1) =>
      if ValidA b c d K k₂₃ then recoupling hbc hcd K 0 k₂₃ k₃₄ else 0)
    (fun k₂₃ : Fin (min b c + 1) => fun l => stateA (c := d) hbc k₂₃ (K - k₂₃) l)]
  · refine sum_congr rfl fun k₂₃ _ => ?_
    split_ifs with hA
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      have hk₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂₃.isLt)
      rw [T4, show b + c - 2 * (k₂₃ : ℕ) + d - 2 * (K - k₂₃) = b + c + d - 2 * K by omega]
    · rw [zero_smul, zero_smul]
  · intro l hl
    have hl' : l ≤ b + c + d - 2 * K := by simp only [mem_range] at hl; omega
    rw [stateB_eq_sum_stateA hbc hcd hb hd ⟨hB1, hB2, hB3⟩ hl']
    refine sum_congr rfl fun k₂₃ _ => ?_
    split_ifs with hA
    · rw [recoupling_eq_recoupling_zero hbc hcd hb hA ⟨hB1, hB2, hB3⟩ hl']
    · rfl

/-- `assocL (x ⊗ (s ⊗ z)) = (assoc⁻¹ (x ⊗ s)) ⊗ z` for `s ∈ V(b) ⊗ V(c)`. -/
lemma assocL_tmul_tmul (x : StandardSl2Module ℝ a) (s : StandardSl2Module ℝ b ⊗[ℝ]
    StandardSl2Module ℝ c) (z : StandardSl2Module ℝ d) :
    assocL a b c d (x ⊗ₜ (s ⊗ₜ z)) = (TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ s) ⊗ₜ z := by
  induction s using TensorProduct.inductionOn with
  | tmul y w => rfl
  | add s s' hs hs' => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hs, hs']

/-- `E23 : V(a) ⊗ V(j₂₃) ⊗ V(d) → V(a) ⊗ V(b) ⊗ V(c) ⊗ V(d)`, through the `k₂₃`-th component of
`V(b) ⊗ V(c)`. -/
noncomputable def E23 (hbc : 0 < b + c) (k₂₃ : Fin (min b c + 1)) :
    Triple a (b + c - 2 * (k₂₃ : ℕ)) d →ₗ[ℝ] Quad a b c d :=
  (assocEmbed hbc k₂₃).rTensor (StandardSl2Module ℝ d)

/-- **Consistency C5**: `(1(23))4` is the `(a j₂₃) d` first-scheme state, pushed in by `E23`. -/
lemma E23_stateA (hbc : 0 < b + c) (k₂₃ : Fin (min b c + 1))
    (h : 0 < a + (b + c - 2 * (k₂₃ : ℕ))) (k₁ : Fin (min a (b + c - 2 * (k₂₃ : ℕ)) + 1))
    (k₄ L : ℕ) :
    E23 (d := d) hbc k₂₃ (stateA h k₁ k₄ L) = T5 (d := d) hbc k₂₃ k₁ k₄ L := by
  rw [stateA, coupledVec_eq_sum, T5, liftR]
  simp only [map_sum, map_smul, LinearMap.rTensor_tmul, embed_normVec, E23]
  rfl

/-- `E23 (assoc⁻¹ (x ⊗ t)) = assocL (x ⊗ (embed₂₃ ⊗ 1) t)`. -/
lemma E23_assoc_symm (hbc : 0 < b + c) (k₂₃ : Fin (min b c + 1)) (x : StandardSl2Module ℝ a)
    (t : StandardSl2Module ℝ (b + c - 2 * (k₂₃ : ℕ)) ⊗[ℝ] StandardSl2Module ℝ d) :
    E23 hbc k₂₃ ((TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ t)) =
      assocL a b c d (x ⊗ₜ (embed hbc k₂₃).rTensor _ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y z =>
    rw [TensorProduct.assoc_symm_tmul, E23, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      assocL_tmul_tmul]
    rfl
  | add t t' ht ht' => simp only [TensorProduct.tmul_add, map_add, ht, ht']

/-- **Consistency C4**: `1((23)4)` is the `a (j₂₃ d)` second-scheme state, pushed in by `E23`. -/
lemma E23_stateB (hbc : 0 < b + c) (k₂₃ : Fin (min b c + 1))
    (h : 0 < b + c - 2 * (k₂₃ : ℕ) + d) (k' : Fin (min (b + c - 2 * (k₂₃ : ℕ)) d + 1))
    (k₁ L : ℕ) :
    E23 (a := a) hbc k₂₃ (stateB h k' k₁ L) = T4 (a := a) hbc k₂₃ k' k₁ L := by
  rw [stateB, coupledVec_eq_sum, T4, liftL]
  simp only [map_sum, map_smul]
  refine sum_congr rfl fun α _ => sum_congr rfl fun l _ => ?_
  rw [assocEmbed, LinearMap.comp_apply, LinearMap.lTensor_tmul, embed_normVec,
    LinearEquiv.coe_coe, E23_assoc_symm]
  rfl

/-- **Relation R2** (recoupling of `(a j₂₃ d)`): `T4 = Σ_{j₁₂₃} R_{a j₂₃ d} · T5`. -/
theorem T4_eq_sum_T5 (hbc : 0 < b + c) (k₂₃ : Fin (min b c + 1))
    (h1 : 0 < a + (b + c - 2 * (k₂₃ : ℕ))) (h2 : 0 < b + c - 2 * (k₂₃ : ℕ) + d) (ha : 0 < a)
    (hd : 0 < d) {K : ℕ} {k' : Fin (min (b + c - 2 * (k₂₃ : ℕ)) d + 1)}
    (hB : ValidB a (b + c - 2 * (k₂₃ : ℕ)) d K k') {L : ℕ}
    (hL : L ≤ a + (b + c - 2 * (k₂₃ : ℕ)) + d - 2 * K) :
    T4 (a := a) hbc k₂₃ k' (K - k') L = ∑ k₁ : Fin (min a (b + c - 2 * (k₂₃ : ℕ)) + 1),
      (if ValidA a (b + c - 2 * (k₂₃ : ℕ)) d K k₁ then recoupling h1 h2 K L k₁ k' else 0) •
        T5 (d := d) hbc k₂₃ k₁ (K - k₁) L := by
  rw [← E23_stateB hbc k₂₃ h2, stateB_eq_sum_stateA h1 h2 ha hd hB hL, map_sum]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [map_smul, E23_stateA]

/-- `E12 (assoc⁻¹ (x ⊗ t)) = assoc⁻¹ (embed₁₂ x ⊗ t)`. -/
lemma E12_assoc_symm (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1))
    (x : StandardSl2Module ℝ (a + b - 2 * (k₁₂ : ℕ)))
    (t : StandardSl2Module ℝ c ⊗[ℝ] StandardSl2Module ℝ d) :
    E12 hab k₁₂ ((TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ t)) =
      (TensorProduct.assoc ℝ _ _ _).symm (embed hab k₁₂ x ⊗ₜ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y z => rfl
  | add t t' ht ht' => simp only [TensorProduct.tmul_add, map_add, ht, ht']

/-- `E34 : V(a) ⊗ V(b) ⊗ V(j₃₄) → V(a) ⊗ V(b) ⊗ V(c) ⊗ V(d)`, through the `k₃₄`-th component of
`V(c) ⊗ V(d)`. -/
noncomputable def E34 (hcd : 0 < c + d) (k₃₄ : Fin (min c d + 1)) :
    Triple a b (c + d - 2 * (k₃₄ : ℕ)) →ₗ[ℝ] Quad a b c d :=
  (TensorProduct.assoc ℝ (StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ b)
    (StandardSl2Module ℝ c) (StandardSl2Module ℝ d)).symm.toLinearMap ∘ₗ
    (embed hcd k₃₄).lTensor _

/-- **Consistency C2**: the `(12)(34)` state is both the `(a b) j₃₄` first-scheme state pushed in
by `E34` and the `j₁₂ (c d)` second-scheme state pushed in by `E12`. -/
lemma E34_stateA (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1)) (hcd : 0 < c + d)
    (k₃₄ : Fin (min c d + 1)) (k L : ℕ) :
    E34 hcd k₃₄ (stateA hab k₁₂ k L) = T2 hab k₁₂ hcd k₃₄ k L := by
  rw [T2, stateA, stateB, coupledVec_eq_sum]
  simp only [map_sum, map_smul]
  refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => ?_
  rw [LinearMap.rTensor_tmul, embed_normVec, assocEmbed, LinearMap.comp_apply,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe, E12_assoc_symm, embed_normVec, embed_normVec,
    E34, LinearMap.comp_apply, LinearMap.lTensor_tmul, embed_normVec]
  rfl

/-- `assocL (x ⊗ assoc⁻¹ (y ⊗ t)) = assoc⁻¹ ((x ⊗ y) ⊗ t)` for `t ∈ V(c) ⊗ V(d)`. -/
lemma assocL_tmul_assoc_symm (x : StandardSl2Module ℝ a) (y : StandardSl2Module ℝ b)
    (t : StandardSl2Module ℝ c ⊗[ℝ] StandardSl2Module ℝ d) :
    assocL a b c d (x ⊗ₜ (TensorProduct.assoc ℝ _ _ _).symm (y ⊗ₜ t)) =
      (TensorProduct.assoc ℝ _ _ _).symm ((x ⊗ₜ y) ⊗ₜ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul u v => rfl
  | add t t' ht ht' => simp only [TensorProduct.tmul_add, map_add, ht, ht']

/-- `E34 (assoc⁻¹ (x ⊗ s)) = assocL (x ⊗ assocEmbed₃₄ s)`. -/
lemma E34_assoc_symm (hcd : 0 < c + d) (k₃₄ : Fin (min c d + 1)) (x : StandardSl2Module ℝ a)
    (s : StandardSl2Module ℝ b ⊗[ℝ] StandardSl2Module ℝ (c + d - 2 * (k₃₄ : ℕ))) :
    E34 hcd k₃₄ ((TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ s)) =
      assocL a b c d (x ⊗ₜ assocEmbed hcd k₃₄ s) := by
  induction s using TensorProduct.inductionOn with
  | tmul y w =>
    rw [TensorProduct.assoc_symm_tmul, E34, LinearMap.comp_apply, LinearMap.lTensor_tmul,
      assocEmbed, LinearMap.comp_apply, LinearMap.lTensor_tmul]
    simp only [LinearEquiv.coe_coe]
    rw [assocL_tmul_assoc_symm]
  | add s s' hs hs' => simp only [TensorProduct.tmul_add, map_add, hs, hs']

/-- **Consistency C3**: `1(2(34))` is the `a (b j₃₄)` second-scheme state, pushed in by `E34`. -/
lemma E34_stateB (hcd : 0 < c + d) (k₃₄ : Fin (min c d + 1))
    (h : 0 < b + (c + d - 2 * (k₃₄ : ℕ))) (k₂ : Fin (min b (c + d - 2 * (k₃₄ : ℕ)) + 1))
    (k₁ L : ℕ) :
    E34 (a := a) hcd k₃₄ (stateB h k₂ k₁ L) = T3 (a := a) hcd k₃₄ k₂ k₁ L := by
  rw [stateB, coupledVec_eq_sum, T3, liftL]
  simp only [map_sum, map_smul]
  refine sum_congr rfl fun α _ => sum_congr rfl fun l _ => ?_
  rw [assocEmbed, LinearMap.comp_apply, LinearMap.lTensor_tmul, embed_normVec,
    LinearEquiv.coe_coe, E34_assoc_symm]
  rfl

/-- **Relation R5** (recoupling of `(a b j₃₄)`): `T3 = Σ_{j₁₂} R_{a b j₃₄} · T2`. -/
theorem T3_eq_sum_T2 (hab : 0 < a + b) (hcd : 0 < c + d) (k₃₄ : Fin (min c d + 1))
    (h : 0 < b + (c + d - 2 * (k₃₄ : ℕ))) (ha : 0 < a) (h34 : 0 < c + d - 2 * (k₃₄ : ℕ)) {K : ℕ}
    {k₂ : Fin (min b (c + d - 2 * (k₃₄ : ℕ)) + 1)}
    (hB : ValidB a b (c + d - 2 * (k₃₄ : ℕ)) K k₂) {L : ℕ}
    (hL : L ≤ a + b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * K) :
    T3 (a := a) hcd k₃₄ k₂ (K - k₂) L = ∑ k₁₂ : Fin (min a b + 1),
      (if ValidA a b (c + d - 2 * (k₃₄ : ℕ)) K k₁₂ then recoupling hab h K L k₁₂ k₂ else 0) •
        T2 hab k₁₂ hcd k₃₄ (K - k₁₂) L := by
  rw [← E34_stateB hcd k₃₄ h, stateB_eq_sum_stateA hab h ha h34 hB hL, map_sum]
  refine sum_congr rfl fun k₁₂ _ => ?_
  rw [map_smul, E34_stateA]

end PhyslibAlpha.Sl2.Pentagon

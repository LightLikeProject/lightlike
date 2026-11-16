module

public import Lightlike.PonzanoRegge.BiedenharnElliott

/-!
# The general Biedenharn–Elliott identity: the recoupling pentagon

The recoupling-pentagon route to `BiedenharnElliott` described in `BiedenharnElliott.lean`. The
identity is now proven for all spins (`Lightlike.Pentagon.biedenharnElliott`, `BEZero.lean`; nonzero
spins via `BEPositive.lean`). Everything here is proven; nothing is assumed.

## Implementation notes

`stateB_eq_sum_stateA`: in `V(a) ⊗ V(b) ⊗ V(c)`,
`|j₁, (j₂ j₃) j₂₃; J M⟩ = Σ_{j₁₂} ⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩ |(j₁ j₂) j₁₂, j₃; J M⟩`.
It follows from Physlib's completeness of the first scheme (`eq_sum_vecA`), its selection rule
(`tripleForm_stateA_stateB_eq_zero`) and the definition of `recoupling`. The coefficient is
evaluated at the same `M` (`l`); Physlib's `recoupling_eq_recoupling_zero` makes it independent
of `M`, which is what lets the pentagon argument factor it out of the outer couplings.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset
open scoped TensorProduct

namespace Lightlike.Pentagon

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

/-! ## Stage 2: the four-fold product and the coupling trees -/

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

/-! ## Stage 3: orthonormality of the `((12)3)4` states -/

variable (a b c d) in
/-- The contravariant form on the four-fold product. -/
noncomputable def quadForm : LinearMap.BilinForm ℝ (Quad a b c d) :=
  LinearMap.BilinForm.tmul (tripleForm a b c) (invForm ℝ d)

lemma quadForm_tmul (x x' : Triple a b c) (y y' : StandardSl2Module ℝ d) :
    quadForm a b c d (x ⊗ₜ y) (x' ⊗ₜ y') = tripleForm a b c x x' * invForm ℝ d y y' := by
  rw [quadForm, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

/-- The first-scheme states of a triple product are orthonormal (ℕ-indexed form of Physlib's
`tripleForm_vecA`). -/
lemma tripleForm_stateA_stateA (hab : 0 < a + b) (hc : 0 < c) {k₁ k₁' : Fin (min a b + 1)}
    {k₂ k₂' l l' : ℕ} (h₂ : k₂ ≤ a + b - 2 * (k₁ : ℕ)) (h₂' : k₂ ≤ c)
    (h₃ : k₂' ≤ a + b - 2 * (k₁' : ℕ)) (h₃' : k₂' ≤ c) (hl : l ≤ a + b - 2 * (k₁ : ℕ) + c - 2 * k₂) :
    tripleForm a b c (stateA hab k₁ k₂ l) (stateA hab k₁' k₂' l') =
      if k₁ = k₁' ∧ k₂ = k₂' ∧ l = l' then 1 else 0 := by
  by_cases hk : k₁ = k₁'
  · subst hk
    rw [stateA, stateA, tripleForm_rTensor_embed,
      tensorForm_coupledVec (by omega) h₂ h₂' h₃ h₃' hl]
    simp only [true_and]
  · rw [stateA, stateA, tripleForm_rTensor_embed_of_ne hab _ hk, ite_eq_right (fun h => hk h.1)]

/-- Pairing a `((12)3)4` state with a product basis vector `stateA ⊗ u_δ'` picks out one
Clebsch–Gordan coefficient. -/
lemma quadForm_T1_tmul (hab : 0 < a + b) (hc : 0 < c) {k₁₂ k₁₂' : Fin (min a b + 1)}
    {k₁₂₃ k₁₂₃' k₄ L l' δ' : ℕ}
    (h₁ : k₁₂₃ ≤ a + b - 2 * (k₁₂ : ℕ)) (h₁' : k₁₂₃ ≤ c)
    (h₂ : k₁₂₃' ≤ a + b - 2 * (k₁₂' : ℕ)) (h₂' : k₁₂₃' ≤ c)
    (hl' : l' ≤ a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃') (hδ' : δ' ≤ d) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (stateA hab k₁₂' k₁₂₃' l' ⊗ₜ normVec d δ') =
      if k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃' then
        cgCoefficient (a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃) d k₄ L l' δ' else 0 := by
  rw [T1, liftR, map_sum, LinearMap.sum_apply]
  simp_rw [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    quadForm_tmul]
  by_cases hk : k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃'
  · obtain ⟨rfl, rfl⟩ := hk
    rw [ite_eq_left ⟨rfl, rfl⟩, sum_eq_single l', sum_eq_single δ']
    · rw [tripleForm_stateA_stateA hab hc h₁ h₁' h₁ h₁' hl', invForm_normVec hδ' hδ']
      simp
    · intro δ hδ hne
      rw [invForm_normVec (by simp only [mem_range] at hδ; omega) hδ', ite_eq_right hne]
      ring
    · intro h; simp only [mem_range] at h; omega
    · intro l hl hne
      refine sum_eq_zero fun δ _ => ?_
      rw [tripleForm_stateA_stateA hab hc h₁ h₁' h₁ h₁' (by simp only [mem_range] at hl; omega),
        ite_eq_right (fun h => hne h.2.2)]
      ring
    · intro h; simp only [mem_range] at h; omega
  · rw [ite_eq_right hk]
    refine sum_eq_zero fun l hl => sum_eq_zero fun δ _ => ?_
    rw [tripleForm_stateA_stateA hab hc h₁ h₁' h₂ h₂' (by simp only [mem_range] at hl; omega),
      ite_eq_right (fun h => hk ⟨h.1, h.2.1⟩)]
    ring

/-- **The `((12)3)4` states are orthonormal.** -/
theorem quadForm_T1_T1 (hab : 0 < a + b) (hc : 0 < c) (hd : 0 < d) {k₁₂ k₁₂' : Fin (min a b + 1)}
    {k₁₂₃ k₁₂₃' k₄ k₄' L L' : ℕ}
    (h₁ : k₁₂₃ ≤ a + b - 2 * (k₁₂ : ℕ)) (h₁' : k₁₂₃ ≤ c)
    (h₂ : k₁₂₃' ≤ a + b - 2 * (k₁₂' : ℕ)) (h₂' : k₁₂₃' ≤ c)
    (h₃ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃) (h₃' : k₄ ≤ d)
    (h₄ : k₄' ≤ a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃') (h₄' : k₄' ≤ d)
    (hL : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃ + d - 2 * k₄) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T1 hab k₁₂' k₁₂₃' k₄' L') =
      if k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃' ∧ k₄ = k₄' ∧ L = L' then 1 else 0 := by
  have hT : T1 (d := d) hab k₁₂' k₁₂₃' k₄' L' =
      ∑ l' ∈ range (a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃' + 1), ∑ δ' ∈ range (d + 1),
        cgCoefficient (a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃') d k₄' L' l' δ' •
          (stateA hab k₁₂' k₁₂₃' l' ⊗ₜ normVec d δ') := rfl
  rw [hT, map_sum]
  simp_rw [map_sum, map_smul, smul_eq_mul]
  rw [sum_congr rfl fun l' hl' => sum_congr rfl fun δ' hδ' => by
    rw [quadForm_T1_tmul hab hc h₁ h₁' h₂ h₂' (by simp only [mem_range] at hl'; omega)
      (by simp only [mem_range] at hδ'; omega)]]
  by_cases hk : k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃'
  · obtain ⟨rfl, rfl⟩ := hk
    simp only [true_and, ite_true]
    rw [sum_congr rfl fun l' _ => sum_congr rfl fun δ' _ => mul_comm _ _,
      sum_cgCoefficient_mul (by omega) h₃ h₃' h₄ h₄' hL]
  · rw [ite_eq_right (fun h => hk ⟨h.1, h.2.1⟩)]
    refine sum_eq_zero fun l' _ => sum_eq_zero fun δ' _ => ?_
    rw [ite_eq_right hk, mul_zero]

/-! ## Stage 4: the pentagon for recoupling coefficients -/

/-- Different `k₁₂`-components of `V(a) ⊗ V(b)` are orthogonal in the four-fold product. -/
lemma quadForm_E12_E12_of_ne (hab : 0 < a + b) {k₁₂ k₁₂' : Fin (min a b + 1)} (hk : k₁₂ ≠ k₁₂')
    (u : Triple (a + b - 2 * (k₁₂ : ℕ)) c d) (v : Triple (a + b - 2 * (k₁₂' : ℕ)) c d) :
    quadForm a b c d (E12 hab k₁₂ u) (E12 hab k₁₂' v) = 0 := by
  induction u using TensorProduct.inductionOn with
  | tmul p z =>
    induction v using TensorProduct.inductionOn with
    | tmul p' z' =>
      rw [E12, E12, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, quadForm_tmul,
        tripleForm_rTensor_embed_of_ne hab _ hk, zero_mul]
    | add v v' hv hv' => rw [map_add, map_add, hv, hv', add_zero]
  | add u u' hu hu' => rw [map_add, map_add, LinearMap.add_apply, hu, hu', add_zero]

/-- `⟨((12)3)4 | (12)(34)⟩` for the same `j₁₂`: one recoupling coefficient of `(j₁₂ c d)`. -/
lemma quadForm_T1_T2 (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1))
    (h12c : 0 < a + b - 2 * (k₁₂ : ℕ) + c) (hcd : 0 < c + d) (h12 : 0 < a + b - 2 * (k₁₂ : ℕ))
    (hc : 0 < c) (hd : 0 < d) (k₁₂₃ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1)) {k₄ : ℕ}
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) ∧ k₄ ≤ d) {K : ℕ}
    {k₃₄ : Fin (min c d + 1)} (hB : ValidB (a + b - 2 * (k₁₂ : ℕ)) c d K k₃₄) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) + d - 2 * k₄)
    (hL : L ≤ a + b - 2 * (k₁₂ : ℕ) + c + d - 2 * K) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T2 hab k₁₂ hcd k₃₄ (K - k₃₄) L) =
      (if ValidA (a + b - 2 * (k₁₂ : ℕ)) c d K k₁₂₃ then recoupling h12c hcd K L k₁₂₃ k₃₄
        else 0) * (if k₄ = K - k₁₂₃ then 1 else 0) := by
  have hk₁₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁₂₃.isLt)
  rw [T2_eq_sum_T1 hab k₁₂ h12c hcd h12 hd hB hL, map_sum, sum_eq_single k₁₂₃]
  · rw [map_smul, smul_eq_mul]
    by_cases hA : ValidA (a + b - 2 * (k₁₂ : ℕ)) c d K k₁₂₃
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      rw [ite_eq_left ⟨hA1, hA2, hA3⟩, quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 hk₁₂₃.1 hk₁₂₃.2
        hk₄.1 hk₄.2 hA2 hA3 hL1]
      by_cases hk4 : k₄ = K - k₁₂₃
      · rw [ite_eq_left ⟨rfl, rfl, hk4, rfl⟩, ite_eq_left hk4]
      · rw [ite_eq_right (fun h => hk4 h.2.2.1), ite_eq_right hk4]
    · rw [ite_eq_right hA, zero_mul, zero_mul]
  · intro k₁' _ hne
    rw [map_smul]
    by_cases hA : ValidA (a + b - 2 * (k₁₂ : ℕ)) c d K k₁'
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      have hk₁' := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁'.isLt)
      rw [quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 hk₁'.1 hk₁'.2 hk₄.1 hk₄.2 hA2 hA3 hL1,
        ite_eq_right (show ¬(k₁₂ = k₁₂ ∧ (k₁₂₃ : ℕ) = k₁' ∧ k₄ = K - k₁' ∧ L = L) from
          fun h => hne (Fin.ext h.2.1.symm)), smul_zero]
    · rw [ite_eq_right hA, zero_smul]
  · simp

/-- **The two-move side of the pentagon**: `⟨((12)3)4 | 1(2(34))⟩` through `(12)(34)`. -/
theorem quadForm_T1_T3_two (hab : 0 < a + b) (hcd : 0 < c + d) (ha : 0 < a) (hc : 0 < c)
    (hd : 0 < d) (k₁₂ : Fin (min a b + 1)) (h12 : 0 < a + b - 2 * (k₁₂ : ℕ))
    (h12c : 0 < a + b - 2 * (k₁₂ : ℕ) + c) (k₃₄ : Fin (min c d + 1))
    (h34 : 0 < c + d - 2 * (k₃₄ : ℕ)) (h5 : 0 < b + (c + d - 2 * (k₃₄ : ℕ)))
    (k₁₂₃ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1)) {k₄ : ℕ}
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) ∧ k₄ ≤ d)
    (k₂ : Fin (min b (c + d - 2 * (k₃₄ : ℕ)) + 1)) {k₁ : ℕ}
    (hk₁ : k₁ ≤ a ∧ k₁ ≤ b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) + d - 2 * k₄)
    (hL3 : L ≤ a + (b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) - 2 * k₁) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T3 hcd k₃₄ k₂ k₁ L) =
      (if ValidA a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) k₁₂ then
        recoupling hab h5 (k₂ + k₁) L k₁₂ k₂ else 0) *
      ((if ValidA (a + b - 2 * (k₁₂ : ℕ)) c d (k₂ + k₁ - k₁₂ + k₃₄) k₁₂₃ then
        recoupling h12c hcd (k₂ + k₁ - k₁₂ + k₃₄) L k₁₂₃ k₃₄ else 0) *
      (if k₄ = k₂ + k₁ - k₁₂ + k₃₄ - k₁₂₃ then 1 else 0)) := by
  have hk₂ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂.isLt)
  have hk₃₄ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₃₄.isLt)
  rw [show T3 (a := a) hcd k₃₄ (k₂ : ℕ) k₁ L = T3 hcd k₃₄ k₂ (k₂ + k₁ - k₂) L by
      rw [Nat.add_sub_cancel_left],
    T3_eq_sum_T2 hab hcd k₃₄ h5 ha h34 ⟨by omega, by omega, by omega⟩ (by omega), map_sum,
    sum_eq_single k₁₂]
  · rw [map_smul, smul_eq_mul]
    by_cases hA : ValidA a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) k₁₂
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      have h2 := quadForm_T1_T2 hab k₁₂ h12c hcd h12 hc hd k₁₂₃ hk₄
        (K := k₂ + k₁ - k₁₂ + k₃₄) (k₃₄ := k₃₄) ⟨by omega, by omega, by omega⟩ hL1 (by omega)
      rw [show k₂ + k₁ - (k₁₂ : ℕ) + k₃₄ - k₃₄ = k₂ + k₁ - k₁₂ by omega] at h2
      rw [ite_eq_left ⟨hA1, hA2, hA3⟩, h2]
    · rw [ite_eq_right hA, zero_mul, zero_mul]
  · intro k₁₂' _ hne
    rw [map_smul, T2, ← E12_stateA hab k₁₂ h12c k₁₂₃ k₄ L,
      quadForm_E12_E12_of_ne hab (Ne.symm hne), smul_zero]
  · simp

/-- Proof-free, ℕ-indexed recoupling coefficient: Physlib's `recoupling` when all labels are
admissible, `0` otherwise. -/
noncomputable def rc (a b c K l k₁ k₃ : ℕ) : ℝ :=
  if h : 0 < a + b ∧ 0 < b + c ∧ k₁ < min a b + 1 ∧ k₃ < min b c + 1 ∧ ValidA a b c K k₁ ∧
      ValidB a b c K k₃ then recoupling h.1 h.2.1 K l ⟨k₁, h.2.2.1⟩ ⟨k₃, h.2.2.2.1⟩ else 0

lemma ite_recoupling_eq_rc (hab : 0 < a + b) (hbc : 0 < b + c) {K : ℕ} (l : ℕ)
    (k₁ : Fin (min a b + 1)) (k₃ : Fin (min b c + 1)) (hB : ValidB a b c K k₃) :
    (if ValidA a b c K k₁ then recoupling hab hbc K l k₁ k₃ else 0) = rc a b c K l k₁ k₃ := by
  unfold rc
  by_cases hA : ValidA a b c K k₁
  · rw [ite_eq_left hA, dite_eq_left ⟨hab, hbc, k₁.isLt, k₃.isLt, hA, hB⟩]
  · rw [ite_eq_right hA, dite_eq_right (fun h => hA h.2.2.2.2.1)]

lemma rc_of_not_validA {K l k₁ k₃ : ℕ} (h : ¬ ValidA a b c K k₁) : rc a b c K l k₁ k₃ = 0 :=
  dite_eq_right (fun h' => h h'.2.2.2.2.1)

/-- **The three-move side of the pentagon**: `⟨((12)3)4 | 1(2(34))⟩` through `1((23)4)` and
`(1(23))4`. -/
theorem quadForm_T1_T3_three (hab : 0 < a + b) (hbc : 0 < b + c) (hcd : 0 < c + d) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (k₁₂ : Fin (min a b + 1)) {k₁₂₃ k₄ : ℕ}
    (hk₁₂₃ : k₁₂₃ ≤ a + b - 2 * (k₁₂ : ℕ) ∧ k₁₂₃ ≤ c)
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃ ∧ k₄ ≤ d) (k₃₄ : Fin (min c d + 1))
    {k₂ : ℕ} (hk₂ : k₂ ≤ b ∧ k₂ ≤ c + d - 2 * (k₃₄ : ℕ)) {k₁ : ℕ}
    (hk₁ : k₁ ≤ a ∧ k₁ ≤ b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * k₂) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃ + d - 2 * k₄)
    (hL3 : L ≤ a + (b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * k₂) - 2 * k₁) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T3 hcd k₃₄ k₂ k₁ L) =
      ∑ k₂₃ : Fin (min b c + 1), rc b c d (k₃₄ + k₂) 0 k₂₃ k₃₄ *
        ∑ k₁' : Fin (min a (b + c - 2 * (k₂₃ : ℕ)) + 1),
          rc a (b + c - 2 * (k₂₃ : ℕ)) d (k₃₄ + k₂ - k₂₃ + k₁) L k₁' (k₃₄ + k₂ - k₂₃) *
            (rc a b c (k₂₃ + k₁') 0 k₁₂ k₂₃ *
              (if k₁₂₃ = k₂₃ + k₁' - k₁₂ ∧ k₄ = k₃₄ + k₂ - k₂₃ + k₁ - k₁' then 1 else 0)) := by
  have hk₃₄ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₃₄.isLt)
  rw [show T3 (a := a) hcd k₃₄ k₂ k₁ L = T3 hcd k₃₄ (k₃₄ + k₂ - k₃₄) k₁ L by
      rw [Nat.add_sub_cancel_left],
    T3_eq_sum_T4 hbc hcd hb hd ⟨by omega, by omega, by omega⟩ k₁ L, map_sum]
  refine sum_congr rfl fun k₂₃ _ => ?_
  have hk₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂₃.isLt)
  rw [map_smul, smul_eq_mul, ite_recoupling_eq_rc hbc hcd 0 k₂₃ k₃₄ ⟨by omega, by omega, by omega⟩]
  by_cases hA3 : ValidA b c d (k₃₄ + k₂) k₂₃
  · congr 1
    obtain ⟨h31, h32, h33⟩ := hA3
    have h2 := T4_eq_sum_T5 (a := a) hbc k₂₃ (by omega) (by omega) ha hd
      (K := k₃₄ + k₂ - k₂₃ + k₁)
      (k' := ⟨k₃₄ + k₂ - k₂₃, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨h32, h33⟩)⟩)
      ⟨by simp only; omega, by simp only; omega, by simp only; omega⟩ (L := L)
      (by omega)
    simp only [show k₃₄ + k₂ - (k₂₃ : ℕ) + k₁ - (k₃₄ + k₂ - k₂₃) = k₁ by omega] at h2
    rw [h2, map_sum]
    refine sum_congr rfl fun k₁' _ => ?_
    have hk₁' := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁'.isLt)
    rw [map_smul, smul_eq_mul, ite_recoupling_eq_rc _ _ L k₁' _
      ⟨by simp only; omega, by simp only; omega, by simp only; omega⟩]
    by_cases hA2 : ValidA a (b + c - 2 * (k₂₃ : ℕ)) d (k₃₄ + k₂ - k₂₃ + k₁) k₁'
    · congr 1
      obtain ⟨h21, h22, h23⟩ := hA2
      rw [show T5 (d := d) hbc k₂₃ (k₁' : ℕ) (k₃₄ + k₂ - k₂₃ + k₁ - k₁') L =
          T5 hbc k₂₃ (k₂₃ + k₁' - k₂₃) (k₃₄ + k₂ - k₂₃ + k₁ - k₁') L by
          rw [Nat.add_sub_cancel_left],
        T5_eq_sum_T1 hab hbc ha hc ⟨by omega, by omega, by omega⟩, map_sum, sum_eq_single k₁₂]
      · rw [map_smul, smul_eq_mul, ite_recoupling_eq_rc hab hbc 0 k₁₂ k₂₃
          ⟨by omega, by omega, by omega⟩]
        by_cases hA1 : ValidA a b c (k₂₃ + k₁') k₁₂
        · congr 1
          obtain ⟨h11, h12, h13⟩ := hA1
          rw [quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 h12 h13 hk₄.1 hk₄.2 (by omega) h23 hL1]
          simp only [true_and, and_true]
        · rw [rc_of_not_validA hA1, zero_mul, zero_mul]
      · intro k₁₂' _ hne
        rw [map_smul]
        by_cases hA1 : ValidA a b c (k₂₃ + k₁') k₁₂'
        · obtain ⟨h11, h12, h13⟩ := hA1
          rw [quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 h12 h13 hk₄.1 hk₄.2 (by omega) h23 hL1,
            ite_eq_right (show ¬(k₁₂ = k₁₂' ∧ _) from fun h => hne h.1.symm), smul_zero]
        · rw [ite_eq_right hA1, zero_smul]
      · simp
    · rw [rc_of_not_validA hA2, zero_mul, zero_mul]
  · rw [rc_of_not_validA hA3, zero_mul, zero_mul]

/-- **The pentagon (Biedenharn–Elliott) identity for recoupling coefficients.** For positive
`j₁, j₂, j₃, j₄, j₁₂, j₃₄`, expanding `⟨((12)3)4 | 1(2(34))⟩` in two moves (via `(12)(34)`) and
in three moves (via `1((23)4)`, `(1(23))4`) gives the same number:
`R_{a b j₃₄} · R_{j₁₂ c d} = Σ_{j₂₃} R_{b c d} · R_{a j₂₃ d} · R_{a b c}` (labels as in the
statement; the indicators enforce the shared intermediate spins). -/
theorem pentagon_rc (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (k₁₂ : Fin (min a b + 1)) (h12 : 0 < a + b - 2 * (k₁₂ : ℕ)) (k₃₄ : Fin (min c d + 1))
    (h34 : 0 < c + d - 2 * (k₃₄ : ℕ)) (k₁₂₃ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1)) {k₄ : ℕ}
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) ∧ k₄ ≤ d)
    (k₂ : Fin (min b (c + d - 2 * (k₃₄ : ℕ)) + 1)) {k₁ : ℕ}
    (hk₁ : k₁ ≤ a ∧ k₁ ≤ b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) + d - 2 * k₄)
    (hL3 : L ≤ a + (b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) - 2 * k₁) :
    rc a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) L k₁₂ k₂ *
        (rc (a + b - 2 * (k₁₂ : ℕ)) c d (k₂ + k₁ - k₁₂ + k₃₄) L k₁₂₃ k₃₄ *
          (if k₄ = k₂ + k₁ - k₁₂ + k₃₄ - k₁₂₃ then 1 else 0)) =
      ∑ k₂₃ : Fin (min b c + 1), rc b c d (k₃₄ + k₂) 0 k₂₃ k₃₄ *
        ∑ k₁' : Fin (min a (b + c - 2 * (k₂₃ : ℕ)) + 1),
          rc a (b + c - 2 * (k₂₃ : ℕ)) d (k₃₄ + k₂ - k₂₃ + k₁) L k₁' (k₃₄ + k₂ - k₂₃) *
            (rc a b c (k₂₃ + k₁') 0 k₁₂ k₂₃ *
              (if (k₁₂₃ : ℕ) = k₂₃ + k₁' - k₁₂ ∧ k₄ = k₃₄ + k₂ - k₂₃ + k₁ - k₁' then 1 else 0)) := by
  have hab : 0 < a + b := by omega
  have hbc : 0 < b + c := by omega
  have hcd : 0 < c + d := by omega
  have h12c : 0 < a + b - 2 * (k₁₂ : ℕ) + c := by omega
  have h5 : 0 < b + (c + d - 2 * (k₃₄ : ℕ)) := by omega
  have hk₂ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂.isLt)
  have hk₁₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁₂₃.isLt)
  have htwo := quadForm_T1_T3_two hab hcd ha hc hd k₁₂ h12 h12c k₃₄ h34 h5 k₁₂₃ hk₄ k₂ hk₁ hL1 hL3
  have hthree := quadForm_T1_T3_three hab hbc hcd ha hb hc hd k₁₂ hk₁₂₃ hk₄ k₃₄ hk₂ hk₁ hL1 hL3
  rw [← hthree, htwo, ite_recoupling_eq_rc hab h5 L k₁₂ k₂ ⟨by omega, by omega, by omega⟩]
  by_cases hA : ValidA a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) k₁₂
  · obtain ⟨hA1, hA2, hA3⟩ := hA
    have hk₃₄ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₃₄.isLt)
    rw [ite_recoupling_eq_rc h12c hcd L k₁₂₃ k₃₄ ⟨by omega, by omega, by omega⟩]
  · rw [rc_of_not_validA hA, zero_mul, zero_mul]

/-! ## Stage 5: from recoupling coefficients to `sixJSym` -/

/-- Edge labels of the dual tetrahedron of `{j₁ j₂ j₃; j₄ j₅ j₆}`, as `sixJSymEdge` indexes them. -/
def edgeM (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Fin 4 → Fin 4 → ℕ :=
  ![![0, j₁, j₂, j₃], ![j₁, 0, j₆, j₅], ![j₂, j₆, 0, j₄], ![j₃, j₅, j₄, 0]]

/-- The same labels as a function on `Sym2 (Fin 4)`. -/
def edgeFn (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Sym2 (Fin 4) → ℕ :=
  Sym2.lift ⟨edgeM j₁ j₂ j₃ j₄ j₅ j₆, by intro i k; fin_cases i <;> fin_cases k <;> rfl⟩

/-- **Tetrahedral symmetry, explicit form**: relabelling the four triads by `σ` does not change
the 6j symbol. -/
lemma sixJSym_perm (σ : Equiv.Perm (Fin 4)) (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 0) (σ 1)) (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 0) (σ 2))
      (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 0) (σ 3)) (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 2) (σ 3))
      (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 1) (σ 3)) (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 1) (σ 2)) =
      sixJSym j₁ j₂ j₃ j₄ j₅ j₆ :=
  sixJSymEdge_comp_map σ (edgeFn j₁ j₂ j₃ j₄ j₅ j₆)

/-- The permutation of `Fin 4` given by a vector (bijectivity by `decide`). -/
noncomputable def permOf (v : Fin 4 → Fin 4) (h : Function.Bijective v) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective v h

lemma sixJSym_P2 (c d x e f q : ℕ) : sixJSym c d x e f q = sixJSym e x f c q d := by
  have := sixJSym_perm (permOf ![2, 3, 1, 0] (by decide)) e x f c q d
  simpa [permOf, edgeM] using this

lemma sixJSym_P3 (e f x b a r : ℕ) : sixJSym e f x b a r = sixJSym e a r b f x := by
  have := sixJSym_perm (permOf ![1, 0, 3, 2] (by decide)) e a r b f x
  simpa [permOf, edgeM] using this

lemma sixJSym_R1 (p q r e a d : ℕ) : sixJSym p q r e a d = sixJSym e a r p q d := by
  have := sixJSym_perm (permOf ![3, 2, 1, 0] (by decide)) e a r p q d
  simpa [permOf, edgeM] using this

lemma sixJSym_R2 (p q r f b c : ℕ) : sixJSym p q r f b c = sixJSym r b f c q p := by
  have := sixJSym_perm (permOf ![1, 2, 3, 0] (by decide)) r b f c q p
  simpa [permOf, edgeM] using this

/-- The triad `(j₁ j₅ j₆)` moved to the front (`σ = (0 1)`). -/
lemma sixJSym_v1 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₆ j₅ j₄ j₃ j₂ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![1, 0, 2, 3] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- The triad `(j₄ j₂ j₆)` moved to the front (`σ = (0 2)`). -/
lemma sixJSym_v2 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₆ j₂ j₄ j₃ j₅ j₁ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![2, 1, 0, 3] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- The triad `(j₄ j₅ j₃)` moved to the front (`σ = (0 3)`). -/
lemma sixJSym_v3 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₅ j₄ j₃ j₂ j₁ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![3, 1, 2, 0] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- An admissible triad (doubled spins): even perimeter and the three triangle inequalities. -/
def Tri (x y z : ℕ) : Prop := (x + y + z) % 2 = 0 ∧ z ≤ x + y ∧ x ≤ y + z ∧ y ≤ x + z

/-- A nonzero 6j symbol has four admissible triads. -/
lemma tri_of_sixJSym_ne_zero {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : sixJSym j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0) :
    Tri j₁ j₂ j₃ ∧ Tri j₁ j₅ j₆ ∧ Tri j₄ j₂ j₆ ∧ Tri j₄ j₅ j₃ := by
  have h0 := triads_of_sixJSym_ne_zero h
  have h1 := triads_of_sixJSym_ne_zero (show sixJSym j₁ j₆ j₅ j₄ j₃ j₂ ≠ 0 by rwa [sixJSym_v1])
  have h2 := triads_of_sixJSym_ne_zero (show sixJSym j₆ j₂ j₄ j₃ j₅ j₁ ≠ 0 by rwa [sixJSym_v2])
  have h3 := triads_of_sixJSym_ne_zero (show sixJSym j₅ j₄ j₃ j₂ j₁ j₆ ≠ 0 by rwa [sixJSym_v3])
  unfold Tri
  omega

/-- **`rc` in terms of the 6j symbol**: `R = (-1)^(j₁+j₂+j₃+J) √((2j₁₂+1)(2j₂₃+1)) {j₁ j₂ j₁₂; j₃ J j₂₃}`
(doubled units), for positive outer spins. -/
lemma rc_eq_sixJSym {x y z K l k₁ k₃ : ℕ} (hx : 0 < x) (hz : 0 < z) (hl : l ≤ x + y + z - 2 * K) :
    rc x y z K l k₁ k₃ =
      if k₁ < min x y + 1 ∧ k₃ < min y z + 1 ∧ ValidA x y z K k₁ ∧ ValidB x y z K k₃ then
        (-1) ^ (x + y + z - K) *
          Real.sqrt (((x + y - 2 * k₁ + 1 : ℕ) : ℝ) * ((y + z - 2 * k₃ + 1 : ℕ) : ℝ)) *
            sixJSym x y (x + y - 2 * k₁) z (x + y + z - 2 * K) (y + z - 2 * k₃)
      else 0 := by
  unfold rc
  by_cases h : k₁ < min x y + 1 ∧ k₃ < min y z + 1 ∧ ValidA x y z K k₁ ∧ ValidB x y z K k₃
  · obtain ⟨h1, h3, hA, hB⟩ := h
    rw [dite_eq_left ⟨by omega, by omega, h1, h3, hA, hB⟩, ite_eq_left ⟨h1, h3, hA, hB⟩,
      recoupling_eq_sixJ (by omega) (by omega) hx (k₁ := ⟨k₁, h1⟩) (k₃ := ⟨k₃, h3⟩) hA hB hl,
      sixJ_eq_sixJSym (by omega) (by omega) hx hz hA hB]
  · rw [ite_eq_right h, dite_eq_right (fun h' => h ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2⟩)]

end Lightlike.Pentagon

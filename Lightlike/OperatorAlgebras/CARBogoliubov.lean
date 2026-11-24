import Lightlike.OperatorAlgebras.CARUnique

/-!
# Fermionic Bogoliubov transformations of the CAR

Let `a, c : Fin n → A` satisfy the CAR in creation-annihilation form (`IsCARPairs`: `aᵢcⱼ + cⱼaᵢ = δᵢⱼ`, `aᵢaⱼ + aⱼaᵢ = 0`,
`cᵢcⱼ + cⱼcᵢ = 0`). For complex `n × n` matrices `α, β`, the **Bogoliubov transform** is
`bᵢ = ∑ⱼ (αᵢⱼ aⱼ + βᵢⱼ cⱼ)` with `bᵢ* := ∑ⱼ (conj αᵢⱼ cⱼ + conj βᵢⱼ aⱼ)` (the formal adjoint, which is the adjoint when `cⱼ = aⱼ*`).

* `bogAnn_bogCre_anticomm`: `bᵢ bₖ* + bₖ* bᵢ = (α α* + β β*)ᵢₖ`;
* `bogAnn_anticomm`: `bᵢ bₖ + bₖ bᵢ = (α βᵀ + β αᵀ)ᵢₖ`;
* `isCARPairs_bog`: if `α α* + β β* = 1` and `α βᵀ + β αᵀ = 0` then `(b, b*)` satisfy the CAR again (sufficiency of the
  fermionic Bogoliubov conditions; for one mode `|α|² + |β|² = 1`, the fermionic counterpart of the bosonic `|α|² − |β|² = 1`).

For a CAR representation on a Hilbert space (`IsCAROn`), the new family is again a CAR representation
(`isCAROn_bog`, with Majorana operators `φ'_{2j} = bⱼ + bⱼ*`, `φ'_{2j+1} = -i (bⱼ - bⱼ*)`), so by uniqueness of the irreducible
representation (`car_irreducible_unitarily_equivalent`) every Bogoliubov transformation of the finite-dimensional Fock
(Jordan-Wigner) representation is unitarily implementable (`bogoliubov_implementable`); in finite dimensions there is no
Shale condition (contrast `ShaleSufficiency` for the bosonic case).
-/

open Matrix

namespace Lightlike.OperatorAlgebras

section Algebraic

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

/-- The Bogoliubov transform of the annihilation operators. -/
noncomputable def bogAnn (α β : Matrix (Fin n) (Fin n) ℂ) (a c : Fin n → A) (i : Fin n) : A :=
  ∑ j, (α i j • a j + β i j • c j)

/-- The formal adjoint of `bogAnn`. -/
noncomputable def bogCre (α β : Matrix (Fin n) (Fin n) ℂ) (a c : Fin n → A) (i : Fin n) : A :=
  ∑ j, ((starRingEnd ℂ) (α i j) • c j + (starRingEnd ℂ) (β i j) • a j)

/-- Anticommutator of two linear combinations of two families. -/
lemma anticomm_lincomb (p q : Fin n → ℂ) (u v : Fin n → A) :
    (∑ j, p j • u j) * (∑ l, q l • v l) + (∑ l, q l • v l) * (∑ j, p j • u j) =
      ∑ j, ∑ l, (p j * q l) • (u j * v l + v l * u j) := by
  have h1 : (∑ j, p j • u j) * (∑ l, q l • v l) = ∑ j, ∑ l, (p j * q l) • (u j * v l) := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
    try rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : (∑ l, q l • v l) * (∑ j, p j • u j) = ∑ j, ∑ l, (p j * q l) • (v l * u j) := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_add]

lemma anticomm_lincomb_delta (p q : Fin n → ℂ) (u v : Fin n → A)
    (hd : ∀ j l, u j * v l + v l * u j = if j = l then 1 else 0) :
    (∑ j, p j • u j) * (∑ l, q l • v l) + (∑ l, q l • v l) * (∑ j, p j • u j) =
      (∑ j, p j * q j) • (1 : A) := by
  rw [anticomm_lincomb]
  simp only [hd, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_smul]

lemma anticomm_lincomb_zero (p q : Fin n → ℂ) (u v : Fin n → A)
    (hd : ∀ j l, u j * v l + v l * u j = 0) :
    (∑ j, p j • u j) * (∑ l, q l • v l) + (∑ l, q l • v l) * (∑ j, p j • u j) = 0 := by
  rw [anticomm_lincomb]
  simp [hd]

lemma anticomm_add4 {A : Type*} [Ring A] (x y z w : A) :
    (x + y) * (z + w) + (z + w) * (x + y) = (x * z + z * x) + (x * w + w * x) + ((y * z + z * y) + (y * w + w * y)) := by
  noncomm_ring

variable {a c : Fin n → A}

/-- `bᵢ bₖ* + bₖ* bᵢ = (α α* + β β*)ᵢₖ`. -/
theorem bogAnn_bogCre_anticomm (h : IsCARPairs a c) (α β : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    bogAnn α β a c i * bogCre α β a c k + bogCre α β a c k * bogAnn α β a c i =
      ((α * αᴴ + β * βᴴ) i k : ℂ) • (1 : A) := by
  have e1 : bogAnn α β a c i = (∑ j, α i j • a j) + ∑ j, β i j • c j := by
    simp [bogAnn, Finset.sum_add_distrib]
  have e2 : bogCre α β a c k = (∑ j, (starRingEnd ℂ) (α k j) • c j) + ∑ j, (starRingEnd ℂ) (β k j) • a j := by
    simp [bogCre, Finset.sum_add_distrib]
  rw [e1, e2, anticomm_add4,
    anticomm_lincomb_delta _ _ _ _ (fun j l => h.ac j l),
    anticomm_lincomb_zero _ _ _ _ (fun j l => h.aa j l),
    anticomm_lincomb_zero _ _ _ _ (fun j l => h.cc j l),
    anticomm_lincomb_delta _ _ _ _ (fun j l => by
      rw [add_comm, h.ac l j]; simp only [eq_comm])]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, add_smul]

/-- `bᵢ bₖ + bₖ bᵢ = (α βᵀ + β αᵀ)ᵢₖ`. -/
theorem bogAnn_anticomm (h : IsCARPairs a c) (α β : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    bogAnn α β a c i * bogAnn α β a c k + bogAnn α β a c k * bogAnn α β a c i =
      ((α * βᵀ + β * αᵀ) i k : ℂ) • (1 : A) := by
  have e1 : ∀ i, bogAnn α β a c i = (∑ j, α i j • a j) + ∑ j, β i j • c j := by
    intro i; simp [bogAnn, Finset.sum_add_distrib]
  rw [e1 i, e1 k, anticomm_add4,
    anticomm_lincomb_zero _ _ _ _ (fun j l => h.aa j l),
    anticomm_lincomb_delta _ _ _ _ (fun j l => h.ac j l),
    anticomm_lincomb_zero _ _ _ _ (fun j l => h.cc j l),
    anticomm_lincomb_delta _ _ _ _ (fun j l => by
      rw [add_comm, h.ac l j]; simp only [eq_comm])]
  simp [Matrix.mul_apply, Matrix.transpose_apply, add_smul, mul_comm]

omit [Algebra ℂ A] in
lemma IsCARPairs.swap (h : IsCARPairs a c) : IsCARPairs c a where
  ac i j := by rw [add_comm, h.ac j i]; simp only [eq_comm]
  aa := h.cc
  cc := h.aa

lemma bogCre_eq (α β : Matrix (Fin n) (Fin n) ℂ) :
    bogCre α β a c = bogAnn (α.map (starRingEnd ℂ)) (β.map (starRingEnd ℂ)) c a := rfl

/-- **Sufficiency of the fermionic Bogoliubov conditions**: if `α α* + β β* = 1` and `α βᵀ + β αᵀ = 0`, then
`(bogAnn, bogCre)` satisfy the CAR again. -/
theorem isCARPairs_bog (h : IsCARPairs a c) (α β : Matrix (Fin n) (Fin n) ℂ)
    (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) :
    IsCARPairs (bogAnn α β a c) (bogCre α β a c) where
  ac i k := by
    rw [bogAnn_bogCre_anticomm h, h1, Matrix.one_apply]
    split_ifs <;> simp
  aa i k := by
    rw [bogAnn_anticomm h, h2]; simp
  cc i k := by
    rw [bogCre_eq, bogAnn_anticomm h.swap]
    have : (α.map (starRingEnd ℂ)) * (β.map (starRingEnd ℂ))ᵀ + (β.map (starRingEnd ℂ)) * (α.map (starRingEnd ℂ))ᵀ = 0 := by
      calc _ = (α * βᵀ + β * αᵀ).map (starRingEnd ℂ) := by
            simp [Matrix.map_mul, Matrix.transpose_map, Matrix.map_add]
        _ = 0 := by rw [h2]; simp
    rw [this]; simp

end Algebraic

section Inverse

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {a c : Fin n → A}

/-- The Bogoliubov matrix `[[α, β], [β̄, ᾱ]]` is unitary, so also `U* U = 1`: the four block identities. -/
lemma bog_matrix_inv (α β : Matrix (Fin n) (Fin n) ℂ) (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) :
    αᴴ * α + βᵀ * β.map (starRingEnd ℂ) = 1 ∧ αᴴ * β + βᵀ * α.map (starRingEnd ℂ) = 0 ∧
      βᴴ * α + αᵀ * β.map (starRingEnd ℂ) = 0 ∧ βᴴ * β + αᵀ * α.map (starRingEnd ℂ) = 1 := by
  set U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.fromBlocks α β (β.map (starRingEnd ℂ)) (α.map (starRingEnd ℂ)) with hU
  have h3 : α.map (starRingEnd ℂ) * αᵀ + β.map (starRingEnd ℂ) * βᵀ = 1 := by
    ext i j
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun h1 i) j)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, map_add, map_sum, map_mul,
      Complex.star_def, Complex.conj_conj, apply_ite, map_one, map_zero, star_star] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply]
    rcases eq_or_ne i j with rfl | hij
    · simpa [mul_comm] using this
    · simpa [hij, Ne.symm hij, mul_comm] using this
  have h4 : α.map (starRingEnd ℂ) * βᴴ + β.map (starRingEnd ℂ) * αᴴ = 0 := by
    ext i j
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun h2 i) j)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, map_add, map_sum, map_mul,
      map_zero] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.zero_apply]
    simpa [mul_comm] using this
  have hct : ∀ M : Matrix (Fin n) (Fin n) ℂ, (M.map (starRingEnd ℂ))ᴴ = Mᵀ := fun M => by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hUU : U * Uᴴ = 1 := by
    rw [hU, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [hct, Matrix.conjTranspose_conjTranspose]
    rw [h1, h2, add_comm (β.map (starRingEnd ℂ) * αᴴ), h4, add_comm (β.map (starRingEnd ℂ) * βᵀ), h3, ← Matrix.fromBlocks_one]
  have hUU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hUU
  rw [hU, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hUU'
  simp only [hct, Matrix.conjTranspose_conjTranspose] at hUU'
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hUU'
  exact ⟨hUU'.1, hUU'.2.1, hUU'.2.2.1, hUU'.2.2.2⟩

/-- Linear combination of the transformed operators in terms of the old ones. -/
lemma bog_comb (α β P Q : Matrix (Fin n) (Fin n) ℂ) (l : Fin n) :
    ∑ i, (P i l • bogAnn α β a c i + Q i l • bogCre α β a c i) =
      ∑ j, ((∑ i, (P i l * α i j + Q i l * (starRingEnd ℂ) (β i j))) • a j +
        (∑ i, (P i l * β i j + Q i l * (starRingEnd ℂ) (α i j))) • c j) := by
  simp only [bogAnn, bogCre, Finset.smul_sum, smul_add, smul_smul, Finset.sum_add_distrib, add_smul, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun i j => (P i l * α i j) • a j), Finset.sum_comm (f := fun i j => (P i l * β i j) • c j),
    Finset.sum_comm (f := fun i j => (Q i l * (starRingEnd ℂ) (α i j)) • c j),
    Finset.sum_comm (f := fun i j => (Q i l * (starRingEnd ℂ) (β i j)) • a j)]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  abel

/-- **The inverse transformation**: `aₗ = ∑ᵢ (conj αᵢₗ bᵢ + βᵢₗ bᵢ*)` and `cₗ = ∑ᵢ (conj βᵢₗ bᵢ + αᵢₗ bᵢ*)`. -/
theorem bog_inv (α β : Matrix (Fin n) (Fin n) ℂ) (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) (l : Fin n) :
    ∑ i, ((starRingEnd ℂ) (α i l) • bogAnn α β a c i + β i l • bogCre α β a c i) = a l ∧
    ∑ i, ((starRingEnd ℂ) (β i l) • bogAnn α β a c i + α i l • bogCre α β a c i) = c l := by
  obtain ⟨m1, m2, m3, m4⟩ := bog_matrix_inv α β h1 h2
  have g1 : ∀ j, ∑ i, ((starRingEnd ℂ) (α i l) * α i j + β i l * (starRingEnd ℂ) (β i j)) = if l = j then 1 else 0 := by
    intro j
    have := congrFun (congrFun m1 l) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Finset.sum_add_distrib] using this
  have g2 : ∀ j, ∑ i, ((starRingEnd ℂ) (α i l) * β i j + β i l * (starRingEnd ℂ) (α i j)) = 0 := by
    intro j
    have := congrFun (congrFun m2 l) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_add_distrib] using this
  have g3 : ∀ j, ∑ i, ((starRingEnd ℂ) (β i l) * α i j + α i l * (starRingEnd ℂ) (β i j)) = 0 := by
    intro j
    have := congrFun (congrFun m3 l) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_add_distrib] using this
  have g4 : ∀ j, ∑ i, ((starRingEnd ℂ) (β i l) * β i j + α i l * (starRingEnd ℂ) (α i j)) = if l = j then 1 else 0 := by
    intro j
    have := congrFun (congrFun m4 l) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Finset.sum_add_distrib] using this
  constructor
  · have := bog_comb (a := a) (c := c) α β (α.map (starRingEnd ℂ)) β l
    simp only [Matrix.map_apply] at this
    rw [this]
    simp only [g1, g2, zero_smul, add_zero, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · have := bog_comb (a := a) (c := c) α β (β.map (starRingEnd ℂ)) α l
    simp only [Matrix.map_apply] at this
    rw [this]
    simp only [g3, g4, zero_smul, zero_add, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Inverse

open scoped InnerProductSpace

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}

/-- The Majorana family of a pair `(a, c)`: `φ_{2j} = aⱼ + cⱼ`, `φ_{2j+1} = -i (aⱼ - cⱼ)`. -/
noncomputable def majFam (a c : Fin n → (E →L[ℂ] E)) : Fin (2 * n) → (E →L[ℂ] E) := fun k =>
  if k.1 % 2 = 0 then a ⟨k.1 / 2, by omega⟩ + c ⟨k.1 / 2, by omega⟩
  else -Complex.I • (a ⟨k.1 / 2, by omega⟩ - c ⟨k.1 / 2, by omega⟩)

lemma majorana_majFam_zero (a c : Fin n → (E →L[ℂ] E)) (j : Fin n) : majorana (majFam a c) j 0 = a j + c j := by
  simp only [majorana, majFam]
  rw [if_pos (by simp)]
  congr 2 <;> ext <;> simp <;> omega

lemma majorana_majFam_one (a c : Fin n → (E →L[ℂ] E)) (j : Fin n) :
    majorana (majFam a c) j 1 = -Complex.I • (a j - c j) := by
  simp only [majorana, majFam]
  rw [if_neg (by simp)]
  congr 3 <;> ext <;> simp <;> omega

lemma carAnnihilation_majFam (a c : Fin n → (E →L[ℂ] E)) (j : Fin n) : carAnnihilation (majFam a c) j = a j := by
  rw [carAnnihilation, majorana_majFam_zero, majorana_majFam_one]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma carCreation_majFam (a c : Fin n → (E →L[ℂ] E)) (j : Fin n) : carCreation (majFam a c) j = c j := by
  rw [carCreation, majorana_majFam_zero, majorana_majFam_one]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

section MajFam

variable {a c : Fin n → (E →L[ℂ] E)} (hp : IsCARPairs a c)
include hp

lemma xx_anticomm (j l : Fin n) :
    (a j + c j) * (a l + c l) + (a l + c l) * (a j + c j) = if j = l then (2 : ℂ) • (1 : E →L[ℂ] E) else 0 := by
  have e : (a j + c j) * (a l + c l) + (a l + c l) * (a j + c j) =
      (a j * a l + a l * a j) + (a j * c l + c l * a j) + ((c j * a l + a l * c j) + (c j * c l + c l * c j)) := by
    noncomm_ring
  rw [e, hp.aa, hp.cc, hp.ac j l, add_comm (c j * a l), hp.ac l j]
  by_cases h : j = l
  · subst h; simp [two_smul]
  · simp [h, Ne.symm h]

lemma yy_anticomm (j l : Fin n) :
    (-Complex.I • (a j - c j)) * (-Complex.I • (a l - c l)) + (-Complex.I • (a l - c l)) * (-Complex.I • (a j - c j)) =
      if j = l then (2 : ℂ) • (1 : E →L[ℂ] E) else 0 := by
  have e : (-Complex.I • (a j - c j)) * (-Complex.I • (a l - c l)) + (-Complex.I • (a l - c l)) * (-Complex.I • (a j - c j)) =
      (-Complex.I * -Complex.I) • ((a j * a l + a l * a j) - (a j * c l + c l * a j) - ((c j * a l + a l * c j) - (c j * c l + c l * c j))) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_add]
    noncomm_ring
  rw [e, hp.aa, hp.cc, hp.ac j l, add_comm (c j * a l), hp.ac l j]
  by_cases h : j = l
  · subst h; simp [two_smul]
  · simp [h, Ne.symm h]

lemma xy_anticomm (j l : Fin n) :
    (a j + c j) * (-Complex.I • (a l - c l)) + (-Complex.I • (a l - c l)) * (a j + c j) = 0 := by
  have e : (a j + c j) * (-Complex.I • (a l - c l)) + (-Complex.I • (a l - c l)) * (a j + c j) =
      (-Complex.I) • ((a j * a l + a l * a j) - (a j * c l + c l * a j) + ((c j * a l + a l * c j) - (c j * c l + c l * c j))) := by
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_add]
    noncomm_ring
  rw [e, hp.aa, hp.cc, hp.ac j l, add_comm (c j * a l), hp.ac l j]
  by_cases h : j = l
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **The Majorana family of a CAR pair with `aⱼ* = cⱼ` is a CAR representation.** -/
theorem isCAROn_majFam (hadj : ∀ j p q, ⟪a j p, q⟫_ℂ = ⟪p, c j q⟫_ℂ) : IsCAROn (majFam a c) where
  symm k v w := by
    have hadj' : ∀ j p q, ⟪c j p, q⟫_ℂ = ⟪p, a j q⟫_ℂ := fun j p q => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    unfold majFam
    split_ifs
    · simp [inner_add_left, inner_add_right, hadj, hadj', add_comm]
    · simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hadj, hadj']
      ring
  anticomm k l := by
    unfold majFam
    have hkl : (k = l) ↔ (k.1 / 2 = l.1 / 2 ∧ k.1 % 2 = l.1 % 2) := by
      rw [Fin.ext_iff]; omega
    have hjl : (⟨k.1 / 2, by omega⟩ : Fin n) = ⟨l.1 / 2, by omega⟩ ↔ k.1 / 2 = l.1 / 2 := by
      rw [Fin.ext_iff]
    by_cases hk : k.1 % 2 = 0 <;> by_cases hl : l.1 % 2 = 0
    · rw [if_pos hk, if_pos hl, xx_anticomm hp]
      simp only [hjl, hkl]; simp [hk, hl]
    · rw [if_pos hk, if_neg hl, xy_anticomm hp]
      have : ¬ k = l := by rw [hkl]; omega
      simp [this]
    · rw [if_neg hk, if_pos hl]
      have := xy_anticomm hp ⟨l.1 / 2, by omega⟩ ⟨k.1 / 2, by omega⟩
      rw [add_comm]; rw [this]
      have : ¬ k = l := by rw [hkl]; omega
      simp [this]
    · rw [if_neg hk, if_neg hl, yy_anticomm hp]
      simp only [hjl, hkl]
      have h2 : k.1 % 2 = l.1 % 2 := by omega
      simp [h2]

end MajFam

/-- **The Bogoliubov-transformed CAR representation** of `φ`: the Majorana family of `(bogAnn α β a c, bogCre α β a c)`
for `a = carAnnihilation φ`, `c = carCreation φ`. -/
noncomputable def bogFam (φ : Fin (2 * n) → (E →L[ℂ] E)) (α β : Matrix (Fin n) (Fin n) ℂ) : Fin (2 * n) → (E →L[ℂ] E) :=
  majFam (bogAnn α β (carAnnihilation φ) (carCreation φ)) (bogCre α β (carAnnihilation φ) (carCreation φ))

lemma carAnnihilation_bogFam (φ : Fin (2 * n) → (E →L[ℂ] E)) (α β : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    carAnnihilation (bogFam φ α β) j = bogAnn α β (carAnnihilation φ) (carCreation φ) j :=
  carAnnihilation_majFam _ _ j

lemma carCreation_bogFam (φ : Fin (2 * n) → (E →L[ℂ] E)) (α β : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    carCreation (bogFam φ α β) j = bogCre α β (carAnnihilation φ) (carCreation φ) j :=
  carCreation_majFam _ _ j

/-- The transformed operators are adjoint to each other: `⟪bᵢ p, q⟫ = ⟪p, bᵢ* q⟫`. -/
lemma bog_adj {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (α β : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (p q : E) :
    ⟪bogAnn α β (carAnnihilation φ) (carCreation φ) i p, q⟫_ℂ = ⟪p, bogCre α β (carAnnihilation φ) (carCreation φ) i q⟫_ℂ := by
  have hc : ∀ j p q, ⟪carCreation φ j p, q⟫_ℂ = ⟪p, carAnnihilation φ j q⟫_ℂ := fun j p q => by
    rw [← inner_conj_symm, ← h.adj, inner_conj_symm]
  simp only [bogAnn, bogCre, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    sum_inner, inner_sum, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h.adj, hc,
    Complex.conj_conj]

/-- **A Bogoliubov transform of a CAR representation is a CAR representation.** -/
theorem isCAROn_bogFam {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (α β : Matrix (Fin n) (Fin n) ℂ)
    (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) : IsCAROn (bogFam φ α β) :=
  isCAROn_majFam (isCARPairs_bog h.isCARPairs α β h1 h2) (bog_adj h α β)

/-- A closed subspace invariant under every `φ'ₖ` is invariant under `aⱼ', cⱼ'` (as combinations of the `φ'ₖ`). -/
lemma invariant_of_majFam {a c : Fin n → (E →L[ℂ] E)} {W : Submodule ℂ E}
    (hW : ∀ k, ∀ w ∈ W, majFam a c k w ∈ W) (j : Fin n) : (∀ w ∈ W, a j w ∈ W) ∧ ∀ w ∈ W, c j w ∈ W := by
  have h0 := hW ⟨2 * j.1, by omega⟩
  have h1 := hW ⟨2 * j.1 + 1, by omega⟩
  have e0 : majFam a c ⟨2 * j.1, by omega⟩ = a j + c j := by
    have := majorana_majFam_zero a c j
    simpa [majorana] using this
  have e1 : majFam a c ⟨2 * j.1 + 1, by omega⟩ = -Complex.I • (a j - c j) := by
    have := majorana_majFam_one a c j
    simpa [majorana] using this
  rw [e0] at h0
  rw [e1] at h1
  constructor
  · intro w hw
    have x0 := h0 w hw
    have x1 := h1 w hw
    have : a j w = (1 / 2 : ℂ) • ((a j + c j) w) + ((1 / 2 : ℂ) * Complex.I) • ((-Complex.I • (a j - c j)) w) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_smul,
        smul_sub, smul_add]
      match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (by simpa using x0)) (Submodule.smul_mem _ _ (by simpa using x1))
  · intro w hw
    have x0 := h0 w hw
    have x1 := h1 w hw
    have : c j w = (1 / 2 : ℂ) • ((a j + c j) w) - ((1 / 2 : ℂ) * Complex.I) • ((-Complex.I • (a j - c j)) w) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_smul,
        smul_sub, smul_add]
      match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    rw [this]
    exact sub_mem (Submodule.smul_mem _ _ (by simpa using x0)) (Submodule.smul_mem _ _ (by simpa using x1))

/-- **A Bogoliubov transform of an irreducible CAR representation is irreducible** (the inverse transformation expresses
`aⱼ, cⱼ` through `bᵢ, bᵢ*`). -/
theorem isIrreducibleCAR_bogFam {φ : Fin (2 * n) → (E →L[ℂ] E)} (hirr : IsIrreducibleCAR φ) (α β : Matrix (Fin n) (Fin n) ℂ)
    (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) : IsIrreducibleCAR (bogFam φ α β) := by
  intro W hWc hW
  have inv : ∀ j, (∀ w ∈ W, bogAnn α β (carAnnihilation φ) (carCreation φ) j w ∈ W) ∧
      ∀ w ∈ W, bogCre α β (carAnnihilation φ) (carCreation φ) j w ∈ W := fun j => by
    have := invariant_of_majFam (a := bogAnn α β (carAnnihilation φ) (carCreation φ))
      (c := bogCre α β (carAnnihilation φ) (carCreation φ)) hW j
    exact this
  have hinv := bog_inv (a := carAnnihilation φ) (c := carCreation φ) α β h1 h2
  have ha : ∀ l, ∀ w ∈ W, carAnnihilation φ l w ∈ W := by
    intro l w hw
    rw [← (hinv l).1, ContinuousLinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    exact add_mem (Submodule.smul_mem _ _ ((inv i).1 w hw)) (Submodule.smul_mem _ _ ((inv i).2 w hw))
  have hc : ∀ l, ∀ w ∈ W, carCreation φ l w ∈ W := by
    intro l w hw
    rw [← (hinv l).2, ContinuousLinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    exact add_mem (Submodule.smul_mem _ _ ((inv i).1 w hw)) (Submodule.smul_mem _ _ ((inv i).2 w hw))
  refine hirr W hWc fun k w hw => ?_
  obtain ⟨j, s, rfl⟩ := exists_majorana_index k
  show majorana φ j s w ∈ W
  rcases fin_two_eq_zero_or_one s with rfl | rfl
  · rw [majorana_zero_eq]
    simpa using add_mem (ha j w hw) (hc j w hw)
  · rw [majorana_one_eq]
    simpa using Submodule.smul_mem _ (-Complex.I) (sub_mem (ha j w hw) (hc j w hw))

/-- **Every fermionic Bogoliubov transformation of an irreducible CAR representation is unitarily implementable**: for
`α α* + β β* = 1`, `α βᵀ + β αᵀ = 0` there is a unitary `U` of `E` with `U φₖ = φ'ₖ U` for the Bogoliubov-transformed
family `φ' = bogFam φ α β` (so `U aⱼ U⁻¹ = bⱼ`, `U aⱼ* U⁻¹ = bⱼ*`). In finite dimensions there is no Shale condition. -/
theorem bogoliubov_implementable [Nontrivial E] {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (hirr : IsIrreducibleCAR φ)
    (α β : Matrix (Fin n) (Fin n) ℂ) (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∀ k v, U (φ k v) = bogFam φ α β k (U v) :=
  car_irreducible_unitarily_equivalent h (isCAROn_bogFam h α β h1 h2) hirr (isIrreducibleCAR_bogFam hirr α β h1 h2)

end Hilbert

end Lightlike.OperatorAlgebras

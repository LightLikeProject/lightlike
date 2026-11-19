import Lightlike.NCG.MatrixUnits
import Lightlike.NCG.QuaternionComplexify

/-!
# Quaternionic summands `Mₙ(ℍ)`

T. Krajewski, arXiv:hep-th/9701081, Section 3.1, p. 10 (read): "`Mₙ(ℝ)` and `Mₙ(ℍ)` have only one irreducible
representation, the fundamental one ... `nᵢ` is the dimension of the irreducible representation `i`", which for `Mₙ(ℍ)`
is `ℂ²ⁿ`: `Mₙ(ℍ) ⊗_ℝ ℂ ≅ M₂ₙ(ℂ)`. For a real-linear `π` of `⊕ Mₙᵢ(ℍ)`, `ρ_αβ(q) = π(E_αβ(q))` and the complexification of
`QuaternionComplexify.lean` give the units `U_{(αs)(βt)} = (ρ_αβ)_ℂ(E_st)` of `M₂ₙ(ℂ)` on `H`, indexed by
`Fin (n · 2) ≃ Fin n × Fin 2`.

* `MatSumH`, `unitH`, `unitH_mul_same`, `unitH_mul_ne`, `star_unitH`, `unitHL`;
* `rhoH`: `q ↦ π(E_αβ(q))`, real-linear;
* `idxH`, `UH`, `UH_mul_same`, `UH_mul_ne`, `star_UH`: the units and their relations;
* `sum_unitH_block`, `eq_sum_unitH`, `phiHFun`, `phiH`: `⊕ Mₙᵢ(ℍ) → ⊕ M₂ₙᵢ(ℂ)`, a real `*`-homomorphism;
* `complexify_entries`, `sum_UH`, `unitsH`, `unitsH_hom_phiH`, `UH_mem_span`, `pi_single_one_ne_zero`: the units form a
  system of matrix units with `σ ∘ φ = π`;
* `quatComplexification`, `exists_unitary_quatSummands`: uniqueness for quaternionic summands.
-/

namespace Lightlike.NCG

noncomputable section

open scoped Quaternion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (n : ι → ℕ) in
/-- `⊕ᵢ Mₙᵢ(ℍ)`. -/
abbrev MatSumH := ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℍ[ℝ]

variable {n : ι → ℕ}

/-- The quaternionic matrix unit `E^i_{αβ}(q)`. -/
def unitH (i : ι) (α β : Fin (n i)) (q : ℍ[ℝ]) : MatSumH n := Pi.single i (Matrix.single α β q)

/-- `E^i_{αβ}(p) E^i_{γδ}(q) = δ_βγ E^i_{αδ}(pq)`. -/
lemma unitH_mul_same (i : ι) (α β γ δ : Fin (n i)) (p q : ℍ[ℝ]) :
    unitH i α β p * unitH i γ δ q = if β = γ then unitH i α δ (p * q) else 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    by_cases hβ : β = γ
    · subst hβ
      simp [unitH, Matrix.single_mul_single_same]
    · simp [unitH, hβ, Matrix.single_mul_single_of_ne (h := hβ)]
  · split_ifs <;> simp [unitH, Pi.single_eq_of_ne hk]

/-- Units of different blocks multiply to `0`. -/
lemma unitH_mul_ne (i j : ι) (hij : i ≠ j) (α β : Fin (n i)) (γ δ : Fin (n j)) (p q : ℍ[ℝ]) :
    unitH i α β p * unitH j γ δ q = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [unitH, Pi.single_eq_of_ne hij]
  · simp [unitH, Pi.single_eq_of_ne hk]

/-- `E^i_{αβ}(q)* = E^i_{βα}(q̄)`. -/
lemma star_unitH (i : ι) (α β : Fin (n i)) (q : ℍ[ℝ]) : star (unitH i α β q) = unitH i β α (star q) := by
  funext k
  by_cases hk : k = i
  · subst hk
    refine Matrix.ext fun γ δ => ?_
    by_cases h1 : α = δ <;> by_cases h2 : β = γ <;> simp [unitH, Matrix.star_apply, Matrix.single_apply, h1, h2]
  · simp [unitH, Pi.single_eq_of_ne hk]

/-- `q ↦ E^i_{αβ}(q)`, real-linear. -/
def unitHL (i : ι) (α β : Fin (n i)) : ℍ[ℝ] →ₗ[ℝ] MatSumH n where
  toFun := unitH i α β
  map_add' p q := by simp only [unitH, Matrix.single_add, Pi.single_add]
  map_smul' r q := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [unitH, Matrix.smul_single]
    · simp [unitH, Pi.single_eq_of_ne hk]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable (T : FiniteSpectralTriple (MatSumH n) H)

/-- `ρ_αβ(q) = π(E^i_{αβ}(q))`, real-linear. -/
def rhoH (i : ι) (α β : Fin (n i)) : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H) :=
  (T.π : MatSumH n →⋆ₐ[ℝ] (H →L[ℂ] H)).toAlgHom.toLinearMap ∘ₗ unitHL i α β

/-- `ρ_αβ(q) = π(E^i_{αβ}(q))`. -/
lemma rhoH_apply (i : ι) (α β : Fin (n i)) (q : ℍ[ℝ]) : rhoH T i α β q = T.π (unitH i α β q) := rfl

/-- The index of `M₂ₙ(ℂ)` as a pair in `Fin n × Fin 2`. -/
def idxH (i : ι) (x : Fin (n i * 2)) : Fin (n i) × Fin 2 := finProdFinEquiv.symm x

/-- **The units of `M₂ₙ(ℂ)` on `H`**: `U_{(αs)(βt)} = (ρ_αβ)_ℂ(E_st)`. -/
def UH (i : ι) (x y : Fin (n i * 2)) : H →L[ℂ] H :=
  complexify (rhoH T i (idxH i x).1 (idxH i y).1) (Matrix.single (idxH i x).2 (idxH i y).2 1)

/-- `U_{xy} U_{zw} = δ_yz U_{xw}`. -/
lemma UH_mul_same (i : ι) (x y z w : Fin (n i * 2)) :
    UH T i x y * UH T i z w = if y = z then UH T i x w else 0 := by
  by_cases hβ : (idxH i y).1 = (idxH i z).1
  · have hρ : ∀ p q, rhoH T i (idxH i x).1 (idxH i y).1 p * rhoH T i (idxH i z).1 (idxH i w).1 q =
        rhoH T i (idxH i x).1 (idxH i w).1 (p * q) := fun p q => by
      rw [rhoH_apply, rhoH_apply, rhoH_apply, ← map_mul, unitH_mul_same, if_pos hβ]
    rw [UH, UH, complexify_mul_of _ _ _ hρ]
    by_cases ht : (idxH i y).2 = (idxH i z).2
    · have hyz : y = z := finProdFinEquiv.symm.injective (Prod.ext hβ ht)
      rw [if_pos hyz, ht, Matrix.single_mul_single_same, one_mul, UH]
    · have hyz : y ≠ z := fun h => ht (by rw [h])
      rw [if_neg hyz, Matrix.single_mul_single_of_ne (h := ht), complexify_zero]
  · have hρ : ∀ p q, rhoH T i (idxH i x).1 (idxH i y).1 p * rhoH T i (idxH i z).1 (idxH i w).1 q =
        (0 : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (p * q) := fun p q => by
      rw [rhoH_apply, rhoH_apply, ← map_mul, unitH_mul_same, if_neg hβ, map_zero, LinearMap.zero_apply]
    have hyz : y ≠ z := fun h => hβ (by rw [h])
    rw [UH, UH, complexify_mul_of _ _ _ hρ, complexify_zero_left, if_neg hyz]

/-- Units of different blocks multiply to `0`. -/
lemma UH_mul_ne (i j : ι) (hij : i ≠ j) (x y : Fin (n i * 2)) (z w : Fin (n j * 2)) :
    UH T i x y * UH T j z w = 0 := by
  have hρ : ∀ p q, rhoH T i (idxH i x).1 (idxH i y).1 p * rhoH T j (idxH j z).1 (idxH j w).1 q =
      (0 : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (p * q) := fun p q => by
    rw [rhoH_apply, rhoH_apply, ← map_mul, unitH_mul_ne i j hij, map_zero, LinearMap.zero_apply]
  rw [UH, UH, complexify_mul_of _ _ _ hρ, complexify_zero_left]

/-- `U_{xy}* = U_{yx}`. -/
lemma star_UH (i : ι) (x y : Fin (n i * 2)) : star (UH T i x y) = UH T i y x := by
  have hρ : ∀ q, star (rhoH T i (idxH i x).1 (idxH i y).1 q) = rhoH T i (idxH i y).1 (idxH i x).1 (star q) :=
    fun q => by rw [rhoH_apply, rhoH_apply, ← map_star, star_unitH]
  rw [UH, star_complexify _ _ hρ, UH]
  congr 1
  ext a b
  by_cases h1 : (idxH i x).2 = b <;> by_cases h2 : (idxH i y).2 = a <;>
    simp [Matrix.star_apply, Matrix.single_apply, h1, h2]

/-- `∑_α E^i_{αα}(1) = 1ᵢ`. -/
lemma sum_unitH_block (i : ι) : ∑ α, unitH (n := n) i α α 1 = Pi.single i 1 := by
  funext k
  rw [Finset.sum_apply]
  by_cases hk : k = i
  · subst hk
    simp only [unitH, Pi.single_eq_same, Matrix.sum_single_one]
  · simp only [unitH, Pi.single_eq_of_ne hk, Finset.sum_const_zero]

/-- `a = ∑ᵢ ∑_αβ E^i_{αβ}(a_αβ)`. -/
lemma eq_sum_unitH (a : MatSumH n) : a = ∑ i, ∑ α, ∑ β, unitH i α β (a i α β) := by
  have h : ∀ i, ∑ α, ∑ β, unitH (n := n) i α β (a i α β) = Pi.single i (a i) := fun i => by
    funext k
    simp only [Finset.sum_apply]
    by_cases hk : k = i
    · subst hk
      simp only [unitH, Pi.single_eq_same]
      exact (Matrix.matrix_eq_sum_single _).symm
    · simp only [unitH, Pi.single_eq_of_ne hk, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.univ_sum_single]

/-- `φ(a)_{(αs)(βt)} = ι(a_αβ)_st`. -/
def phiHFun (a : MatSumH n) : MatSum (fun i => n i * 2) :=
  fun i => Matrix.of fun x y => quatToMat (a i (idxH i x).1 (idxH i y).1) (idxH i x).2 (idxH i y).2

/-- The entries of `φ(a)`. -/
lemma phiHFun_apply (a : MatSumH n) (i : ι) (x y : Fin (n i * 2)) :
    phiHFun a i x y = quatToMat (a i (idxH i x).1 (idxH i y).1) (idxH i x).2 (idxH i y).2 := rfl

/-- `φ` is multiplicative: block multiplication over `Fin (n · 2) ≃ Fin n × Fin 2`. -/
lemma phiHFun_mul (a b : MatSumH n) : phiHFun (a * b) = phiHFun a * phiHFun b := by
  funext i; ext x y
  simp only [phiHFun_apply, Pi.mul_apply, Matrix.mul_apply, map_sum, Matrix.sum_apply, map_mul]
  rw [← finProdFinEquiv.sum_comp]
  simp only [idxH, Equiv.symm_apply_apply, Fintype.sum_prod_type]

/-- `φ(1) = 1`. -/
lemma phiHFun_one : phiHFun (1 : MatSumH n) = 1 := by
  funext i; ext x y
  rw [phiHFun_apply, Pi.one_apply, Pi.one_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, if_pos rfl, map_one, Matrix.one_apply_eq]
  · rw [if_neg hxy]
    by_cases hαβ : (idxH i x).1 = (idxH i y).1
    · rw [if_pos hαβ, map_one, Matrix.one_apply, if_neg]
      intro hst
      exact hxy (finProdFinEquiv.symm.injective (Prod.ext hαβ hst))
    · rw [if_neg hαβ, map_zero, Matrix.zero_apply]

/-- `φ(0) = 0`. -/
lemma phiHFun_zero : phiHFun (0 : MatSumH n) = 0 := by
  funext i; ext x y
  simp [phiHFun_apply]

/-- `φ` is additive. -/
lemma phiHFun_add (a b : MatSumH n) : phiHFun (a + b) = phiHFun a + phiHFun b := by
  funext i; ext x y
  simp [phiHFun_apply, map_add]

/-- `φ` is real-linear. -/
lemma phiHFun_smul (r : ℝ) (a : MatSumH n) : phiHFun (r • a) = r • phiHFun a := by
  funext i; ext x y
  simp [phiHFun_apply, map_smul]

/-- `φ(a*) = φ(a)*`. -/
lemma phiHFun_star (a : MatSumH n) : phiHFun (star a) = star (phiHFun a) := by
  funext i; ext x y
  simp [phiHFun_apply, Matrix.star_apply, map_star]

/-- **`⊕ Mₙᵢ(ℍ) → ⊕ M₂ₙᵢ(ℂ)`**, a real `*`-homomorphism. -/
def phiH : MatSumH n →⋆ₐ[ℝ] MatSum (fun i => n i * 2) where
  toFun := phiHFun
  map_one' := phiHFun_one
  map_mul' := phiHFun_mul
  map_zero' := phiHFun_zero
  map_add' := phiHFun_add
  commutes' r := by
    show phiHFun (algebraMap ℝ (MatSumH n) r) = algebraMap ℝ (MatSum (fun i => n i * 2)) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, phiHFun_smul, phiHFun_one]
  map_star' := phiHFun_star

/-- `phiH` is `phiHFun`. -/
lemma phiH_apply (a : MatSumH n) : phiH a = phiHFun a := rfl

/-- **`∑_{st} M_st ρ_ℂ(E_st) = ρ_ℂ(M)`.** -/
lemma complexify_entries (ρ : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ s, ∑ t, M s t • complexify ρ (Matrix.single s t 1) = complexify ρ M := by
  have hM : M = ∑ s, ∑ t, M s t • Matrix.single s t (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_rhs => rw [hM]
  rw [show complexify ρ (∑ s, ∑ t, M s t • Matrix.single s t 1) =
    complexifyL ρ (∑ s, ∑ t, M s t • Matrix.single s t 1) from rfl]
  simp only [map_sum, map_smul, complexifyL_apply]

/-- **The block sums**: `∑ₓ U_xx = π(1ᵢ)`. -/
lemma sum_UH (i : ι) : ∑ x, UH T i x x = T.π (Pi.single i 1) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [UH, idxH, Equiv.symm_apply_apply]
  have h1 : ∀ α, ∑ s : Fin 2, complexify (rhoH T i α α) (Matrix.single s s 1) = T.π (unitH i α α 1) := fun α => by
    calc ∑ s : Fin 2, complexify (rhoH T i α α) (Matrix.single s s 1)
        = complexifyL (rhoH T i α α) (∑ s : Fin 2, Matrix.single s s 1) := (map_sum (complexifyL _) _ _).symm
      _ = complexify (rhoH T i α α) (quatToMat 1) := by rw [Matrix.sum_single_one, ← map_one quatToMat]; rfl
      _ = T.π (unitH i α α 1) := complexify_quatToMat _ _
  simp only [h1]
  rw [← map_sum, sum_unitH_block]

/-- **The units of a quaternionic triple.** -/
def unitsH : MatrixUnits (fun i => n i * 2) H where
  U := UH T
  mul_same := UH_mul_same T
  mul_ne := UH_mul_ne T
  star_U := star_UH T
  sum_U := by
    simp only [sum_UH]
    rw [← map_sum, Finset.univ_sum_single (fun i => (1 : Matrix (Fin (n i)) (Fin (n i)) ℍ[ℝ]))]
    exact map_one T.π

/-- **`σ ∘ φ = π`**: `∑_{st} ι(a_αβ)_st U_{(αs)(βt)} = (ρ_αβ)_ℂ(ι(a_αβ)) = π(E_αβ(a_αβ))`. -/
lemma unitsH_hom_phiH (a : MatSumH n) : (unitsH T).hom (phiH a) = T.π a := by
  rw [MatrixUnits.hom_apply]
  conv_rhs => rw [eq_sum_unitH a]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [phiH_apply, phiHFun_apply, unitsH, UH, idxH, Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [complexify_entries, complexify_quatToMat, rhoH_apply]

/-- The units lie in the complex span of `π(A)`. -/
lemma UH_mem_span (i : ι) (x y : Fin (n i * 2)) : UH T i x y ∈ Submodule.span ℂ (Set.range T.π) := by
  rw [UH, complexify]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨unitH i _ _ (quatBasis k), (rhoH_apply T i _ _ _).symm⟩)

/-- `1ᵢ ≠ 0` acts nontrivially. -/
lemma pi_single_one_ne_zero [∀ i, NeZero (n i)] (i : ι) : T.π (Pi.single i 1) ≠ 0 := by
  intro h
  have h0 : (Pi.single i 1 : MatSumH n) = 0 := T.injective_π (h.trans (map_zero T.π).symm)
  have := congrFun h0 i
  simp at this

/-- **The complexification of a triple over `⊕ Mₙᵢ(ℍ)`**: `⊕ M₂ₙᵢ(ℂ)` through the units `U_{(αs)(βt)}`. -/
def quatComplexification [∀ i, NeZero (n i)] : Complexification T (fun i => n i * 2) where
  σ := (unitsH T).hom
  injective_σ := (unitsH T).hom_injective_of_block fun i => by
    rw [show ∑ x, (unitsH T).U i x x = ∑ x, UH T i x x from rfl, sum_UH]
    exact pi_single_one_ne_zero T i
  φ := phiH
  pi_eq a := (unitsH_hom_phiH T a).symm
  mem_span Y := (unitsH T).hom_mem _ (fun i x y => UH_mem_span T i x y) Y

/-- **Uniqueness for quaternionic summands** (Krajewski, Section 3.1, p. 10, with Section 3.2, p. 13): a real finite
spectral triple over `⊕ Mₙᵢ(ℍ)` is unitarily equivalent to the model `⊕ ℂ^{2nᵢ} ⊗ ℂ^{rᵢⱼ} ⊗ ℂ^{2nⱼ}` of the multiplicity
matrix of its complexification, with `π(a)` acting as the complex `2nᵢ × 2nᵢ` matrices of `a` on the fundamental
representations. -/
theorem exists_unitary_quatSummands [∀ i, NeZero (n i)] (R : RealStructure T) :
    ∃ U : H ≃ₗᵢ[ℂ] HK (fun i => n i * 2) (fun i j => multiplicity ((quatComplexification T).realStructure R) i j),
      (∀ a x, U (T.π a x) = piK (phiH a) (U x)) ∧
        ∀ x, U (R.J x) = JK (multiplicity_symm ((quatComplexification T).realStructure R)) (U x) :=
  (quatComplexification T).exists_unitary R

end

end Lightlike.NCG

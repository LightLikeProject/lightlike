import Lightlike.OperatorAlgebras.FockJW
import Lightlike.OperatorAlgebras.CARUnique
/-!
# The Fock inner product on the exterior algebra `Λ(ℂⁿ)`

Dereziński (arXiv:math-ph/0511030, read), Section 5.3, p. 20: the fermionic Fock space `Γₐ(Z)` is the antisymmetric part of
`⊗Z` with the tensor inner product; Section 7.1, p. 29: `a*(w)` and `a(w)` on `Γₐ(Z)`, mutually adjoint, with
`a*(w)Ψ = √(n+1) w ⊗ₐ Ψ`. In `Γₐ(ℂⁿ)` the vectors `a*(e_{i₁}) ⋯ a*(e_{iₚ}) Ω`, `i₁ < ⋯ < iₚ`, are orthonormal, which on the exterior
algebra is the inner product `fockInner` making the ordered products `∏_{xⱼ = 1} eⱼ` orthonormal.

* `fockInner n u w`: the inner product of `Λ(ℂⁿ)` in the configuration coordinates of `fockEquiv`, so `fockEquiv` is unitary
  (`fockInner_fockEquiv`);
* `fockInner_creation`, `fockInner_annihilation`: `a*(eⱼ)` and `a(eⱼ*)` are mutually adjoint;
* `fockInner_unique`: it is the only sesquilinear form on `Λ(ℂⁿ)` with `⟪1, 1⟫ = 1` for which `a*(eⱼ)` and `a(eⱼ*)` are mutually
  adjoint: the Fock inner product is determined by the vacuum and the CAR;
* `fock_irreducible`: Theorem 28 (p. 29) for `Z = ℂⁿ`, the Fock representation is irreducible: a subspace invariant under all
  `a*(eⱼ)` and `a(eⱼ*)` is `0` or `Λ(ℂⁿ)` (from the irreducibility of the Jordan-Wigner representation through `fockEquiv`).
-/

namespace Lightlike.OperatorAlgebras

open ExteriorAlgebra Matrix

/-! ### Words of linear endomorphisms and sesquilinear forms -/

section Sesq

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

lemma IsCARPairs.a0_cWord_tail_end {n : ℕ} {a c : Fin (n + 1) → Module.End ℂ M} (h : IsCARPairs a c) {v : M}
    (hv : a 0 v = 0) (y : Fin n → Fin 2) : a 0 (cWord (Fin.tail c) y v) = 0 := by
  have := mul_cWord (z := a 0) (c := Fin.tail c) (fun k => h.ac_ne (Fin.succ_ne_zero k).symm) y
  rw [← Module.End.mul_apply, this, LinearMap.smul_apply, Module.End.mul_apply, hv, map_zero, smul_zero]

lemma IsCARPairs.a0_c0_apply_end {n : ℕ} {a c : Fin (n + 1) → Module.End ℂ M} (h : IsCARPairs a c) {u : M}
    (hu : a 0 u = 0) : a 0 (c 0 u) = u := by
  have := congrArg (fun T : Module.End ℂ M => T u) (h.ac_self 0)
  simp only [LinearMap.add_apply, Module.End.mul_apply, hu, map_zero, add_zero, Module.End.one_apply] at this
  exact this

/-- **Orthonormality of the creation words for a sesquilinear form** for which the `aⱼ` and `cⱼ` are mutually adjoint. -/
theorem sesq_cWord (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) {n : ℕ} {a c : Fin n → Module.End ℂ M} (h : IsCARPairs a c)
    (hca : ∀ j p q, B (c j p) q = B p (a j q)) (hac : ∀ j p q, B (a j p) q = B p (c j q)) {v w : M}
    (hv : ∀ j, a j v = 0) (hw : ∀ j, a j w = 0) (x y : Fin n → Fin 2) :
    B (cWord c x v) (cWord c y w) = if x = y then B v w else 0 := by
  induction n with
  | zero => simp [cWord, Subsingleton.elim x y]
  | succ n ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    obtain ⟨t, y', rfl⟩ : ∃ t y', y = Fin.cons t y' := ⟨y 0, Fin.tail y, (Fin.cons_self_tail y).symm⟩
    have ih' := ih h.tail (fun j p q => hca j.succ p q) (fun j p q => hac j.succ p q) (fun j => hv j.succ)
      (fun j => hw j.succ) x' y'
    have hu := h.a0_cWord_tail_end (hv 0) x'
    have hu' := h.a0_cWord_tail_end (hw 0) y'
    simp only [cWord_cons, Fin.cons_inj]
    rcases fin_two_eq_zero_or_one s with rfl | rfl <;> rcases fin_two_eq_zero_or_one t with rfl | rfl
    · simp only [ite_fin_zero, ite_true, ite_false, one_mul]
      simpa using ih'
    · rw [ite_fin_zero, ite_fin_one, one_mul, Module.End.mul_apply, ← hac, hu, map_zero, LinearMap.zero_apply]
      simp
    · rw [ite_fin_one, ite_fin_zero, one_mul, Module.End.mul_apply, hca, hu', map_zero]
      simp
    · rw [ite_fin_one, Module.End.mul_apply, Module.End.mul_apply, hca, h.a0_c0_apply_end hu']
      simpa using ih'

end Sesq

/-! ### The Fock inner product -/

/-- The Fock creation and annihilation operators `a*(eⱼ)`, `a(eⱼ*)` on `Λ(ℂⁿ)` satisfy the CAR. -/
lemma isCARPairs_fock (n : ℕ) :
    IsCARPairs (fun j => annihilation (R := ℂ) (coordFun n j)) (fun j => creation (R := ℂ) (stdVecC n j)) where
  ac i j := by
    rw [show annihilation (coordFun n i) * creation (stdVecC n j) + creation (stdVecC n j) * annihilation (coordFun n i) =
      annihilation (coordFun n i) ∘ₗ creation (stdVecC n j) + creation (stdVecC n j) ∘ₗ annihilation (coordFun n i) from rfl,
      annihilation_creation_anticomm]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      simp [coordFun, stdVecC, Module.End.one_eq_id]
    · rw [if_neg hij]
      simp [coordFun, stdVecC, Pi.single_apply, hij]
  aa i j := annihilation_anticomm _ _
  cc i j := creation_anticomm _ _

/-- `shift` carries a creation word in `e₀, …` to the creation word in `e₁, …`. -/
lemma fockShift_cWord {n m : ℕ} (g : Fin m → (Fin n → ℂ)) (x : Fin m → Fin 2) (u : ExteriorAlgebra ℂ (Fin n → ℂ)) :
    fockShift n (cWord (fun k => creation (R := ℂ) (g k)) x u) =
      cWord (fun k => creation (R := ℂ) (shiftLin n (g k))) x (fockShift n u) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [cWord_cons, cWord_cons, Module.End.mul_apply, Module.End.mul_apply]
    have := ih (Fin.tail g) x'
    split_ifs
    · rw [creation_apply, creation_apply, map_mul, fockShift, ExteriorAlgebra.map_apply_ι, ← fockShift]
      exact congrArg (fun t => ι ℂ (shiftLin n (g 0)) * t) this
    · exact this

/-- The configuration vectors are the creation words on the vacuum. -/
lemma fockVec_eq_cWord : ∀ (n : ℕ) (x : Fin n → Fin 2),
    fockVec n x = cWord (fun k => creation (R := ℂ) (stdVecC n k)) x 1
  | 0, _ => rfl
  | n + 1, x => by
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [fockVec_succ, Fin.cons_zero, Fin.tail_cons, cWord_cons, Module.End.mul_apply, fockVec_eq_cWord n x',
      fockShift_cWord, map_one]
    simp only [shiftLin_stdVecC]
    split_ifs
    · rfl
    · rw [one_mul]; rfl

/-- The configuration coordinates `Λ(ℂⁿ) ≃ ℂ^{Fin n → Fin 2}` (the inverse of `fockEquiv`), as a Euclidean space. -/
noncomputable def fockCoord (n : ℕ) : ExteriorAlgebra ℂ (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n → Fin 2) :=
  (fockEquiv n).symm.trans (WithLp.linearEquiv 2 ℂ ((Fin n → Fin 2) → ℂ)).symm

lemma fockCoord_fockEquiv (n : ℕ) (p : (Fin n → Fin 2) → ℂ) : fockCoord n (fockEquiv n p) = WithLp.toLp 2 p := by
  simp [fockCoord, WithLp.coe_symm_linearEquiv]

/-- **The Fock inner product** on `Λ(ℂⁿ)`: `⟪u, w⟫ = ∑ₓ conj(uₓ) wₓ` in the configuration coordinates. -/
noncomputable def fockInner (n : ℕ) : ExteriorAlgebra ℂ (Fin n → ℂ) →ₗ⋆[ℂ] ExteriorAlgebra ℂ (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun u w => inner ℂ (fockCoord n u) (fockCoord n w))
    (fun u u' w => by simp [inner_add_left]) (fun c u w => by simp [inner_smul_left])
    (fun u w w' => by simp [inner_add_right]) (fun c u w => by simp [inner_smul_right])

lemma fockInner_apply (n : ℕ) (u w : ExteriorAlgebra ℂ (Fin n → ℂ)) :
    fockInner n u w = inner ℂ (fockCoord n u) (fockCoord n w) := rfl

/-- `fockEquiv` is unitary: `⟪U p, U q⟫ = ∑ₓ conj(pₓ) qₓ`. -/
lemma fockInner_fockEquiv (n : ℕ) (p q : (Fin n → Fin 2) → ℂ) :
    fockInner n (fockEquiv n p) (fockEquiv n q) = q ⬝ᵥ star p := by
  rw [fockInner_apply, fockCoord_fockEquiv, fockCoord_fockEquiv, EuclideanSpace.inner_eq_star_dotProduct]

/-- **The configuration vectors are orthonormal** for the Fock inner product. -/
lemma fockInner_fockVec (n : ℕ) (x y : Fin n → Fin 2) :
    fockInner n (fockVec n x) (fockVec n y) = if x = y then 1 else 0 := by
  rw [← fockMap_single, ← fockMap_single, ← fockEquiv_apply, ← fockEquiv_apply, fockInner_fockEquiv]
  by_cases h : x = y
  · subst h; simp [dotProduct, Pi.single_apply]
  · rw [if_neg h, dotProduct, Finset.sum_eq_zero]
    intro z _
    by_cases hz : z = y
    · subst hz; simp [Pi.single_apply, Ne.symm h]
    · simp [Pi.single_apply, hz]

lemma inner_toLp_mulVec {κ : Type*} [Fintype κ] (C : Matrix κ κ ℂ) (p q : κ → ℂ) :
    inner ℂ (WithLp.toLp 2 (C *ᵥ p) : EuclideanSpace ℂ κ) (WithLp.toLp 2 q) =
      inner ℂ (WithLp.toLp 2 p : EuclideanSpace ℂ κ) (WithLp.toLp 2 (Cᴴ *ᵥ q)) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_mulVec]
  rw [dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]

lemma fockCoord_creation (n : ℕ) (j : Fin n) (u : ExteriorAlgebra ℂ (Fin n → ℂ)) :
    fockCoord n (ι ℂ (stdVecC n j) * u) = WithLp.toLp 2 (carCreation (jordanWigner n) j *ᵥ (fockEquiv n).symm u) := by
  conv_lhs => rw [← (fockEquiv n).apply_symm_apply u, ← creation_apply, ← fockEquiv_carCreation]
  rw [fockCoord_fockEquiv]

lemma fockCoord_annihilation (n : ℕ) (j : Fin n) (u : ExteriorAlgebra ℂ (Fin n → ℂ)) :
    fockCoord n (CliffordAlgebra.contractLeft (coordFun n j) u) =
      WithLp.toLp 2 (carAnnihilation (jordanWigner n) j *ᵥ (fockEquiv n).symm u) := by
  conv_lhs => rw [← (fockEquiv n).apply_symm_apply u, ← annihilation_apply, ← fockEquiv_carAnnihilation]
  rw [fockCoord_fockEquiv]

lemma fockCoord_eq (n : ℕ) (u : ExteriorAlgebra ℂ (Fin n → ℂ)) : fockCoord n u = WithLp.toLp 2 ((fockEquiv n).symm u) := by
  conv_lhs => rw [← (fockEquiv n).apply_symm_apply u]
  rw [fockCoord_fockEquiv]

/-- **`a*(eⱼ)` is the adjoint of `a(eⱼ*)`** for the Fock inner product. -/
theorem fockInner_creation (n : ℕ) (j : Fin n) (u w : ExteriorAlgebra ℂ (Fin n → ℂ)) :
    fockInner n (ι ℂ (stdVecC n j) * u) w = fockInner n u (CliffordAlgebra.contractLeft (coordFun n j) w) := by
  rw [fockInner_apply, fockInner_apply, fockCoord_creation, fockCoord_annihilation, fockCoord_eq, fockCoord_eq,
    inner_toLp_mulVec, carCreation_eq_conjTranspose (isCARRep_jordanWigner n), conjTranspose_conjTranspose]

/-- **`a(eⱼ*)` is the adjoint of `a*(eⱼ)`** for the Fock inner product. -/
theorem fockInner_annihilation (n : ℕ) (j : Fin n) (u w : ExteriorAlgebra ℂ (Fin n → ℂ)) :
    fockInner n (CliffordAlgebra.contractLeft (coordFun n j) u) w = fockInner n u (ι ℂ (stdVecC n j) * w) := by
  rw [fockInner_apply, fockInner_apply, fockCoord_creation, fockCoord_annihilation, fockCoord_eq, fockCoord_eq,
    inner_toLp_mulVec, carCreation_eq_conjTranspose (isCARRep_jordanWigner n)]

/-- **The Fock inner product is determined by the vacuum and the CAR**: a sesquilinear form on `Λ(ℂⁿ)` with `⟪1, 1⟫ = 1` for
which `a*(eⱼ)` and `a(eⱼ*)` are mutually adjoint is `fockInner`. -/
theorem fockInner_unique (n : ℕ) (B : ExteriorAlgebra ℂ (Fin n → ℂ) →ₗ⋆[ℂ] ExteriorAlgebra ℂ (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (h1 : B 1 1 = 1)
    (hca : ∀ j u w, B (ι ℂ (stdVecC n j) * u) w = B u (CliffordAlgebra.contractLeft (coordFun n j) w))
    (hac : ∀ j u w, B (CliffordAlgebra.contractLeft (coordFun n j) u) w = B u (ι ℂ (stdVecC n j) * w)) :
    B = fockInner n := by
  have hB : ∀ x y, B (fockVec n x) (fockVec n y) = if x = y then 1 else 0 := by
    intro x y
    rw [fockVec_eq_cWord, fockVec_eq_cWord,
      sesq_cWord B (isCARPairs_fock n) (fun j p q => hca j p q) (fun j p q => hac j p q)
        (fun j => annihilation_one _) (fun j => annihilation_one _), h1]
  refine LinearMap.ext₂ fun u w => ?_
  rw [← (fockEquiv n).apply_symm_apply u, ← (fockEquiv n).apply_symm_apply w]
  generalize (fockEquiv n).symm u = p
  generalize (fockEquiv n).symm w = q
  rw [fockInner_fockEquiv, fockEquiv_apply, fockEquiv_apply, fockMap, Fintype.linearCombination_apply,
    Fintype.linearCombination_apply]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hB, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [dotProduct, mul_comm, Complex.star_def]

open ExteriorAlgebra Matrix

lemma fockCoord_symm_toLp (n : ℕ) (p : (Fin n → Fin 2) → ℂ) : (fockCoord n).symm (WithLp.toLp 2 p) = fockEquiv n p := by
  apply (fockCoord n).injective
  rw [LinearEquiv.apply_symm_apply, fockCoord_fockEquiv]

/-- **Dereziński, Theorem 28, for `Z = ℂⁿ`: the Fock representation is irreducible.** A subspace of `Λ(ℂⁿ)` invariant under every
`a*(eⱼ)` and `a(eⱼ*)` (equivalently, under every field operator `φ(y) = a*(w) + a(w)`) is `0` or `Λ(ℂⁿ)`. -/
theorem fock_irreducible (n : ℕ) (W : Submodule ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)))
    (hc : ∀ j, ∀ w ∈ W, ι ℂ (stdVecC n j) * w ∈ W)
    (ha : ∀ j, ∀ w ∈ W, CliffordAlgebra.contractLeft (coordFun n j) w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  set W' : Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin 2)) := W.map (fockCoord n : _ →ₗ[ℂ] _) with hW'
  have hmem : ∀ e, e ∈ W' ↔ (fockCoord n).symm e ∈ W := fun e => Submodule.mem_map_equiv W
  have hC : ∀ j, ∀ e ∈ W', Matrix.toEuclideanCLM (𝕜 := ℂ) (carCreation (jordanWigner n) j) e ∈ W' := by
    intro j e he
    rw [hmem] at he ⊢
    rw [← WithLp.toLp_ofLp (p := 2) e, toEuclideanCLM_toLp, fockCoord_symm_toLp, fockEquiv_carCreation, creation_apply,
      ← fockCoord_symm_toLp, WithLp.toLp_ofLp]
    exact hc j _ he
  have hA : ∀ j, ∀ e ∈ W', Matrix.toEuclideanCLM (𝕜 := ℂ) (carAnnihilation (jordanWigner n) j) e ∈ W' := by
    intro j e he
    rw [hmem] at he ⊢
    rw [← WithLp.toLp_ofLp (p := 2) e, toEuclideanCLM_toLp, fockCoord_symm_toLp, fockEquiv_carAnnihilation, annihilation_apply,
      ← fockCoord_symm_toLp, WithLp.toLp_ofLp]
    exact ha j _ he
  have hinv : ∀ b, ∀ e ∈ W', Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n b) e ∈ W' := by
    intro b e he
    obtain ⟨j, s, rfl⟩ := exists_majorana_index b
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (majorana (jordanWigner n) j s) e ∈ W'
    rcases fin_two_eq_zero_or_one s with rfl | rfl
    · rw [majorana_zero_eq, map_add, ContinuousLinearMap.add_apply]
      exact W'.add_mem (hA j e he) (hC j e he)
    · rw [majorana_one_eq, map_smul, map_sub, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
      exact W'.smul_mem _ (W'.sub_mem (hA j e he) (hC j e he))
  have hclosed : IsClosed (W' : Set (EuclideanSpace ℂ (Fin n → Fin 2))) := W'.closed_of_finiteDimensional
  rcases isIrreducibleCAR_jordanWigner n W' hclosed hinv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have : fockCoord n w ∈ W' := (hmem _).mpr (by rwa [LinearEquiv.symm_apply_apply])
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact (fockCoord n).map_eq_zero_iff.mp this
  · right
    rw [eq_top_iff]
    intro w _
    have := (hmem (fockCoord n w)).mp (h ▸ Submodule.mem_top)
    rwa [LinearEquiv.symm_apply_apply] at this

end Lightlike.OperatorAlgebras

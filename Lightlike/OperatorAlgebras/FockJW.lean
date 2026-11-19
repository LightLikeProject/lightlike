import Lightlike.OperatorAlgebras.FiniteCAR
import Lightlike.OperatorAlgebras.FermionFock
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.Powerset

/-!
# The Jordan-Wigner representation is the Fock representation on the exterior algebra

The configuration space `⊗ⁿ ℂ² = ℂ^{Fin n → Fin 2}` of the Jordan-Wigner representation and the exterior algebra `Λ(ℂⁿ)` (the
fermionic Fock space `Γₐ(ℂⁿ)` of Dereziński, Sections 5.3 and 7.1, read) are identified by the linear isomorphism `fockEquiv n`, which
maps the configuration `x` to the ordered product `∏_{x_j = 1} e_j` (with `1` the vacuum), and which intertwines the Jordan-Wigner
creation operators `aⱼ*` with the creation operators `a*(eⱼ)` (left multiplication by `eⱼ`, `fockEquiv_carCreation`) and the
annihilation operators `aⱼ` with the contractions `a(eⱼ*)` (`fockEquiv_carAnnihilation`). It is built one site at a time:
`|a, x'⟩ ↦ e₀^a · shift(|x'⟩)`, where `shift` is induced by `eⱼ ↦ eⱼ₊₁`; it is onto because the vacuum and the creation operators
generate `Λ(ℂⁿ)` (`ιMulti_span`), and injective because both spaces have dimension `2ⁿ`.
-/

open Matrix
open scoped Kronecker

namespace Lightlike.OperatorAlgebras

open ExteriorAlgebra

/-- The basis vector `eⱼ` of `ℂⁿ`. -/
def stdVecC (n : ℕ) (j : Fin n) : Fin n → ℂ := Pi.single j 1

/-- `v ↦ (0, v)`: the inclusion `ℂⁿ → ℂⁿ⁺¹`, `eⱼ ↦ eⱼ₊₁`. -/
def shiftLin (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons 0 v
  map_add' v w := by
    funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> simp
  map_smul' c v := by
    funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> simp

lemma shiftLin_stdVecC (n : ℕ) (j : Fin n) : shiftLin n (stdVecC n j) = stdVecC (n + 1) j.succ := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [shiftLin, stdVecC, Pi.single_apply, (Fin.succ_ne_zero j).symm]
  · simp [shiftLin, stdVecC, Pi.single_apply, Fin.succ_inj]

/-- `shift : Λ(ℂⁿ) → Λ(ℂⁿ⁺¹)`, the algebra map induced by `shiftLin`. -/
noncomputable def fockShift (n : ℕ) : ExteriorAlgebra ℂ (Fin n → ℂ) →ₐ[ℂ] ExteriorAlgebra ℂ (Fin (n + 1) → ℂ) :=
  ExteriorAlgebra.map (shiftLin n)

/-- The Fock vector of a configuration: `∏_{x_j = 1} e_j`, ordered by site. -/
noncomputable def fockVec : (n : ℕ) → (Fin n → Fin 2) → ExteriorAlgebra ℂ (Fin n → ℂ)
  | 0, _ => 1
  | n + 1, x => (if x 0 = 1 then ι ℂ (stdVecC (n + 1) 0) else 1) * fockShift n (fockVec n (Fin.tail x))

lemma fockVec_succ (n : ℕ) (x : Fin (n + 1) → Fin 2) :
    fockVec (n + 1) x = (if x 0 = 1 then ι ℂ (stdVecC (n + 1) 0) else 1) * fockShift n (fockVec n (Fin.tail x)) := rfl

/-- The linear map `ℂ^{Fin n → Fin 2} → Λ(ℂⁿ)` sending the configuration basis vector `|x⟩` to `fockVec n x`. -/
noncomputable def fockMap (n : ℕ) : ((Fin n → Fin 2) → ℂ) →ₗ[ℂ] ExteriorAlgebra ℂ (Fin n → ℂ) :=
  Fintype.linearCombination ℂ (fockVec n)

lemma fockMap_single (n : ℕ) (x : Fin n → Fin 2) : fockMap n (Pi.single x 1) = fockVec n x := by
  rw [fockMap, Fintype.linearCombination_apply]
  rw [Finset.sum_eq_single x (fun y _ hy => by rw [Pi.single_eq_of_ne hy, zero_smul]) (by simp)]
  simp

/-- The vacuum `|0…0⟩` goes to `1`. -/
lemma fockVec_zero (n : ℕ) : fockVec n (fun _ => 0) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fockVec_succ]
    simp only [Fin.isValue, zero_ne_one, if_false, one_mul]
    rw [show Fin.tail (fun _ : Fin (n + 1) => (0 : Fin 2)) = fun _ => 0 from rfl, ih, map_one]

lemma single_comp_consEquiv (n : ℕ) (x : Fin (n + 1) → Fin 2) :
    (Pi.single x (1 : ℂ) : (Fin (n + 1) → Fin 2) → ℂ) ∘ (Fin.consEquiv (fun _ => Fin 2)) =
      fun p => (Pi.single (x 0) 1 : Fin 2 → ℂ) p.1 * (Pi.single (Fin.tail x) 1 : (Fin n → Fin 2) → ℂ) p.2 := by
  funext ⟨a, y⟩
  show (Pi.single x (1 : ℂ) : (Fin (n + 1) → Fin 2) → ℂ) (Fin.cons a y) =
    (Pi.single (x 0) 1 : Fin 2 → ℂ) a * (Pi.single (Fin.tail x) 1 : (Fin n → Fin 2) → ℂ) y
  simp only [Pi.single_apply]
  by_cases h : Fin.cons a y = x
  · subst h
    simp [Fin.tail_cons]
  · rw [if_neg h]
    by_cases ha : a = x 0
    · by_cases hy : y = Fin.tail x
      · exfalso; apply h; subst ha; subst hy; exact Fin.cons_self_tail x
      · simp [hy]
    · simp [ha]

/-- `fockMap` on a product vector, one site at a time. -/
lemma fockMap_succ_prod (n : ℕ) (f : Fin 2 → ℂ) (g : (Fin n → Fin 2) → ℂ) :
    fockMap (n + 1) ((fun p => f p.1 * g p.2) ∘ (Fin.consEquiv (fun _ => Fin 2)).symm) =
      (f 0 • (1 : ExteriorAlgebra ℂ (Fin (n + 1) → ℂ)) + f 1 • ι ℂ (stdVecC (n + 1) 0)) * fockShift n (fockMap n g) := by
  rw [fockMap, Fintype.linearCombination_apply, fockMap, Fintype.linearCombination_apply,
    ← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, map_sum, map_smul, Finset.mul_sum, add_mul,
    Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, fockVec_succ, Fin.cons_zero, Fin.tail_cons, ite_fin_zero, ite_true, ite_false, one_mul,
      smul_mul_assoc, mul_smul]
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, fockVec_succ, Fin.cons_zero, Fin.tail_cons, ite_fin_one, ite_true, ite_false,
      smul_mul_assoc, mul_smul_comm, mul_smul]
    first | rfl | exact smul_comm _ _ _

/-- **The Jordan-Wigner creation operators are the Fock creation operators**: `U (aⱼ* |x⟩) = eⱼ ∧ U |x⟩`. -/
theorem fockMap_carCreation (n : ℕ) :
    ∀ (j : Fin n) (x : Fin n → Fin 2),
      fockMap n (carCreation (jordanWigner n) j *ᵥ Pi.single x 1) = ι ℂ (stdVecC n j) * fockVec n x := by
  induction n with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    intro j x
    obtain ⟨a, ha⟩ : ∃ a, x 0 = a := ⟨_, rfl⟩
    refine Fin.cases ?_ (fun j' => ?_) j
    · rw [carCreation_jordanWigner_zero, submatrix_mulVec_equiv, Equiv.symm_symm, single_comp_consEquiv,
        kronecker_mulVec_prod, fockMap_succ_prod, one_mulVec, fockMap_single, fockVec_succ, ha]
      fin_cases a
      · simp [mulVec, dotProduct, Fin.sum_univ_two, pauli1, pauli2, Pi.single_apply]
        norm_num
      · simp [mulVec, dotProduct, Fin.sum_univ_two, pauli1, pauli2, Pi.single_apply, ← mul_assoc,
          ExteriorAlgebra.ι_sq_zero]
    · have h' : ι ℂ (stdVecC (n + 1) j'.succ) * ι ℂ (stdVecC (n + 1) 0) =
          -(ι ℂ (stdVecC (n + 1) 0) * ι ℂ (stdVecC (n + 1) j'.succ)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (stdVecC (n + 1) j'.succ) (stdVecC (n + 1) 0))
      rw [carCreation_jordanWigner_succ, submatrix_mulVec_equiv, Equiv.symm_symm, single_comp_consEquiv,
        kronecker_mulVec_prod, fockMap_succ_prod, ih j' (Fin.tail x), fockShift, map_mul, ExteriorAlgebra.map_apply_ι,
        shiftLin_stdVecC, fockVec_succ, ha]
      fin_cases a
      · simp [mulVec, dotProduct, Fin.sum_univ_two, pauli3, Pi.single_apply, fockShift]
      · simp [mulVec, dotProduct, Fin.sum_univ_two, pauli3, Pi.single_apply, fockShift]
        rw [← mul_assoc, ← mul_assoc, h', neg_mul]

open ExteriorAlgebra

/-- The range of `fockMap` is closed under every creation operator `a*(v)`. -/
lemma ι_mul_mem_range_fockMap (n : ℕ) (v : Fin n → ℂ) {r : ExteriorAlgebra ℂ (Fin n → ℂ)}
    (hr : r ∈ LinearMap.range (fockMap n)) : ι ℂ v * r ∈ LinearMap.range (fockMap n) := by
  obtain ⟨w, rfl⟩ := hr
  have hj : ∀ j, ι ℂ (stdVecC n j) * fockMap n w ∈ LinearMap.range (fockMap n) := by
    intro j
    rw [fockMap, Fintype.linearCombination_apply, Finset.mul_sum]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [mul_smul_comm, ← fockMap_carCreation]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  have hv : v = ∑ j, v j • stdVecC n j := by
    funext i
    simp [stdVecC, Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, smul_mul_assoc]
  exact Submodule.smul_mem _ _ (hj j)

/-- **The Fock map is onto**: the vacuum and the creation operators generate `Λ(ℂⁿ)`. -/
theorem fockMap_surjective (n : ℕ) : Function.Surjective (fockMap n) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← ιMulti_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨k, u⟩, rfl⟩
  show ιMulti ℂ k u ∈ _
  induction k with
  | zero =>
    simp only [ιMulti_zero_apply]
    exact ⟨Pi.single (fun _ => 0) 1, by rw [fockMap_single, fockVec_zero]⟩
  | succ k ih =>
    simp only [ιMulti_succ_apply]
    exact ι_mul_mem_range_fockMap n _ (ih _)

lemma finrank_exteriorAlgebra (n : ℕ) : Module.finrank ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) = 2 ^ n := by
  rw [Module.finrank_eq_card_basis (Pi.basisFun ℂ (Fin n)).ExteriorAlgebra, Fintype.card_finset, Fintype.card_fin]

/-- **The Fock isomorphism** `ℂ^{Fin n → Fin 2} ≃ Λ(ℂⁿ)`: bijective, both spaces having dimension `2ⁿ`. -/
noncomputable def fockEquiv (n : ℕ) : ((Fin n → Fin 2) → ℂ) ≃ₗ[ℂ] ExteriorAlgebra ℂ (Fin n → ℂ) :=
  haveI : Module.Finite ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) :=
    Module.Finite.of_basis (Pi.basisFun ℂ (Fin n)).ExteriorAlgebra
  LinearEquiv.ofBijective (fockMap n)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        rw [finrank_exteriorAlgebra, Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin])).mpr (fockMap_surjective n), fockMap_surjective n⟩

lemma fockEquiv_apply (n : ℕ) (w : (Fin n → Fin 2) → ℂ) : fockEquiv n w = fockMap n w := rfl

/-- **The Jordan-Wigner representation is the Fock representation**: `fockEquiv` maps the vacuum to `1` and intertwines the
Jordan-Wigner creation operators with `a*(eⱼ)` (`creation`). -/
theorem fockEquiv_carCreation (n : ℕ) (j : Fin n) (w : (Fin n → Fin 2) → ℂ) :
    fockEquiv n (carCreation (jordanWigner n) j *ᵥ w) = creation (stdVecC n j) (fockEquiv n w) := by
  have hw : w = ∑ x, w x • Pi.single x 1 := by
    funext y; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw, mulVec_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mulVec_smul, map_smul, map_smul, map_smul, fockEquiv_apply, fockEquiv_apply, fockMap_carCreation, fockMap_single,
    creation_apply]

lemma fockEquiv_vacuum (n : ℕ) : fockEquiv n (jwVacuum n) = 1 := by
  rw [fockEquiv_apply, jwVacuum, fockMap_single, fockVec_zero]

open ExteriorAlgebra

/-- Contraction commutes with the algebra map induced by a linear map: `d ⌋ (map f y) = map f ((d ∘ f) ⌋ y)`. -/
lemma contractLeft_map {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (d : Module.Dual ℂ N) (y : ExteriorAlgebra ℂ M) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f y) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d ∘ₗ f) y) := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι]
    conv_lhs => rw [CliffordAlgebra.contractLeft_ι_mul]
    conv_rhs => rw [CliffordAlgebra.contractLeft_ι_mul]
    rw [hx, map_sub, map_smul, map_mul, ExteriorAlgebra.map_apply_ι]
    rfl

/-- The coordinate functional `v ↦ vⱼ`. -/
def coordFun (n : ℕ) (j : Fin n) : Module.Dual ℂ (Fin n → ℂ) := LinearMap.proj j

lemma coordFun_comp_shiftLin_zero (n : ℕ) : coordFun (n + 1) 0 ∘ₗ shiftLin n = 0 := by
  ext v; simp [coordFun, shiftLin]

lemma coordFun_comp_shiftLin_succ (n : ℕ) (j : Fin n) : coordFun (n + 1) j.succ ∘ₗ shiftLin n = coordFun n j := by
  ext v; simp [coordFun, shiftLin]

lemma coordFun_stdVecC_zero (n : ℕ) : coordFun (n + 1) 0 (stdVecC (n + 1) 0) = 1 := by
  simp [coordFun, stdVecC]

lemma coordFun_succ_stdVecC_zero (n : ℕ) (j : Fin n) : coordFun (n + 1) j.succ (stdVecC (n + 1) 0) = 0 := by
  simp [coordFun, stdVecC, Pi.single_apply, Fin.succ_ne_zero]

/-- **The Jordan-Wigner annihilation operators are the contractions**: `U (aⱼ |x⟩) = eⱼ* ⌋ U |x⟩`. -/
theorem fockMap_carAnnihilation (n : ℕ) :
    ∀ (j : Fin n) (x : Fin n → Fin 2),
      fockMap n (carAnnihilation (jordanWigner n) j *ᵥ Pi.single x 1) = annihilation (coordFun n j) (fockVec n x) := by
  induction n with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    intro j x
    have hx := fin_two_eq_zero_or_one (x 0)
    refine Fin.cases ?_ (fun j' => ?_) j
    · have h0 : CliffordAlgebra.contractLeft (coordFun (n + 1) 0) (fockShift n (fockVec n (Fin.tail x))) = 0 := by
        rw [fockShift, contractLeft_map, coordFun_comp_shiftLin_zero, map_zero, LinearMap.zero_apply, map_zero]
      rw [carAnnihilation_jordanWigner_zero, submatrix_mulVec_equiv, Equiv.symm_symm, single_comp_consEquiv,
        kronecker_mulVec_prod, fockMap_succ_prod, one_mulVec, fockMap_single, fockVec_succ, annihilation_apply]
      rcases hx with ha | ha
      · rw [ha, if_neg (by decide), one_mul, h0]
        simp [mulVec, dotProduct, Fin.sum_univ_two, pauli1, pauli2, Pi.single_apply]
      · rw [ha, if_pos rfl, CliffordAlgebra.contractLeft_ι_mul, h0, mul_zero, sub_zero, coordFun_stdVecC_zero, one_smul]
        simp [mulVec, dotProduct, Fin.sum_univ_two, pauli1, pauli2, Pi.single_apply, Complex.I_mul_I]
        try norm_num
    · have hS : CliffordAlgebra.contractLeft (coordFun (n + 1) j'.succ) (fockShift n (fockVec n (Fin.tail x))) =
          fockShift n (CliffordAlgebra.contractLeft (coordFun n j') (fockVec n (Fin.tail x))) := by
        rw [fockShift, contractLeft_map, coordFun_comp_shiftLin_succ]
      rw [carAnnihilation_jordanWigner_succ, submatrix_mulVec_equiv, Equiv.symm_symm, single_comp_consEquiv,
        kronecker_mulVec_prod, fockMap_succ_prod, ih j' (Fin.tail x), fockVec_succ]
      simp only [annihilation_apply]
      rcases hx with ha | ha
      · rw [ha, if_neg (by decide), one_mul, hS]
        simp [mulVec, dotProduct, Fin.sum_univ_two, pauli3, Pi.single_apply]
      · rw [ha, if_pos rfl, CliffordAlgebra.contractLeft_ι_mul, hS, coordFun_succ_stdVecC_zero, zero_smul, zero_sub]
        simp [mulVec, dotProduct, Fin.sum_univ_two, pauli3, Pi.single_apply]

/-- **The Jordan-Wigner representation is the Fock representation, annihilation operators**: `U aⱼ = a(eⱼ*) U`. -/
theorem fockEquiv_carAnnihilation (n : ℕ) (j : Fin n) (w : (Fin n → Fin 2) → ℂ) :
    fockEquiv n (carAnnihilation (jordanWigner n) j *ᵥ w) = annihilation (coordFun n j) (fockEquiv n w) := by
  have hw : w = ∑ x, w x • Pi.single x 1 := by
    funext y; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw, mulVec_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mulVec_smul, map_smul, map_smul, map_smul, fockEquiv_apply, fockEquiv_apply, fockMap_carAnnihilation,
    fockMap_single]

end Lightlike.OperatorAlgebras

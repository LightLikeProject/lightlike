import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
/-!
# The canonical anticommutation relations in finite dimensions: the Jordan-Wigner representation

J. Dereziński, "Introduction to representations of the canonical commutation and anticommutation relations", arXiv:math-ph/0511030
(read): Section 4.1, p. 14: a representation of the CAR over `ℝᵐ` is a family `(φ₁, …, φₘ)` of bounded self-adjoint operators with
`[φᵢ, φⱼ]₊ = 2δᵢⱼ` (eq. (26)); p. 15: if `(φ, I)` is a representation over `Y₁ ⊕ ℝ` and `ψ` one over `Y₂`, then
`(y₁, y₂) ↦ φ(y₁) ⊗ 1 + I ⊗ ψ(y₂)` is a representation over `Y₁ ⊕ Y₂`; Section 4.2, p. 16: the Pauli matrices `(σ₁, σ₂, σ₃)` are a
representation over `ℝ³` (eq. (30)), and the Jordan-Wigner operators
`σ₁⁽¹⁾, σ₂⁽¹⁾, I₁σ₁⁽²⁾, I₁σ₂⁽²⁾, …, Iₙ₋₁σ₁⁽ⁿ⁾, Iₙ₋₁σ₂⁽ⁿ⁾` (`Iⱼ = σ₃⁽¹⁾ ⋯ σ₃⁽ʲ⁾`) are a representation of the CAR over `ℝ²ⁿ` on `⊗ⁿ ℂ²`.

Here `IsCARRep φ` is eq. (26) for matrices, `isCARRep_pauli` is (30), `IsCARRep.tensor` the tensor construction of p. 15, and
`jordanWigner n` the Jordan-Wigner family on `⊗ⁿ ℂ² = ℂ^{Fin n → Fin 2}`, built by the tensor construction one site at a time
(the first site carries `σ₁, σ₂`, the others `σ₃ ⊗ ·`), with `isCARRep_jordanWigner`. In creation-annihilation form (Section 7.1, p. 30,
`a(w) = (φ(w) + iφ(iw))/2`): `carAnnihilation φ j = (φ_{2j} + iφ_{2j+1})/2` and `carCreation φ j = (carAnnihilation φ j)*` satisfy
`aᵢ aⱼ* + aⱼ* aᵢ = δᵢⱼ` and `aᵢ aⱼ + aⱼ aᵢ = 0` for every CAR family over `ℝ²ⁿ` (`carAnnihilation_carCreation`,
`carAnnihilation_anticomm`), and the empty configuration is the Fock vacuum: every `aⱼ` kills it (`jwVacuum`,
`carAnnihilation_jordanWigner_vacuum`).
-/

open Matrix
open scoped Kronecker

namespace Lightlike.OperatorAlgebras

/-- **A representation of the CAR over `ℝᵐ`** (Dereziński, eq. (26)): self-adjoint matrices with `φₐ φ_b + φ_b φₐ = 2 δₐ_b`. -/
structure IsCARRep {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (φ : Fin m → Matrix ι ι ℂ) : Prop where
  selfAdjoint : ∀ a, (φ a)ᴴ = φ a
  anticomm : ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : Matrix ι ι ℂ) else 0

/-- The Pauli matrices. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `(σ₁, σ₂, σ₃)`. -/
def pauliFamily : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![pauli1, pauli2, pauli3]

/-- **The Pauli matrices are a representation of the CAR over `ℝ³`** (Dereziński, eq. (30), p. 16). -/
theorem isCARRep_pauli : IsCARRep pauliFamily := by
  constructor
  · intro a
    fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliFamily, pauli1, pauli2, pauli3, conjTranspose_apply, Complex.conj_I]
  · intro a b
    fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliFamily, pauli1, pauli2, pauli3, mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> try norm_num

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma castAdd_ne_natAdd' {m k : ℕ} (i : Fin m) (j : Fin k) : Fin.castAdd k i ≠ Fin.natAdd m j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
  omega

lemma IsCARRep.sq_eq_one {m : ℕ} {φ : Fin m → Matrix ι ι ℂ} (hφ : IsCARRep φ) (a : Fin m) : φ a * φ a = 1 := by
  have h := hφ.anticomm a a
  rw [if_pos rfl, ← two_smul ℂ (φ a * φ a)] at h
  exact smul_right_injective _ two_ne_zero h

/-- **The tensor construction** (Dereziński, p. 15): if `(φ, I)` is a representation over `ℝᵐ⁺¹` and `ψ` one over `ℝᵏ`, then
`(φ ⊗ 1, I ⊗ ψ)` is a representation over `ℝᵐ⁺ᵏ`. -/
theorem IsCARRep.tensor {m k : ℕ} {φ : Fin m → Matrix ι ι ℂ} {I : Matrix ι ι ℂ} (hφ : IsCARRep (Fin.snoc (α := fun _ => _) φ I))
    {ψ : Fin k → Matrix κ κ ℂ} (hψ : IsCARRep ψ) :
    IsCARRep (Fin.append (fun a => φ a ⊗ₖ (1 : Matrix κ κ ℂ)) (fun b => I ⊗ₖ ψ b)) := by
  have hφa : ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : Matrix ι ι ℂ) else 0 := by
    intro a b
    have := hφ.anticomm (Fin.castSucc a) (Fin.castSucc b)
    simpa [Fin.snoc_castSucc, Fin.castSucc_inj] using this
  have hφI : ∀ a, φ a * I + I * φ a = 0 := by
    intro a
    have := hφ.anticomm (Fin.castSucc a) (Fin.last m)
    simpa [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_ne_last] using this
  have hII : I * I = 1 := by
    have := hφ.sq_eq_one (Fin.last m)
    simpa [Fin.snoc_last] using this
  have hφs : ∀ a, (φ a)ᴴ = φ a := by
    intro a
    have := hφ.selfAdjoint (Fin.castSucc a)
    simpa [Fin.snoc_castSucc] using this
  have hIs : Iᴴ = I := by
    have := hφ.selfAdjoint (Fin.last m)
    simpa [Fin.snoc_last] using this
  constructor
  · intro a
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · simp [Fin.append_left, conjTranspose_kronecker, hφs]
    · simp [Fin.append_right, conjTranspose_kronecker, hIs, hψ.selfAdjoint]
  · intro a b
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a <;> refine Fin.addCases (fun i' => ?_) (fun j' => ?_) b
    · simp only [Fin.append_left]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, ← add_kronecker, Matrix.one_mul, hφa]
      by_cases h : i = i'
      · subst h; simp [smul_kronecker, one_kronecker_one]
      · simp [h, (Fin.castAdd_injective _ _).eq_iff]
    · simp only [Fin.append_left, Fin.append_right]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, ← add_kronecker, hφI]
      simp [castAdd_ne_natAdd']
    · simp only [Fin.append_left, Fin.append_right]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, ← add_kronecker, add_comm, hφI]
      simp [Ne.symm (castAdd_ne_natAdd' _ _)]
    · simp only [Fin.append_right]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, hII, ← kronecker_add, hψ.anticomm]
      by_cases h : j = j'
      · subst h; simp [kronecker_smul, one_kronecker_one]
      · simp [h, (Fin.natAdd_injective _ _).eq_iff]

/-- The CAR is preserved by relabelling the basis. -/
theorem IsCARRep.submatrix {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {m : ℕ} {φ : Fin m → Matrix ι ι ℂ} (hφ : IsCARRep φ)
    (e : ι' ≃ ι) : IsCARRep fun a => (φ a).submatrix e e := by
  constructor
  · intro a
    rw [conjTranspose_submatrix, hφ.selfAdjoint]
  · intro a b
    rw [submatrix_mul_equiv, submatrix_mul_equiv,
      show (φ a * φ b).submatrix e e + (φ b * φ a).submatrix e e = (φ a * φ b + φ b * φ a).submatrix e e from rfl,
      hφ.anticomm]
    split_ifs
    · rw [show ((2 : ℂ) • (1 : Matrix ι ι ℂ)).submatrix e e = (2 : ℂ) • (1 : Matrix ι ι ℂ).submatrix e e from rfl,
        submatrix_one_equiv]
    · rfl

/-- The CAR is preserved by relabelling the family. -/
theorem IsCARRep.comp_equiv {m m' : ℕ} {φ : Fin m → Matrix ι ι ℂ} (hφ : IsCARRep φ) (e : Fin m' ≃ Fin m) :
    IsCARRep (φ ∘ e) := by
  constructor
  · intro a; exact hφ.selfAdjoint _
  · intro a b
    simp only [Function.comp_apply]
    rw [hφ.anticomm]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg (fun h' => h (e.injective h')), if_neg h]

/-- `(σ₁, σ₂)` with `I = σ₃`: the Pauli representation as `Fin.snoc`. -/
lemma pauliFamily_eq_snoc : pauliFamily = Fin.snoc (α := fun _ => _) ![pauli1, pauli2] pauli3 := by
  funext a
  fin_cases a <;> rfl

/-- **The Jordan-Wigner family** on `⊗ⁿ ℂ² = ℂ^{Fin n → Fin 2}` (Dereziński, Section 4.2, p. 16): `σ₁, σ₂` on the first site,
followed by `σ₃ ⊗` the Jordan-Wigner family of the remaining sites. -/
noncomputable def jordanWigner : (n : ℕ) → Fin (2 * n) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | 0 => Fin.elim0
  | n + 1 => fun a =>
    (Fin.append (fun i => ![pauli1, pauli2] i ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
      (fun b => pauli3 ⊗ₖ jordanWigner n b) (Fin.cast (by ring) a)).submatrix
      (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm

/-- **The Jordan-Wigner operators are a representation of the CAR over `ℝ²ⁿ`** (Dereziński, Section 4.2, p. 16). -/
theorem isCARRep_jordanWigner (n : ℕ) : IsCARRep (jordanWigner n) := by
  induction n with
  | zero => exact ⟨fun a => a.elim0, fun a => a.elim0⟩
  | succ n ih =>
    have h1 : IsCARRep (Fin.snoc (α := fun _ => _) ![pauli1, pauli2] pauli3) := pauliFamily_eq_snoc ▸ isCARRep_pauli
    have h2 := (h1.tensor ih).comp_equiv (finCongr (show 2 * (n + 1) = 2 + 2 * n by ring))
    exact h2.submatrix (Fin.consEquiv (fun _ => Fin 2)).symm

/-- The Majorana pair `(φ_{2j}, φ_{2j+1})` of a CAR family over `ℝ²ⁿ`. -/
def majorana {A : Type*} {n : ℕ} (φ : Fin (2 * n) → A) (j : Fin n) (s : Fin 2) : A :=
  φ ⟨2 * j.1 + s.1, by omega⟩

lemma majorana_index_inj {n : ℕ} {j j' : Fin n} {s s' : Fin 2}
    (h : (⟨2 * j.1 + s.1, by omega⟩ : Fin (2 * n)) = ⟨2 * j'.1 + s'.1, by omega⟩) : j = j' ∧ s = s' := by
  have h1 := congrArg Fin.val h
  simp only at h1
  constructor <;> ext <;> omega

/-- **The annihilation operators** `aⱼ = (φ_{2j} + i φ_{2j+1}) / 2` (Dereziński, Section 7.1, p. 30: `a(w) = (φ(w) + iφ(iw))/2`). -/
noncomputable def carAnnihilation {A : Type*} [AddCommGroup A] [Module ℂ A] {n : ℕ} (φ : Fin (2 * n) → A) (j : Fin n) : A :=
  (1 / 2 : ℂ) • (majorana φ j 0 + Complex.I • majorana φ j 1)

/-- The creation operators `aⱼ* = (φ_{2j} - i φ_{2j+1}) / 2`. -/
noncomputable def carCreation {A : Type*} [AddCommGroup A] [Module ℂ A] {n : ℕ} (φ : Fin (2 * n) → A) (j : Fin n) : A :=
  (1 / 2 : ℂ) • (majorana φ j 0 - Complex.I • majorana φ j 1)

lemma fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

lemma ite_fin_one {α : Sort*} (a b : α) : (if (1 : Fin 2) = 1 then a else b) = a := if_pos rfl

lemma ite_fin_zero {α : Sort*} (a b : α) : (if (0 : Fin 2) = 1 then a else b) = b := if_neg (by decide)

/-- Every index of `ℝ²ⁿ` is a Majorana index `2j + s`. -/
lemma exists_majorana_index {n : ℕ} (b : Fin (2 * n)) : ∃ (j : Fin n) (s : Fin 2), b = ⟨2 * j.1 + s.1, by omega⟩ :=
  ⟨⟨b / 2, by omega⟩, ⟨b % 2, by omega⟩, Fin.ext (by simp only; omega)⟩

section Ring

variable {A : Type*} [Ring A] [Module ℂ A]

lemma majorana_anticomm {n : ℕ} {φ : Fin (2 * n) → A}
    (hφ : ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : A) else 0) (j j' : Fin n) (s s' : Fin 2) :
    majorana φ j s * majorana φ j' s' + majorana φ j' s' * majorana φ j s =
      if j = j' ∧ s = s' then (2 : ℂ) • (1 : A) else 0 := by
  rw [majorana, majorana, hφ]
  by_cases h : j = j' ∧ s = s'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg (fun h' => h (majorana_index_inj h')), if_neg h]

lemma majorana_zero_eq {n : ℕ} (φ : Fin (2 * n) → A) (j : Fin n) :
    majorana φ j 0 = carAnnihilation φ j + carCreation φ j := by
  simp only [carAnnihilation, carCreation]
  module

lemma majorana_one_eq {n : ℕ} (φ : Fin (2 * n) → A) (j : Fin n) :
    majorana φ j 1 = -Complex.I • (carAnnihilation φ j - carCreation φ j) := by
  have : carAnnihilation φ j - carCreation φ j = Complex.I • majorana φ j 1 := by
    simp only [carAnnihilation, carCreation]
    module
  rw [this, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

end Ring

/-- `aⱼ* = (aⱼ)*`. -/
theorem carCreation_eq_conjTranspose {n : ℕ} {φ : Fin (2 * n) → Matrix ι ι ℂ} (hφ : IsCARRep φ) (j : Fin n) :
    carCreation φ j = (carAnnihilation φ j)ᴴ := by
  simp only [carCreation, carAnnihilation, conjTranspose_smul, conjTranspose_add, majorana, hφ.selfAdjoint]
  simp [sub_eq_add_neg, Complex.conj_I]

/-- **The CAR in creation-annihilation form**: `aᵢ aⱼ* + aⱼ* aᵢ = δᵢⱼ`. -/
theorem carAnnihilation_carCreation {A : Type*} [Ring A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {n : ℕ} {φ : Fin (2 * n) → A}
    (hφ : ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : A) else 0) (i j : Fin n) :
    carAnnihilation φ i * carCreation φ j + carCreation φ j * carAnnihilation φ i =
      if i = j then (1 : A) else 0 := by
  have h00 := majorana_anticomm hφ i j 0 0
  have h11 := majorana_anticomm hφ i j 1 1
  have h01 := majorana_anticomm hφ i j 0 1
  have h10 := majorana_anticomm hφ i j 1 0
  simp only [and_true, and_false, if_false, (by decide : (0 : Fin 2) ≠ 1), (by decide : (1 : Fin 2) ≠ 0)] at h00 h11 h01 h10
  simp only [carAnnihilation, carCreation, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_smul]
  by_cases h : i = j
  · subst h
    simp only [if_true] at h00 h11 ⊢
    linear_combination (norm := (match_scalars <;> (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)))) (1 / 4 : ℂ) • h00 + (1 / 4 : ℂ) • h11 - (Complex.I / 4) • h01 + (Complex.I / 4) • h10
  · simp only [h, if_false] at h00 h11 ⊢
    linear_combination (norm := (match_scalars <;> (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)))) (1 / 4 : ℂ) • h00 + (1 / 4 : ℂ) • h11 - (Complex.I / 4) • h01 + (Complex.I / 4) • h10

/-- `aᵢ aⱼ + aⱼ aᵢ = 0`. -/
theorem carAnnihilation_anticomm {A : Type*} [Ring A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {n : ℕ} {φ : Fin (2 * n) → A}
    (hφ : ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : A) else 0) (i j : Fin n) :
    carAnnihilation φ i * carAnnihilation φ j + carAnnihilation φ j * carAnnihilation φ i = 0 := by
  have h00 := majorana_anticomm hφ i j 0 0
  have h11 := majorana_anticomm hφ i j 1 1
  have h01 := majorana_anticomm hφ i j 0 1
  have h10 := majorana_anticomm hφ i j 1 0
  simp only [and_true, and_false, if_false, (by decide : (0 : Fin 2) ≠ 1), (by decide : (1 : Fin 2) ≠ 0)] at h00 h11 h01 h10
  simp only [carAnnihilation, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  by_cases h : i = j
  · subst h
    simp only [if_true] at h00 h11
    linear_combination (norm := (match_scalars <;> (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)))) (1 / 4 : ℂ) • h00 - (1 / 4 : ℂ) • h11 + (Complex.I / 4) • h01 + (Complex.I / 4) • h10
  · simp only [h, if_false] at h00 h11
    linear_combination (norm := (match_scalars <;> (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)))) (1 / 4 : ℂ) • h00 - (1 / 4 : ℂ) • h11 + (Complex.I / 4) • h01 + (Complex.I / 4) • h10

/-- `aᵢ* aⱼ* + aⱼ* aᵢ* = 0`. -/
theorem carCreation_anticomm {A : Type*} [Ring A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {n : ℕ} {φ : Fin (2 * n) → A}
    (hφ : ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : A) else 0) (i j : Fin n) :
    carCreation φ i * carCreation φ j + carCreation φ j * carCreation φ i = 0 := by
  have h00 := majorana_anticomm hφ i j 0 0
  have h11 := majorana_anticomm hφ i j 1 1
  have h01 := majorana_anticomm hφ i j 0 1
  have h10 := majorana_anticomm hφ i j 1 0
  simp only [and_true, and_false, if_false, (by decide : (0 : Fin 2) ≠ 1), (by decide : (1 : Fin 2) ≠ 0)] at h00 h11 h01 h10
  simp only [carCreation, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  by_cases h : i = j
  · subst h
    simp only [if_true] at h00 h11
    linear_combination (norm := (match_scalars <;> (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)))) (1 / 4 : ℂ) • h00 - (1 / 4 : ℂ) • h11 - (Complex.I / 4) • h01 - (Complex.I / 4) • h10
  · simp only [h, if_false] at h00 h11
    linear_combination (norm := (match_scalars <;> (ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)))) (1 / 4 : ℂ) • h00 - (1 / 4 : ℂ) • h11 - (Complex.I / 4) • h01 - (Complex.I / 4) • h10

/-- **The Fock vacuum** of the Jordan-Wigner representation: the basis vector of the empty configuration. -/
noncomputable def jwVacuum (n : ℕ) : (Fin n → Fin 2) → ℂ := Pi.single (fun _ => 0) 1

lemma kronecker_mulVec_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (v : ι → ℂ)
    (w : κ → ℂ) : (A ⊗ₖ B) *ᵥ (fun p => v p.1 * w p.2) = fun p => (A *ᵥ v) p.1 * (B *ᵥ w) p.2 := by
  funext p
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma jwVacuum_comp_consEquiv (n : ℕ) :
    jwVacuum (n + 1) ∘ (Fin.consEquiv (fun _ => Fin 2)) = fun p => (Pi.single 0 1 : Fin 2 → ℂ) p.1 * jwVacuum n p.2 := by
  funext ⟨a, x⟩
  simp only [Function.comp_apply, jwVacuum]
  by_cases ha : a = 0 <;> by_cases hx : x = fun _ => 0
  · subst ha; subst hx
    simp only [Pi.single_eq_same, mul_one]
    rw [show (Fin.consEquiv (fun _ => Fin 2) (0, fun _ => 0) : Fin (n + 1) → Fin 2) = fun _ => 0 by
      funext i; refine Fin.cases rfl (fun _ => rfl) i]
    simp
  · rw [Pi.single_eq_of_ne hx, mul_zero, Pi.single_eq_of_ne]
    intro h
    apply hx
    funext i
    have := congrFun h i.succ
    simpa [Fin.consEquiv] using this
  · rw [Pi.single_eq_of_ne ha, zero_mul, Pi.single_eq_of_ne]
    intro h
    apply ha
    have := congrFun h 0
    simpa [Fin.consEquiv] using this
  · rw [Pi.single_eq_of_ne ha, zero_mul, Pi.single_eq_of_ne]
    intro h
    apply ha
    have := congrFun h 0
    simpa [Fin.consEquiv] using this

/-- `σ⁻ = (σ₁ + iσ₂)/2` kills `|0⟩`. -/
lemma sigmaMinus_mulVec_zero :
    ((1 / 2 : ℂ) • (pauli1 + Complex.I • pauli2)) *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) = 0 := by
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, pauli1, pauli2, Complex.I_mul_I]

lemma jordanWigner_succ_apply (n : ℕ) (a : Fin (2 * (n + 1))) :
    jordanWigner (n + 1) a =
      (Fin.append (fun i => ![pauli1, pauli2] i ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
        (fun b => pauli3 ⊗ₖ jordanWigner n b) (Fin.cast (show 2 * (n + 1) = 2 + 2 * n by ring) a)).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := rfl

lemma majorana_jordanWigner_zero (n : ℕ) (s : Fin 2) :
    majorana (jordanWigner (n + 1)) 0 s =
      (![pauli1, pauli2] s ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
  rw [majorana, jordanWigner_succ_apply,
    show (Fin.cast (show 2 * (n + 1) = 2 + 2 * n by ring) ⟨2 * (0 : Fin (n + 1)).1 + s.1, by omega⟩ : Fin (2 + 2 * n)) =
      Fin.castAdd (2 * n) s from Fin.ext (by simp), Fin.append_left]

lemma majorana_jordanWigner_succ (n : ℕ) (j : Fin n) (s : Fin 2) :
    majorana (jordanWigner (n + 1)) j.succ s =
      (pauli3 ⊗ₖ majorana (jordanWigner n) j s).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
  rw [majorana, jordanWigner_succ_apply,
    show (Fin.cast (show 2 * (n + 1) = 2 + 2 * n by ring) ⟨2 * j.succ.1 + s.1, by omega⟩ : Fin (2 + 2 * n)) =
      Fin.natAdd 2 ⟨2 * j.1 + s.1, by omega⟩ from Fin.ext (by simp; omega), Fin.append_right]
  rfl

lemma carCreation_jordanWigner_zero (n : ℕ) :
    carCreation (jordanWigner (n + 1)) 0 =
      (((1 / 2 : ℂ) • (pauli1 - Complex.I • pauli2)) ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
  ext i k
  simp only [carCreation, majorana_jordanWigner_zero, Matrix.smul_apply, Matrix.sub_apply, submatrix_apply,
    kroneckerMap_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

lemma carCreation_jordanWigner_succ (n : ℕ) (j : Fin n) :
    carCreation (jordanWigner (n + 1)) j.succ =
      (pauli3 ⊗ₖ carCreation (jordanWigner n) j).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
  ext i k
  simp only [carCreation, majorana_jordanWigner_succ, Matrix.smul_apply, Matrix.sub_apply, submatrix_apply,
    kroneckerMap_apply, smul_eq_mul]
  ring

lemma carAnnihilation_jordanWigner_zero (n : ℕ) :
    carAnnihilation (jordanWigner (n + 1)) 0 =
      (((1 / 2 : ℂ) • (pauli1 + Complex.I • pauli2)) ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
  ext i k
  simp only [carAnnihilation, majorana_jordanWigner_zero, Matrix.smul_apply, Matrix.add_apply, submatrix_apply,
    kroneckerMap_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

lemma carAnnihilation_jordanWigner_succ (n : ℕ) (j : Fin n) :
    carAnnihilation (jordanWigner (n + 1)) j.succ =
      (pauli3 ⊗ₖ carAnnihilation (jordanWigner n) j).submatrix
        (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
  ext i k
  simp only [carAnnihilation, majorana_jordanWigner_succ, Matrix.smul_apply, Matrix.add_apply, submatrix_apply,
    kroneckerMap_apply, smul_eq_mul]
  ring

/-- **The Jordan-Wigner annihilation operators kill the Fock vacuum** (Dereziński, Theorem 29, p. 30, for `c = 0`: `a(z) Ω = 0`). -/
theorem carAnnihilation_jordanWigner_vacuum (n : ℕ) :
    ∀ j : Fin n, carAnnihilation (jordanWigner n) j *ᵥ jwVacuum n = 0 := by
  induction n with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    intro j
    refine Fin.cases ?_ (fun j' => ?_) j
    · have hA : carAnnihilation (jordanWigner (n + 1)) 0 =
          (((1 / 2 : ℂ) • (pauli1 + Complex.I • pauli2)) ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)).submatrix
            (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
        ext i k
        simp only [carAnnihilation, majorana_jordanWigner_zero, Matrix.smul_apply, Matrix.add_apply, submatrix_apply,
          kroneckerMap_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        ring
      rw [hA, submatrix_mulVec_equiv, Equiv.symm_symm, jwVacuum_comp_consEquiv, kronecker_mulVec_prod,
        sigmaMinus_mulVec_zero]
      funext x
      simp
    · have hA : carAnnihilation (jordanWigner (n + 1)) j'.succ =
          (pauli3 ⊗ₖ carAnnihilation (jordanWigner n) j').submatrix
            (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := by
        ext i k
        simp only [carAnnihilation, majorana_jordanWigner_succ, Matrix.smul_apply, Matrix.add_apply, submatrix_apply,
          kroneckerMap_apply, smul_eq_mul]
        ring
      rw [hA, submatrix_mulVec_equiv, Equiv.symm_symm, jwVacuum_comp_consEquiv, kronecker_mulVec_prod, ih j']
      funext x
      simp

end Lightlike.OperatorAlgebras

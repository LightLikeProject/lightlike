import Lightlike.Spin4.Ladder
import Lightlike.Spin4.ClebschGordan
import PhyslibAlpha.QuantumMechanics.AngularMomentum.ClebschGordanFormula
import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!
# Physlib's Clebsch–Gordan coefficients intertwine the group representations

Physlib defines the Clebsch–Gordan coefficients `⟨j₁ m₁ j₂ m₂ | J M⟩` for the Lie algebra `sl₂`
(`PhyslibAlpha.Sl2.cgCoefficient`, real numbers), proves their orthogonality relations and relates
them to its 3j symbols `threeJ`. This file shows that the same numbers couple the *group*
representations `SU2.spinMat` of this library.

For doubled spins `n, m` and `k ≤ min(n, m)`, put `N = n + m - 2k` (twice the coupled spin
`J = (n+m)/2 - k`). `cgMatrix n m k` is the `(n+1)(m+1) × (N+1)` matrix of the coefficients
`⟨n/2, n/2 - a; m/2, m/2 - b | J, J - l⟩`. Then:

* `cgMatrix_equivariant`: `(D^{n/2}(g) ⊗ D^{m/2}(g)) C = C D^{N/2}(g)` for every `g ∈ SU(2)`;
* `cgMatrix_isometry`, `cgMatrix_orth`, `cgMatrix_complete`: the columns of all `cgMatrix n m k`,
  `k = 0, …, min(n,m)`, form an orthonormal basis of `ℂ^{(n+1)(m+1)}`;
* `cgMatrix_eq_threeJ`: the entries are `(-1)^{n+k+l} √(N+1) (n m N; n-2a, m-2b, -(N-2l))` in
  Physlib's 3j symbols `threeJ` (doubled units);
* `cgMatrix_top_sign`: the coefficients of the highest state `l = 0` alternate in sign,
  `(-1)^a` times a positive number (Condon–Shortley convention).

## Proof

The basis `e_a` of `ℂ^{n+1}` carries the same matrix elements of `E, F, H` as Physlib's normalised
basis `u_a` (`Lightlike/Spin4/Ladder.lean`). Physlib's contravariant form makes `E` and `F` adjoint
(`tensorForm_tensorE`), and the coupled vectors obey the ladder relations of `|J, M⟩`. Taking the
form with `u_a ⊗ u_b` turns each ladder relation into a relation between Clebsch–Gordan
coefficients (`cg_F_rel`, `cg_E_rel`, `cg_H_rel`), which is the statement that `cgMatrix`
intertwines the differentials (`cgMatrix_F`, `cgMatrix_E`, `cgMatrix_H`, `cgMatrix_lie`). Every
`g ∈ SU(2)` is an exponential, so the group relation follows (`Spin4.intertwine_exp'`).

## References

* D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*,
  World Scientific (1988), Ch. 8 (Clebsch–Gordan coefficients, their relation to 3j symbols and
  the Condon–Shortley phase convention).
-/

open Matrix Finset PhyslibAlpha.Sl2
open scoped Kronecker TensorProduct

namespace Lightlike.Spin4

open SU2 PhyslibAlpha.Sl2.StandardSl2Module

variable {n m k : ℕ}

/-! ## A. Physlib's ladder operators on the normalised basis, for all labels -/

lemma normVec_of_lt {a : ℕ} (ha : n < a) : normVec n a = 0 := by
  rw [normVec, vNat_of_lt ha, smul_zero]

lemma ρE_normVec' (a : ℕ) :
    (ρE : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n a) =
      if 0 < a ∧ a ≤ n then lad n (a - 1) • normVec n (a - 1) else 0 := by
  by_cases h : 0 < a ∧ a ≤ n
  · rw [ite_eq_left h]
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [ρE_normVec_succ (by omega)]
    rfl
  · rw [ite_eq_right h]
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, normVec, map_smul, ρE_vNat_zero, smul_zero]
    · rw [normVec_of_lt (by omega), map_zero]

lemma ρF_normVec' (a : ℕ) :
    (ρF : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n a) =
      if a < n then lad n a • normVec n (a + 1) else 0 := by
  by_cases h : a < n
  · rw [ite_eq_left h, ρF_normVec h]
    rfl
  · rw [ite_eq_right h]
    rcases eq_or_lt_of_le (not_lt.mp h) with h0 | h0
    · rw [← h0, normVec, map_smul, ρF_vNat, vNat_of_lt (by omega), smul_zero]
    · rw [normVec_of_lt h0, map_zero]

lemma ρH_normVec' (a : ℕ) :
    (ρH : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n a) =
      ((n : ℝ) - 2 * a) • normVec n a := ρH_normVec a

/-! ## B. The coupled vectors at the ends of their strings -/

lemma coupledVec_eq_smul (k l : ℕ) :
    ∃ c : ℝ, coupledVec n m k l = c • stringVec n m k l := ⟨_, rfl⟩

lemma tensorF_coupledVec_last (hk : k ≤ n) (hk' : k ≤ m) (hnm : 0 < n + m) :
    tensorF n m (coupledVec n m k (n + m - 2 * k)) = 0 := by
  obtain ⟨c, hc⟩ := coupledVec_eq_smul (n := n) (m := m) k (n + m - 2 * k)
  rw [hc, map_smul, tensorF_stringVec, stringVec_eq_zero hnm hk hk' (by omega), smul_zero]

lemma tensorE_coupledVec_zero (hk : k ≤ n) (hk' : k ≤ m) :
    tensorE n m (coupledVec n m k 0) = 0 := by
  obtain ⟨c, hc⟩ := coupledVec_eq_smul (n := n) (m := m) k 0
  rw [hc, map_smul, tensorE_stringVec_zero hk hk', smul_zero]

/-! ## C. The ladder relations of the Clebsch–Gordan coefficients -/

/-- The diagonal raising operator on a product of basis vectors, paired with any `x`. -/
lemma form_tensorE_tmul (x : StandardSl2Module ℝ n ⊗[ℝ] StandardSl2Module ℝ m) (a b : ℕ) :
    tensorForm n m (tensorE n m (normVec n a ⊗ₜ normVec m b)) x =
      (if 0 < a ∧ a ≤ n then lad n (a - 1) * tensorForm n m (normVec n (a - 1) ⊗ₜ normVec m b) x
        else 0) +
      (if 0 < b ∧ b ≤ m then lad m (b - 1) * tensorForm n m (normVec n a ⊗ₜ normVec m (b - 1)) x
        else 0) := by
  rw [tensorE, diagEnd_tmul, map_add, LinearMap.add_apply, ρE_normVec', ρE_normVec']
  congr 1
  · split_ifs
    · rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, smul_eq_mul]
    · simp
  · split_ifs
    · rw [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    · simp

/-- The diagonal lowering operator on a product of basis vectors, paired with any `x`. -/
lemma form_tensorF_tmul (x : StandardSl2Module ℝ n ⊗[ℝ] StandardSl2Module ℝ m) (a b : ℕ) :
    tensorForm n m (tensorF n m (normVec n a ⊗ₜ normVec m b)) x =
      (if a < n then lad n a * tensorForm n m (normVec n (a + 1) ⊗ₜ normVec m b) x else 0) +
      (if b < m then lad m b * tensorForm n m (normVec n a ⊗ₜ normVec m (b + 1)) x else 0) := by
  rw [tensorF, diagEnd_tmul, map_add, LinearMap.add_apply, ρF_normVec', ρF_normVec']
  congr 1
  · split_ifs
    · rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, smul_eq_mul]
    · simp
  · split_ifs
    · rw [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    · simp

/-- **Lowering recursion**: `√(a(n-a+1)) C(l; a-1, b) + √(b(m-b+1)) C(l; a, b-1) =
√((l+1)(N-l)) C(l+1; a, b)` (the coefficients `C(l; a, b) = cgCoefficient n m k l a b`). -/
lemma cg_F_rel (hk : k ≤ n) (hk' : k ≤ m) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ m) (l : ℕ)
    (hl : l ≤ n + m - 2 * k) :
    (if 0 < a then lad n (a - 1) * cgCoefficient n m k l (a - 1) b else 0) +
      (if 0 < b then lad m (b - 1) * cgCoefficient n m k l a (b - 1) else 0) =
      if l < n + m - 2 * k then lad (n + m - 2 * k) l * cgCoefficient n m k (l + 1) a b
        else 0 := by
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hnm
  · have : a = 0 ∧ b = 0 ∧ n + m - 2 * k = 0 := by omega
    obtain ⟨rfl, rfl, hN⟩ := this
    simp [hN]
  have h := form_tensorE_tmul (coupledVec n m k l) a b
  simp only [cgCoefficient] at h ⊢
  have e1 : (0 < a ∧ a ≤ n) ↔ 0 < a := ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩
  have e2 : (0 < b ∧ b ≤ m) ↔ 0 < b := ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩
  simp only [e1, e2] at h
  rw [← h, tensorForm_tensorE]
  rcases lt_or_eq_of_le hl with hl' | hl'
  · rw [ite_eq_left hl', tensorF_coupledVec hk hk' hl', map_smul, smul_eq_mul]
    rfl
  · rw [ite_eq_right (by omega), hl', tensorF_coupledVec_last hk hk' hnm, map_zero]

/-- **Raising recursion**: `√((a+1)(n-a)) C(l; a+1, b) + √((b+1)(m-b)) C(l; a, b+1) =
√(l(N-l+1)) C(l-1; a, b)`. -/
lemma cg_E_rel (hk : k ≤ n) (hk' : k ≤ m) (a b l : ℕ) (hl : l ≤ n + m - 2 * k) :
    (if a < n then lad n a * cgCoefficient n m k l (a + 1) b else 0) +
      (if b < m then lad m b * cgCoefficient n m k l a (b + 1) else 0) =
      if 0 < l then lad (n + m - 2 * k) (l - 1) * cgCoefficient n m k (l - 1) a b else 0 := by
  have h := form_tensorF_tmul (coupledVec n m k l) a b
  simp only [cgCoefficient] at h ⊢
  rw [← h, tensorForm_tensorF]
  rcases Nat.eq_zero_or_pos l with h0 | hl0
  · rw [ite_eq_right (by omega), h0, tensorE_coupledVec_zero hk hk', map_zero]
  · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have hnm : 0 < n + m := by omega
    rw [ite_eq_left hl0, tensorE_coupledVec_succ hnm hk hk' (by omega), map_smul, smul_eq_mul]
    rfl

/-- **Weight relation**: `(n - 2a + m - 2b) C(l; a, b) = C(l; a, b) (N - 2l)`. -/
lemma cg_H_rel (hk : k ≤ n) (hk' : k ≤ m) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ m) {l : ℕ}
    (hl : l ≤ n + m - 2 * k) :
    ((n : ℝ) - 2 * a + ((m : ℝ) - 2 * b)) * cgCoefficient n m k l a b =
      cgCoefficient n m k l a b * (((n + m - 2 * k : ℕ) : ℝ) - 2 * l) := by
  by_cases h : a + b = k + l
  · have : ((n + m - 2 * k : ℕ) : ℝ) = (n : ℝ) + m - 2 * k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]
    have h' : (a : ℝ) + b = k + l := by exact_mod_cast h
    linear_combination (-2 : ℝ) * cgCoefficient n m k l a b * h'
  · have hnm : 0 < n + m := by omega
    rw [cgCoefficient_eq_zero_of_ne hnm hk hk' h]
    ring

/-! ## D. The Clebsch–Gordan matrix and the Lie algebra -/

/-- **The Clebsch–Gordan matrix** of `n/2 ⊗ m/2 → (n+m)/2 - k`: rows `(a, b)` (the product state
`|n/2, n/2 - a⟩ ⊗ |m/2, m/2 - b⟩`), columns `l` (the coupled state `|J, J - l⟩`,
`J = (n+m)/2 - k`), entries Physlib's `cgCoefficient n m k l a b`. -/
noncomputable def cgMatrix (n m k : ℕ) : Matrix (Idx n m) (Fin (n + m - 2 * k + 1)) ℂ :=
  Matrix.of fun p l => (cgCoefficient n m k l p.1 p.2 : ℂ)

lemma cgMatrix_apply (p : Idx n m) (l : Fin (n + m - 2 * k + 1)) :
    cgMatrix n m k p l = (cgCoefficient n m k l p.1 p.2 : ℂ) := rfl

/-- The differential `X ⊗ 1 + 1 ⊗ X` of `D^{n/2}(g) ⊗ D^{m/2}(g)` (the diagonal SU(2)). -/
noncomputable def dDiag (n m : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Idx n m) (Idx n m) ℂ :=
  dSpin n X ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) +
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ dSpin m X

lemma dDiag_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    dDiag n m (X + Y) = dDiag n m X + dDiag n m Y := by
  simp only [dDiag, dSpin_add, add_kronecker, kronecker_add]
  abel

lemma dDiag_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    dDiag n m (c • X) = c • dDiag n m X := by
  simp only [dDiag, dSpin_smul, smul_kronecker, kronecker_smul, smul_add]

/-- `cgMatrix` intertwines the lowering operators. -/
theorem cgMatrix_F (hk : k ≤ n) (hk' : k ≤ m) :
    dDiag n m matF * cgMatrix n m k = cgMatrix n m k * dSpin (n + m - 2 * k) matF := by
  ext ⟨a, b⟩ l
  rw [dDiag, kron_sum_mul_apply, mul_apply]
  simp only [cgMatrix_apply]
  rw [sum_dSpin_F_mul (fun a' => (cgCoefficient n m k l a' b : ℂ)) a,
    sum_dSpin_F_mul (fun b' => (cgCoefficient n m k l a b' : ℂ)) b,
    sum_mul_dSpin_F (fun l' => (cgCoefficient n m k l' a b : ℂ)) l]
  have h := cg_F_rel hk hk' (Nat.lt_succ_iff.mp a.2) (Nat.lt_succ_iff.mp b.2) l
    (Nat.lt_succ_iff.mp l.2)
  split_ifs at h ⊢ <;>
    (have h' := congrArg (fun x : ℝ => (x : ℂ)) h; push_cast at h'; linear_combination h')

/-- `cgMatrix` intertwines the raising operators. -/
theorem cgMatrix_E (hk : k ≤ n) (hk' : k ≤ m) :
    dDiag n m matE * cgMatrix n m k = cgMatrix n m k * dSpin (n + m - 2 * k) matE := by
  ext ⟨a, b⟩ l
  rw [dDiag, kron_sum_mul_apply, mul_apply]
  simp only [cgMatrix_apply]
  rw [sum_dSpin_E_mul (fun a' => (cgCoefficient n m k l a' b : ℂ)) a,
    sum_dSpin_E_mul (fun b' => (cgCoefficient n m k l a b' : ℂ)) b,
    sum_mul_dSpin_E (fun l' => (cgCoefficient n m k l' a b : ℂ)) l]
  have h := cg_E_rel hk hk' a b l (Nat.lt_succ_iff.mp l.2)
  split_ifs at h ⊢ <;>
    (have h' := congrArg (fun x : ℝ => (x : ℂ)) h; push_cast at h'; linear_combination h')

/-- `cgMatrix` intertwines the weight operators. -/
theorem cgMatrix_H (hk : k ≤ n) (hk' : k ≤ m) :
    dDiag n m matH * cgMatrix n m k = cgMatrix n m k * dSpin (n + m - 2 * k) matH := by
  ext ⟨a, b⟩ l
  rw [dDiag, kron_sum_mul_apply, mul_apply]
  simp only [cgMatrix_apply]
  rw [sum_dSpin_H_mul (fun a' => (cgCoefficient n m k l a' b : ℂ)) a,
    sum_dSpin_H_mul (fun b' => (cgCoefficient n m k l a b' : ℂ)) b,
    sum_mul_dSpin_H (fun l' => (cgCoefficient n m k l' a b : ℂ)) l]
  have h := cg_H_rel hk hk' (Nat.lt_succ_iff.mp a.2) (Nat.lt_succ_iff.mp b.2)
    (Nat.lt_succ_iff.mp l.2)
  have h' := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at h'
  linear_combination h'

/-- **Lie-algebra Clebsch–Gordan**: for every traceless `X`,
`(X ⊗ 1 + 1 ⊗ X) C = C X^{(N)}`. -/
theorem cgMatrix_lie (hk : k ≤ n) (hk' : k ≤ m) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h : X 1 1 = -X 0 0) :
    dDiag n m X * cgMatrix n m k = cgMatrix n m k * dSpin (n + m - 2 * k) X := by
  rw [traceless_eq h, dDiag_add, dDiag_add, dDiag_smul, dDiag_smul, dDiag_smul, dSpin_add,
    dSpin_add, dSpin_smul, dSpin_smul, dSpin_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    cgMatrix_H hk hk', cgMatrix_E hk hk', cgMatrix_F hk hk']

/-! ## E. The group relation -/

/-- A matrix identity from its action on vectors. -/
lemma matrix_eq_of_mulVec {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    {M N : Matrix ι κ ℂ} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-- **Clebsch–Gordan for the group SU(2)**:
`(D^{n/2}(g) ⊗ D^{m/2}(g)) C = C D^{(n+m)/2-k}(g)` for every `g ∈ SU(2)`. -/
theorem cgMatrix_equivariant (hk : k ≤ n) (hk' : k ≤ m) (g : SU2) :
    (spinMat n g ⊗ₖ spinMat m g) * cgMatrix n m k =
      cgMatrix n m k * spinMat (n + m - 2 * k) g := by
  obtain ⟨X, hX, rfl⟩ := exists_Γ_one g
  rw [spinMat_Γ, spinMat_Γ, spinMat_Γ, exp_kronecker]
  have key := intertwine_exp' (Matrix.toLin' (cgMatrix n m k))
    (A := dSpin (n + m - 2 * k) X) (B := dDiag n m X) (fun v => by
      simp only [Matrix.toLin'_apply, mulVec_mulVec, ← cgMatrix_lie hk hk' hX.trace_eq])
  refine (matrix_eq_of_mulVec fun v => ?_).symm
  have := key v
  simp only [Matrix.toLin'_apply, mulVec_mulVec] at this
  exact this

/-! ## F. Orthonormality and completeness -/

lemma sum_idx (f : ℕ → ℕ → ℂ) :
    ∑ p : Idx n m, f p.1 p.2 = ∑ a ∈ range (n + 1), ∑ b ∈ range (m + 1), f a b := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (m + 1), f a b)]
  exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (f a) _

/-- The coupled states `|J, M⟩` and `|J', M'⟩` are orthonormal, in coordinates. -/
lemma conjTranspose_cgMatrix_mul_apply {k' : ℕ} (hk : k ≤ n) (hk' : k ≤ m) (hk2 : k' ≤ n)
    (hk2' : k' ≤ m) (l : Fin (n + m - 2 * k + 1)) (l' : Fin (n + m - 2 * k' + 1)) :
    ((cgMatrix n m k)ᴴ * cgMatrix n m k') l l' =
      if k = k' ∧ (l : ℕ) = l' then 1 else 0 := by
  rw [mul_apply]
  simp only [conjTranspose_apply, cgMatrix_apply, Complex.star_def, Complex.conj_ofReal]
  rw [sum_idx (fun a b => ((cgCoefficient n m k l a b : ℝ) : ℂ) * (cgCoefficient n m k' l' a b))]
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hnm
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ k' = 0 := by omega
    have hl : (l : ℕ) = 0 := by have := l.2; omega
    have hl' : (l' : ℕ) = 0 := by have := l'.2; omega
    simp [cgCoefficient_stretched]
  · have h := sum_cgCoefficient_mul hnm hk hk' hk2 hk2' (Nat.lt_succ_iff.mp l.2) (l' := l')
    have h' := congrArg (fun x : ℝ => (x : ℂ)) h
    push_cast at h'
    rw [h']
    split_ifs <;> simp

/-- **The coupled states are orthonormal**: `Cᴴ C = 1`. -/
theorem cgMatrix_isometry (hk : k ≤ n) (hk' : k ≤ m) :
    (cgMatrix n m k)ᴴ * cgMatrix n m k = 1 := by
  ext l l'
  rw [conjTranspose_cgMatrix_mul_apply hk hk' hk hk', one_apply]
  simp [Fin.ext_iff]

/-- **Different spins are orthogonal**: `C_kᴴ C_{k'} = 0` for `k ≠ k'`. -/
theorem cgMatrix_orth {k' : ℕ} (hk : k ≤ n) (hk' : k ≤ m) (hk2 : k' ≤ n) (hk2' : k' ≤ m)
    (hne : k ≠ k') : (cgMatrix n m k)ᴴ * cgMatrix n m k' = 0 := by
  ext l l'
  rw [conjTranspose_cgMatrix_mul_apply hk hk' hk2 hk2']
  simp [hne]

/-- **Completeness**: `Σ_k C_k C_kᴴ = 1`, i.e. the coupled states of all spins
`(n+m)/2 - k`, `k = 0, …, min(n,m)`, form an orthonormal basis. -/
theorem cgMatrix_complete :
    ∑ k ∈ range (min n m + 1), cgMatrix n m k * (cgMatrix n m k)ᴴ = 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [Matrix.sum_apply]
  simp only [mul_apply, conjTranspose_apply, cgMatrix_apply, Complex.star_def,
    Complex.conj_ofReal]
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hnm
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
    have ha : a = 0 := Fin.ext (by have := a.2; omega)
    have hb : b = 0 := Fin.ext (by have := b.2; omega)
    have ha' : a' = 0 := Fin.ext (by have := a'.2; omega)
    have hb' : b' = 0 := Fin.ext (by have := b'.2; omega)
    subst ha hb ha' hb'
    simp [cgCoefficient_stretched]
  · have h := sum_cgCoefficient_mul_cgCoefficient hnm (Nat.lt_succ_iff.mp a.2)
      (Nat.lt_succ_iff.mp b.2) (Nat.lt_succ_iff.mp a'.2) (Nat.lt_succ_iff.mp b'.2)
    have h' := congrArg (fun x : ℝ => (x : ℂ)) h
    push_cast at h'
    rw [one_apply]
    have e : ((a, b) = (a', b')) ↔ ((a : ℕ) = a' ∧ (b : ℕ) = b') := by
      simp [Prod.ext_iff, Fin.ext_iff]
    simp only [e]
    have h'' : (((if (a : ℕ) = a' ∧ (b : ℕ) = b' then 1 else 0 : ℝ)) : ℂ) =
        if (a : ℕ) = a' ∧ (b : ℕ) = b' then 1 else 0 := by split_ifs <;> simp
    rw [← h'', ← h']
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun l => ((cgCoefficient n m k l a b : ℝ) : ℂ) *
      (cgCoefficient n m k l a' b' : ℝ)) _

/-! ## G. The 3j symbols and the highest state -/

/-- **The Clebsch–Gordan matrix in Physlib's 3j symbols** (doubled units):
`⟨n/2 m₁ m/2 m₂ | J M⟩ = (-1)^{n+k+l} √(N+1) (n m N; m₁ m₂ -M)` with `m₁ = n - 2a`,
`m₂ = m - 2b`, `M = N - 2l`. -/
theorem cgMatrix_eq_threeJ (hk : k ≤ n) (hk' : k ≤ m) (p : Idx n m)
    (l : Fin (n + m - 2 * k + 1)) :
    cgMatrix n m k p l = (((-1 : ℝ) ^ (n + k + (l : ℕ)) *
      Real.sqrt ((n + m - 2 * k + 1 : ℕ) : ℝ) *
      threeJ n m (n + m - 2 * k) ((n : ℤ) - 2 * (p.1 : ℕ)) ((m : ℤ) - 2 * (p.2 : ℕ))
        (-(((n + m - 2 * k : ℕ) : ℤ) - 2 * (l : ℕ))) : ℝ) : ℂ) := by
  rw [cgMatrix_apply]
  congr 1
  have ha := Nat.lt_succ_iff.mp p.1.2
  have hb := Nat.lt_succ_iff.mp p.2.2
  have hl := Nat.lt_succ_iff.mp l.2
  rw [← wigner3j_eq_threeJ hk hk' hl ha hb]
  by_cases h : (p.1 : ℕ) + p.2 = k + l
  · rw [cgCoefficient_eq_threeJR hk hk' hl ha hb h, wigner3j, ite_eq_left h]
  · have hnm : 0 < n + m := by omega
    rw [cgCoefficient_eq_zero_of_ne hnm hk hk' h, wigner3j, ite_eq_right h, mul_zero]

/-- **Condon–Shortley signs of the highest state**: the coefficients of `|J, J⟩` are
`⟨n/2, n/2 - a; m/2, m/2 - (k - a) | J J⟩ = (-1)^a c` with `c > 0`. -/
theorem cgCoefficient_top_sign (hk : k ≤ n) (hk' : k ≤ m) {a : ℕ} (ha : a ≤ k) :
    ∃ c : ℝ, 0 < c ∧ cgCoefficient n m k 0 a (k - a) = (-1) ^ a * c := by
  rw [cgCoefficient_top hk hk' ha, cgCoeff]
  refine ⟨((k.choose a * (m - k + a).factorial * (n - a).factorial : ℕ) : ℝ) *
    Real.sqrt (normSq n a) * Real.sqrt (normSq m (k - a)) / Real.sqrt (hwNormSq n m k), ?_, ?_⟩
  · have h1 : (0 : ℝ) < ((k.choose a * (m - k + a).factorial * (n - a).factorial : ℕ) : ℝ) := by
      have := Nat.choose_pos ha
      positivity
    have h2 : (0 : ℝ) < Real.sqrt (normSq n a) :=
      Real.sqrt_pos.mpr (by exact_mod_cast normSq_pos (by omega))
    have h3 : (0 : ℝ) < Real.sqrt (normSq m (k - a)) :=
      Real.sqrt_pos.mpr (by exact_mod_cast normSq_pos (by omega))
    have h4 : (0 : ℝ) < Real.sqrt (hwNormSq n m k) := Real.sqrt_pos.mpr (hwNormSq_pos hk hk')
    positivity
  · ring

end Lightlike.Spin4

module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Poincare
public import Lightlike.Lorentz.PoincareIrreps.SpinCasimir

/-!
# The Pauli–Lubanski vector of a massive one-particle representation

HA6 (Wigner's classification), ninth piece: the *pointwise* Pauli–Lubanski vector. At a mass-shell
momentum `p = L(p)·(m,0,0,0)` the Pauli–Lubanski vector acts on the fibre `ℂ^{n+1}` of the induced
representation by `W^μ(p) = m · Σ_k L(p)^μ{}_k J_k`, where `J_k` are the spin matrices of the
spin-`n/2` representation of the little group `SU(2)` and `L(p) ∈ SL(2,ℂ)` is the standard boost.

* `coord`, `ofVec_coord`: the real components of a Hermitian matrix (inverse of `ofVec`);
* `spinJ n`: the spin matrices `J_x, J_y, J_z` built from `opE, opF, opH` of `spinRep n`;
* `spinJ_casimir`: `J_x² + J_y² + J_z² = s(s+1)`, `s = n/2`;
* `pauliLubanski`: the vector `W^μ`; `pauliLubanski_square`: **`W² = −m² s(s+1)`** in the signature
  `(+,−,−,−)`; `momentum_dot_pauliLubanski`: `P·W = 0` (with `P = L(p)(m,0,0,0)`).

The covariance of `W` under the induced representation is not part of this file.

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open SU2Spin

/-! ## Components of a Hermitian matrix -/

/-- The real components `(p₀,p₁,p₂,p₃)` of a Hermitian `2×2` matrix (inverse of `ofVec`). -/
noncomputable def coord (Q : Herm2) : Fin 4 → ℝ :=
  ![(Q.1 0 0 + Q.1 1 1).re / 2, (Q.1 1 0).re, (Q.1 1 0).im, (Q.1 0 0 - Q.1 1 1).re / 2]

lemma herm_im_diag (Q : Herm2) (i : Fin 2) : (Q.1 i i).im = 0 := by
  have h := Q.2.apply i i
  have := congrArg Complex.im h
  simp at this
  linarith

lemma herm_offdiag (Q : Herm2) : Q.1 0 1 = star (Q.1 1 0) := (Q.2.apply 0 1).symm

/-- `ofVec` is a left inverse of `coord`. -/
theorem ofVec_coord (Q : Herm2) : ofVec (coord Q) = Q := by
  apply Subtype.ext
  ext i j
  have h0 := herm_im_diag Q 0
  have h1 := herm_im_diag Q 1
  have h01 := herm_offdiag Q
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · simp [ofVec, coord]; ring
    · simp [ofVec, coord, h0]
  · show (ofVec (coord Q)).1 0 1 = Q.1 0 1
    rw [h01]; apply Complex.ext <;> simp [ofVec, coord]
  · apply Complex.ext <;> simp [ofVec, coord]
  · apply Complex.ext
    · simp [ofVec, coord]; ring
    · simp [ofVec, coord, h1]

/-- The unit four-vectors as Hermitian matrices. -/
noncomputable def unitVec : Fin 4 → Herm2 :=
  ![ofVec ![1, 0, 0, 0], ofVec ![0, 1, 0, 0], ofVec ![0, 0, 1, 0], ofVec ![0, 0, 0, 1]]

/-- The Minkowski form on component vectors in signature `(+,−,−,−)`. -/
def mink (p a : Fin 4 → ℝ) : ℝ := p 0 * a 0 - p 1 * a 1 - p 2 * a 2 - p 3 * a 3

/-- Lorentz transformations preserve the Minkowski form of the components. -/
theorem mink_coord_smul (A : SL2C) (X Y : Herm2) :
    mink (coord (A • X)) (coord (A • Y)) = pairing X Y := by
  rw [← pairing_smul A X Y, ← ofVec_coord (A • X), ← ofVec_coord (A • Y), pairing_ofVec]
  simp [mink, ofVec_coord]

lemma pairing_unitVec (ν ρ : Fin 4) :
    pairing (unitVec ν) (unitVec ρ) = if ν = ρ then (if ν = 0 then 1 else -1) else 0 := by
  fin_cases ν <;> fin_cases ρ <;> simp [unitVec, pairing_ofVec]

/-- The orthogonality relations of the Lorentz matrix `L(A)^μ{}_ν = coord (A • eν) μ`. -/
theorem lorentz_orth (A : SL2C) (ν ρ : Fin 4) :
    mink (coord (A • unitVec ν)) (coord (A • unitVec ρ)) =
      if ν = ρ then (if ν = 0 then 1 else -1) else 0 := by
  rw [mink_coord_smul, pairing_unitVec]

/-! ## Spin matrices -/

section Spin

variable {d : ℕ}

/-- Algebraic form of `J² = C/4`: with `J_x = (E+F)/2`, `J_y = −i(E−F)/2`, `J_z = H/2`. -/
lemma J_sq_sum {H E F : Matrix (Fin d) (Fin d) ℂ} (h3 : E * F - F * E = H) :
    ((1 / 2 : ℂ) • (E + F)) * ((1 / 2 : ℂ) • (E + F)) +
      ((-Complex.I / 2 : ℂ) • (E - F)) * ((-Complex.I / 2 : ℂ) • (E - F)) +
      ((1 / 2 : ℂ) • H) * ((1 / 2 : ℂ) • H) = (1 / 4 : ℂ) • sl2Casimir H E F := by
  have hI : (-Complex.I / 2 : ℂ) * (-Complex.I / 2) = -1 / 4 := by
    linear_combination (1 / 4 : ℂ) * Complex.I_sq
  simp only [smul_mul_smul_comm, hI, sl2Casimir, mul_add, add_mul, mul_sub, sub_mul]
  linear_combination (norm := module) (1 / 2 : ℂ) • h3

end Spin

/-- The spin matrices `J_x, J_y, J_z` of the spin-`n/2` representation. -/
noncomputable def spinJ (n : ℕ) : Fin 3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  ![(1 / 2 : ℂ) • (opE (σ n) + opF (σ n)), (-Complex.I / 2 : ℂ) • (opE (σ n) - opF (σ n)),
    (1 / 2 : ℂ) • opH (σ n)]

/-- **`J_x² + J_y² + J_z² = s(s+1)` with `s = n/2`.** -/
theorem spinJ_casimir (n : ℕ) :
    spinJ n 0 * spinJ n 0 + spinJ n 1 * spinJ n 1 + spinJ n 2 * spinJ n 2 =
      ((n : ℂ) * (n + 2) / 4) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have h := J_sq_sum (sl2_rel (continuous_σ n)).2.2
  rw [spin_casimir] at h
  simp only [spinJ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [h, smul_smul]
  congr 1
  ring

/-! ## The Pauli–Lubanski vector -/

/-- The Pauli–Lubanski vector `W^μ = m Σ_k L(A)^μ{}_k J_k` at the momentum `A·(m,0,0,0)`. -/
noncomputable def pauliLubanski (m : ℝ) (n : ℕ) (A : SL2C) (μ : Fin 4) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (m : ℂ) • ∑ k : Fin 3, ((coord (A • unitVec k.succ) μ : ℝ) : ℂ) • spinJ n k

lemma minkSq_expand {d : ℕ} (m : ℂ) (a : Fin 4 → Fin 3 → ℂ)
    (J : Fin 3 → Matrix (Fin d) (Fin d) ℂ) :
    (m • ∑ k, a 0 k • J k) * (m • ∑ k, a 0 k • J k) -
      (m • ∑ k, a 1 k • J k) * (m • ∑ k, a 1 k • J k) -
      (m • ∑ k, a 2 k • J k) * (m • ∑ k, a 2 k • J k) -
      (m • ∑ k, a 3 k • J k) * (m • ∑ k, a 3 k • J k) =
    m ^ 2 • ∑ k, ∑ l, (a 0 k * a 0 l - a 1 k * a 1 l - a 2 k * a 2 l - a 3 k * a 3 l) •
      (J k * J l) := by
  simp only [Fin.sum_univ_three, smul_add, add_mul, mul_add, smul_mul_smul_comm, smul_smul]
  module

/-- **The Pauli–Lubanski square is `W² = −m² s(s+1)`**, `s = n/2`, in signature `(+,−,−,−)`:
`W⁰W⁰ − W¹W¹ − W²W² − W³W³ = −m² (n/2)(n/2+1)`. -/
theorem pauliLubanski_square (m : ℝ) (n : ℕ) (A : SL2C) :
    pauliLubanski m n A 0 * pauliLubanski m n A 0 - pauliLubanski m n A 1 * pauliLubanski m n A 1 -
      pauliLubanski m n A 2 * pauliLubanski m n A 2 -
      pauliLubanski m n A 3 * pauliLubanski m n A 3 =
    (-((m : ℂ) ^ 2 * ((n : ℂ) * (n + 2) / 4))) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  unfold pauliLubanski
  refine (minkSq_expand (m : ℂ) (fun μ k => ((coord (A • unitVec k.succ) μ : ℝ) : ℂ))
    (spinJ n)).trans ?_
  have hg : ∀ k l : Fin 3, ((coord (A • unitVec k.succ) 0 : ℝ) : ℂ) * (coord (A • unitVec l.succ) 0 : ℝ) -
      (coord (A • unitVec k.succ) 1 : ℝ) * (coord (A • unitVec l.succ) 1 : ℝ) -
      (coord (A • unitVec k.succ) 2 : ℝ) * (coord (A • unitVec l.succ) 2 : ℝ) -
      (coord (A • unitVec k.succ) 3 : ℝ) * (coord (A • unitVec l.succ) 3 : ℝ) =
      ((if k = l then (-1 : ℝ) else 0 : ℝ) : ℂ) := by
    intro k l
    have h := lorentz_orth A k.succ l.succ
    simp only [mink] at h
    have h' : ((coord (A • unitVec k.succ) 0 * coord (A • unitVec l.succ) 0 -
      coord (A • unitVec k.succ) 1 * coord (A • unitVec l.succ) 1 -
      coord (A • unitVec k.succ) 2 * coord (A • unitVec l.succ) 2 -
      coord (A • unitVec k.succ) 3 * coord (A • unitVec l.succ) 3 : ℝ) : ℂ) =
      ((if k = l then (-1 : ℝ) else 0 : ℝ) : ℂ) := by
      rw [h]
      congr 1
      by_cases hkl : k = l
      · simp [hkl, Fin.succ_ne_zero]
      · simp [hkl, (Fin.succ_injective _).ne hkl]
    push_cast at h' ⊢
    exact h'
  simp only [hg, Fin.sum_univ_three]
  have := spinJ_casimir n
  have e01 : (0 : Fin 3) ≠ 1 := by decide
  have e02 : (0 : Fin 3) ≠ 2 := by decide
  have e12 : (1 : Fin 3) ≠ 2 := by decide
  simp only [ite_true, e01, e02, e12, e01.symm, e02.symm, e12.symm, ite_false]
  linear_combination (norm := module) (-(m : ℂ) ^ 2) • this

lemma smul_restMom_coe (m : ℝ) (A : SL2C) :
    (A • restMom m).1 = (m : ℂ) • (A • unitVec 0).1 := by
  have h : (unitVec 0).1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitVec, ofVec]
  rw [coe_smul, coe_smul, h]
  simp [restMom]

/-- The momentum `A·(m,0,0,0)` has components `m · L(A)^μ{}_0`. -/
lemma coord_smul_restMom (m : ℝ) (A : SL2C) (μ : Fin 4) :
    coord (A • restMom m) μ = m * coord (A • unitVec 0) μ := by
  unfold coord
  rw [smul_restMom_coe]
  fin_cases μ <;> simp [← mul_add, ← mul_sub] <;> ring

lemma dot_expand {d : ℕ} (m : ℂ) (c : Fin 4 → ℂ) (b : Fin 4 → Fin 3 → ℂ)
    (J : Fin 3 → Matrix (Fin d) (Fin d) ℂ) :
    c 0 • (m • ∑ k, b 0 k • J k) - c 1 • (m • ∑ k, b 1 k • J k) -
      c 2 • (m • ∑ k, b 2 k • J k) - c 3 • (m • ∑ k, b 3 k • J k) =
    m • ∑ k, (c 0 * b 0 k - c 1 * b 1 k - c 2 * b 2 k - c 3 * b 3 k) • J k := by
  simp only [Fin.sum_univ_three, smul_add, smul_smul]
  module

/-- **`P·W = 0`**: the Pauli–Lubanski vector is orthogonal to the momentum
`P = A·(m,0,0,0)`, `P⁰W⁰ − P¹W¹ − P²W² − P³W³ = 0`. -/
theorem momentum_dot_pauliLubanski (m : ℝ) (n : ℕ) (A : SL2C) :
    ((coord (A • restMom m) 0 : ℝ) : ℂ) • pauliLubanski m n A 0 -
      ((coord (A • restMom m) 1 : ℝ) : ℂ) • pauliLubanski m n A 1 -
      ((coord (A • restMom m) 2 : ℝ) : ℂ) • pauliLubanski m n A 2 -
      ((coord (A • restMom m) 3 : ℝ) : ℂ) • pauliLubanski m n A 3 = 0 := by
  unfold pauliLubanski
  refine (dot_expand (m : ℂ) (fun μ => ((coord (A • restMom m) μ : ℝ) : ℂ))
    (fun μ k => ((coord (A • unitVec k.succ) μ : ℝ) : ℂ)) (spinJ n)).trans ?_
  have hk : ∀ k : Fin 3, ((coord (A • restMom m) 0 : ℝ) : ℂ) *
      ((coord (A • unitVec k.succ) 0 : ℝ) : ℂ) -
      ((coord (A • restMom m) 1 : ℝ) : ℂ) * ((coord (A • unitVec k.succ) 1 : ℝ) : ℂ) -
      ((coord (A • restMom m) 2 : ℝ) : ℂ) * ((coord (A • unitVec k.succ) 2 : ℝ) : ℂ) -
      ((coord (A • restMom m) 3 : ℝ) : ℂ) * ((coord (A • unitVec k.succ) 3 : ℝ) : ℂ) = 0 := by
    intro k
    have h := lorentz_orth A 0 k.succ
    simp only [mink] at h
    have hne : (0 : Fin 4) ≠ k.succ := (Fin.succ_ne_zero k).symm
    simp only [hne, ite_false] at h
    simp only [coord_smul_restMom]
    have h' : ((m * (coord (A • unitVec 0) 0 * coord (A • unitVec k.succ) 0 -
      coord (A • unitVec 0) 1 * coord (A • unitVec k.succ) 1 -
      coord (A • unitVec 0) 2 * coord (A • unitVec k.succ) 2 -
      coord (A • unitVec 0) 3 * coord (A • unitVec k.succ) 3) : ℝ) : ℂ) = 0 := by
      rw [h]; simp
    push_cast at h' ⊢
    linear_combination h'
  simp only [hk, zero_smul, Finset.sum_const_zero, smul_zero]

end Lightlike.Lorentz.Poincare

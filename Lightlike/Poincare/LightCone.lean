module

public import Lightlike.Poincare.LittleGroupsH
public import Lightlike.Poincare.InducedGeneric

/-!
# The forward light cone and the massless helicity representations

Momenta are Hermitian `2 × 2` matrices, `SL(2,ℂ)` acting by `A • P = A P Aᴴ`. The forward light cone is the set of
nonzero positive semidefinite singular Hermitian matrices (`p² = det P = 0`, `p⁰ > 0`), invariant under `SL(2,ℂ)`
(`actP_mem_lightCone`). Its base point is `K = diag(2, 0)` (`p = (1, 0, 0, 1)`), with little group the upper
triangular matrices `[[e^{iθ}, b], [0, e^{−iθ}]]` (`LittleGroupsH`).

* **Standard lift** (`coneLift`): an explicit `L(P) ∈ SL(2,ℂ)` with `L(P) • K = P` for every `P` on the cone
  (`coneLift_smul`): the cone is one orbit.
* **Helicity characters** (`helicityChar n`): `A ↦ (A₀₀)ⁿ` on the little group, a unitary character (`n = 2h`,
  `h ∈ ½ℤ` the helicity); the translations `b` of the little group act trivially, the finite-helicity case.
* **Massless induced representations** (`helicityAct`): by the construction of `InducedGeneric`, an action of
  `SL(2,ℂ)` on wave functions on the light cone.

**Difference from the source (kind: representation).** Bekaert–Boulanger state the massless little group as
`ISO(D−2)` inside `SO(D−1,1)↑` and the helicity representations as representations of its short little group
`SO(D−2)` (§3.2, §3.3); here everything is in the universal cover `SL(2,ℂ)`, where the little group is the double
cover of `E(2)` and the helicity `h` runs over `½ℤ` (their §1.1, page 3: representations are meant as representations
of the spin group).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2 (page 12 of v2: the stabiliser of a light-like vector is `ISO(D − 2)`), §3.3 (pages
  14–15: helicity representations, the "translations" of the little group acting trivially; the helicity short
  little group `SO(2)` is abelian, so its irreducible representations are one-dimensional, page 41).
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz
open scoped ComplexOrder

namespace Lightlike.Poincare

/-- The forward light cone: nonzero positive semidefinite singular Hermitian matrices. -/
def LightConeH : Set (Matrix (Fin 2) (Fin 2) ℂ) := {P | P.PosSemidef ∧ P.det = 0 ∧ P ≠ 0}

/-- The light cone as a type. -/
abbrev LightCone := {P : Matrix (Fin 2) (Fin 2) ℂ // P ∈ LightConeH}

lemma actP_inv_actP (A : SL2C) (P : Matrix (Fin 2) (Fin 2) ℂ) : actP A⁻¹ (actP A P) = P := by
  rw [← actP_mul, inv_mul_cancel, actP_one]

lemma actP_zero (A : SL2C) : actP A 0 = 0 := by simp [actP]

/-- The light cone is invariant under `SL(2,ℂ)`. -/
lemma actP_mem_lightCone (A : SL2C) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ LightConeH) :
    actP A P ∈ LightConeH := by
  refine ⟨hP.1.mul_mul_conjTranspose_same _, by rw [det_actP]; exact hP.2.1, fun h => hP.2.2 ?_⟩
  rw [← actP_inv_actP A P, h, actP_zero]

instance : MulAction SL2C LightCone where
  smul A P := ⟨actP A P.1, actP_mem_lightCone A P.2⟩
  one_smul P := Subtype.ext (actP_one P.1)
  mul_smul A B P := Subtype.ext (actP_mul A B P.1)

lemma coe_smul_lightCone (A : SL2C) (P : LightCone) : ((A • P : LightCone) : Matrix (Fin 2) (Fin 2) ℂ) =
    actP A P.1 := rfl

lemma masslessH_eq_diagonal : masslessH = Matrix.diagonal ![2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [masslessH]

/-- The base point `K = diag(2, 0)` of the light cone. -/
def coneBase : LightCone :=
  ⟨masslessH, by
    refine ⟨?_, by simp [masslessH, Matrix.det_fin_two], fun h => ?_⟩
    · rw [masslessH_eq_diagonal, posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> simp
    · have := congrFun (congrFun h 0) 0
      simp [masslessH] at this⟩

/-! ## The standard lift -/

/-- The real number `α = P₀₀ ≥ 0`. -/
def alphaC (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (P 0 0).re

/-- The real number `δ = P₁₁ ≥ 0`. -/
def deltaC (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (P 1 1).re

lemma alphaC_def (P : Matrix (Fin 2) (Fin 2) ℂ) : alphaC P = (P 0 0).re := rfl

lemma deltaC_def (P : Matrix (Fin 2) (Fin 2) ℂ) : deltaC P = (P 1 1).re := rfl

lemma diag_real {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.PosSemidef) (i : Fin 2) :
    P i i = ((P i i).re : ℂ) ∧ 0 ≤ (P i i).re := by
  have h := hP.diag_nonneg (i := i)
  rw [Complex.le_def] at h
  exact ⟨Complex.ext (by simp) (by simp [← h.2]), by simpa using h.1⟩

lemma cone_offdiag {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ LightConeH) : P 1 0 = starRingEnd ℂ (P 0 1) :=
  (hP.1.isHermitian.apply 1 0).symm

/-- `α δ = |β|²` on the light cone (`det P = 0`). -/
lemma cone_alpha_delta {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ LightConeH) :
    alphaC P * deltaC P = Complex.normSq (P 0 1) := by
  have hdet := hP.2.1
  rw [Matrix.det_fin_two, cone_offdiag hP, (diag_real hP.1 0).1, (diag_real hP.1 1).1, Complex.mul_conj] at hdet
  have := congrArg Complex.re hdet
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.zero_re] at this
  simp only [alphaC, deltaC]
  linarith

lemma cone_alpha_nonneg {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ LightConeH) : 0 ≤ alphaC P :=
  (diag_real hP.1 0).2

lemma cone_delta_nonneg {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ LightConeH) : 0 ≤ deltaC P :=
  (diag_real hP.1 1).2

/-- If `α = 0` on the light cone then `β = 0` and `δ > 0`. -/
lemma cone_of_not_alpha_pos {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ LightConeH) (ha : ¬ 0 < alphaC P) :
    P 0 1 = 0 ∧ 0 < deltaC P := by
  have ha0 : alphaC P = 0 := le_antisymm (not_lt.1 ha) (cone_alpha_nonneg hP)
  have hb : P 0 1 = 0 := by
    have h := cone_alpha_delta hP
    rw [ha0, zero_mul, eq_comm, Complex.normSq_eq_zero] at h
    exact h
  refine ⟨hb, lt_of_le_of_ne (cone_delta_nonneg hP) fun hd => hP.2.2 ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.zero_apply]; rw [(diag_real hP.1 0).1, ← alphaC_def, ha0]; simp
  · simpa using hb
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.zero_apply]; rw [cone_offdiag hP, hb]; simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.zero_apply]; rw [(diag_real hP.1 1).1, ← deltaC_def, ← hd]; simp

/-- The standard lift of a point of the light cone: an element `L(P)` of `SL(2,ℂ)` with `L(P) • K = P`. -/
def coneLiftMat (P : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if 0 < alphaC P then
    !![((Real.sqrt (alphaC P / 2) : ℝ) : ℂ), 0;
       starRingEnd ℂ (P 0 1) / (2 * ((Real.sqrt (alphaC P / 2) : ℝ) : ℂ)),
       1 / ((Real.sqrt (alphaC P / 2) : ℝ) : ℂ)]
  else
    !![0, -1 / ((Real.sqrt (deltaC P / 2) : ℝ) : ℂ);
       ((Real.sqrt (deltaC P / 2) : ℝ) : ℂ), 0]

lemma det_coneLiftMat {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ LightConeH) :
    (coneLiftMat P).det = 1 := by
  unfold coneLiftMat
  split_ifs with ha
  · have hs : ((Real.sqrt (alphaC P / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by linarith)).ne'
    rw [Matrix.det_fin_two_of]
    field_simp
    ring
  · have hd : 0 < deltaC P := (cone_of_not_alpha_pos hP ha).2
    have hs : ((Real.sqrt (deltaC P / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by linarith)).ne'
    rw [Matrix.det_fin_two_of]
    field_simp
    ring


/-- The standard lift as an element of `SL(2,ℂ)`. -/
def coneLift (P : LightCone) : SL2C := ⟨coneLiftMat P.1, det_coneLiftMat P.2⟩

lemma masslessH_entry (L : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (L * masslessH * Lᴴ) i j = 2 * (L i 0 * starRingEnd ℂ (L j 0)) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, masslessH, Matrix.conjTranspose_apply]
  simp
  ring

/-- **The light cone is one orbit**: the standard lift takes `K = diag(2, 0)` to `P`. -/
theorem coneLift_smul (P : LightCone) : coneLift P • coneBase = P := by
  apply Subtype.ext
  show coneLiftMat P.1 * masslessH * (coneLiftMat P.1)ᴴ = P.1
  have hP := P.2
  have h00 := (diag_real hP.1 0).1
  have h11 := (diag_real hP.1 1).1
  have h10 := cone_offdiag hP
  have had := cone_alpha_delta hP
  ext i j
  rw [masslessH_entry]
  by_cases ha : 0 < alphaC P.1
  · have ha2 : Real.sqrt (alphaC P.1 / 2) * Real.sqrt (alphaC P.1 / 2) = alphaC P.1 / 2 :=
      Real.mul_self_sqrt (by linarith)
    have hapos : 0 < Real.sqrt (alphaC P.1 / 2) := Real.sqrt_pos.2 (by linarith)
    have hac : ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hapos.ne'
    have hL0 : coneLiftMat P.1 0 0 = ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) := by simp [coneLiftMat, ha]
    have hL1 : coneLiftMat P.1 1 0 =
        starRingEnd ℂ (P.1 0 1) / (2 * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)) := by
      simp [coneLiftMat, ha]
    have hconj : starRingEnd ℂ (starRingEnd ℂ (P.1 0 1) / (2 * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ))) =
        P.1 0 1 / (2 * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)) := by
      rw [map_div₀, Complex.conj_conj, map_mul, Complex.conj_ofReal, map_ofNat]
    have hα : ((alphaC P.1 : ℝ) : ℂ) =
        2 * (((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)) := by
      have : alphaC P.1 = 2 * (Real.sqrt (alphaC P.1 / 2) * Real.sqrt (alphaC P.1 / 2)) := by
        rw [ha2]; ring
      conv_lhs => rw [this]
      push_cast; ring
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [hL0, Complex.conj_ofReal, h00, ← alphaC_def, hα]
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      rw [hL0, hL1, hconj]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]
      rw [hL0, hL1, Complex.conj_ofReal, h10]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue]
      rw [hL1, hconj, h11, ← deltaC_def]
      have hαne : ((alphaC P.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      have key : ((deltaC P.1 : ℝ) : ℂ) = starRingEnd ℂ (P.1 0 1) * P.1 0 1 / ((alphaC P.1 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, ← had]
        push_cast
        field_simp
      rw [key, hα]
      field_simp
  · obtain ⟨hb, hd⟩ := cone_of_not_alpha_pos hP ha
    have ha0 : alphaC P.1 = 0 := le_antisymm (not_lt.1 ha) (cone_alpha_nonneg hP)
    have hc2 : Real.sqrt (deltaC P.1 / 2) * Real.sqrt (deltaC P.1 / 2) = deltaC P.1 / 2 :=
      Real.mul_self_sqrt (by linarith)
    have hL0 : coneLiftMat P.1 0 0 = 0 := by simp [coneLiftMat, ha]
    have hL1 : coneLiftMat P.1 1 0 = ((Real.sqrt (deltaC P.1 / 2) : ℝ) : ℂ) := by simp [coneLiftMat, ha]
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [hL0, h00, ← alphaC_def, ha0]; simp
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      rw [hL0, hb]; simp
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]
      rw [hL0, h10, hb]; simp
    · simp only [Fin.mk_one, Fin.isValue]
      rw [hL1, Complex.conj_ofReal, h11, ← deltaC_def]
      have : deltaC P.1 = 2 * (Real.sqrt (deltaC P.1 / 2) * Real.sqrt (deltaC P.1 / 2)) := by
        rw [hc2]; ring
      conv_rhs => rw [this]
      push_cast; ring

/-! ## Helicity characters and the massless induced action -/

/-- An element of the little group of `K` has `A₁₀ = 0` and `|A₀₀| = 1`. -/
lemma stab_coneBase {A : SL2C} (hA : A ∈ MulAction.stabilizer SL2C coneBase) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧ ‖(A : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1 := by
  rw [MulAction.mem_stabilizer_iff] at hA
  exact (actP_massless_eq_iff A).1 (congrArg Subtype.val hA)

/-- The `(0,0)` entry is multiplicative on the little group. -/
lemma stab_mul_apply_zero_zero {A B : SL2C} (hB : B ∈ MulAction.stabilizer SL2C coneBase) :
    ((A * B : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (B : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, (stab_coneBase hB).1]
  ring

/-- **The helicity character** `A ↦ (A₀₀)ⁿ` of the massless little group (`n = 2h`), acting on `ℂ`. -/
def helicityChar (n : ℤ) : MulAction.stabilizer SL2C coneBase →* (ℂ →ₗ[ℂ] ℂ) where
  toFun A := ((A.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ n) • LinearMap.id
  map_one' := by ext; simp
  map_mul' A B := by
    rw [Subgroup.coe_mul, stab_mul_apply_zero_zero B.2, mul_zpow]
    ext; simp [mul_comm]

/-- The helicity character is unitary: `|(A₀₀)ⁿ| = 1`. -/
lemma norm_helicity (n : ℤ) (A : MulAction.stabilizer SL2C coneBase) :
    ‖(A.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ n‖ = 1 := by
  rw [norm_zpow, (stab_coneBase A.2).2, _root_.one_zpow]

/-- The translations `[[1, b], [0, 1]]` of the little group act trivially: finite helicity. -/
lemma helicityChar_trans (n : ℤ) (b : ℂ) (hb : masslessTrans b ∈ MulAction.stabilizer SL2C coneBase) :
    helicityChar n ⟨masslessTrans b, hb⟩ = LinearMap.id := by
  simp [helicityChar, masslessTrans]

/-- **The massless induced representation of helicity `n/2`**, on wave functions on the light cone. -/
def helicityAct (n : ℤ) (A : SL2C) (ψ : LightCone → ℂ) : LightCone → ℂ :=
  inducedActG (x₀ := coneBase) (L := coneLift) coneLift_smul (helicityChar n) A ψ

theorem helicityAct_mul (n : ℤ) (A' A : SL2C) (ψ : LightCone → ℂ) :
    helicityAct n (A' * A) ψ = helicityAct n A' (helicityAct n A ψ) :=
  inducedActG_mul _ _ _ _ _

theorem helicityAct_one (n : ℤ) (ψ : LightCone → ℂ) : helicityAct n 1 ψ = ψ :=
  inducedActG_one _ _ _

end Lightlike.Poincare

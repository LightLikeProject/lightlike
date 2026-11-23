module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Momentum

/-!
# The positive-energy light cone as an `SL(2,ℂ)`-orbit

HA6 (Wigner's classification), fourth piece: the massless analogue of `Boost.lean`. In the
Hermitian-matrix model of Minkowski space (`Herm2`), a momentum is lightlike with positive energy
iff `det P = 0` and `tr P > 0`. We prove that this set `lightCone` is a single `SL(2,ℂ)`-orbit,
the orbit of `lightMom 1` (`exists_smul_lightMom`), and we choose a standard boost `lightBoost P`
with `lightBoost P • lightMom 1 = P`.

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the statements
proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

/-- The positive-energy light cone: `det P = 0` and `tr P > 0`. -/
def lightCone : Set Herm2 :=
  {P | P.1.det = 0 ∧ 0 < P.1.trace.re}

/-- Entries of a Hermitian `2 × 2` matrix: real diagonal, conjugate off-diagonal. -/
lemma herm_entries (P : Herm2) :
    P.1 0 0 = ((P.1 0 0).re : ℂ) ∧ P.1 1 1 = ((P.1 1 1).re : ℂ) ∧
      P.1 1 0 = (starRingEnd ℂ) (P.1 0 1) := by
  have h := P.2.eq
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.conjTranspose_apply, Complex.star_def] at e00 e11 e10
  refine ⟨?_, ?_, e10.symm⟩
  · exact ((Complex.conj_eq_iff_re).mp e00).symm
  · exact ((Complex.conj_eq_iff_re).mp e11).symm

/-- **The positive-energy light cone is the orbit of `lightMom 1`.** -/
theorem exists_smul_lightMom {P : Herm2} (hP : P ∈ lightCone) :
    ∃ A : SL2C, A • lightMom 1 = P := by
  obtain ⟨hd, ht⟩ := hP
  obtain ⟨h00, h11, h10⟩ := herm_entries P
  set a := (P.1 0 0).re with ha
  set d := (P.1 1 1).re with hdd
  set b := P.1 0 1 with hb
  have htr : 0 < a + d := by
    simpa [Matrix.trace_fin_two, ha, hdd] using ht
  have hdet : (a : ℂ) * d = (Complex.normSq b : ℝ) := by
    rw [Matrix.det_fin_two, h00, h11, h10, ← hb] at hd
    rw [Complex.normSq_eq_conj_mul_self]
    linear_combination hd
  have hdetR : a * d = Complex.normSq b := by exact_mod_cast hdet
  have hns := Complex.normSq_nonneg b
  have key : (starRingEnd ℂ) b * b = (a : ℂ) * d := by
    rw [hdet, Complex.normSq_eq_conj_mul_self]
  by_cases ha0 : a = 0
  · -- then `b = 0` and `d > 0`
    have hb0 : b = 0 := by
      rw [ha0, zero_mul] at hdetR
      exact Complex.normSq_eq_zero.mp hdetR.symm
    have hb0' : P.1 0 1 = 0 := hb0
    have hdpos : 0 < d := by rw [ha0] at htr; linarith
    have ht0 : (Real.sqrt d : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hdpos).ne'
    have hsq : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = d := by
      exact_mod_cast Real.mul_self_sqrt hdpos.le
    refine ⟨SL2C.mk 0 (-(1 / (Real.sqrt d : ℂ))) (Real.sqrt d) 0 (by field_simp; ring), ?_⟩
    apply Subtype.ext
    ext i j
    rw [smul_lightMom_apply]
    fin_cases i <;> fin_cases j
    · simp [h00, ha0]
    · simp [hb0']
    · simp [h10, hb0]
    · simp [h11, ← hsq]
  · have hapos : 0 < a := by
      rcases lt_or_gt_of_ne ha0 with h | h
      · exfalso
        have : d ≤ 0 := by nlinarith
        linarith
      · exact h
    have hs0 : (Real.sqrt a : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hapos).ne'
    have hsq : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = a := by
      exact_mod_cast Real.mul_self_sqrt hapos.le
    refine ⟨SL2C.mk (Real.sqrt a) 0 ((starRingEnd ℂ) b / Real.sqrt a) (1 / Real.sqrt a)
      (by rw [mul_one_div, div_self hs0]; simp), ?_⟩
    apply Subtype.ext
    ext i j
    rw [smul_lightMom_apply]
    fin_cases i <;> fin_cases j
    · simp [h00, ← hsq]
    · simp
      show _ = b
      field_simp
    · simp
      rw [h10]
      field_simp
    · simp
      rw [h11, div_mul_div_comm, key, ← hsq]
      field_simp

/-- The trace of `A (1·diag(1,0)) A†` is `|A₀₀|² + |A₁₀|² > 0`. -/
lemma trace_smul_lightMom_pos (A : SL2C) : 0 < ((A • lightMom 1 : Herm2).1).trace.re := by
  have h0 := smul_lightMom_apply A 1 0 0
  have h1 := smul_lightMom_apply A 1 1 1
  have key : ((A • lightMom 1 : Herm2).1).trace.re = Complex.normSq (A 0 0) + Complex.normSq (A 1 0) := by
    rw [Matrix.trace_fin_two, Complex.add_re, h0, h1]
    simp [Complex.mul_conj]
  rw [key]
  by_contra hneg
  have e0 := Complex.normSq_nonneg (A 0 0)
  have e1 := Complex.normSq_nonneg (A 1 0)
  have c0 : Complex.normSq (A 0 0) = 0 := by linarith
  have c1 : Complex.normSq (A 1 0) = 0 := by linarith
  rw [Complex.normSq_eq_zero] at c0 c1
  have := SL2C.det_eq A
  rw [c0, c1] at this
  simp at this

/-- **The orbit of `lightMom 1` is the positive-energy light cone** (the converse of
`exists_smul_lightMom`). -/
theorem smul_lightMom_mem_lightCone (A : SL2C) : A • lightMom 1 ∈ lightCone := by
  refine ⟨?_, trace_smul_lightMom_pos A⟩
  rw [det_smul]
  simp [lightMom]

/-- The positive-energy light cone is stable under `SL(2,ℂ)`. -/
lemma smul_mem_lightCone (A : SL2C) {P : Herm2} (hP : P ∈ lightCone) : A • P ∈ lightCone := by
  obtain ⟨B, rfl⟩ := exists_smul_lightMom hP
  rw [← mul_smul]
  exact smul_lightMom_mem_lightCone _

/-- The action of `SL(2,ℂ)` on the light cone. -/
def lightSMul (A : SL2C) (P : lightCone) : lightCone :=
  ⟨A • P.1, smul_mem_lightCone A P.2⟩

lemma lightSMul_one (P : lightCone) : lightSMul 1 P = P := Subtype.ext (one_smul _ _)

lemma lightSMul_mul (A B : SL2C) (P : lightCone) :
    lightSMul (A * B) P = lightSMul A (lightSMul B P) := Subtype.ext (mul_smul _ _ _)

lemma lightSMul_inv_smul (A : SL2C) (P : lightCone) : lightSMul A (lightSMul A⁻¹ P) = P := by
  rw [← lightSMul_mul, mul_inv_cancel, lightSMul_one]

/-- **The standard boost of a light-cone momentum**: an element of `SL(2,ℂ)` carrying `lightMom 1`
to `P`. -/
noncomputable def lightBoost (P : lightCone) : SL2C :=
  Classical.choose (exists_smul_lightMom P.2)

lemma lightBoost_smul (P : lightCone) : lightBoost P • lightMom 1 = P.1 :=
  Classical.choose_spec (exists_smul_lightMom P.2)

/-- **The massless Wigner rotation** `L(A P)⁻¹ A L(P)`. -/
noncomputable def lightWignerSL (A : SL2C) (P : lightCone) : SL2C :=
  (lightBoost (lightSMul A P))⁻¹ * A * lightBoost P

/-- The massless Wigner rotation lies in the little group of `lightMom 1`. -/
theorem lightWignerSL_mem_stabilizer (A : SL2C) (P : lightCone) :
    lightWignerSL A P ∈ MulAction.stabilizer SL2C (lightMom 1) := by
  rw [MulAction.mem_stabilizer_iff]
  unfold lightWignerSL
  rw [mul_assoc, mul_smul, mul_smul, lightBoost_smul, inv_smul_eq_iff]
  exact (lightBoost_smul (lightSMul A P)).symm

/-- The massless Wigner rotation as an element of the little group. -/
noncomputable def lightWigner (A : SL2C) (P : lightCone) :
    MulAction.stabilizer SL2C (lightMom 1) :=
  ⟨lightWignerSL A P, lightWignerSL_mem_stabilizer A P⟩

/-- **The massless Wigner cocycle identity** `W(A B, P) = W(A, B P) W(B, P)`. -/
theorem lightWigner_mul (A B : SL2C) (P : lightCone) :
    lightWigner (A * B) P = lightWigner A (lightSMul B P) * lightWigner B P := by
  apply Subtype.ext
  change lightWignerSL (A * B) P = lightWignerSL A (lightSMul B P) * lightWignerSL B P
  simp only [lightWignerSL, lightSMul_mul]
  group

lemma lightWigner_one (P : lightCone) : lightWigner 1 P = 1 := by
  apply Subtype.ext
  change lightWignerSL 1 P = 1
  simp [lightWignerSL, lightSMul_one]

/-! ## The induced representation of helicity `h/2` -/

/-- The character `A ↦ phase(A)^h` of the massless little group. For the matrix
`diag(e^{iθ}, e^{-iθ})` (a rotation by `2θ` of the transverse plane) it is `e^{ihθ}`, so `h`
corresponds to helicity `h/2`. -/
noncomputable def helChar (h : ℤ) : MulAction.stabilizer SL2C (lightMom 1) →* Circle :=
  (zpowGroupHom h).comp phase

lemma helChar_apply (h : ℤ) (A : MulAction.stabilizer SL2C (lightMom 1)) :
    helChar h A = phase A ^ h := rfl

/-- The operator `ψ ↦ (P ↦ χ_h(W(A, A⁻¹ P)) ψ(A⁻¹ P))`. -/
noncomputable def lightInducedOp (h : ℤ) (A : SL2C) :
    (lightCone → ℂ) →ₗ[ℂ] (lightCone → ℂ) where
  toFun ψ P := ((helChar h (lightWigner A (lightSMul A⁻¹ P)) : Circle) : ℂ) * ψ (lightSMul A⁻¹ P)
  map_add' ψ φ := by
    funext P
    simp [mul_add]
  map_smul' c ψ := by
    funext P
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **The pointwise induced representation of `SL(2,ℂ)` on the light cone from the character
`phase^h` of the massless little group** (helicity `h/2`):
`(U(A) ψ)(P) = χ_h(W(A, A⁻¹ P)) ψ(A⁻¹ P)`. -/
noncomputable def lightInducedRep (h : ℤ) : Representation ℂ SL2C (lightCone → ℂ) where
  toFun A := lightInducedOp h A
  map_one' := by
    ext ψ P
    simp [lightInducedOp, lightSMul_one, lightWigner_one]
  map_mul' A B := by
    ext ψ P
    have h1 : lightSMul (A * B)⁻¹ P = lightSMul B⁻¹ (lightSMul A⁻¹ P) := by
      rw [_root_.mul_inv_rev, lightSMul_mul]
    have h2 : lightWigner (A * B) (lightSMul B⁻¹ (lightSMul A⁻¹ P)) =
        lightWigner A (lightSMul A⁻¹ P) *
          lightWigner B (lightSMul B⁻¹ (lightSMul A⁻¹ P)) := by
      rw [lightWigner_mul, lightSMul_inv_smul]
    simp only [Module.End.mul_apply, lightInducedOp, LinearMap.coe_mk, AddHom.coe_mk, h1, h2,
      map_mul, Circle.coe_mul, mul_assoc]

lemma lightInducedRep_apply (h : ℤ) (A : SL2C) (ψ : lightCone → ℂ) (P : lightCone) :
    lightInducedRep h A ψ P =
      ((helChar h (lightWigner A (lightSMul A⁻¹ P)) : Circle) : ℂ) * ψ (lightSMul A⁻¹ P) := rfl

end Lightlike.Lorentz.Poincare

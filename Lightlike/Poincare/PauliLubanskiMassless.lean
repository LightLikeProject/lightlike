import Lightlike.Poincare.PauliLubanskiGenerators
import Lightlike.Poincare.LightCone

/-!
# The Pauli–Lubanski operator of a massless induced representation, from the generators

For the massless helicity representation `helicityAct n` on wave functions on the light cone (helicity `h = n/2`)
the Lorentz generators `M_{νρ}` are the pointwise derivatives `d/dt (U(γ_{νρ}(t)) ψ)(P)` along curves `γ_{νρ}` in
`SL(2,ℂ)` with velocities `lorGen ν ρ`, on wave functions differentiable at `P` in the chart of the spatial momentum.
At a momentum `P` with `P₀₀ > 0` (every point of the cone except the negative `z`-axis) the derivative is

* the helicity phase `i n (helCoef P X) ψ(P)`, where `helCoef P X = Im X₀₀ + Im(X₀₁ P₁₀)/P₀₀`
  (`hasDerivAt_helicityAct_curve`), plus
* the derivative of `ψ` along the moved momentum `−(X P + P Xᴴ)`.

For the Pauli–Lubanski velocity `X^μ_P` (`plGen`) the moved momentum is zero (`plGen_fix`) and the helicity
coefficient is `p^μ/2` (`helCoef_plGen`, from the explicit entries of `plGen` and `det P = 0`), so
`W^μ = ½ ε^{μνρσ} p_σ M_{νρ}` acts as `i h p^μ`, `h = n/2` (`hasDerivAt_pauliLubanski_massless`,
`hasDerivAt_pauliLubanski_massless_lorCurve`): the massless Pauli–Lubanski relation `W = h P` from the full
generators, not only at the level of the little group.

**Scope.** On the chart `P₀₀ > 0` of the light cone, which has full invariant measure. The standard lift `coneLift`
has no continuous extension through the negative `z`-axis (`P₀₀ = 0`, where it jumps to its second branch), so the
pointwise derivative is not available there for this choice of section; a model with a smooth section on the second
chart differs from this one by a phase function.

Supporting lemmas; no catalogue entry.
-/

noncomputable section

open Matrix Complex Lightlike.Lorentz

namespace Lightlike.Poincare

/-- the helicity velocity coefficient -/
lemma plGen_helicity (p0 : ℝ) (p : Fin 3 → ℝ) (hn : p0 ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2)
    (hα : 0 < p0 + p 2) (μ : Fin 4) :
    ((plGen p0 p μ) 0 0).im + (((plGen p0 p μ) 0 1) * (momH p0 p) 1 0).im / (p0 + p 2) =
      (![p0, p 0, p 1, p 2] μ) / 2 := by
  have hne : p0 + p 2 ≠ 0 := hα.ne'
  fin_cases μ <;> simp [plGen, pauliM, momH] <;> field_simp <;> nlinarith [hn]


/-- the `(0,0)` entry of the Wigner element of the massless induced action, in the chart `α > 0` -/
lemma wigner00 (P Q : LightCone) (A : SL2C) (hPQ : A • Q = P) (hP : 0 < alphaC P.1) (hQ : 0 < alphaC Q.1) :
    ((wignerG coneLift A Q : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * ((Real.sqrt (alphaC Q.1 / 2) : ℝ) : ℂ) +
        (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (starRingEnd ℂ (Q.1 0 1) /
          (2 * ((Real.sqrt (alphaC Q.1 / 2) : ℝ) : ℂ)))) / ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) := by
  have h1 : coneLift (A • Q) = coneLift P := by rw [hPQ]
  unfold wignerG
  rw [h1]
  have hsP : ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by linarith)).ne'
  have hLP : ((coneLift P)⁻¹ : SL2C).1 = !![1 / ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ), 0;
      -(starRingEnd ℂ (P.1 0 1) / (2 * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ))), ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp only [coneLift, coneLiftMat, hP, if_true, Matrix.adjugate_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hLQ : (coneLift Q : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = ((Real.sqrt (alphaC Q.1 / 2) : ℝ) : ℂ) ∧
      (coneLift Q : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = starRingEnd ℂ (Q.1 0 1) /
        (2 * ((Real.sqrt (alphaC Q.1 / 2) : ℝ) : ℂ)) := by
    simp [coneLift, coneLiftMat, hQ]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hLP, hLQ.1, hLQ.2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  simp
  field_simp


/-- algebra of the derivative of the helicity phase factor -/
lemma helicity_phase_deriv (X P : Matrix (Fin 2) (Fin 2) ℂ) (hh : P.IsHermitian) (hα : 0 < (P 0 0).re) :
    let α := (P 0 0).re
    let a := Real.sqrt (α / 2)
    let a' := (-(X * P + P * Xᴴ) 0 0).re / 2 / (2 * a)
    (X 0 0 * (a : ℂ) + (a' : ℂ) + X 0 1 * (starRingEnd ℂ (P 0 1) / (2 * (a : ℂ)))) / (a : ℂ) =
      Complex.I * (((X 0 0).im + (X 0 1 * P 1 0).im / α : ℝ) : ℂ) := by
  intro α a a'
  have hapos : 0 < a := Real.sqrt_pos.2 (by linarith)
  have ha2 : a * a = α / 2 := Real.mul_self_sqrt (by linarith)
  have hP10 : P 1 0 = starRingEnd ℂ (P 0 1) := (hh.apply 1 0).symm
  have hP00 : P 0 0 = (α : ℂ) := by
    have h := hh.apply 0 0
    apply Complex.ext
    · simp [α]
    · have := congrArg Complex.im h
      simp at this ⊢
      linarith
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast hapos.ne'
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hXP : ((X * P + P * Xᴴ) 0 0).re = 2 * α * (X 0 0).re + 2 * (X 0 1 * P 1 0).re := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hP00, hP10,
      Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, star_def]
    ring
  have ha' : a' = -((α * (X 0 0).re + (X 0 1 * P 1 0).re) / (2 * a)) := by
    simp only [a', Complex.neg_re, hXP]
    field_simp
  have hP01 : starRingEnd ℂ (P 0 1) = P 1 0 := hP10.symm
  rw [ha', hP01]
  have h2a : (2 : ℂ) * (a : ℂ) * (a : ℂ) = (α : ℂ) := by
    have : ((a * a : ℝ) : ℂ) = ((α / 2 : ℝ) : ℂ) := by rw [ha2]
    push_cast at this
    linear_combination 2 * this
  have e1 : X 0 0 = ((X 0 0).re : ℂ) + ((X 0 0).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have e2 : X 0 1 * P 1 0 = ((X 0 1 * P 1 0).re : ℂ) + ((X 0 1 * P 1 0).im : ℂ) * Complex.I :=
    (Complex.re_add_im _).symm
  have e3 : X 0 1 * (P 1 0 / (2 * (a : ℂ))) = (X 0 1 * P 1 0) / (2 * (a : ℂ)) := by ring
  rw [e3]
  have hαa : (α : ℂ) = 2 * (a : ℂ) * (a : ℂ) := h2a.symm
  push_cast
  generalize (X 0 1 * P 1 0).re = u at e2 ⊢
  generalize (X 0 1 * P 1 0).im = v at e2 ⊢
  generalize (X 0 0).re = x at e1 ⊢
  generalize (X 0 0).im = y at e1 ⊢
  rw [e2]
  rw [e1]
  rw [hαa]
  field_simp
  ring


/-- The helicity coefficient of a velocity `X` at the momentum `P`: `Im X₀₀ + Im(X₀₁ P₁₀)/P₀₀`. -/
def helCoef (P X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (X 0 0).im + (X 0 1 * P 1 0).im / (P 0 0).re

/-- The helicity action at a point is the helicity phase times the wave function at the moved point. -/
lemma helicityAct_apply (n : ℤ) (A : SL2C) (ψ : LightCone → ℂ) (P : LightCone) :
    helicityAct n A ψ P =
      ((wignerG coneLift A (A⁻¹ • P) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ n * ψ (A⁻¹ • P) := by
  simp [helicityAct, inducedActG, helicityChar, wignerStab]

/-- **The generator of the helicity representation in the chart `P₀₀ > 0`.** Along a curve `γ` through `1` with
velocity `X`, the derivative of `t ↦ (U(γ(t)) ψ)(P)` at `0` is `i n (helCoef P X) ψ(P)` (the helicity phase) plus the
derivative of `ψ` along the moved momentum. -/
theorem hasDerivAt_helicityAct_curve (n : ℤ) {γ : ℝ → SL2C} {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : IsCurveAt γ X) (P : LightCone) (hP : 0 < alphaC P.1) {ψ : LightCone → ℂ} {φ : (Fin 3 → ℝ) → ℂ}
    {φ' : (Fin 3 → ℝ) →L[ℝ] ℂ} (hψ : ∀ Q : LightCone, ψ Q = φ (coordV Q.1))
    (hd : HasFDerivAt φ φ' (coordV P.1)) :
    HasDerivAt (fun t => helicityAct n (γ t) ψ P)
      (Complex.I * ((n : ℂ) * (helCoef P.1 X : ℂ)) * ψ P + φ' (coordV (moveVel P.1 X))) 0 := by
  have hγ0 : γ 0 = 1 := Subtype.ext (hγ.zero.trans Matrix.SpecialLinearGroup.coe_one.symm)
  set Q : ℝ → LightCone := fun t => (γ t)⁻¹ • P with hQdef
  have hQ : ∀ t, (Q t).1 = actP (γ t)⁻¹ P.1 := fun t => rfl
  have hQ0 : Q 0 = P := by simp [hQdef, hγ0]
  have hc : ∀ i j, HasDerivAt (fun t => (Q t).1 i j) (moveVel P.1 X i j) 0 := fun i j => by
    simpa only [hQ, moveVel, Matrix.neg_apply] using hasDerivAt_actP_inv hγ P.1 i j
  -- positivity of the (0,0) entry near 0
  have hcont : ContinuousAt (fun t => alphaC (Q t).1) 0 :=
    (Complex.continuous_re.continuousAt).comp (hc 0 0).continuousAt
  have hev : ∀ᶠ t in nhds (0 : ℝ), 0 < alphaC (Q t).1 := by
    have h0 : 0 < alphaC (Q 0).1 := by rw [hQ0]; exact hP
    exact hcont.eventually (lt_mem_nhds h0)
  have hPpos : 0 < Real.sqrt (alphaC P.1 / 2) := Real.sqrt_pos.2 (by linarith)
  have hPc : ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  -- the phase factor as a function of `t`
  set aQ : ℝ → ℝ := fun t => Real.sqrt (alphaC (Q t).1 / 2) with haQ
  set z : ℝ → ℂ := fun t => (((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (aQ t : ℂ) +
      ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * ((Q t).1 1 0 / (2 * (aQ t : ℂ)))) /
        ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) with hz
  have hfun : (fun t => helicityAct n (γ t) ψ P) =ᶠ[nhds 0] fun t => z t ^ n * φ (coordV (Q t).1) := by
    filter_upwards [hev] with t ht
    rw [helicityAct_apply, hψ]
    have hPQ : (γ t) • Q t = P := smul_inv_smul _ _
    have := wigner00 P (Q t) (γ t) hPQ hP ht
    change ((wignerG coneLift (γ t) (Q t) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ n * _ = _
    rw [this, ← cone_offdiag (Q t).2]
  -- derivatives of the pieces
  have hα : HasDerivAt (fun t => alphaC (Q t).1) ((moveVel P.1 X 0 0).re) 0 := hasDerivAt_re (hc 0 0)
  have hα0 : alphaC (Q 0).1 = alphaC P.1 := by rw [hQ0]
  have haQ' : HasDerivAt aQ ((moveVel P.1 X 0 0).re / 2 / (2 * Real.sqrt (alphaC P.1 / 2))) 0 := by
    have h1 := (hα.div_const 2).sqrt (by rw [hα0]; linarith)
    rw [hα0] at h1
    exact h1
  have haQC : HasDerivAt (fun t => (aQ t : ℂ))
      (((moveVel P.1 X 0 0).re / 2 / (2 * Real.sqrt (alphaC P.1 / 2)) : ℝ) : ℂ) 0 := haQ'.ofReal_comp
  have haQ0 : aQ 0 = Real.sqrt (alphaC P.1 / 2) := by simp only [haQ, hα0]
  have haQ0c : ((aQ 0 : ℝ) : ℂ) ≠ 0 := by rw [haQ0]; exact hPc
  have hg00 : (((γ 0 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := hγ.zero
  have hnum : HasDerivAt (fun t => ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (aQ t : ℂ) +
      ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * ((Q t).1 1 0 / (2 * (aQ t : ℂ))))
      (X 0 0 * (aQ 0 : ℂ) + ((γ 0 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
          (((moveVel P.1 X 0 0).re / 2 / (2 * Real.sqrt (alphaC P.1 / 2)) : ℝ) : ℂ) +
        (X 0 1 * ((Q 0).1 1 0 / (2 * (aQ 0 : ℂ))) +
          ((γ 0 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (((moveVel P.1 X 1 0) * (2 * (aQ 0 : ℂ)) -
            (Q 0).1 1 0 * (2 * (((moveVel P.1 X 0 0).re / 2 / (2 * Real.sqrt (alphaC P.1 / 2)) : ℝ) : ℂ))) /
              (2 * (aQ 0 : ℂ)) ^ 2))) 0 := by
    refine ((hγ.deriv 0 0).mul haQC).add ((hγ.deriv 0 1).mul ((hc 1 0).div ?_ ?_))
    · exact (haQC.const_mul 2)
    · simpa using haQ0c
  have hz' : HasDerivAt z (Complex.I * (helCoef P.1 X : ℂ)) 0 := by
    have h1 := hnum.div_const ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)
    refine h1.congr_deriv ?_
    rw [hg00, hQ0, haQ0]
    have key := helicity_phase_deriv X P.1 P.2.1.1 hP
    simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), zero_mul, add_zero, one_mul]
    rw [← cone_offdiag P.2] at key
    simp only [moveVel] at key ⊢
    simpa [helCoef, alphaC] using key
  have hz0 : z 0 = 1 := by
    simp only [hz, hg00, hQ0, haQ0, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      one_mul, zero_mul, add_zero]
    exact div_self hPc
  have hd' : HasFDerivAt φ φ' (coordV (Q 0).1) := by rw [hQ0]; exact hd
  have hφ : HasDerivAt (fun t => φ (coordV (Q t).1)) (φ' (coordV (moveVel P.1 X))) 0 :=
    hd'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_coordV hc)
  have hzn : HasDerivAt (fun t => z t ^ n) (Complex.I * (helCoef P.1 X : ℂ) * (n : ℂ)) 0 := by
    have h1 := (hasDerivAt_zpow n (z 0) (Or.inl (by rw [hz0]; exact one_ne_zero))).scomp (0 : ℝ) hz'
    refine h1.congr_deriv ?_
    rw [hz0]; simp [smul_eq_mul]
  refine (((hzn.mul hφ).congr_deriv ?_).congr_of_eventuallyEq hfun)
  rw [hz0, hQ0, hψ P]
  simp
  left
  ring

/-! ## The Pauli–Lubanski combination -/

lemma helCoef_add (P X Y : Matrix (Fin 2) (Fin 2) ℂ) : helCoef P (X + Y) = helCoef P X + helCoef P Y := by
  simp only [helCoef, Matrix.add_apply, Complex.add_im, add_mul]
  ring

lemma helCoef_smul (P X : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) : helCoef P ((r : ℂ) • X) = r * helCoef P X := by
  simp only [helCoef, Matrix.smul_apply, smul_eq_mul, mul_assoc, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  ring

/-- The generator with velocity `X` applied to a chart-smooth helicity wave function at `P`. -/
def genValM (n : ℤ) (P : LightCone) (ψ : LightCone → ℂ) (φ' : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Complex.I * ((n : ℂ) * (helCoef P.1 X : ℂ)) * ψ P + φ' (coordV (moveVel P.1 X))

lemma genValM_add (n : ℤ) (P : LightCone) (ψ : LightCone → ℂ) (φ' : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (X Y : Matrix (Fin 2) (Fin 2) ℂ) : genValM n P ψ φ' (X + Y) = genValM n P ψ φ' X + genValM n P ψ φ' Y := by
  simp only [genValM, helCoef_add, moveVel_add, coordV_add, map_add]
  push_cast
  ring

lemma genValM_smul (n : ℤ) (P : LightCone) (ψ : LightCone → ℂ) (φ' : (Fin 3 → ℝ) →L[ℝ] ℂ) (r : ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : genValM n P ψ φ' ((r : ℂ) • X) = (r : ℂ) * genValM n P ψ φ' X := by
  simp only [genValM, helCoef_smul, moveVel_smul, coordV_smul, map_smul]
  push_cast
  rw [Complex.real_smul]
  ring

lemma genValM_zero (n : ℤ) (P : LightCone) (ψ : LightCone → ℂ) (φ' : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    genValM n P ψ φ' 0 = 0 := by
  have := genValM_smul n P ψ φ' 0 0
  simpa using this

/-- The generators as an additive map. -/
def genAddM (n : ℤ) (P : LightCone) (ψ : LightCone → ℂ) (φ' : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →+ ℂ where
  toFun := genValM n P ψ φ'
  map_zero' := genValM_zero n P ψ φ'
  map_add' := genValM_add n P ψ φ'

lemma genAddM_apply (n : ℤ) (P : LightCone) (ψ : LightCone → ℂ) (φ' : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : genAddM n P ψ φ' X = genValM n P ψ φ' X := rfl

/-- The momentum components `(p⁰, p¹, p², p³)` of a Hermitian matrix. -/
def momVec (P : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ := ![coord0 P, coordV P 0, coordV P 1, coordV P 2]

lemma helCoef_momH (p0 : ℝ) (p : Fin 3 → ℝ) (hn : p0 ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) (hα : 0 < p0 + p 2)
    (μ : Fin 4) : helCoef (momH p0 p) (plGen p0 p μ) = (![p0, p 0, p 1, p 2] μ) / 2 := by
  have h00 : (momH p0 p 0 0).re = p0 + p 2 := by simp [momH]
  simp only [helCoef, h00]
  exact plGen_helicity p0 p hn hα μ

lemma helCoef_plGen (P : LightCone) (hP : 0 < alphaC P.1) (μ : Fin 4) :
    helCoef P.1 (plGen (coord0 P.1) (coordV P.1) μ) = momVec P.1 μ / 2 := by
  have hH := momH_coords P.2.1.1
  have hdet := det_momH (coord0 P.1) (coordV P.1)
  rw [hH, P.2.2.1] at hdet
  have hn : coord0 P.1 ^ 2 = coordV P.1 0 ^ 2 + coordV P.1 1 ^ 2 + coordV P.1 2 ^ 2 := by
    have h0 : (0 : ℝ) = coord0 P.1 ^ 2 - coordV P.1 0 ^ 2 - coordV P.1 1 ^ 2 - coordV P.1 2 ^ 2 := by
      exact_mod_cast hdet
    linarith
  have hα : alphaC P.1 = coord0 P.1 + coordV P.1 2 := by
    conv_lhs => rw [alphaC, ← hH]
    simp [momH]
  have := helCoef_momH (coord0 P.1) (coordV P.1) hn (by rw [← hα]; exact hP) μ
  rw [hH] at this
  exact this

/-- **`W^μ = ½ ε^{μνρσ} p_σ M_{νρ}` acts at `P` of the light cone by `i n p^μ / 2`**: the combination of the
generators has no orbital part, and the helicity phase gives `i h p^μ` with `h = n/2`. -/
theorem plComb_genValM (n : ℤ) (P : LightCone) (hP : 0 < alphaC P.1) (ψ : LightCone → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] ℂ) (μ : Fin 4) :
    ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) *
        genValM n P ψ φ' (lorGen ν ρ) = Complex.I * ((n : ℂ) * ((momVec P.1 μ / 2 : ℝ) : ℂ)) * ψ P := by
  have hsum : genValM n P ψ φ' (plComb (coord0 P.1) (coordV P.1) μ) =
      ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) *
        genValM n P ψ φ' (lorGen ν ρ) := by
    rw [← genAddM_apply, plComb]
    simp only [map_sum, genAddM_apply]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
    exact genValM_smul n P ψ φ' _ _
  rw [← hsum, plComb_eq]
  have hfix : moveVel P.1 (plGen (coord0 P.1) (coordV P.1) μ) = 0 := by
    have := plGen_fix (coord0 P.1) (coordV P.1) μ
    rw [momH_coords P.2.1.1] at this
    rw [moveVel, this, neg_zero]
  simp only [genValM, hfix, coordV_zero, map_zero, add_zero, helCoef_plGen P hP μ]

/-- **`W^μ = ½ ε^{μνρσ} p_σ M_{νρ} = i h p^μ` on the massless helicity representation, from the generators.**
For curves `γ_{νρ}` in `SL(2,ℂ)` through `1` with the Lorentz generators `M_{νρ}` as velocities, and a wave function
`ψ` on the light cone that is differentiable at `P` (with `P₀₀ > 0`) in the chart of the spatial momentum, the
derivative of `t ↦ ½ ε^{μνρσ} p_σ (U(γ_{νρ}(t)) ψ)(P)` at `0` is `i (n/2) p^μ ψ(P)`: the helicity `h = n/2` times `p^μ`. -/
theorem hasDerivAt_pauliLubanski_massless (n : ℤ) (γ : Fin 4 → Fin 4 → ℝ → SL2C)
    (hγ : ∀ ν ρ, IsCurveAt (γ ν ρ) (lorGen ν ρ)) (P : LightCone) (hP : 0 < alphaC P.1) {ψ : LightCone → ℂ}
    {φ : (Fin 3 → ℝ) → ℂ} {φ' : (Fin 3 → ℝ) →L[ℝ] ℂ} (hψ : ∀ Q : LightCone, ψ Q = φ (coordV Q.1))
    (hd : HasFDerivAt φ φ' (coordV P.1)) (μ : Fin 4) :
    HasDerivAt (fun t => ∑ ν, ∑ ρ, ∑ σ,
        ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) * helicityAct n (γ ν ρ t) ψ P)
      (Complex.I * ((n : ℂ) * ((momVec P.1 μ / 2 : ℝ) : ℂ)) * ψ P) 0 := by
  rw [← plComb_genValM n P hP ψ φ' μ]
  refine HasDerivAt.fun_sum fun ν _ => HasDerivAt.fun_sum fun ρ _ => HasDerivAt.fun_sum fun σ _ => ?_
  exact (hasDerivAt_helicityAct_curve n (hγ ν ρ) P hP hψ hd).const_mul _

/-- The same along the chosen curves `lorCurve ν ρ` of the Lorentz generators. -/
theorem hasDerivAt_pauliLubanski_massless_lorCurve (n : ℤ) (P : LightCone) (hP : 0 < alphaC P.1)
    {ψ : LightCone → ℂ} {φ : (Fin 3 → ℝ) → ℂ} {φ' : (Fin 3 → ℝ) →L[ℝ] ℂ}
    (hψ : ∀ Q : LightCone, ψ Q = φ (coordV Q.1)) (hd : HasFDerivAt φ φ' (coordV P.1)) (μ : Fin 4) :
    HasDerivAt (fun t => ∑ ν, ∑ ρ, ∑ σ,
        ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) * helicityAct n (lorCurve ν ρ t) ψ P)
      (Complex.I * ((n : ℂ) * ((momVec P.1 μ / 2 : ℝ) : ℂ)) * ψ P) 0 :=
  hasDerivAt_pauliLubanski_massless n lorCurve isCurveAt_lorCurve P hP hψ hd μ

end Lightlike.Poincare

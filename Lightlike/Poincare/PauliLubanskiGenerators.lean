import Lightlike.Poincare.PauliLubanskiCasimir
import Lightlike.Poincare.PauliLubanskiMassive
import Lightlike.Poincare.GeneratorCurves
import Lightlike.Poincare.LiftDerivative
import Lightlike.Poincare.LorentzCurves

/-!
# The Pauli–Lubanski operator `W^μ = ½ ε^{μνρσ} M_{νρ} P_σ` of a massive induced representation

Let `U` be the induced massive representation of `SL(2,ℂ)` on the spin representation `spinRep n`, and let `ψ` be a
wave function that is differentiable at the momentum `P` in the chart of the mass shell by the spatial momentum
(`ChartSmoothAt`). For every curve `γ` in `SL(2,ℂ)` through `1` with velocity `X`, the derivative of
`t ↦ (U(γ(t)) ψ)(P)` at `0` is `M_X ψ(P) = dSpin(w_X) ψ(P) + dφ(−(X P + P Xᴴ))` (`hasDerivAt_inducedAct_curve`),
with the Wigner velocity `w_X = L(P)⁻¹ X L(P) + L(P)⁻¹ dL(P)[−(X P + P Xᴴ)]` (spin part) and the derivative of the
wave function along the moved momentum (orbital part). It depends on the curve only through `X` and is real-linear in
`X`.

For the Lorentz generators `M_{νρ}` (`lorGen`, fixed by their action on momenta, `lorGen_act`), the combination
`W^μ ψ(P) = ½ ε^{μνρσ} p_σ (M_{νρ} ψ)(P)` is `M_{X^μ_P} ψ(P)` for the Pauli–Lubanski combination `X^μ_P`
(`plComb_eq`), which fixes `P` (`plGen_fix`): the orbital part and the derivative of the lift drop out, and
`W^μ ψ(P) = dSpin(L(P)⁻¹ X^μ_P L(P)) ψ(P)` (`plComb_genVal`, `hasDerivAt_pauliLubanski`). With the Hermitian
operators `i W^μ`, the Fierz identity gives `W_μ W^μ = −m² s(s+1)` at every momentum (`pauliLubanski_sq_generators`).

**Difference from the source (kind: weaker).** The generators `M_{νρ}` are the pointwise derivatives
`d/dt (U(γ(t)) ψ)(P)` along curves with velocity `M_{νρ}` on wave functions differentiable at `P` in the chart of the
mass shell, not the Stone generators of the unitary one-parameter groups on `L²`. The product `P_σ` acts by
multiplication, written to the left of `M_{νρ}` (`p_σ M_{νρ}`); the two orders agree because the commutator
`[M_{νρ}, P_σ]` is symmetric under the contraction with `ε^{μνρσ}`, which is not formalised. The square
`W_μ W^μ` is the product of the matrices by which `W^μ` acts at `P`.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §1.2 (page 4 of v2: `W^μ = ½ ε^{μνρσ} M_{νρ} P_σ`), §5.2, equation (54) (page 39 of v2:
  the square of the Pauli–Lubanski vector on a massive field of spin `s` is `m² s(s+1)`, signature `(−,+,+,+)`).
-/

noncomputable section

open Matrix Lightlike.Lorentz Lightlike.SU2 Complex

namespace Lightlike.Poincare

/-! ## The chart of the mass shell -/

lemma coordV_add (A B : Matrix (Fin 2) (Fin 2) ℂ) : coordV (A + B) = coordV A + coordV B := by
  funext i; fin_cases i <;> simp [coordV] <;> ring

lemma coordV_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : coordV ((r : ℂ) • A) = r • coordV A := by
  funext i; fin_cases i <;> simp [coordV] <;> ring

lemma coordV_zero : coordV (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  funext i; fin_cases i <;> simp [coordV]

lemma hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun t => (f t).im) f'.im 0 :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

/-- The chart coordinates along a curve of matrices. -/
lemma hasDerivAt_coordV {c : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {c' : Matrix (Fin 2) (Fin 2) ℂ}
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (c' i j) 0) :
    HasDerivAt (fun t => coordV (c t)) (coordV c') 0 := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [coordV] using hasDerivAt_re (hc 1 0)
  · simpa [coordV] using hasDerivAt_im (hc 1 0)
  · simpa [coordV] using hasDerivAt_re (((hc 0 0).sub (hc 1 1)).div_const 2)

/-- A wave function on the mass shell that is differentiable at `P` in the chart by the spatial momentum:
`ψ(Q) = φ(q)` for every `Q`, with `φ` differentiable at `p` with derivative `φ'`. -/
structure ChartSmoothAt {m : ℝ} {n : ℕ} (ψ : MassShell m → Fin (n + 1) → ℂ) (P : MassShell m)
    (φ : (Fin 3 → ℝ) → Fin (n + 1) → ℂ) (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) : Prop where
  eq : ∀ Q : MassShell m, ψ Q = φ (coordV Q.1)
  deriv : HasFDerivAt φ φ' (coordV P.1)

/-! ## The generators -/

/-- The velocity of the momentum `P` under the curve `γ(t)⁻¹`, `−(X P + P Xᴴ)`. -/
def moveVel (P X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := -(X * P + P * Xᴴ)

lemma moveVel_add (P X Y : Matrix (Fin 2) (Fin 2) ℂ) : moveVel P (X + Y) = moveVel P X + moveVel P Y := by
  simp only [moveVel, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel

lemma moveVel_smul (P X : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) :
    moveVel P ((r : ℂ) • X) = (r : ℂ) • moveVel P X := by
  simp only [moveVel, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, smul_neg]

/-- The velocity of the Wigner rotation at `P` under a curve with velocity `X`. -/
def wigVel {m : ℝ} (hm : 0 < m) (P : MassShell m) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * X * (stdLift hm P : Matrix (Fin 2) (Fin 2) ℂ) +
    (((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * dStdLift m P.1 (moveVel P.1 X)

/-- The generator with velocity `X` applied to a chart-smooth wave function at `P`. -/
def genVal {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) (X : Matrix (Fin 2) (Fin 2) ℂ) : Fin (n + 1) → ℂ :=
  dSpin n (wigVel hm P X) *ᵥ ψ P + φ' (coordV (moveVel P.1 X))

lemma genVal_add {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    genVal hm n P ψ φ' (X + Y) = genVal hm n P ψ φ' X + genVal hm n P ψ φ' Y := by
  simp only [genVal, wigVel, moveVel_add, dStdLift_add, Matrix.mul_add, Matrix.add_mul, dSpin_add,
    Matrix.add_mulVec, coordV_add, map_add]
  abel

lemma wigVel_smul {m : ℝ} (hm : 0 < m) (P : MassShell m) (r : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    wigVel hm P ((r : ℂ) • X) = (r : ℂ) • wigVel hm P X := by
  simp only [wigVel, moveVel_smul, dStdLift_smul, Matrix.mul_smul, Matrix.smul_mul, smul_add]

lemma genVal_smul {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) (r : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    genVal hm n P ψ φ' ((r : ℂ) • X) = (r : ℂ) • genVal hm n P ψ φ' X := by
  rw [genVal, genVal, wigVel_smul, dSpin_smul, Matrix.smul_mulVec, moveVel_smul, coordV_smul, map_smul,
    smul_add]
  simp only [Complex.coe_smul]

lemma genVal_zero {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) : genVal hm n P ψ φ' 0 = 0 := by
  have := genVal_smul hm n P ψ φ' 0 0
  simpa using this

/-- The generators as an additive map. -/
def genAdd {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) : Matrix (Fin 2) (Fin 2) ℂ →+ (Fin (n + 1) → ℂ) where
  toFun := genVal hm n P ψ φ'
  map_zero' := genVal_zero hm n P ψ φ'
  map_add' := genVal_add hm n P ψ φ'

lemma genAdd_apply {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    genAdd hm n P ψ φ' X = genVal hm n P ψ φ' X := rfl

/-- **The generators of the induced representation.** Along every curve `γ` in `SL(2,ℂ)` through `1` with velocity
`X`, the derivative of `t ↦ (U(γ(t)) ψ)(P)` at `0` is `genVal X`: the spin part `dSpin(w_X) ψ(P)` plus the derivative
of `ψ` along the moved momentum. -/
theorem hasDerivAt_inducedAct_curve {m : ℝ} (hm : 0 < m) (n : ℕ) {γ : ℝ → SL2C}
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hγ : IsCurveAt γ X) (P : MassShell m) {ψ : MassShell m → Fin (n + 1) → ℂ}
    {φ : (Fin 3 → ℝ) → Fin (n + 1) → ℂ} {φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)}
    (hψ : ChartSmoothAt ψ P φ φ') :
    HasDerivAt (fun t => inducedAct hm (spinRep n) (γ t) ψ P) (genVal hm n P ψ φ' X) 0 := by
  have hγ0 : γ 0 = 1 := Subtype.ext (hγ.zero.trans Matrix.SpecialLinearGroup.coe_one.symm)
  have hc0 : shellAct (γ 0)⁻¹ P = P := by rw [hγ0, inv_one, shellAct_one]
  -- the moved momentum
  have hc : ∀ i j, HasDerivAt (fun t => (shellAct (γ t)⁻¹ P).1 i j) (moveVel P.1 X i j) 0 :=
    fun i j => hasDerivAt_actP_inv hγ P.1 i j
  -- the standard lift along it
  have hL : ∀ i j, HasDerivAt (fun t => stdLiftMat m (shellAct (γ t)⁻¹ P).1 i j)
      (dStdLift m P.1 (moveVel P.1 X) i j) 0 := by
    intro i j
    have := hasDerivAt_stdLiftMat hm (c := fun t => (shellAct (γ t)⁻¹ P).1) hc (shellAct (γ 0)⁻¹ P).2 i j
    simp only [hc0] at this
    exact this
  -- the Wigner rotation along the curve
  have hPP : ∀ t, shellAct (γ t) (shellAct (γ t)⁻¹ P) = P := fun t => by
    rw [← shellAct_mul, mul_inv_cancel, shellAct_one]
  have hw : ∀ t, ((wignerSU2 hm (γ t) (shellAct (γ t)⁻¹ P) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
        stdLiftMat m (shellAct (γ t)⁻¹ P).1 := fun t => by
    simp only [wignerSU2, wigner, hPP t, Matrix.SpecialLinearGroup.coe_mul]
    rfl
  have h1 : ∀ a b, HasDerivAt (fun t => ((((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) a b)
      (((((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * X) a b) 0 := by
    intro a b
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hγ.deriv k b).const_mul _
  have hw' : ∀ i j, HasDerivAt (fun t => ((((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * stdLiftMat m (shellAct (γ t)⁻¹ P).1) i j)
      (wigVel hm P X i j) 0 := by
    intro i j
    refine (hasDerivAt_mul_entry h1 hL i j).congr_deriv ?_
    simp only [hγ.zero, Matrix.mul_one, hc0, wigVel]
    rfl
  have hw0 : (((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * ((γ 0 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
      stdLiftMat m (shellAct (γ 0)⁻¹ P).1 = 1 := by
    rw [hγ.zero, Matrix.mul_one, hc0]
    change (((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((stdLift hm P : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hspin : ∀ k l, HasDerivAt (fun t => spinMat n ((((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * stdLiftMat m (shellAct (γ t)⁻¹ P).1) k l)
      (dSpin n (wigVel hm P X) k l) 0 :=
    fun k l => hasDerivAt_spinMat hw0 hw' k l
  -- the orbital part
  have hd : HasFDerivAt φ φ' (coordV (shellAct (γ 0)⁻¹ P).1) := by rw [hc0]; exact hψ.deriv
  have hφ : HasDerivAt (fun t => φ (coordV (shellAct (γ t)⁻¹ P).1)) (φ' (coordV (moveVel P.1 X))) 0 :=
    hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_coordV hc)
  -- assemble
  have hfun : (fun t => inducedAct hm (spinRep n) (γ t) ψ P) = fun t => fun k => ∑ l,
      spinMat n ((((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
        stdLiftMat m (shellAct (γ t)⁻¹ P).1) k l * φ (coordV (shellAct (γ t)⁻¹ P).1) l := by
    funext t k
    rw [← hw t]
    simp only [inducedAct, Matrix.mulVec, dotProduct, hψ.eq, spinRep_apply]
  rw [hfun]
  refine hasDerivAt_pi.2 fun k => ?_
  refine (HasDerivAt.fun_sum fun l _ => (hspin k l).mul (hasDerivAt_pi.1 hφ l)).congr_deriv ?_
  rw [hw0, spinMat_one, hc0, ← hψ.eq P]
  simp only [genVal, Finset.sum_add_distrib, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ## The Pauli–Lubanski operator -/

/-- The matrix by which the Pauli–Lubanski operator `W^μ` acts at `P`: `dSpin(L(P)⁻¹ X^μ_P L(P))`. -/
def plMat {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (μ : Fin 4) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  dSpin n ((((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * plGen (coord0 P.1) (coordV P.1) μ *
    (stdLift hm P : Matrix (Fin 2) (Fin 2) ℂ))

lemma momH_coords_shell {m : ℝ} (P : MassShell m) : momH (coord0 P.1) (coordV P.1) = P.1 :=
  momH_coords P.2.1.1

/-- **`W^μ = ½ ε^{μνρσ} p_σ M_{νρ}` acts at `P` by `plMat`**: the combination of the generators has no orbital part. -/
theorem plComb_genVal {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ)
    (φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)) (μ : Fin 4) :
    ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) •
        genVal hm n P ψ φ' (lorGen ν ρ) = plMat hm n P μ *ᵥ ψ P := by
  have hsum : genVal hm n P ψ φ' (plComb (coord0 P.1) (coordV P.1) μ) =
      ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) •
        genVal hm n P ψ φ' (lorGen ν ρ) := by
    rw [← genAdd_apply, plComb]
    simp only [map_sum, genAdd_apply, genVal_smul]
  rw [← hsum, plComb_eq]
  have hfix : moveVel P.1 (plGen (coord0 P.1) (coordV P.1) μ) = 0 := by
    have := plGen_fix (coord0 P.1) (coordV P.1) μ
    rw [momH_coords_shell] at this
    rw [moveVel, this, neg_zero]
  simp only [genVal, wigVel, hfix, dStdLift_zero, Matrix.mul_zero, add_zero, coordV_zero, map_zero]
  rfl

/-- **The Pauli–Lubanski operator from the generators.** For any curves `γ_{νρ}` in `SL(2,ℂ)` through `1` with the
Lorentz generators `M_{νρ}` as velocities, and `ψ` differentiable at `P` in the chart,
`½ ε^{μνρσ} p_σ (M_{νρ} ψ)(P) = dSpin(L(P)⁻¹ X^μ_P L(P)) ψ(P)`, where `(M_{νρ} ψ)(P)` is the derivative of
`t ↦ (U(γ_{νρ}(t)) ψ)(P)` at `0`. -/
theorem hasDerivAt_pauliLubanski {m : ℝ} (hm : 0 < m) (n : ℕ) (γ : Fin 4 → Fin 4 → ℝ → SL2C)
    (hγ : ∀ ν ρ, IsCurveAt (γ ν ρ) (lorGen ν ρ)) (P : MassShell m) {ψ : MassShell m → Fin (n + 1) → ℂ}
    {φ : (Fin 3 → ℝ) → Fin (n + 1) → ℂ} {φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)}
    (hψ : ChartSmoothAt ψ P φ φ') (μ : Fin 4) :
    HasDerivAt (fun t => ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) •
        inducedAct hm (spinRep n) (γ ν ρ t) ψ P) (plMat hm n P μ *ᵥ ψ P) 0 := by
  rw [← plComb_genVal hm n P ψ φ' μ]
  refine HasDerivAt.fun_sum fun ν _ => HasDerivAt.fun_sum fun ρ _ => HasDerivAt.fun_sum fun σ _ => ?_
  exact (hasDerivAt_inducedAct_curve hm n (hγ ν ρ) P hψ).const_smul
    (((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ))

/-- **`W^μ = ½ ε^{μνρσ} M_{νρ} P_σ` along the chosen curves** `lorCurve ν ρ` of the Lorentz generators. -/
theorem hasDerivAt_pauliLubanski_lorCurve {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m)
    {ψ : MassShell m → Fin (n + 1) → ℂ} {φ : (Fin 3 → ℝ) → Fin (n + 1) → ℂ}
    {φ' : (Fin 3 → ℝ) →L[ℝ] (Fin (n + 1) → ℂ)} (hψ : ChartSmoothAt ψ P φ φ') (μ : Fin 4) :
    HasDerivAt (fun t => ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ * pLow (coord0 P.1) (coordV P.1) σ : ℝ) : ℂ) •
        inducedAct hm (spinRep n) (lorCurve ν ρ t) ψ P) (plMat hm n P μ *ᵥ ψ P) 0 :=
  hasDerivAt_pauliLubanski hm n lorCurve isCurveAt_lorCurve P hψ μ

/-- The Minkowski square of the coordinates of a momentum on the mass shell is `m²`. -/
lemma coords_sq {m : ℝ} (P : MassShell m) :
    coord0 P.1 ^ 2 - coordV P.1 0 ^ 2 - coordV P.1 1 ^ 2 - coordV P.1 2 ^ 2 = m ^ 2 := by
  have h := P.2.2
  rw [← momH_coords_shell P, det_momH] at h
  exact_mod_cast h

/-- **`W_μ W^μ = −m² s(s+1)` from the generators**: with the Hermitian Pauli–Lubanski operators `i W^μ` acting at `P`
by `i plMat`, the Minkowski square is `−m² s(s+1)` (signature `(+,−,−,−)`, `s = n/2`), at every momentum `P`. -/
theorem pauliLubanski_sq_generators {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) :
    ∑ μ, minkW μ • ((Complex.I • plMat hm n P μ) * (Complex.I • plMat hm n P μ)) =
      (-(m : ℂ) ^ 2 * ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1))) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have hNL : (((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((stdLift hm P : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : ∑ μ, minkW μ • (plMat hm n P μ * plMat hm n P μ) =
      ((m : ℂ) ^ 2 * ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1))) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
    casimir_plGen_conj m n (coord0 P.1) (coordV P.1) (coords_sq P) _ _ hNL
  have hμ : ∀ μ, minkW μ • ((Complex.I • plMat hm n P μ) * (Complex.I • plMat hm n P μ)) =
      -(minkW μ • (plMat hm n P μ * plMat hm n P μ)) := fun μ => by
    rw [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul, smul_neg]
  rw [Finset.sum_congr rfl fun μ _ => hμ μ, Finset.sum_neg_distrib, key, ← neg_smul, neg_mul]

/-- `W_μ W^μ ψ(P) = −m² s(s+1) ψ(P)`. -/
theorem pauliLubanski_sq_apply {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ) :
    (∑ μ, minkW μ • ((Complex.I • plMat hm n P μ) * (Complex.I • plMat hm n P μ))) *ᵥ ψ P =
      (-(m : ℂ) ^ 2 * ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1))) • ψ P := by
  rw [pauliLubanski_sq_generators, Matrix.smul_mulVec, Matrix.one_mulVec]

end Lightlike.Poincare

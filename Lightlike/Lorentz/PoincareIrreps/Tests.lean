module

public import Lightlike.Lorentz.PoincareIrreps.Momentum
public import Lightlike.Lorentz.PoincareIrreps.Wigner
public import Lightlike.Lorentz.PoincareIrreps.Massless
public import Lightlike.Lorentz.PoincareIrreps.Measure
public import Lightlike.Lorentz.PoincareIrreps.Poincare
public import Lightlike.Lorentz.PoincareIrreps.LightPoincare
public import Lightlike.Lorentz.PoincareIrreps.SpinCasimir
public import Lightlike.Lorentz.PoincareIrreps.PauliLubanski
public import Lightlike.Lorentz.PoincareIrreps.MasslessPL
public import Lightlike.Lorentz.PoincareIrreps.Fibre
public import Lightlike.Lorentz.PoincareIrreps.MasslessMeasure
public import Lightlike.Lorentz.PoincareIrreps.Classification

/-!
# Checks for the little groups of the Poincaré group (HA6, first piece)

* the three standard momenta have `p² = m²`, `0`, `-m²` in the signature `(+,−,−,−)`;
* the Lorentz action preserves `p²`;
* the massive little group is `SU(2)`, and the spin-1/2 representation of `SU(2)` has two states
  per momentum;
* the massless little group fixes `E·diag(1,0)`, and a boost does not (a wrong-group control);
* the tachyonic little group is not compact.
-/

@[expose] public section

open Lightlike.Lorentz Lightlike.Lorentz.Poincare

/-- A massive momentum has `p² = m²`. -/
example (m : ℝ) : (restMom m).1.det = ((m ^ 2 : ℝ) : ℂ) := by
  rw [restMom_eq_ofVec, det_ofVec]; simp

/-- A massless momentum has `p² = 0`. -/
example (E : ℝ) : (lightMom E).1.det = 0 := by
  rw [lightMom_eq_ofVec, det_ofVec]; simp

/-- A tachyonic momentum has `p² = -m²`. -/
example (m : ℝ) : (tachMom m).1.det = ((-m ^ 2 : ℝ) : ℂ) := by
  rw [tachMom_eq_ofVec, det_ofVec]; simp

/-- The Lorentz action keeps a massive momentum on its mass shell. -/
example (A : SL2C) (m : ℝ) : (A • restMom m).1.det = ((m ^ 2 : ℝ) : ℂ) := by
  rw [det_smul, restMom_eq_ofVec, det_ofVec]; simp

/-- Massive spin `1/2`: `SU(2)` acts on a space of dimension `2` at each momentum. -/
example : Fintype.card (Fin (1 + 1)) = 2 := by simp

/-- Control: the massive little group is `SU(2)`, so the identity is in it and a hyperbolic boost
`diag(2, 1/2)` is not. -/
example : SL2C.diagSL 2 two_ne_zero ∉ MulAction.stabilizer SL2C (restMom 1) := by
  rw [mem_stabilizer_restMom_iff one_ne_zero]
  intro h
  have := congrFun (congrFun h 0) 0
  simp [SL2C.diagSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, map_ofNat] at this
  norm_num at this

/-- Control: a boost does not fix a massless momentum, since its `A₁₀` is non-zero. -/
example : SL2C.lower 1 ∉ MulAction.stabilizer SL2C (lightMom 1) := by
  rw [mem_stabilizer_lightMom one_ne_zero]
  intro h
  simpa [SL2C.lower] using h.1

/-- The phase of a massless little group element composed with a translation `upper t` is trivial. -/
example (t : ℂ) (h : SL2C.upper t ∈ MulAction.stabilizer SL2C (lightMom 1)) :
    phase ⟨SL2C.upper t, h⟩ = 1 := by
  apply Subtype.ext
  simp [coe_phase, SL2C.upper]

/-- The tachyonic little group is not compact. -/
example : ¬ IsCompact ((MulAction.stabilizer SL2C (tachMom 1) : Subgroup SL2C) : Set SL2C) :=
  not_isCompact_stabilizer_tachMom 1

/-- The standard boost carries the rest momentum to `P`. -/
example {m : ℝ} (hm : 0 < m) (P : massShell m) : boost hm P • restMom m = P.1 :=
  boost_smul_rest hm P

/-- The Wigner rotation is a cocycle in `SU(2)`. -/
example {m : ℝ} (hm : 0 < m) (A B : SL2C) (P : massShell m) :
    wignerSU2 hm (A * B) P = wignerSU2 hm A (shellSMul hm B P) * wignerSU2 hm B P :=
  wignerSU2_mul hm A B P

/-- The induced action is a representation: the identity acts trivially. -/
example {m : ℝ} (hm : 0 < m) (n : ℕ) : inducedRep hm n 1 = 1 := (inducedRep hm n).map_one

#print axioms wignerSU2_mul
#print axioms inducedRep

/-- The light cone is exactly the orbit of `lightMom 1`. -/
example (P : Herm2) : P ∈ lightCone ↔ ∃ A : SL2C, A • lightMom 1 = P :=
  ⟨exists_smul_lightMom, by rintro ⟨A, rfl⟩; exact smul_lightMom_mem_lightCone A⟩

/-- The massless induced action is a representation, in every helicity. -/
example (h : ℤ) (A B : SL2C) : lightInducedRep h (A * B) = lightInducedRep h A * lightInducedRep h B :=
  (lightInducedRep h).map_mul A B

/-- Helicity `0`: the induced representation is the trivial-character one. -/
example (A : SL2C) (ψ : lightCone → ℂ) (P : lightCone) :
    lightInducedRep 0 A ψ P = ψ (lightSMul A⁻¹ P) := by
  simp [lightInducedRep_apply, helChar_apply]

#print axioms lightInducedRep
#print axioms exists_smul_lightMom

/-- The invariant measure on the mass shell is `SL(2,ℂ)`-invariant. -/
example {m : ℝ} (hm : 0 < m) (A : SL2C) :
    (shellMeasure hm).map (shellSMul hm A) = shellMeasure hm :=
  map_shellSMul_shellMeasure hm A

/-- Control: the fibre norm of a vector is non-negative and zero only for `0` (spin 1/2). -/
example (v : Fin 2 → ℂ) (h : fibreNormSq v = 0) : v = 0 := by
  funext i
  have h0 : ∀ j ∈ Finset.univ, ‖v j‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h
  simpa using h0 i (Finset.mem_univ i)

#print axioms map_shellSMul_shellMeasure
#print axioms lintegral_inducedRep_normSq

/-- Control: the Minkowski product of `(1,0,0,0)` with `(2,1,0,0)` is `2` (signature `(+,−,−,−)`). -/
example : pairing (ofVec ![1, 0, 0, 0]) (ofVec ![2, 1, 0, 0]) = 2 := by
  rw [pairing_ofVec]
  simp

/-- Control: the rest momentum has `P² = m²`. -/
example : (restMom 3).1.det = ((9 : ℝ) : ℂ) := by
  simp [restMom]
  norm_num

#print axioms pairing_smul
#print axioms inducedRep_translate
#print axioms poincareRep
#print axioms lightInducedRep_translate
#print axioms lightPoincareRep
#print axioms spin_casimir
#print axioms opE_spin_highest
#print axioms spinJ_casimir
#print axioms pauliLubanski_square
#print axioms momentum_dot_pauliLubanski
#print axioms ofVec_coord

/-- Control: massive spin-`1/2` (`n = 1`), `m = 2`: `W² = −m² s(s+1) = −3` in the rest frame. -/
example : pauliLubanski 2 1 1 0 * pauliLubanski 2 1 1 0 - pauliLubanski 2 1 1 1 * pauliLubanski 2 1 1 1 -
    pauliLubanski 2 1 1 2 * pauliLubanski 2 1 1 2 - pauliLubanski 2 1 1 3 * pauliLubanski 2 1 1 3 =
    (-3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauliLubanski_square]
  congr 1
  push_cast
  norm_num

/-- Control: for spin `1/2` (`n = 1`) the Casimir `4 s (s+1)` is `3`. -/
example : sl2Casimir (SU2Spin.opH (SU2Spin.σ 1)) (SU2Spin.opE (SU2Spin.σ 1))
    (SU2Spin.opF (SU2Spin.σ 1)) = (3 : ℂ) • 1 := by
  rw [spin_casimir]; norm_num

/-- Control: the translation `T(0)` on the light cone is the identity. -/
example (ψ : lightCone → ℂ) : lightTranslateOp 0 ψ = ψ := by
  funext P
  simp [lightTranslateOp, pairing_zero_right]

#print axioms lightPL_eq
#print axioms lightPL_square
#print axioms helChar_rotZ
#print axioms coord_smul_eq_sum

/-- Massive spin `1/2` tied to `inducedRep`: two states per momentum (a control: spin 1 gives 3). -/
example (m : ℝ) (P : massShell m) : Module.finrank ℂ (atMomentum m 1 P) = 2 :=
  finrank_atMomentum_spinHalf m P

example (m : ℝ) (P : massShell m) : Module.finrank ℂ (atMomentum m 2 P) = 3 :=
  finrank_atMomentum m 2 P

#print axioms finrank_atMomentum
#print axioms inducedRep_apply_smul
#print axioms inducedRep_atMomentum

/-- Little-group irreducibility of the spin-1/2 fibre, and the summary theorems apply. -/
example {m : ℝ} (hm : 0 < m) (W : Submodule ℂ (massShell m → Fin 2 → ℂ))
    (hWle : W ≤ atMomentum m 1 (restShell hm))
    (hinv : ∀ g : Lightlike.SU2, ∀ ψ ∈ W, inducedRep hm 1 (SL2C.ofSU2 g) ψ ∈ W) :
    W = ⊥ ∨ W = atMomentum m 1 (restShell hm) :=
  atRest_irreducible hm 1 W hWle hinv

example {m : ℝ} (hm : 0 < m) (P : massShell m) : P.1.1.det = ((m ^ 2 : ℝ) : ℂ) :=
  (wigner_massive m hm 1).2.2.1 P

example (h : ℤ) (A : SL2C) (μ : Fin 4) :
    lightPL h A μ = (lightHelicity h : ℂ) * (coord (A • lightMom 1) μ : ℝ) :=
  (wigner_massless h).2.2.1 A μ

#print axioms atRest_irreducible
#print axioms wignerSU2_ofSU2
#print axioms wigner_massive
#print axioms wigner_massless

/-- The spinor map `z z†` is equivariant, and the light-cone measure is nonzero and invariant. -/
example (A : SL2C) (z : Spinor) :
    spinProj (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) z) = A • spinProj z := spinProj_mulVec A z

example (A : SL2C) : coneMeasure.map (lightSMul A) = coneMeasure := map_lightSMul_coneMeasure A

#print axioms map_spinorMap_volume
#print axioms map_lightSMul_coneMeasure
#print axioms coneMeasure_ne_zero
#print axioms lintegral_lightInducedRep_normSq

/-- Control: helicity `1` (`h = 2`) at the standard momentum: `W = P` at `A = 1`, component `3`. -/
example : lightPL 2 1 3 = ((coord (lightMom 1) 3 : ℝ) : ℂ) := by
  rw [lightPL_eq, one_smul]
  simp [lightHelicity]

/-- Control: the character of the rotation by `2π` is `(-1)^h`: for `h = 1` it is `-1`
(a spinor), i.e. `e^{i (1/2) 2π} = -1`. -/
example : ((helChar 1 ⟨rotZ (2 * Real.pi), rotZ_mem_stabilizer _⟩ : Circle) : ℂ) = -1 := by
  rw [helChar_rotZ]
  have : Complex.I * (((lightHelicity 1 * (2 * Real.pi) : ℝ)) : ℂ) = Real.pi * Complex.I := by
    simp [lightHelicity]; ring
  rw [this, Complex.exp_pi_mul_I]

/-- Control: the translations of the massless little group carry no helicity. -/
example (h : ℤ) (t : ℂ) : helChar h ⟨SL2C.upper t, upper_mem_stabilizer t⟩ = 1 :=
  helChar_upper h t _

/-- The massive little group is compact. -/
example : IsCompact ((MulAction.stabilizer SL2C (restMom 1) : Subgroup SL2C) : Set SL2C) :=
  isCompact_stabilizer_restMom one_ne_zero

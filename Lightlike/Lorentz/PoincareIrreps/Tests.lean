module

public import Lightlike.Lorentz.PoincareIrreps.Momentum
public import Lightlike.Lorentz.PoincareIrreps.Wigner
public import Lightlike.Lorentz.PoincareIrreps.Massless

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

/-- The massive little group is compact. -/
example : IsCompact ((MulAction.stabilizer SL2C (restMom 1) : Subgroup SL2C) : Set SL2C) :=
  isCompact_stabilizer_restMom one_ne_zero

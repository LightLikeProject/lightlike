module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Massless
public import Lightlike.Lorentz.PoincareIrreps.PauliLubanski

/-!
# Massless representations: the Pauli–Lubanski vector is `W = h P`

HA6 (Wigner's classification), tenth piece. For the massless induced representation
`lightInducedRep h` (helicity `h/2`) the Pauli–Lubanski vector at the standard momentum
`k = (1/2, 0, 0, 1/2)` has the components `W^μ = (E J_z, T₁, T₂, E J_z)` with `E = 1/2`, where

* `J_z` is the generator of the rotations `rotZ α` about the `z`-axis in the little group; its
  eigenvalue is the helicity: `helChar_rotZ` shows that the character of `rotZ α` is `e^{i (h/2) α}`;
* `T₁, T₂` are the combinations of the null rotations (translations of `ISO(2)`) that appear in the
  transverse components of `W`; they act by `0` because the character is trivial on the kernel of
  `phase` (`helChar_upper`).

So `W(k) = (h/2) · k` (`stdLightPL`), and at the momentum `A·k` the vector is transported by the
Lorentz matrix `L(A)` (`lightPL`). The main result is **`lightPL_eq`**: `W^μ = (h/2) P^μ` for
every `A`, so the massless Pauli–Lubanski vector is the helicity times the momentum, in particular
it depends only on the momentum `P = A·k`.

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

/-! ## Linearity of the Lorentz action on components -/

lemma ofVec_coe_sum (v : Fin 4 → ℝ) :
    (ofVec v).1 = ∑ ν : Fin 4, (v ν : ℂ) • (unitVec ν).1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (apply Complex.ext <;> simp [ofVec, unitVec, Fin.sum_univ_four, sub_eq_add_neg])

/-- The components of `A·X` are the `L(A)`-combination of the components of `X`:
`(A X)^μ = Σ_ν L(A)^μ{}_ν X^ν`, with `L(A)^μ{}_ν = coord (A • eν) μ`. -/
theorem coord_smul_eq_sum (A : SL2C) (X : Herm2) (μ : Fin 4) :
    coord (A • X) μ = ∑ ν : Fin 4, coord X ν * coord (A • unitVec ν) μ := by
  have h1 : X.1 = ∑ ν : Fin 4, ((coord X ν : ℝ) : ℂ) • (unitVec ν).1 := by
    conv_lhs => rw [← ofVec_coord X]
    exact ofVec_coe_sum _
  have h2 : (A • X : Herm2).1 =
      ∑ ν : Fin 4, ((coord X ν : ℝ) : ℂ) • (A • unitVec ν : Herm2).1 := by
    rw [coe_smul, h1, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [coe_smul]
    simp
  fin_cases μ <;>
    simp [coord, h2, Matrix.sum_apply, Fin.sum_univ_four] <;> ring

lemma coord_ofVec (v : Fin 4 → ℝ) : coord (ofVec v) = v := by
  funext μ
  fin_cases μ <;> simp [coord, ofVec]

/-! ## Helicity as the eigenvalue of the rotation generator -/

/-- The rotation about the `z`-axis through the angle `α`, `diag(e^{iα/2}, e^{-iα/2})`. -/
noncomputable def rotZ (α : ℝ) : SL2C :=
  SL2C.mk (Complex.exp (Complex.I * (α / 2 : ℝ))) 0 0 (Complex.exp (-(Complex.I * (α / 2 : ℝ))))
    (by rw [← Complex.exp_add]; simp)

lemma rotZ_mem_stabilizer (α : ℝ) : rotZ α ∈ MulAction.stabilizer SL2C (lightMom 1) := by
  rw [mem_stabilizer_lightMom one_ne_zero]
  refine ⟨by simp [rotZ, SL2C.mk], ?_⟩
  simp only [rotZ, SL2C.coe_mk]
  simp [Complex.norm_exp]

/-- `rotZ` is a one-parameter group: its generator `J_z` is well defined. -/
lemma rotZ_add (α β : ℝ) : rotZ (α + β) = rotZ α * rotZ β := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, rotZ, SL2C.coe_mk]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add] <;>
    (congr 1; ring)

/-- The helicity `h/2` of the representation `lightInducedRep h`. -/
noncomputable def lightHelicity (h : ℤ) : ℝ := (h : ℝ) / 2

/-- **The helicity is the `J_z`-eigenvalue**: the character `helChar h` of the rotation through `α`
is `e^{i (h/2) α}`. -/
theorem helChar_rotZ (h : ℤ) (α : ℝ) :
    ((helChar h ⟨rotZ α, rotZ_mem_stabilizer α⟩ : Circle) : ℂ) =
      Complex.exp (Complex.I * ((lightHelicity h * α : ℝ) : ℂ)) := by
  rw [helChar_apply, Circle.coe_zpow, coe_phase]
  change (rotZ α 0 0) ^ h = _
  have : rotZ α 0 0 = Complex.exp (Complex.I * (α / 2 : ℝ)) := by simp [rotZ, SL2C.mk]
  rw [this, ← Complex.exp_int_mul]
  congr 1
  simp [lightHelicity]
  ring

/-- **The character is trivial on the translations** of the little group: the transverse
Pauli–Lubanski generators act by `0`. -/
theorem helChar_upper (h : ℤ) (t : ℂ)
    (ht : SL2C.upper t ∈ MulAction.stabilizer SL2C (lightMom 1)) :
    helChar h ⟨SL2C.upper t, ht⟩ = 1 := by
  have : phase ⟨SL2C.upper t, ht⟩ = 1 := by
    apply Subtype.ext
    simp [coe_phase, SL2C.upper]
  rw [helChar_apply, this, _root_.one_zpow]

lemma upper_mem_stabilizer (t : ℂ) : SL2C.upper t ∈ MulAction.stabilizer SL2C (lightMom 1) := by
  rw [mem_stabilizer_lightMom one_ne_zero]
  simp [SL2C.upper, SL2C.mk]

/-! ## The Pauli–Lubanski vector -/

/-- The Pauli–Lubanski vector at the standard momentum `k = (1/2,0,0,1/2)`:
`(E J_z, T₁, T₂, E J_z)` with `E = 1/2`, `J_z = h/2` (`helChar_rotZ`) and `T₁ = T₂ = 0`
(`helChar_upper`). -/
noncomputable def stdLightPL (h : ℤ) : Fin 4 → ℂ :=
  ![((1 / 2 : ℝ) : ℂ) * (lightHelicity h : ℂ), 0, 0, ((1 / 2 : ℝ) : ℂ) * (lightHelicity h : ℂ)]

/-- The Pauli–Lubanski vector at the momentum `A·k`: `W^μ = Σ_ν L(A)^μ{}_ν w^ν`. -/
noncomputable def lightPL (h : ℤ) (A : SL2C) (μ : Fin 4) : ℂ :=
  ∑ ν : Fin 4, stdLightPL h ν * (coord (A • unitVec ν) μ : ℝ)

/-- **Massless finite-helicity states satisfy `W = h P`** (helicity `h/2`):
`W^μ = (h/2) P^μ` for the momentum `P = A·k`, `k = (1/2,0,0,1/2)`. -/
theorem lightPL_eq (h : ℤ) (A : SL2C) (μ : Fin 4) :
    lightPL h A μ = (lightHelicity h : ℂ) * (coord (A • lightMom 1) μ : ℝ) := by
  rw [coord_smul_eq_sum, lightMom_eq_ofVec, coord_ofVec]
  simp only [lightPL, stdLightPL, Fin.sum_univ_four]
  simp
  ring

/-- `W` depends only on the momentum: two group elements with the same momentum give the same `W`. -/
theorem lightPL_eq_of_smul_eq (h : ℤ) {A B : SL2C} (hAB : A • lightMom 1 = B • lightMom 1)
    (μ : Fin 4) : lightPL h A μ = lightPL h B μ := by
  rw [lightPL_eq, lightPL_eq, hAB]

/-- For `P` on the light cone, `W(P) = (h/2) P` with `W` computed at the standard boost of `P`. -/
theorem lightPL_boost (h : ℤ) (P : lightCone) (μ : Fin 4) :
    lightPL h (lightBoost P) μ = (lightHelicity h : ℂ) * (coord P.1 μ : ℝ) := by
  rw [lightPL_eq, lightBoost_smul]

/-- The massless Pauli–Lubanski vector is null and orthogonal to `P`: `W² = 0` (the massless
analogue of `W² = −m² s(s+1)`). -/
theorem lightPL_square (h : ℤ) (A : SL2C) :
    lightPL h A 0 * lightPL h A 0 - lightPL h A 1 * lightPL h A 1 -
      lightPL h A 2 * lightPL h A 2 - lightPL h A 3 * lightPL h A 3 = 0 := by
  simp only [lightPL_eq]
  have hd := mink_coord_smul A (lightMom 1) (lightMom 1)
  have hp : pairing (lightMom 1) (lightMom 1) = 0 := by
    rw [lightMom_eq_ofVec, pairing_ofVec]; simp
  rw [hp] at hd
  simp only [mink] at hd
  have : ((coord (A • lightMom 1) 0 * coord (A • lightMom 1) 0 -
      coord (A • lightMom 1) 1 * coord (A • lightMom 1) 1 -
      coord (A • lightMom 1) 2 * coord (A • lightMom 1) 2 -
      coord (A • lightMom 1) 3 * coord (A • lightMom 1) 3 : ℝ) : ℂ) = 0 := by
    rw [hd]; simp
  push_cast at this
  linear_combination (lightHelicity h : ℂ) ^ 2 * this

end Lightlike.Lorentz.Poincare

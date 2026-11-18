import Lightlike.Gauge.Constraints

/-!
# Basic facts on constrained Hamiltonian systems

The bracket matrix of the constraints is antisymmetric, the Dirac bracket is antisymmetric and kills the
constraints, an even number of constraints is second class, and for a linear symplectic action the reduced
tangent space at a zero of the moment map has dimension `dim E - 2 dim (orbit)` (Marsden-Weinstein, without
quotient manifolds). Definitions in `Lightlike/Gauge/Constraints.lean`.

## References

* M. Henneaux and C. Teitelboim, *Quantization of Gauge Systems*, Princeton University Press (1992), Chapter 1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer (2001), the
  Marsden-Weinstein-Meyer theorem.
-/
open ClassicalMechanics InnerProductSpace Matrix
namespace Lightlike.Gauge
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {m : ℕ}

/-- The bracket matrix of the constraints is antisymmetric. -/
theorem bracketMatrix_transpose (φ : Fin m → X → X → ℝ) (p q : X) :
    (bracketMatrix φ p q)ᵀ = -bracketMatrix φ p q := by
  ext a b
  simp [bracketMatrix, poissonBracket_antisymm (φ b) (φ a) p q]

/-- The Dirac bracket of any observable with a constraint vanishes where the bracket matrix is nonsingular:
`{f, φ_c}_D = 0` (Henneaux-Teitelboim, Chapter 1). -/
theorem diracBracket_constraint (φ : Fin m → X → X → ℝ) (f : X → X → ℝ) (c : Fin m) (p q : X)
    (hC : (bracketMatrix φ p q).det ≠ 0) :
    diracBracket φ f (φ c) p q = 0 := by
  have hu : IsUnit (bracketMatrix φ p q).det := isUnit_iff_ne_zero.mpr hC
  have h1 : (bracketMatrix φ p q)⁻¹ * bracketMatrix φ p q = 1 := Matrix.nonsing_inv_mul _ hu
  unfold diracBracket
  have : ∀ a, ∑ b, (bracketMatrix φ p q)⁻¹ a b * poissonBracket (φ b) (φ c) p q
      = if a = c then 1 else 0 := by
    intro a
    have := congrFun (congrFun h1 a) c
    simpa [Matrix.mul_apply, bracketMatrix, Matrix.one_apply] using this
  have e : ∀ a, ∑ b, poissonBracket f (φ a) p q * (bracketMatrix φ p q)⁻¹ a b * poissonBracket (φ b) (φ c) p q
      = poissonBracket f (φ a) p q * (if a = c then 1 else 0) := by
    intro a
    rw [← this a, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e]
  simp

/-- The Dirac bracket is antisymmetric. -/
theorem diracBracket_antisymm (φ : Fin m → X → X → ℝ) (f g : X → X → ℝ) (p q : X) :
    diracBracket φ f g p q = -diracBracket φ g f p q := by
  have hT : ((bracketMatrix φ p q)⁻¹)ᵀ = -(bracketMatrix φ p q)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, bracketMatrix_transpose]
    by_cases hu : IsUnit (bracketMatrix φ p q).det
    · have h1 : (bracketMatrix φ p q) * (bracketMatrix φ p q)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
      refine Matrix.inv_eq_right_inv ?_
      rw [neg_mul_neg, h1]
    · have hu' : ¬ IsUnit (-bracketMatrix φ p q).det := by
        rw [Matrix.det_neg]
        intro h
        exact hu (by simpa using (IsUnit.mul_iff.mp h).2)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.nonsing_inv_apply_not_isUnit _ hu']
      simp
  have hij : ∀ a b, (bracketMatrix φ p q)⁻¹ b a = -(bracketMatrix φ p q)⁻¹ a b := by
    intro a b
    have := congrFun (congrFun hT a) b
    simpa using this
  have hS : ∑ a, ∑ b, poissonBracket g (φ a) p q * (bracketMatrix φ p q)⁻¹ a b * poissonBracket (φ b) f p q
      = -∑ a, ∑ b, poissonBracket f (φ a) p q * (bracketMatrix φ p q)⁻¹ a b * poissonBracket (φ b) g p q := by
    rw [← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hij a b, poissonBracket_antisymm g (φ b) p q, poissonBracket_antisymm (φ a) f p q]
    ring
  unfold diracBracket
  rw [hS, poissonBracket_antisymm f g p q]
  ring
/-- Second-class constraints come in an even number: an antisymmetric matrix of odd size is singular. -/
theorem even_of_isSecondClass (φ : Fin m → X → X → ℝ) (h : IsSecondClass φ)
    (hne : (constraintSet φ).Nonempty) : Even m := by
  obtain ⟨x, hx⟩ := hne
  have hd := h x hx
  by_contra hodd
  have hodd' : Odd m := Nat.not_even_iff_odd.mp hodd
  have h1 : (bracketMatrix φ x.1 x.2).det = (-1) ^ m * (bracketMatrix φ x.1 x.2).det := by
    conv_lhs => rw [← Matrix.det_transpose, bracketMatrix_transpose, Matrix.det_neg]
    simp
  rw [hodd'.neg_one_pow] at h1
  apply hd
  linarith
section Reduction

variable {E : Type} [AddCommGroup E] [Module ℝ E] {g : Type} [LieRing g] [LieAlgebra ℝ g]
  {σ : LinearMap.BilinForm ℝ E}

/-- The orbit directions and their `σ`-orthogonal have complementary dimensions in a finite-dimensional
symplectic space. -/
theorem finrank_orbit_add_momentTangent [FiniteDimensional ℝ E]
    (hσ : IsSymplecticForm σ) (ρ : AffineSymplecticAction σ g) (x : E) :
    Module.finrank ℝ (orbitDirections ρ x) + Module.finrank ℝ (momentTangent ρ x) =
      Module.finrank ℝ E := by
  have := LinearMap.BilinForm.finrank_orthogonal hσ.nondeg (orbitDirections ρ x)
  have h2 := Submodule.finrank_le (orbitDirections ρ x)
  unfold momentTangent
  omega

/-- The orbit through a zero of the moment map of a linear action is isotropic: its directions lie in the
level-set directions (Souriau (11.17 d) with zero cocycle). -/
theorem orbitDirections_le_momentTangent (hσ : IsSymplecticForm σ) (ρ : AffineSymplecticAction σ g)
    (hb : ρ.b = 0) (x : E) (hx : ∀ Z, ρ.moment x Z = 0) :
    orbitDirections ρ x ≤ momentTangent ρ x := by
  rintro v ⟨Z, rfl⟩
  rw [momentTangent, LinearMap.BilinForm.mem_orthogonal_iff]
  rintro w ⟨Z', rfl⟩
  change σ (ρ.A Z' x) (ρ.A Z x) = 0
  have h := ρ.sigma_vectorField_vectorField hσ Z' Z x
  simp only [AffineSymplecticAction.vectorField, hb, LinearMap.zero_apply, add_zero] at h
  rw [h, hx, AffineSymplecticAction.cocycle_eq_zero_of_linear ρ hb]
  simp

/-- The tangent space of the reduced space of a linear action at `x`: the level-set directions
modulo the orbit directions. -/
abbrev reducedTangent (ρ : AffineSymplecticAction σ g) (x : E) : Type :=
  momentTangent ρ x ⧸ Submodule.comap (momentTangent ρ x).subtype (orbitDirections ρ x)

/-- **Marsden-Weinstein reduction for a linear symplectic action, at the level of tangent spaces**: at a zero
of the moment map the reduced space has dimension `dim E - 2 dim (orbit)`. -/
theorem finrank_reducedTangent [FiniteDimensional ℝ E]
    (hσ : IsSymplecticForm σ) (ρ : AffineSymplecticAction σ g)
    (hb : ρ.b = 0) (x : E) (hx : ∀ Z, ρ.moment x Z = 0) :
    Module.finrank ℝ (reducedTangent ρ x) =
      Module.finrank ℝ E - 2 * Module.finrank ℝ (orbitDirections ρ x) := by
  have hle := orbitDirections_le_momentTangent hσ ρ hb x hx
  have h4 := finrank_orbit_add_momentTangent hσ ρ x
  have h1 := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (momentTangent ρ x).subtype (orbitDirections ρ x))
  have h2 : Module.finrank ℝ (Submodule.comap (momentTangent ρ x).subtype (orbitDirections ρ x))
      = Module.finrank ℝ (orbitDirections ρ x) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  unfold reducedTangent
  omega

end Reduction
end Lightlike.Gauge

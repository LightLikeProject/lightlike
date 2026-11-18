import Lightlike.Gauge.Constraints

/-!
# First-class constraints generate gauge directions

On Physlib's flat phase space `X × X` (Lightlike.Gauge.Constraints): the Hamiltonian vector field `X_g = (-∂_q g, ∂_p g)`
of an observable `g` has `df(X_g) = {f, g}`; so for a first-class set of constraints the Hamiltonian field of each
constraint is tangent to the constraint surface, and it lies in the kernel of the symplectic form restricted to the
tangent directions of the surface (the gauge directions). Infinitesimal statements only: the flows (gauge
transformations as one-parameter groups preserving the surface) are not covered here.

* `hamField`, `pairing_hamField`: the field and `df(X_g) = {f, g}`.
* `pairing_hamField_eq_zero_of_firstClass`: tangency to the surface for first-class constraints.
* `gradForm_hamField`, `gradForm_hamField_eq_zero`: `Ω(X_g, v) = dg(v)`, so `X_{φ_a}` is `Ω`-orthogonal to every vector
  tangent to the surface (annihilated by all `dφ_b`).
-/

open InnerProductSpace
open ClassicalMechanics

namespace Lightlike.Gauge

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {m : ℕ}

/-- The Hamiltonian vector field `X_g = (-∂_q g, ∂_p g)` of an observable `g` at `(p, q)`. -/
noncomputable def hamField (g : X → X → ℝ) (p q : X) : X × X :=
  (-(phaseGrad g p q).2, (phaseGrad g p q).1)

/-- **`df(X_g) = {f, g}`**. -/
theorem pairing_hamField (f g : X → X → ℝ) (p q : X) :
    pairing (phaseGrad f p q) (hamField g p q) = poissonBracket f g p q := by
  rw [poissonBracket_eq_gradForm]
  simp only [pairing, hamField, gradForm, LinearMap.mk₂_apply, inner_neg_right]
  ring

/-- **Tangency**: for first-class constraints the Hamiltonian field of each constraint is annihilated by all
the differentials `dφ_b` on the constraint surface, i.e. tangent to it. -/
theorem pairing_hamField_eq_zero_of_firstClass (φ : Fin m → X → X → ℝ) (hφ : IsFirstClass φ)
    {x : X × X} (hx : x ∈ constraintSet φ) (a b : Fin m) :
    pairing (phaseGrad (φ b) x.1 x.2) (hamField (φ a) x.1 x.2) = 0 := by
  rw [pairing_hamField]
  have := congrFun (congrFun (hφ x hx) b) a
  simpa [bracketMatrix] using this

/-- **`Ω (X_g, v) = dg (v)`**. -/
theorem gradForm_hamField (g : X → X → ℝ) (p q : X) (v : X × X) :
    gradForm (hamField g p q) v = pairing (phaseGrad g p q) v := by
  simp only [pairing, hamField, gradForm, LinearMap.mk₂_apply, inner_neg_left]
  ring

/-- **The gauge directions are in the kernel of the form on the surface's tangent space**: for a vector `v`
annihilated by every `dφ_b`, `Ω (X_{φ_a}, v) = 0`. -/
theorem gradForm_hamField_eq_zero (φ : Fin m → X → X → ℝ) (p q : X) (v : X × X)
    (hv : ∀ b, pairing (phaseGrad (φ b) p q) v = 0) (a : Fin m) :
    gradForm (hamField (φ a) p q) v = 0 := by
  rw [gradForm_hamField, hv a]

/-- **Non-vacuity**: a single constraint is first class (`{φ, φ} = 0`), so the tangency theorem applies to every
single constraint function. -/
theorem isFirstClass_single (φ : Fin 1 → X → X → ℝ) : IsFirstClass φ := by
  intro x _
  ext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha hb
  simp only [bracketMatrix, poissonBracket_eq_gradForm, Matrix.zero_apply]
  exact isSymplecticForm_gradForm.alt _

end Lightlike.Gauge

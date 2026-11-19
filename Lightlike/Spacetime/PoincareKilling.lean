import Lightlike.Spacetime.FlatConnection
import Lightlike.Spacetime.LieMetric

/-!
# Killing fields of Minkowski space: the Poincaré algebra (GE12 trust checks)

On `ℝⁿ` with the Minkowski metric `η` and the flat connection (its Levi-Civita connection), the affine fields
`affField A c : y ↦ A y + c` (`A` an endomorphism, `c` a vector) satisfy:

* `affField_killing_iff`: `affField A c` is Killing at every point iff `A` is `η`-skew,
  `η(A v, w) + η(v, A w) = 0` (translations `A = 0`, Lorentz generators);
* `not_isKillingAt_dilation`: the dilation `y ↦ y` is not Killing (`L_X η = 2 η ≠ 0`);
* `mlieBracket_affField`: `[affField A c, affField B d] = affField (B A - A B) (B c - A d)`, the Poincaré relations
  (`[P, P'] = 0`, `[M, P] = P`, `[M, M'] = M''`);
* `skew_comm_skew`: the commutator of two `η`-skew endomorphisms is `η`-skew, so the Killing affine fields are closed
  under the bracket.

**Limits.** That these affine fields are *all* the Killing fields of Minkowski space (so that there are `n(n+1)/2` of them)
is not proved. The trust check of the round 2-sphere (a rotation field is Killing, a dilation is not) is not in this file.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The affine vector field `y ↦ A y + c` of `ℝⁿ`. -/
def affField (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (c : Fin n → ℝ) :
    Π y : Fin n → ℝ, TangentSpace 𝓘(ℝ, Fin n → ℝ) y := fun y => A y + c

theorem fderiv_affField (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (c : Fin n → ℝ) (x : Fin n → ℝ) :
    fderiv ℝ ((affField A c : Π y : Fin n → ℝ, TangentSpace 𝓘(ℝ, Fin n → ℝ) y) : (Fin n → ℝ) → (Fin n → ℝ)) x = A := by
  have : HasFDerivAt (fun y : Fin n → ℝ => A y + c) A x := A.hasFDerivAt.add_const c
  exact this.fderiv

/-- **Affine fields are Killing iff the linear part is `η`-skew.** -/
theorem affField_killing_iff (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (c : Fin n → ℝ) (x : Fin n → ℝ) :
    IsKillingAt (flatConnection (Fin n → ℝ)) (minkowskiMetric n) (affField A c) x ↔
      ∀ v w : Fin n → ℝ, minkowskiForm n (A v) w + minkowskiForm n v (A w) = 0 := by
  unfold IsKillingAt
  simp only [flatConnection_apply, fderiv_affField]
  rfl

/-- **The dilation is not a Killing field** of Minkowski space (`n ≥ 1`). -/
theorem not_isKillingAt_dilation (x : Fin (n + 1) → ℝ) :
    ¬ IsKillingAt (flatConnection (Fin (n + 1) → ℝ)) (minkowskiMetric (n + 1))
      (affField (ContinuousLinearMap.id ℝ _) 0) x := by
  rw [affField_killing_iff]
  intro h
  have := h (Pi.single 0 1) (Pi.single 0 1)
  have h0 := minkowskiForm_single (n := n + 1) 0 0
  simp only [ContinuousLinearMap.id_apply, h0] at this
  simp [eta_apply, etaDiag] at this

/-- **The brackets of affine fields**: `[A y + c, B y + d] = (B A - A B) y + (B c - A d)`. -/
theorem mlieBracket_affField (A B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (c d : Fin n → ℝ) (x : Fin n → ℝ) :
    (mlieBracket 𝓘(ℝ, Fin n → ℝ) (affField A c) (affField B d) x : Fin n → ℝ) =
      affField (B * A - A * B) (B c - A d) x := by
  rw [mlieBracket_flat, fderiv_affField, fderiv_affField]
  simp [affField]
  abel

/-- **The commutator of two `η`-skew endomorphisms is `η`-skew.** -/
theorem skew_comm_skew {A B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hA : ∀ v w, minkowskiForm n (A v) w + minkowskiForm n v (A w) = 0)
    (hB : ∀ v w, minkowskiForm n (B v) w + minkowskiForm n v (B w) = 0) :
    ∀ v w, minkowskiForm n ((B * A - A * B) v) w + minkowskiForm n v ((B * A - A * B) w) = 0 := by
  intro v w
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub,
    ContinuousLinearMap.sub_apply]
  have a1 := hA (B v) w
  have a2 := hA v (B w)
  have b1 := hB (A v) w
  have b2 := hB v (A w)
  have a3 := hA w (B v)
  linarith [a1, a2, b1, b2, (minkowskiForm n).map_zero]

end Lightlike

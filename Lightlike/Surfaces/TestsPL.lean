import Lightlike.Surfaces.PLClassify
import Lightlike.Surfaces.Tests

/-!
# Checks for the classification up to PL homeomorphism

The kernel-checked surface certificates of `Tests.lean` are PL homeomorphic to their standard
models; the two tori are PL homeomorphic to each other and to the standard model with one handle;
and wrong models, the projective plane and the sphere against a torus, are rejected.
-/

open Finset Lightlike.PL Lightlike.PL.SComplex

namespace Lightlike.Surfaces

/-- **Known value: the projective plane.** `P6` is PL homeomorphic to `stdModel false 0`. -/
theorem P6_plHomeomorphic_model : PLHomeomorphic (closure P6) (closure (stdModel false 0)) := by
  obtain ⟨f, h⟩ := P6_model
  exact (PLHomeomorphic.of_stellarEquiv ((stellarEquiv_of_eqvGen_move2 h).2 isTri2_P6)).trans
    (plHomeomorphic_liftK f).symm

/-- **Known value: the two tori.** The 9-vertex torus and Möbius' 7-vertex torus are PL
homeomorphic, with no move between them given. -/
theorem T9_plHomeomorphic_T7 : PLHomeomorphic (closure T9) (closure T7) :=
  plHomeomorphic_of_invariants isSurface_T9 isSurface_T7
    (iff_of_true isOrientable_T9 isOrientable_T7) (by rw [euler2_T9, euler2_T7])

/-- **Wrong model: the projective plane is not a torus**, though both have a standard model. -/
theorem T7_not_plHomeomorphic_P6 : ¬ PLHomeomorphic (closure T7) (closure P6) := fun h =>
  not_isOrientable_P6 (((invariants_of_plHomeomorphic isSurface_T7 isSurface_P6 h).1).mp
    isOrientable_T7)

/-- **Wrong model: the sphere is not a torus**: the Euler characteristics `0` and `2` differ. -/
theorem T7_not_plHomeomorphic_sphere :
    ¬ PLHomeomorphic (closure T7) (closure (stdModel true 0)) := fun h => by
  have hS : IsSurface (stdModel true 0) := by
    simpa [liftK_refl] using isSurface_liftK_stdModel (Function.Embedding.refl ℕ) true 0
  have := (invariants_of_plHomeomorphic isSurface_T7 hS h).2
  rw [euler2_T7, euler2_stdModel_true] at this
  norm_num at this

/-- **The torus and the Klein bottle are different**: the same Euler characteristic, but
orientability tells them apart. -/
theorem torus_not_plHomeomorphic_klein :
    ¬ PLHomeomorphic (closure (stdModel true 1)) (closure (stdModel false 1)) := fun h => by
  have := stdModel_eq_of_plHomeomorphic h
  exact absurd this.1 (by decide)

end Lightlike.Surfaces

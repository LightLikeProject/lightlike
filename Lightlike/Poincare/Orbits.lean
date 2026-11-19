module

public import Lightlike.Poincare.StandardMomenta
public import Physlib.Relativity.LorentzGroup.Boosts.Generalized

/-!
# The mass shell is one orbit of the restricted Lorentz group

Signature `(+,−,−,−)`. For `m > 0` every momentum `p` with `p² = m²` and `p⁰ > 0` is the image of the rest
momentum `(m, 0, 0, 0)` under an orthochronous (in fact restricted) Lorentz transformation, namely the
generalised boost of Physlib taking the velocity `e₀` to `p / m`. So the standard boost `L(p)` of the Wigner
construction exists, and the forward mass shell is a single orbit (`exists_boost_massiveStd`).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1 (the standard Lorentz transformation `L(p)`) and §3.2 (orbits).
-/

@[expose] public section

noncomputable section

open Lorentz LorentzGroup
open scoped Lorentz.Vector

namespace Lightlike.Poincare

/-- The rest velocity `e₀` as an element of `Velocity 3`. -/
def restVelocity : Velocity 3 :=
  ⟨Lorentz.Vector.basis (Sum.inl 0), by
    rw [Velocity.mem_iff]
    refine ⟨?_, ?_⟩
    · simpa [massiveStd] using minkowskiProduct_massiveStd 1
    · simp [Lorentz.Vector.timeComponent, Lorentz.Vector.basis_apply]⟩

/-- The velocity `p / m` of a momentum `p` on the forward mass shell of mass `m > 0`. -/
def velocityOfMomentum {m : ℝ} (hm : 0 < m) {p : Lorentz.Vector 3} (hp : ⟪p, p⟫ₘ = m ^ 2)
    (hp0 : 0 < p.timeComponent) : Velocity 3 :=
  ⟨(1 / m) • p, by
    rw [Velocity.mem_iff]
    refine ⟨?_, ?_⟩
    · rw [Lorentz.Vector.minkowskiProduct_smul_self, hp]
      field_simp
    · simpa [Lorentz.Vector.timeComponent] using mul_pos (one_div_pos.2 hm) hp0⟩

/-- **The forward mass shell is one orbit of the restricted Lorentz group.** -/
theorem exists_boost_massiveStd {m : ℝ} (hm : 0 < m) {p : Lorentz.Vector 3}
    (hp : ⟪p, p⟫ₘ = m ^ 2) (hp0 : 0 < p.timeComponent) :
    ∃ Λ : LorentzGroup 3, IsOrthochronous Λ ∧ Λ • massiveStd m = p := by
  refine ⟨generalizedBoost restVelocity (velocityOfMomentum hm hp hp0),
    generalizedBoost_isOrthochronous _ _, ?_⟩
  have h1 : massiveStd m = m • restVelocity.1 := rfl
  have h2 := generalizedBoost_apply_fst restVelocity (velocityOfMomentum hm hp hp0)
  rw [h1, Lorentz.Vector.smul_eq_mulVec, Matrix.mulVec_smul, ← Lorentz.Vector.smul_eq_mulVec, h2]
  show m • ((1 / m) • p) = p
  rw [smul_smul]
  field_simp
  simp

end Lightlike.Poincare

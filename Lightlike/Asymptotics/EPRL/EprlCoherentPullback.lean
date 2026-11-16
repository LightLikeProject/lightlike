import Lightlike.Asymptotics.EPRL.EprlCoherentNode

/-!
# The pairing of a Spin(4) basis intertwiner with the EPRL lift of a coherent intertwiner

The pullback `(Y₁ ⊗ Y₂)ᴴ (ι⁺_x ⊗ ι⁻_y) (Y₃ ⊗ Y₄)` of a Spin(4) basis intertwiner along the EPRL
map is an `SU(2)` intertwiner (`pullback_isIntertwiner`), so group averaging does not change its
pairing with a Hom form (`hsInner_homForm_avgP`); with `eprlLift_homForm_prod` this gives the product
formula `hsInner_ivec4_eprlLift_cohInt`.

## Main results

* `pullback_isIntertwiner`: the pullback is an `SU(2)` intertwiner.
* `hsInner_ivec4_eprlLift_cohInt`: `⟨ι⁺_x ⊗ ι⁻_y, Φ̃(ι_{n+m}(g))⟩ = ⟨ι_x, ι_n(g)⟩ ⟨ι_y, ι_m(g)⟩` in Hom form.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, §3.
-/

open Matrix
open scoped Matrix
open scoped Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling PhyslibAlpha.Sl2 Finset

section Spin4Side

variable (n m : Fin 4 → ℕ)

/-- The pullback of a Spin(4) basis intertwiner is an `SU(2)` intertwiner. -/
theorem pullback_isIntertwiner {x y : ℕ} (hx : x ∈ channel (n 0) (n 1) (n 2) (n 3))
    (hy : y ∈ channel (m 0) (m 1) (m 2) (m 3)) :
    IsIntertwiner (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3) (pullback n m x y) := by
  intro g
  rw [mem_channel] at hx hy
  have hi : (pairMat (n 0) (n 1) g ⊗ₖ pairMat (m 0) (m 1) g) *
      ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y =
      ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y *
        (pairMat (n 2) (n 3) g ⊗ₖ pairMat (m 2) (m 3) g) := by
    unfold ivec4
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ivec_isIntertwiner hx.1 hx.2 g, ivec_isIntertwiner hy.1 hy.2 g]
  have h1 := eprlPair_conjTranspose_equivariant (n₁ := n 0) (m₁ := m 0) (n₂ := n 1) (m₂ := m 1) g
  have h2 := eprlPair_equivariant (n₁ := n 2) (m₁ := m 2) (n₂ := n 3) (m₂ := m 3) g
  unfold pullback
  calc pairMat (n 0 + m 0) (n 1 + m 1) g * ((eprlPair (n 0) (m 0) (n 1) (m 1))ᴴ *
        ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y *
          eprlPair (n 2) (m 2) (n 3) (m 3))
      = ((pairMat (n 0 + m 0) (n 1 + m 1) g * (eprlPair (n 0) (m 0) (n 1) (m 1))ᴴ) *
        ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y) *
          eprlPair (n 2) (m 2) (n 3) (m 3) := by simp only [Matrix.mul_assoc]
    _ = ((eprlPair (n 0) (m 0) (n 1) (m 1))ᴴ * (pairMat (n 0) (n 1) g ⊗ₖ pairMat (m 0) (m 1) g) *
        ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y) *
          eprlPair (n 2) (m 2) (n 3) (m 3) := by rw [h1]
    _ = (eprlPair (n 0) (m 0) (n 1) (m 1))ᴴ *
        (ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y *
          ((pairMat (n 2) (n 3) g ⊗ₖ pairMat (m 2) (m 3) g) *
            eprlPair (n 2) (m 2) (n 3) (m 3))) := by
          rw [Matrix.mul_assoc (eprlPair (n 0) (m 0) (n 1) (m 1))ᴴ, hi]
          simp only [Matrix.mul_assoc]
    _ = (eprlPair (n 0) (m 0) (n 1) (m 1))ᴴ *
        ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y *
          eprlPair (n 2) (m 2) (n 3) (m 3) * pairMat (n 2 + m 2) (n 3 + m 3) g := by
          rw [h2]; simp only [Matrix.mul_assoc]

/-- **The pairing of a Spin(4) basis intertwiner with the EPRL lift of a coherent intertwiner is the
product of the two `SU(2)` pairings.** -/
theorem hsInner_ivec4_eprlLift_cohInt (g : Fin 4 → SU2) {x y : ℕ}
    (hx : x ∈ channel (n 0) (n 1) (n 2) (n 3)) (hy : y ∈ channel (m 0) (m 1) (m 2) (m 3)) :
    hsInner (ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y)
        (eprlLift (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
          (homForm (n + m) (cohInt (n + m) g))) =
      hsInner (ivec (n 0) (n 1) (n 2) (n 3) x) (homForm n (cohInt n g)) *
        hsInner (ivec (m 0) (m 1) (m 2) (m 3) y) (homForm m (cohInt m g)) := by
  have hR := pullback_isIntertwiner n m hx hy
  rw [mem_channel] at hx hy
  have hxi := ivec_isIntertwiner hx.1 hx.2
  have hyi := ivec_isIntertwiner hy.1 hy.2
  have e1 := hsInner_ivec4_eprlLift n m x y (homForm (n + m) (cohInt (n + m) g))
  have e2 : hsInner (pullback n m x y) (homForm (n + m) (cohInt (n + m) g)) =
      hsInner (pullback n m x y)
        (homForm (n + m) (prodVec (n + m) fun l => cohState ((n + m) l) (g l))) :=
    hsInner_homForm_avgP (n + m) hR _
  have e3 := hsInner_ivec4_eprlLift n m x y
    (homForm (n + m) (prodVec (n + m) fun l => cohState ((n + m) l) (g l)))
  have e4 := eprlLift_homForm_prod n m g
  have e5 : hsInner (ivec (n 0) (n 1) (n 2) (n 3) x) (homForm n (cohInt n g)) =
      hsInner (ivec (n 0) (n 1) (n 2) (n 3) x)
        (homForm n (prodVec n fun l => cohState (n l) (g l))) := hsInner_homForm_avgP n hxi _
  have e6 : hsInner (ivec (m 0) (m 1) (m 2) (m 3) y) (homForm m (cohInt m g)) =
      hsInner (ivec (m 0) (m 1) (m 2) (m 3) y)
        (homForm m (prodVec m fun l => cohState (m l) (g l))) := hsInner_homForm_avgP m hyi _
  rw [e1, e2, ← e3, e4, e5, e6]
  exact hsInner_kronecker _ _ _ _

end Spin4Side

end Lightlike.Asymptotics.EPRL

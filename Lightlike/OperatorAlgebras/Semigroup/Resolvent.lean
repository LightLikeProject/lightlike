import Lightlike.OperatorAlgebras.Semigroup.Defs
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The resolvent of a Hille–Yosida operator

The hypotheses of the Hille–Yosida generation theorem for contraction semigroups on a Banach space `X`:
an operator `A` (a `LinearPMap`) with dense domain such that, for every `λ > 0`, `λ - A` is bounded
below, `λ ‖x‖ ≤ ‖λ x - A x‖` (dissipativity), and surjective onto `X`. (Closedness of `A` follows.)
Then `λ - A` has an inverse `R(λ)`, a bounded operator on `X` of norm at most `λ⁻¹`
(`HYHyp.exists_resolvent`).

## References

* Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
  <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, Section 1: the resolvent
  of a contraction-generator and the Yosida approximation.

The comparison of the statements with the notes at a location is pending.
-/

open Filter Topology NNReal
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **The hypotheses of the Hille–Yosida theorem**: `A` is densely defined, and for every `λ > 0` the
operator `λ - A` is bounded below by `λ` (dissipativity) and surjective. -/
structure HYHyp (A : X →ₗ.[𝕜] X) : Prop where
  /-- The domain is dense. -/
  dense : Dense (A.domain : Set X)
  /-- `λ ‖x‖ ≤ ‖λ x - A x‖`. -/
  dissip : ∀ l : ℝ, 0 < l → ∀ x : A.domain, l * ‖(x : X)‖ ≤ ‖(l : 𝕜) • (x : X) - A x‖
  /-- `λ - A` is surjective. -/
  surj : ∀ l : ℝ, 0 < l → ∀ y : X, ∃ x : A.domain, (l : 𝕜) • (x : X) - A x = y

namespace HYHyp

variable {A : X →ₗ.[𝕜] X} (h : HYHyp A)

include h in
/-- `λ - A` is injective. -/
lemma inj {l : ℝ} (hl : 0 < l) {x y : A.domain}
    (hxy : (l : 𝕜) • (x : X) - A x = (l : 𝕜) • (y : X) - A y) : x = y := by
  have := h.dissip l hl (x - y)
  have e : (l : 𝕜) • ((x - y : A.domain) : X) - A (x - y) = 0 := by
    rw [Submodule.coe_sub, LinearPMap.map_sub, smul_sub]
    rw [show (l : 𝕜) • (x : X) - (l : 𝕜) • (y : X) - (A x - A y) =
        ((l : 𝕜) • (x : X) - A x) - ((l : 𝕜) • (y : X) - A y) by abel, hxy, sub_self]
  rw [e, norm_zero] at this
  have : ‖((x - y : A.domain) : X)‖ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos hl hpos]
  have h0 : ((x - y : A.domain) : X) = 0 := norm_le_zero_iff.1 this
  exact sub_eq_zero.1 (Subtype.ext h0)

variable [CompleteSpace X]

include h in
/-- **The resolvent**: `λ - A` has a bounded inverse `R` on `X`, of norm at most `λ⁻¹`. -/
theorem exists_resolvent {l : ℝ} (hl : 0 < l) :
    ∃ R : X →L[𝕜] X, ‖R‖ ≤ l⁻¹ ∧
      (∀ y, ∃ x : A.domain, (x : X) = R y ∧ (l : 𝕜) • (x : X) - A x = y) ∧
      ∀ x : A.domain, R ((l : 𝕜) • (x : X) - A x) = x := by
  choose r hr using h.surj l hl
  have hinj := fun {x y : A.domain} => h.inj hl (x := x) (y := y)
  have hadd : ∀ y z, r (y + z) = r y + r z := fun y z => by
    apply hinj
    rw [hr, Submodule.coe_add, LinearPMap.map_add, smul_add]
    calc y + z = ((l : 𝕜) • (r y : X) - A (r y)) + ((l : 𝕜) • (r z : X) - A (r z)) := by
          rw [hr, hr]
      _ = _ := by abel
  have hsmul : ∀ (c : 𝕜) y, r (c • y) = c • r y := fun c y => by
    apply hinj
    rw [hr, Submodule.coe_smul, LinearPMap.map_smul, smul_comm (l : 𝕜) c, ← smul_sub, hr]
  let L : X →ₗ[𝕜] X :=
    { toFun := fun y => (r y : X)
      map_add' := fun y z => by simp [hadd]
      map_smul' := fun c y => by simp [hsmul] }
  have hb : ∀ y, ‖L y‖ ≤ l⁻¹ * ‖y‖ := fun y => by
    have := h.dissip l hl (r y)
    rw [hr] at this
    show ‖(r y : X)‖ ≤ _
    rw [inv_mul_eq_div, le_div_iff₀ hl]
    linarith
  refine ⟨L.mkContinuous l⁻¹ hb, ?_, fun y => ⟨r y, rfl, hr y⟩, fun x => ?_⟩
  · exact LinearMap.mkContinuous_norm_le _ (by positivity) hb
  · show ((r _ : A.domain) : X) = x
    congr 1
    exact hinj (by rw [hr])

end HYHyp

end Lightlike.OperatorAlgebras

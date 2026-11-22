import Mathlib
import Lightlike.Dirac.Tests
import Lightlike.Dirac.SelfAdjoint

/-!
# Trust checks for `Lightlike.Dirac.SelfAdjoint`

* Non-vacuity: the Clifford module `repC` on `ℂ` (with `e₀ ↦ i`) is skew (`isSkewRep_repC`), so
  the self-adjointness, the integrated formula and the vanishing theorem apply to it.
* Compact support is needed in the vanishing theorem: the constant function `1` satisfies
  `D 1 = 0` on `ℝ¹` but is not `0` (`dirac_one_repC`, `one_ne_zero_fun`).
-/

open InnerProductSpace

namespace Lightlike.Dirac

/-- The module `repC` is skew: `⟪i z, u⟫ = -⟪z, i u⟫` for the real inner product on `ℂ`. -/
lemma isSkewRep_repC : IsSkewRep repC := by
  intro i w u
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [gam_repC, gam_repC]
  simp [Complex.inner]
  ring

/-- `D` kills constants (a non-compactly supported solution of `D f = 0`). -/
lemma dirac_one_repC (x : E 1) : dirac repC (fun _ => (1 : ℂ)) x = 0 := by
  simp [dirac]

/-- The constant `1` is a nonzero solution of `D f = 0`, so compact support in
`eq_zero_of_dirac_eq_zero` cannot be dropped. -/
lemma one_ne_zero_fun : (fun _ : E 1 => (1 : ℂ)) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

/-- Instance of the vanishing theorem on the model `repC`. -/
example {f : E 1 → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hD : ∀ x, dirac repC f x = 0) : f = 0 :=
  eq_zero_of_dirac_eq_zero isSkewRep_repC hf hfc hD

end Lightlike.Dirac

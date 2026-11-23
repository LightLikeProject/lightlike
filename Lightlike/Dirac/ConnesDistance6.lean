import Mathlib
import Lightlike.Dirac.ConnesDistance5

/-!
# Bridge: the circle test functions as `Lip1` functions on `ℝ¹`

For `g : ℝ → ℝ` put `liftFn g : E 1 → ℝ`, `x ↦ g (x 0)`.  Then `∇(liftFn g) = g' · e₀`, so
`‖[D, liftFn g]‖ = ‖cliff(∇ …)‖ = |g'|` and `Lip1 ρ (liftFn g) ↔ (g ∈ C¹ ∧ |g'| ≤ 1)`.
This identifies the hand-written circle condition `|f'| ≤ 1` of `LipCirc` with the commutator-norm
condition for the Dirac operator `D = γ d/dx`.
-/

open CliffordAlgebra InnerProductSpace

namespace Lightlike.Dirac

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A function of one real variable seen as a function on `ℝ¹ = E 1`. -/
noncomputable def liftFn (g : ℝ → ℝ) : E 1 → ℝ := fun x => g (x 0)

lemma hasFDerivAt_liftFn {g : ℝ → ℝ} {x : E 1} (hg : DifferentiableAt ℝ g (x 0)) :
    HasFDerivAt (liftFn g) ((fderiv ℝ g (x 0)).comp (EuclideanSpace.proj (0 : Fin 1))) x :=
  by
    have hp : HasFDerivAt (⇑(EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ))
        (EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ).hasFDerivAt
    exact HasFDerivAt.comp (g := g) x hg.hasFDerivAt hp

lemma fderiv_liftFn_e0 {g : ℝ → ℝ} {x : E 1} (hg : DifferentiableAt ℝ g (x 0)) :
    fderiv ℝ (liftFn g) x (e 0) = deriv g (x 0) := by
  rw [(hasFDerivAt_liftFn hg).fderiv, ContinuousLinearMap.comp_apply]
  have h1 : (EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ) (e 0) = 1 := by
    simp [e]
  rw [h1]
  rfl

/-- The gradient of `x ↦ g (x 0)` is `g'(x 0) • e₀`. -/
lemma gradient_liftFn {g : ℝ → ℝ} {x : E 1} (hg : DifferentiableAt ℝ g (x 0)) :
    gradient (liftFn g) x = deriv g (x 0) • e 0 := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [gradient_apply_eq, fderiv_liftFn_e0 hg]
  simp [e]

lemma norm_gradient_liftFn {g : ℝ → ℝ} {x : E 1} (hg : DifferentiableAt ℝ g (x 0)) :
    ‖gradient (liftFn g) x‖ = |deriv g (x 0)| := by
  rw [gradient_liftFn hg, norm_smul, e]
  simp

/-- The commutator norm `‖[D, g]‖ = ‖cliff(∇g)‖` for a function of the single coordinate is `|g'|`. -/
lemma opNorm_cliff_gradient_liftFn {ρ : CliffordRep 1 V} (hρ : IsSkewRep ρ) [Nontrivial V]
    {g : ℝ → ℝ} {x : E 1} (hg : DifferentiableAt ℝ g (x 0)) :
    ‖cliff ρ (gradient (liftFn g) x)‖ = |deriv g (x 0)| := by
  rw [opNorm_cliff hρ, norm_gradient_liftFn hg]

lemma contDiff_liftFn {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (liftFn g) :=
  hg.comp (EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ).contDiff

/-- **Bridge.** `liftFn g` is a test function for the Dirac operator on `ℝ¹` iff `g` is `C¹` with
`|g'| ≤ 1`. -/
theorem lip1_liftFn_iff {ρ : CliffordRep 1 V} (hρ : IsSkewRep ρ) [Nontrivial V] {g : ℝ → ℝ} :
    Lip1 ρ (liftFn g) ↔ ContDiff ℝ 1 g ∧ ∀ t, |deriv g t| ≤ 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hg : ContDiff ℝ 1 g := by
      have : g = liftFn g ∘ fun t : ℝ => t • e (0 : Fin 1) := by
        ext t; simp [liftFn, e]
      rw [this]
      exact h1.comp (contDiff_id.smul contDiff_const)
    refine ⟨hg, fun t => ?_⟩
    have hd : DifferentiableAt ℝ g ((EuclideanSpace.single (0 : Fin 1) t : E 1) 0) :=
      (hg.differentiable one_ne_zero).differentiableAt
    have := h2 (EuclideanSpace.single (0 : Fin 1) t)
    rw [opNorm_cliff_gradient_liftFn hρ hd] at this
    simpa using this
  · rintro ⟨hg, hd⟩
    refine ⟨contDiff_liftFn hg, fun x => ?_⟩
    rw [opNorm_cliff_gradient_liftFn hρ (hg.differentiable one_ne_zero).differentiableAt]
    exact hd _

/-- Circle test functions are exactly the periodic functions whose lift is a `Lip1` function. -/
theorem lipCirc_iff {ρ : CliffordRep 1 V} (hρ : IsSkewRep ρ) [Nontrivial V] {L : ℝ} {g : ℝ → ℝ} :
    LipCirc L g ↔ Function.Periodic g L ∧ Lip1 ρ (liftFn g) := by
  rw [lip1_liftFn_iff hρ, LipCirc]

end Lightlike.Dirac

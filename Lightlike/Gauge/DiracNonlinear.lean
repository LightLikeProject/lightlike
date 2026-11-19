import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.TangentCone.Basic

/-!
# The Dirac consistency algorithm on general constraint sets: what holds without regularity

Attempt at the nonlinear Dirac algorithm (Henneaux and Teitelboim 1992, Chapter One, "Constrained Hamiltonian
Systems"), without a manifold API: the stage sets `S_k` are arbitrary subsets of a finite-dimensional real normed
space `E`, and "the evolution stays in `S`" is expressed with Mathlib's tangent cone `tangentConeAt ℝ S x`, so no
implicit function theorem is needed. The evolution is `x' = V x + ∑ u_a W_a x`, with `V` the Hamiltonian vector
field and `W_a` those of the primary constraints, collected as a family `W : ι → E → E`.

* `dStep`, `dChain`: one step and the chain.
* `dChain_antitone`: the chain decreases.
* `le_dChain`: every consistent subset lies in every stage (maximality).

**What fails.** Termination. A decreasing chain of closed subsets of `E` need not stabilize (`{x ≤ 1/(k+1)}` in `ℝ`),
and nothing in the definition prevents the stage sets of the algorithm from doing so; the finite-dimensional argument
of the linear case (`Lightlike.Gauge.diracChain_stabilizes`) used the Artinian property of subspaces. To get
termination one needs a regularity hypothesis (constant rank at each stage, so that each stage is a submanifold
and the dimension drops at every proper step), which needs the tangent cone of a regular zero set to be the kernel
of the derivative and an invariance of dimension for such sets; neither is in Mathlib.
-/

namespace Lightlike.Gauge

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- **One step of the Dirac algorithm on a set**: the points `x` of `S` for which some multiplier `u` gives an
evolution velocity `V x + ∑ u_a W_a x` in the tangent cone of `S` at `x`. -/
def dStep [Fintype ι] (V : E → E) (W : ι → E → E) (S : Set E) : Set E :=
  {x ∈ S | ∃ u : ι → ℝ, V x + ∑ a, u a • W a x ∈ tangentConeAt ℝ S x}

/-- The chain of stage sets. -/
def dChain [Fintype ι] (V : E → E) (W : ι → E → E) (S₀ : Set E) (n : ℕ) : Set E :=
  (dStep V W)^[n] S₀

lemma dStep_subset [Fintype ι] (V : E → E) (W : ι → E → E) (S : Set E) : dStep V W S ⊆ S :=
  fun _ hx => hx.1

lemma dChain_succ [Fintype ι] (V : E → E) (W : ι → E → E) (S₀ : Set E) (n : ℕ) :
    dChain V W S₀ (n + 1) = dStep V W (dChain V W S₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- The chain decreases. -/
theorem dChain_antitone [Fintype ι] (V : E → E) (W : ι → E → E) (S₀ : Set E) :
    Antitone (dChain V W S₀) :=
  antitone_nat_of_succ_le fun n => by rw [dChain_succ]; exact dStep_subset _ _ _

/-- **Maximality**: a subset `D ⊆ S₀` on which the evolution is consistent (a multiplier with the velocity in the
tangent cone of `D`) lies in every stage. -/
theorem le_dChain [Fintype ι] (V : E → E) (W : ι → E → E) (S₀ D : Set E) (hD : D ⊆ S₀)
    (hcons : ∀ x ∈ D, ∃ u : ι → ℝ, V x + ∑ a, u a • W a x ∈ tangentConeAt ℝ D x) (n : ℕ) :
    D ⊆ dChain V W S₀ n := by
  induction n with
  | zero => exact hD
  | succ n ih =>
    rw [dChain_succ]
    intro x hx
    obtain ⟨u, hu⟩ := hcons x hx
    exact ⟨ih hx, u, tangentConeAt_mono ih hu⟩

end Lightlike.Gauge

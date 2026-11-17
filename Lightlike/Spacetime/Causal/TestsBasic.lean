import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.TestsMinkowski

/-!
# Checks of the basic causal relations on Minkowski space

Non-vacuity of the transitivity statements of `Lightlike/Spacetime/Causal/BasicRelations.lean`: two
timelike steps of Minkowski space `ℝ^{d+1}` are glued by `chron_trans` into one timelike curve, so
`x + ∂₀ + ∂₀ ∈ I⁺(x)`, and `I⁺(x) ⊆ J⁺(x)` contains it. The hypotheses are satisfied by genuine
curves.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {d : ℕ}

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity: two future timelike steps `∂₀` give a point of `I⁺(x)` and of `J⁺(x)`. -/
example (x : Fin (d + 1) → ℝ) :
    x + Pi.single 0 1 + Pi.single 0 1 ∈ chronFuture (minkowskiOrientation d) x ∧
      x + Pi.single 0 1 + Pi.single 0 1 ∈ causalFuture (minkowskiOrientation d) x := by
  have h1 : x + Pi.single 0 1 ∈ chronFuture (minkowskiOrientation d) x :=
    line_mem_chronFuture x _ ⟨form_e0.trans_lt (by norm_num), form_e0.trans_lt (by norm_num)⟩
  have h2 : x + Pi.single 0 1 + Pi.single 0 1 ∈
      chronFuture (minkowskiOrientation d) (x + Pi.single 0 1) :=
    line_mem_chronFuture (x + Pi.single 0 1) _
      ⟨form_e0.trans_lt (by norm_num), form_e0.trans_lt (by norm_num)⟩
  have h3 := chron_trans _ h1 h2
  exact ⟨h3, chron_subset_causal _ x h3⟩

end Lightlike.Causal

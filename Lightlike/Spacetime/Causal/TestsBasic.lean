import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.MinkowskiGH
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

set_option synthInstance.maxHeartbeats 200000 in
/-- Trust check of `minkowski_causalFuture_eq`: the point one time unit in the past is not in the
causal future, while the point one time unit ahead and the point itself are. -/
example (x : Fin (d + 1) → ℝ) :
    x - Pi.single 0 1 ∉ causalFuture (minkowskiOrientation d) x ∧
      x + Pi.single 0 1 ∈ causalFuture (minkowskiOrientation d) x := by
  rw [minkowski_causalFuture_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have := h.1
    simp at this
    linarith
  · refine ⟨by simp, ?_⟩
    have := form_e0 (d := d)
    simp only [add_sub_cancel_left]
    linarith

set_option synthInstance.maxHeartbeats 200000 in
/-- Wrong model: a spacelike displacement is not in the causal future (`d + 2` dimensions). -/
example (x : Fin (d + 2) → ℝ) :
    x + Pi.single (Fin.succ 0) 1 ∉ causalFuture (minkowskiOrientation (d + 1)) x := by
  rw [minkowski_causalFuture_eq]
  rintro ⟨-, h⟩
  have := form_e1 (d := d)
  simp only [add_sub_cancel_left] at h
  linarith

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity of the diamond statement of global hyperbolicity: `x` itself lies in the compact
causal diamond between `x` and `x + ∂₀`. -/
example (x : Fin (d + 1) → ℝ) :
    x ∈ causalFuture (minkowskiOrientation d) x ∩
      causalPast (minkowskiOrientation d) (x + Pi.single 0 1) := by
  refine ⟨self_mem_causalFuture _ x, ?_⟩
  show x + Pi.single 0 1 ∈ causalFuture (minkowskiOrientation d) x
  rw [minkowski_causalFuture_eq]
  refine ⟨by simp, ?_⟩
  have := form_e0 (d := d)
  simp only [add_sub_cancel_left]
  linarith

example : IsCompact (causalFuture (minkowskiOrientation d) 0 ∩
    causalPast (minkowskiOrientation d) (Pi.single 0 1)) := minkowski_globallyHyperbolic.2 _ _

end Lightlike.Causal

import Mathlib
import Lightlike.Regge.Linear.AngleDeriv

/-!
# The deficit at the centre of a thin kite is not uniformly controlled

A vertex `v` with four neighbours `(±1, 0)`, `(0, ±η)` is the centre of a flat star of four right
triangles with squared sides `1, η², 1 + η²`. If the four outer edges are perturbed by `ε` in
squared length, the Regge deficit angle at `v` is `2π - 4 θ(ε)`, where `θ` is the angle at `v`.
Its value at `ε = 0` is `0` (flat background) and its derivative is `-2/η`, which is unbounded as
the kite becomes thin. This is the vertex-level form of the failure of uniform estimates over a
non-fat family; it does not claim that a concrete sequence of triangulations of a manifold fails to
converge.
-/

open Real Lightlike.CMS

namespace Lightlike.Regge.Linearized

open Lightlike.Regge.Linear

/-- The deficit angle at the centre of the kite with half-axes `1` and `η`, when the squared
lengths of the four outer edges are perturbed by `ε`. -/
noncomputable def kiteDeficit (η ε : ℝ) : ℝ :=
  2 * π - 4 * triAngle (1 + ε * 0) (η ^ 2 + ε * 0) (1 + η ^ 2 + ε * 1)

/-- A flat kite has zero deficit. -/
theorem kiteDeficit_zero (η : ℝ) (hη : 0 < η) : kiteDeficit η 0 = 0 := by
  unfold kiteDeficit triAngle
  have h1 : √(1 * η ^ 2) = η := by
    rw [one_mul]; exact Real.sqrt_sq hη.le
  have h2 : (1 + η ^ 2 - (1 + η ^ 2)) / (2 * √(1 * η ^ 2)) = 0 := by
    simp
  simp only [zero_mul, add_zero]
  rw [h2, Real.arccos_zero]
  ring

/-- The first variation of the kite deficit is `-2/η`. -/
theorem kiteDeficit_hasDerivAt (η : ℝ) (hη : 0 < η) :
    HasDerivAt (kiteDeficit η) (-(2 / η)) 0 := by
  have hD : disc 1 (η ^ 2) (1 + η ^ 2) = (2 * η) ^ 2 := by unfold disc; ring
  have hDpos : 0 < disc 1 (η ^ 2) (1 + η ^ 2) := by rw [hD]; positivity
  have hder := hasDerivAt_triAngle (a := 1) (b := η ^ 2) (c := 1 + η ^ 2) (a₁ := 0) (b₁ := 0)
    (c₁ := 1) one_pos (by positivity) hDpos
  have hroot : √(disc 1 (η ^ 2) (1 + η ^ 2)) = 2 * η := by
    rw [hD]; exact Real.sqrt_sq (by positivity)
  rw [hroot] at hder
  have := (hder.const_mul 4).const_sub (2 * π)
  unfold kiteDeficit
  convert this using 1
  field_simp
  ring

/-- **No uniform bound for the kite deficit.** For every `M` there is a kite with zero deficit
at `ε = 0` whose deficit has derivative below `-M` under a unit perturbation of the squared
lengths of the outer edges. -/
theorem kiteDeficit_sensitivity_unbounded (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ kiteDeficit η 0 = 0 ∧
      ∃ d : ℝ, HasDerivAt (kiteDeficit η) d 0 ∧ d < -M := by
  set η : ℝ := 1 / (2 * (|M| + 1)) with hη
  have hM : 0 < |M| + 1 := by positivity
  have hpos : 0 < η := by positivity
  have hlt : η < 1 := by
    rw [hη, div_lt_one (by positivity)]
    nlinarith [abs_nonneg M]
  refine ⟨η, hpos, hlt, kiteDeficit_zero η hpos, _, kiteDeficit_hasDerivAt η hpos, ?_⟩
  have : 2 / η = 4 * (|M| + 1) := by rw [hη]; field_simp; ring
  rw [this]
  linarith [le_abs_self M, abs_nonneg M]

/-- **No uniform Lipschitz constant for the kite deficit.** For every `L`, some thin kite has a
deficit that is not `L`-Lipschitz in the perturbation `ε` on any neighbourhood of `0`. -/
theorem kiteDeficit_not_uniformly_lipschitz (L : NNReal) :
    ∃ η : ℝ, 0 < η ∧ ∀ s ∈ nhds (0 : ℝ), ¬ LipschitzOnWith L (kiteDeficit η) s := by
  obtain ⟨η, hη, -, -, d, hd, hM⟩ := kiteDeficit_sensitivity_unbounded (L : ℝ)
  refine ⟨η, hη, fun s hs hlip => ?_⟩
  have := hd.le_of_lipschitzOn hs hlip
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le d, L.coe_nonneg]

end Lightlike.Regge.Linearized

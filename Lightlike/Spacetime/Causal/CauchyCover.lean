import Lightlike.Spacetime.Causal.Extension

/-!
# Inextendible timelike curves through a point; a Cauchy surface covers the manifold

On a Hausdorff, second countable manifold without boundary every point lies on an inextendible
future-directed timelike curve. Hence a Cauchy surface `S` meets such a curve through any point
`p`, so `p` lies in `S`, in the chronological future of a point of `S`, or in the chronological
past of a point of `S`.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Chapter 6.

The comparison of the statements with the book at its location is pending.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [SecondCountableTopology M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Through every point there is an inextendible future-directed timelike curve.** -/
theorem exists_inextendible_through (q : M) :
    ∃ (G : ℝ → M) (s : Set ℝ) (t : ℝ), IsInextendibleFutureTimelike T G s ∧ t ∈ s ∧ G t = q := by
  have hfd : FiniteDimensional ℝ E := by
    obtain ⟨e, -⟩ := g.lorentzian q
    exact Module.Finite.of_basis e
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨X', hXs, hX⟩ := exists_smooth_field T
  have hY : CMDiff 1 (fun x ↦ (⟨x, X' x⟩ : TangentBundle I M)) := hXs.of_le (by norm_num)
  have hYT : ∀ x, T.IsFutureTimelike (X' x) := fun x => hX x
  have hY0 : ∀ x, X' x ≠ 0 := fun x h0 => by
    have := (hYT x).1
    rw [h0] at this
    simp at this
  obtain ⟨R, D, hDo, hDc, h0D, hR0, hint, -⟩ := exists_ray_future hY hY0 q 0
  have hRT : IsFutureTimelikeCurve T R D :=
    isFutureTimelikeCurve_of_integralCurve T hY.continuous hYT hDo hDc hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDo 0 h0D
  have hsub : Icc 0 (ε / 2) ⊆ D := fun t ht => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨G, s, hG, h0s, -, hG0, -⟩ := exists_inextendible_of_timelike T (show (0 : ℝ) < ε / 2 by linarith)
    (hRT.restrict T hsub (by linarith))
  exact ⟨G, s, 0, hG, h0s, by rw [hG0, hR0]⟩

/-- **A Cauchy surface covers the manifold**: every point is in `S`, in the chronological future
of a point of `S`, or in its chronological past. -/
theorem IsCauchySurface.cover {S : Set M} (h : IsCauchySurface T S) (p : M) :
    p ∈ S ∨ (∃ x ∈ S, p ∈ chronFuture T x) ∨ ∃ x ∈ S, x ∈ chronFuture T p := by
  obtain ⟨G, s, t₀, hG, ht₀, hGp⟩ := exists_inextendible_through T p
  obtain ⟨t, ⟨hts, htS⟩, -⟩ := h G s hG
  have hsub : ∀ u v, u ∈ s → v ∈ s → u < v → G v ∈ chronFuture T (G u) := fun u v hu hv huv =>
    ⟨G, u, v, huv, hG.1.restrict T (fun r hr => hG.1.1.ordConnected.out hu hv hr) huv, rfl, rfl⟩
  rcases lt_trichotomy t t₀ with hlt | heq | hgt
  · right; left
    exact ⟨G t, htS, hGp ▸ hsub t t₀ hts ht₀ hlt⟩
  · left
    rw [← hGp, ← heq]; exact htS
  · right; right
    exact ⟨G t, htS, hGp ▸ hsub t₀ t ht₀ hts hgt⟩

end Causal

end Lightlike

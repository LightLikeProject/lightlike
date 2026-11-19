import Lightlike.Canonical.Foliation
import Lightlike.Spacetime.CausalLadder.ConeAlgebra

/-!
# The leaves of a time function of a Lorentzian metric are spacelike

For a Lorentzian metric, every nonzero vector tangent to a leaf of a time function is spacelike, and the induced metric
is positive on it (`spatialMetric_pos`): a vector orthogonal to the timelike normal that were causal would vanish
(`IsLorentzianForm.eq_zero_of_orthogonal_timelike`). So the leaves `Σ_t` are spacelike hypersurfaces and `γ` is a
Riemannian metric on their tangent spaces, the setting of Gourgoulhon, arXiv:gr-qc/0703035, Sec. 3.2.2 (p. 40: "We
assume that all `Σ_t`'s are spacelike"), here a consequence of the timelike gradient.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]

variable {k : ℕ} {g : LorentzianMetric 𝓘(ℝ, E) M k} {τ : M → ℝ}

/-- **Tangent vectors of the leaves are spacelike**: for a Lorentzian metric and a time function, a nonzero
`w` with `dτ(w) = 0` has `γ(w, w) = g(w, w) > 0`. -/
theorem spatialMetric_pos (h : IsTimeFunction g.toNondegMetric τ) {x : M} {w : TangentSpace 𝓘(ℝ, E) x}
    (hw : dTime τ x w = 0) (hw0 : w ≠ 0) : 0 < spatialMetric g.toNondegMetric τ x w w := by
  rw [spatialMetric_of_tangent h hw]
  by_contra hle
  rw [not_lt] at hle
  have hn : g.toNondegMetric.g x (unitNormal g.toNondegMetric τ x) (unitNormal g.toNondegMetric τ x) < 0 := by
    rw [g_unitNormal_self h x]; norm_num
  have hwn : g.toNondegMetric.g x w (unitNormal g.toNondegMetric τ x) = 0 := by
    rw [g.toNondegMetric.symm]; exact (dTime_eq_zero_iff h x w).1 hw
  exact hw0 ((g.lorentzian x).eq_zero_of_orthogonal_timelike hn hwn hle)

end Lightlike.Canonical

import Lightlike.Spacetime.Causal.OpenPast
import Lightlike.Spacetime.CausalLadder.NearFuture

/-!
# One step of a chain of timelike pieces going down a causal curve

Let `p' ≤ p` along a causal curve (`p ∈ J⁺(p')`) and `q ∈ I⁺(p)`. If the push-up
`J⁺ then I⁺ ⊆ I⁺` holds (`T-GE2-P6`, the hypothesis `hpush`), then `q ∈ I⁺(p')`, so `p'` lies in the open
set `I⁻(q)`, and every neighbourhood `U` of `p'` contains a point `q'` of `I⁺(p')` that lies in `I⁻(q)`
(`exists_chain_step`). Iterating produces a descending chain `q ≫ q' ≫ q'' ≫ ⋯` of points above `p, p', p'', …`
that can be joined by timelike pieces: the construction of an inextendible timelike curve near a past
inextendible causal curve (the perturbation step of the proof that a Cauchy surface has full domain of
dependence).

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **One step of the chain.** See the module docstring. -/
theorem exists_chain_step
    (hpush : ∀ x y z : M, y ∈ causalFuture T x → z ∈ chronFuture T y → z ∈ chronFuture T x)
    {p' p q : M} (hle : p ∈ causalFuture T p') (hq : q ∈ chronFuture T p) {U : Set M} (hU : U ∈ 𝓝 p') :
    ∃ q' ∈ U, q' ∈ chronFuture T p' ∧ q ∈ chronFuture T q' := by
  have hq' : q ∈ chronFuture T p' := hpush p' p q hle hq
  have hV : U ∩ chronPast T q ∈ 𝓝 p' := inter_mem hU ((isOpen_chronPast T q).mem_nhds hq')
  obtain ⟨q', hq'V, hq'F⟩ := exists_mem_chronFuture_near T p' hV
  exact ⟨q', hq'V.1, hq'F, hq'V.2⟩

end Lightlike.Causal

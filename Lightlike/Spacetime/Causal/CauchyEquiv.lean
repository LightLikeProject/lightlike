import Lightlike.Spacetime.Causal.CauchyAssembly
import Lightlike.Spacetime.Causal.PerturbCauchy

/-!
# An achronal set is a Cauchy surface iff its domain of dependence is the whole manifold

`⇐` is `isCauchySurface_of_domainDep_eq_univ`. `⇒` assembles the covering by a Cauchy surface, the
perturbation of causal curves into timelike curves (`perturb_future_of_cauchy`,
`perturb_past_of_cauchy`) and `IsCauchySurface.domainDep_eq_univ_of_perturb`. The perturbation steps
use the push-up properties of the causal and chronological futures, here hypotheses
(`hpushF`, `hpushP`): `x ≤ y ≪ z ⇒ x ≪ z` and `x ≪ y ≤ z ⇒ x ≪ z`.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.6.

The comparison of the statements with the book at its location is pending.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M] [BoundarylessManifold I M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **An achronal set is a Cauchy surface iff its domain of dependence is the whole manifold**,
given the two push-up properties of the causal and chronological futures. -/
theorem isCauchySurface_iff_domainDep_eq_univ_of_push
    (hpushF : ∀ x y z : M, y ∈ causalFuture T x → z ∈ chronFuture T y → z ∈ chronFuture T x)
    (hpushP : ∀ x y z : M, y ∈ chronFuture T x → z ∈ causalFuture T y → z ∈ chronFuture T x)
    {S : Set M} (hA : IsAchronal T S) :
    IsCauchySurface T S ↔ domainDep T S = Set.univ :=
  ⟨fun h => h.domainDep_eq_univ_of_perturb T (perturb_future_of_cauchy T hpushF hA h)
      (perturb_past_of_cauchy T hpushP hA h),
    isCauchySurface_of_domainDep_eq_univ T hA⟩

end Causal

end Lightlike

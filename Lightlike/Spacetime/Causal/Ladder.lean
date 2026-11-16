import Lightlike.Spacetime.Causal.Relations

/-!
# The causal ladder and Cauchy surfaces

The *causal ladder* of a time-oriented Lorentzian manifold, from the weakest to the strongest
condition: chronological, causal, strongly causal, stably causal, causally simple, globally
hyperbolic. Each is a `Prop` of the time orientation; the implications between them are
statements in `Tasks/Causal/`.

Conventions. *Causal*: `J⁺` is antisymmetric (no closed causal curve through two distinct
points). *Strongly causal*: every point has arbitrarily small causally convex neighbourhoods.
*Stably causal* is defined through its characterisation by a time function. The original
definition is that causality survives every small widening of the light cones; Hawking (1969)
proved that this holds iff a time function exists, and that equivalence is not formalised here.
*Causally simple*: causal with closed `J⁺(x)` and `J⁻(x)`. *Globally hyperbolic*: strongly causal
with compact causal diamonds `J⁺(x) ∩ J⁻(y)`. A *Cauchy surface* is a set met exactly once by every
inextendible timelike curve.

## Main definitions

* `Causal.IsChronological`, `IsCausal`, `IsStronglyCausal`, `IsStablyCausal`, `IsCausallySimple`,
  `IsGloballyHyperbolic`.
* `Causal.IsTimeFunction`, `Causal.IsAchronal`, `Causal.IsCauchySurface`.

## References

* E. Minguzzi and M. Sánchez, *The causal hierarchy of spacetimes*, in *Recent developments in
  pseudo-Riemannian geometry*, EMS (2008), Sections 3 and 4.
* S. W. Hawking, *The existence of cosmic time functions*, Proc. R. Soc. Lond. A 308 (1969).
* R. Geroch, *Domain of dependence*, J. Math. Phys. 11 (1970).
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Chronology**: there is no closed timelike curve, `x ∉ I⁺(x)` for all `x`. -/
def IsChronological : Prop := ∀ x : M, x ∉ chronFuture T x

/-- **Causality**: if `y ∈ J⁺(x)` and `x ∈ J⁺(y)` then `x = y`. -/
def IsCausal : Prop := ∀ x y : M, y ∈ causalFuture T x → x ∈ causalFuture T y → x = y

/-- **Strong causality**: every neighbourhood `U` of a point contains a neighbourhood `V` that is
causally convex: a causal curve with both ends in `V` lies in `V`. -/
def IsStronglyCausal : Prop :=
  ∀ x : M, ∀ U ∈ nhds x, ∃ V ∈ nhds x, V ⊆ U ∧
    ∀ y ∈ V, ∀ z ∈ V, ∀ w : M, w ∈ causalFuture T y → z ∈ causalFuture T w → w ∈ V

/-- A **time function**: a continuous function strictly increasing along future causal curves
between distinct points. -/
def IsTimeFunction (τ : M → ℝ) : Prop :=
  Continuous τ ∧ ∀ x y : M, y ∈ causalFuture T x → y ≠ x → τ x < τ y

/-- **Stable causality**, defined by the existence of a time function. By Hawking's theorem (1969)
this is equivalent to causality being stable under small widenings of the light cones, which was
the original definition; that equivalence is not formalised here. -/
def IsStablyCausal : Prop := ∃ τ : M → ℝ, IsTimeFunction T τ

/-- **Causal simplicity**: causal, and the causal futures and pasts of points are closed. -/
def IsCausallySimple : Prop :=
  IsCausal T ∧ ∀ x : M, IsClosed (causalFuture T x) ∧ IsClosed (causalPast T x)

/-- **Global hyperbolicity**: strongly causal with compact causal diamonds `J⁺(x) ∩ J⁻(y)`. -/
def IsGloballyHyperbolic : Prop :=
  IsStronglyCausal T ∧ ∀ x y : M, IsCompact (causalFuture T x ∩ causalPast T y)

/-- A set is **achronal** if no two of its points are joined by a timelike curve. -/
def IsAchronal (S : Set M) : Prop := ∀ x ∈ S, ∀ y ∈ S, y ∉ chronFuture T x

/-- A **Cauchy surface**: a set that every inextendible future-directed timelike curve meets
exactly once. -/
def IsCauchySurface (S : Set M) : Prop :=
  ∀ (γ : ℝ → M) (s : Set ℝ), IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureTimelike v) γ s →
    ∃! t, t ∈ s ∧ γ t ∈ S

end Causal

end Lightlike

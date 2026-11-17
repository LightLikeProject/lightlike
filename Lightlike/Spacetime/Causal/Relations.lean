import Lightlike.Spacetime.Causal.CausalCurve

/-!
# Chronological and causal futures and pasts

For a point `x` of a time-oriented Lorentzian manifold the *chronological future* `I⁺(x)` is the set
of points reached from `x` by a future-directed timelike curve, and the *causal future* `J⁺(x)` the
set of points reached by a future-directed causal curve, constant curves included, so `x ∈ J⁺(x)`,
while `x ∈ I⁺(x)` only if there is a closed timelike curve through `x`. The pasts are defined by
`y ∈ I⁻(x) ↔ x ∈ I⁺(y)`. The *future horismos* is `E⁺(x) = J⁺(x) \ I⁺(x)`.

## Main definitions

* `Causal.chronFuture`, `chronPast`, `causalFuture`, `causalPast`: `I⁺`, `I⁻`, `J⁺`, `J⁻`.
* `Causal.horismos`: `E⁺ = J⁺ \ I⁺`.
* `Causal.chronFutureSet`, `causalFutureSet`: the same for a set.

## References

* R. Penrose, *Techniques of Differential Topology in Relativity*, SIAM (1972), Chapter 2.
* E. Minguzzi and M. Sánchez, *The causal hierarchy of spacetimes*, in *Recent developments in
  pseudo-Riemannian geometry*, EMS (2008), Section 2.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The **chronological future** `I⁺(x)`: points reached from `x` by a future-directed timelike
curve of positive parameter length. -/
def chronFuture (x : M) : Set M :=
  {y | ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = x ∧ γ b = y}

/-- The **causal future** `J⁺(x)`: points reached from `x` by a future-directed causal curve,
including `x` itself (a constant curve). -/
def causalFuture (x : M) : Set M :=
  {y | ∃ (γ : ℝ → M) (a b : ℝ), a ≤ b ∧ IsFutureCausalCurve T γ (Icc a b) ∧ γ a = x ∧ γ b = y}

/-- The **chronological past** `I⁻(x)`: the points `y` with `x ∈ I⁺(y)`. -/
def chronPast (x : M) : Set M := {y | x ∈ chronFuture T y}

/-- The **causal past** `J⁻(x)`: the points `y` with `x ∈ J⁺(y)`. -/
def causalPast (x : M) : Set M := {y | x ∈ causalFuture T y}

/-- The **future horismos** `E⁺(x) = J⁺(x) \ I⁺(x)`: the points on the future light cone of `x`. -/
def horismos (x : M) : Set M := causalFuture T x \ chronFuture T x

/-- The chronological future `I⁺(S)` of a set. -/
def chronFutureSet (S : Set M) : Set M := ⋃ x ∈ S, chronFuture T x

/-- The causal future `J⁺(S)` of a set. -/
def causalFutureSet (S : Set M) : Set M := ⋃ x ∈ S, causalFuture T x

end Causal

end Lightlike

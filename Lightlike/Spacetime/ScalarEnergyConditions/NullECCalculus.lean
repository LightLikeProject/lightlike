import Lightlike.Spacetime.ScalarEnergyConditions.KleinGordonRicci

/-!
# Calculus of the null energy condition; Einstein–Klein–Gordon with a cosmological constant (G1-010)

The null energy condition `NullEC g T` (`T(k, k) ≥ 0` on null `k`) is a convex cone condition in `T`, and every
multiple of the metric satisfies it with equality. Consequently the energy condition is stable under adding sources
(several scalar fields, a sigma model, a cosmological term of either sign).

* `NullEC.add`, `NullEC.smul`, `NullEC.zero`, `NullEC.sum`: closure under sums and nonnegative multiples.
* `nullEC_smul_metric`: `NullEC g (c • g)` for every real `c`.
* `NullEC.add_cosmoT`: adding a cosmological term (either sign) preserves `NullEC`.
* `scalarT_sum_nullEC`: a sigma model (finitely many scalar fields with individual potentials) satisfies `NullEC`.
* `scalarField_ricciAt_null_cosmo`: for `G + Λ g = κ T` with the Klein–Gordon `T`, `Ric(k, k) = κ (dφ k)²` on null `k`
  (the cosmological constant does not enter).

**Limits.** Pointwise statements, Lorentzian 4-manifold, `κ ≠ 0` in the cosmological version.
-/

open Manifold
open scoped ContDiff

noncomputable section
namespace Lightlike

section Pointwise
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {g T₁ T₂ : V →L[ℝ] V →L[ℝ] ℝ}

/-- The zero tensor satisfies the null energy condition. -/
theorem NullEC.zero : NullEC g 0 := fun k _ => by simp

/-- The null energy condition is closed under addition. -/
theorem NullEC.add (h₁ : NullEC g T₁) (h₂ : NullEC g T₂) : NullEC g (T₁ + T₂) := fun k hk => by
  have := add_nonneg (h₁ k hk) (h₂ k hk)
  simpa using this

/-- The null energy condition is closed under multiplication by a nonnegative scalar. -/
theorem NullEC.smul (h : NullEC g T₁) {c : ℝ} (hc : 0 ≤ c) : NullEC g (c • T₁) := fun k hk => by
  have := mul_nonneg hc (h k hk)
  simpa using this

/-- The null energy condition is closed under finite sums. -/
theorem NullEC.sum {ι : Type*} (s : Finset ι) {T : ι → V →L[ℝ] V →L[ℝ] ℝ} (h : ∀ i ∈ s, NullEC g (T i)) :
    NullEC g (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (NullEC.zero : NullEC g 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Every multiple of the metric satisfies the null energy condition (with equality). -/
theorem nullEC_smul_metric (c : ℝ) : NullEC g (c • g) := fun k hk => by
  simp [hk]

/-- Adding a cosmological term, of either sign, preserves the null energy condition. -/
theorem NullEC.add_cosmoT (h : NullEC g T₁) (ρΛ : ℝ) : NullEC g (T₁ + cosmoT g ρΛ) :=
  h.add (nullEC_smul_metric _)

end Pointwise

section Sigma
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- **A sigma model satisfies the null energy condition**: a finite family of scalar fields with their own gradients and
potential values, the stress-energies added. -/
theorem scalarT_sum_nullEC (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) {ι : Type*} (s : Finset ι)
    (dφ : ι → V →L[ℝ] ℝ) (Vp : ι → ℝ) : NullEC g (∑ i ∈ s, scalarT g hg (dφ i) (Vp i)) :=
  NullEC.sum s fun i _ => scalar_nullEC g hg (dφ i) (Vp i)

end Sigma

section Geometric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
  {g : LorentzianMetric 𝓘(ℝ, E) M 4} {cov : Connection 𝓘(ℝ, E) M} {κ Λ : ℝ}

/-- **Null focusing with a cosmological constant**: if `G + Λ g = κ T` with `T` the Klein–Gordon stress-energy and
`κ ≠ 0`, then `Ric(k, k) = κ (dφ k)²` for null `k`; `Λ` drops out on null vectors. -/
theorem scalarField_ricciAt_null_cosmo (φ : M → ℝ) (Vpot : ℝ → ℝ) (hκ : κ ≠ 0)
    (h : g.toNondegMetric.EinsteinEq cov Λ κ (fun x v w => g.scalarField φ Vpot x v w)) (x : M)
    {k : TangentSpace 𝓘(ℝ, E) x} (hk : g.g x k k = 0) :
    cov.ricciAt x k k = κ * (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x k) ^ 2 := by
  have h' := (LorentzianMetric.einsteinEq_iff_absorb (g := g) (cov := cov) (T := g.scalarField φ Vpot) hκ).1 h
  rw [LorentzianMetric.ricciAt_of_einsteinEq h' x, hk, mul_zero, add_zero]
  congr 1
  simp only [add_apply, cosmoT, smul_apply, smul_eq_mul, hk, mul_zero,
    add_zero]
  exact scalarT_null (g.g x) (g.lorentzian x) _ _ hk

/-- Under `G + Λ g = κ T` with Klein–Gordon `T` and `κ ≥ 0`, `κ ≠ 0`, the Ricci tensor is nonnegative on null vectors. -/
theorem scalarField_ricciAt_null_cosmo_nonneg (φ : M → ℝ) (Vpot : ℝ → ℝ) (hκ : 0 < κ)
    (h : g.toNondegMetric.EinsteinEq cov Λ κ (fun x v w => g.scalarField φ Vpot x v w)) (x : M)
    {k : TangentSpace 𝓘(ℝ, E) x} (hk : g.g x k k = 0) : 0 ≤ cov.ricciAt x k k := by
  rw [scalarField_ricciAt_null_cosmo φ Vpot hκ.ne' h x hk]; positivity

end Geometric

end Lightlike

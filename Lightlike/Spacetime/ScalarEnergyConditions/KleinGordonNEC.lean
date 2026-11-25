import Lightlike.Spacetime.EnergyConditionsField

/-!
# The null energy condition for the Klein–Gordon field (G1-010)

The stress-energy of a Klein–Gordon field `φ` with potential `V` is `T = dφ ⊗ dφ − (½ |dφ|² + V(φ)) g`
(`scalarT`, `scalarField`; Carroll, gr-qc/9712019, eq. (1.112), p. 30). On a null vector `k` the metric term
drops out, so `T(k, k) = (dφ k)² ≥ 0` whatever the potential is.

* `scalarT_apply`: `scalarT g hg dφ Vp v w = dφ v * dφ w − (½ tr_g(dφ ⊗ dφ) + Vp) g(v, w)`.
* `scalarT_null`: `scalarT g hg dφ Vp k k = (dφ k)²` for a null `k`.
* `scalar_nullEC`: the null energy condition holds at a point, for every potential value.
* `scalarField_nullECField`: the null energy condition holds for the field `scalarField φ V` everywhere.
* `scalar_nullEC_not_weakEC`: trust check, at a point of vanishing gradient with a negative potential value the null
  condition holds and the weak one fails, so the null condition is the weaker one.

**Limits.** Pointwise statements, and the field on a Lorentzian 4-manifold as in `EnergyConditionsField.lean`; no source
location for the statement itself was read (Curiel, arXiv 1405.0403v1, p. 30 lists the Klein–Gordon field among the
possible violators of the other conditions only), so there is no comparison with a source for the null condition;
the form of `T` is Carroll's (1.112).
-/

open Manifold
open scoped ContDiff

noncomputable section
namespace Lightlike

section Pointwise
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- The value of the Klein–Gordon stress-energy on two vectors. -/
theorem scalarT_apply (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ) (v w : V) :
    scalarT g hg dφ Vp v w =
      dφ v * dφ w - ((1 / 2) * traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate + Vp) * g v w := by
  simp [scalarT]

/-- On a null vector the Klein–Gordon stress-energy is the square of the derivative. -/
theorem scalarT_null (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ) {k : V}
    (hk : g k k = 0) : scalarT g hg dφ Vp k k = (dφ k) ^ 2 := by
  rw [scalarT_apply, hk]; ring

/-- **The null energy condition for a Klein–Gordon field** at a point, for every gradient and every potential value. -/
theorem scalar_nullEC (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ) :
    NullEC g (scalarT g hg dφ Vp) := fun k hk => by
  rw [scalarT_null g hg dφ Vp hk]; positivity

/-- Equality case: for a null `k`, `T(k, k) = 0` exactly when `dφ k = 0`. -/
theorem scalarT_null_eq_zero_iff (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ)
    {k : V} (hk : g k k = 0) : scalarT g hg dφ Vp k k = 0 ↔ dφ k = 0 := by
  rw [scalarT_null g hg dφ Vp hk]; exact pow_eq_zero_iff (two_ne_zero)

/-- **Trust check**: with a negative potential value and `dφ = 0` the null condition holds and the weak one fails. -/
theorem scalar_nullEC_not_weakEC (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) {Vp : ℝ} (hV : Vp < 0) :
    NullEC g (scalarT g hg 0 Vp) ∧ ¬ WeakEC g (scalarT g hg 0 Vp) :=
  ⟨scalar_nullEC g hg 0 Vp, scalar_negative_potential_violates_weak hg hV⟩

end Pointwise

section Field
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The Klein–Gordon field satisfies the null energy condition everywhere**, for any `φ` and any potential. -/
theorem scalarField_nullECField (g : LorentzianMetric I M 4) (φ : M → ℝ) (Vpot : ℝ → ℝ) :
    g.NullECField (g.scalarField φ Vpot) := fun x =>
  scalar_nullEC (g.g x) (g.lorentzian x) _ _

/-- **Trust check on a manifold**: a constant field with a negative potential value satisfies the null energy condition
and violates the weak one. -/
theorem scalarField_const_nullEC_not_weakEC [Nonempty M] (g : LorentzianMetric I M 4) {c : ℝ} {Vpot : ℝ → ℝ}
    (hV : Vpot c < 0) :
    g.NullECField (g.scalarField (fun _ => c) Vpot) ∧ ¬ g.WeakECField (g.scalarField (fun _ => c) Vpot) :=
  ⟨scalarField_nullECField g _ _, LorentzianMetric.scalarField_const_violates_weak hV⟩

end Field

end Lightlike

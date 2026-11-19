import Lightlike.Spacetime.CausalLadder.NullBoundaryManifold
import Lightlike.Spacetime.CausalLadder.FullSupportMeasure
import Lightlike.Spacetime.CausalLadder.TimeFunctionAssembly

/-!
# Causal simplicity implies stable causality

On a second-countable Hausdorff manifold modelled on `ℝⁿ` (`Fin n → ℝ`), a causally simple Lorentzian
manifold is stably causal (`isStablyCausal_of_isCausallySimple_euclid`). The time function is Hawking's
`x ↦ μ(J⁻(x))` for a finite measure `μ`, positive on nonempty open sets, with the null sets of the volume measure
(`exists_finite_fullSupport_measure`): `μ(J⁻(x))` is continuous
(`continuous_measure_causalPast`: upper semicontinuity from the closedness of `J⁺`, lower semicontinuity from
Fatou's lemma on the interior part `Ĩ⁻(x) = {a | J⁺(a) ∈ 𝓝 x}` of `J⁻(x)`), and the null horismos
`J⁻(x) \ Ĩ⁻(x)` lies in the frontier of the past set `J⁻(x)`, which is null (`volumeMeasure_horismos_eq_zero`: the
push-up lemmas give `a ∈ int J⁻(x) ⇒ x ∈ int J⁺(a)`; a cone argument in chart boxes gives a Lebesgue-null
frontier).

Source read (pdftotext): E. Minguzzi, *Causality theory for closed cone structures with applications*,
arXiv:1709.06494 (Rev. Math. Phys. 31, 2019): Definition 2.18 (\"causally simple if J is closed and antisymmetric\", p. 40),
the causal ladder, Theorem 2.47 (p. 59: \"Causally simple ⇒ Causally continuous ⇒ Causally easy ⇒ Stably causal ⇒ ...\"), and
Theorem 3.17 (p. 117): \"Let (M, C) be a causally simple closed cone structure, then (M, C) is stably causal and J = J_S = K = T₁ = T₂\".
Differences recorded in `docs/notes/p11-source-and-differences.md`: causal simplicity here is pointwise closedness of `J⁺(x)`, `J⁻(x)`
(the Hawking–Ellis form) plus causality, against the closedness of the relation `J` in `M × M`; stable causality here is the existence of a
time function (`IsStablyCausal`), against the source's widening of the cones (their equivalence, Hawking's theorem, is not formalized);
the setting is a smooth Lorentzian manifold modelled on `ℝⁿ`, a special case of the source's closed cone structures. Hawking–Ellis,
ch. 6: not read at a location.
-/

open MeasureTheory Set Filter Topology Manifold
open scoped ContDiff ENNReal Manifold

namespace Lightlike.Causal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : TimeOrientation g)

/-- **Causal simplicity implies stable causality**, for manifolds modelled on `ℝⁿ` (with the Borel
`σ`-algebra). -/
theorem isStablyCausal_of_isCausallySimple_euclid (h : IsCausallySimple T) : IsStablyCausal T := by
  obtain ⟨ν, hfin, hpos, hνv, -⟩ := Lightlike.exists_finite_fullSupport_measure g
  exact isStablyCausal_of_null_horismos T ν hpos
    (fun x => hνv (volumeMeasure_horismos_eq_zero T x)) h

end Lightlike.Causal

import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.LieMetric
/-!
# Coordinate fields along which the metric is constant are Killing

`coordField_killing`: for the Levi-Civita connection of a metric of any signature, a coordinate field `∂_k` of a chart is a Killing
field (`IsKillingAt`, `LieMetric.lean`) at every point of the chart domain when the coordinate components of the metric do not depend
on the coordinate `x^k`. The proof is the identity `g_{νλ} Γ^ν_{μk} + g_{μν} Γ^ν_{λk} = ∂_k g_{μλ}` (metric compatibility in
coordinates) applied to `∇_{∂_μ} ∂_k = Γ^ν_{μk} ∂_ν`.

**Limits.** Manifolds modelled on `Fin n → ℝ` without boundary; the Killing equation is stated with a connection, so it is `L_X g = 0`
for a Levi-Civita connection (`isKillingAt_iff_lieDerivMetric_eq_zero`), which is what the theorem assumes.

Compared with Carroll, *Lecture Notes on General Relativity* (gr-qc/9712019), p. 140, after eq. (5.40): "if all of the components are
independent of one of the coordinates, then the partial derivative vector field associated with that coordinate generates a symmetry of
the tensor", for the metric a Killing field ((5.41)-(5.42)); example (5.45), p. 141: match.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)

/-- **A coordinate field along which the metric components are constant is Killing.** -/
theorem coordField_killing (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g) (k : Fin n)
    (hind : ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target, ∀ a b : Fin n,
      pd k (fun z => g.coordMetric x₀ z a b) y = 0)
    {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    IsKillingAt cov g (coordField x₀ k) p := by
  have hgc := g.isCoordMetric_coordMetric x₀
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  have hy : ψ p ∈ ψ.target := ψ.map_source hp
  have hp0 : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := by
    simpa [tTriv, TangentBundle.trivializationAt_baseSet, hψ, extChartAt_source] using hp
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hX := mdiffAt_coordField x₀ k hp0
  have hcov : cov (coordField x₀ k) p = leviCivita g (coordField x₀ k) p := leviCivita_unique g h hLC hX
  have e1 : ∀ c, coordBasis x₀ hp0 c = coordField x₀ c p := fun c =>
    (coordBasis_apply x₀ hp0 c).trans (symmL_eq_coordField x₀ hp0 c)
  -- the covariant derivative of `∂_k` along `∂_μ`
  have hD : ∀ μ, cov (coordField x₀ k) p (coordField x₀ μ p) =
      ∑ ν, christoffel (g.coordMetric x₀) ν μ k (ψ p) • coordField x₀ ν p := by
    intro μ
    rw [hcov]
    have := leviCivita_coordField g x₀ hy μ k
    rw [ψ.left_inv hp] at this
    exact this
  have hG : ∀ a b, g.g p (coordField x₀ a p) (coordField x₀ b p) = g.coordMetric x₀ (ψ p) a b := by
    intro a b
    have := g_coordField g x₀ a b hy
    rwa [ψ.left_inv hp] at this
  set B : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v w => g.g p (cov (coordField x₀ k) p v) w + g.g p v (cov (coordField x₀ k) p w))
      (fun v v' w => by simp only [map_add, add_apply]; ring)
      (fun c v w => by simp only [map_smul, smul_apply, smul_eq_mul]; ring)
      (fun v w w' => by simp only [map_add]; ring)
      (fun c v w => by simp only [map_smul, smul_eq_mul]; ring) with hB
  have hB0 : B = 0 := by
    refine LinearMap.BilinForm.ext_basis (coordBasis x₀ hp0) fun μ l => ?_
    simp only [hB, LinearMap.mk₂_apply, LinearMap.zero_apply, e1]
    rw [hD μ, hD l]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hG]
    have hs : ∀ a b, g.coordMetric x₀ (ψ p) a b = g.coordMetric x₀ (ψ p) b a := fun a b => by
      have := congrFun (congrFun (hgc.symm (ψ p) hy) a) b
      simpa [Matrix.transpose_apply] using this.symm
    have hF : ∀ a b c, christoffelFirst (g.coordMetric x₀) a b c (ψ p) = christoffelFirst (g.coordMetric x₀) a c b (ψ p) := by
      intro a b c
      simp only [christoffelFirst]
      rw [hgc.pd_symm hy a b c]
      ring
    have t1 : ∑ x, christoffel (g.coordMetric x₀) x μ k (ψ p) * g.coordMetric x₀ (ψ p) x l =
        christoffelFirst (g.coordMetric x₀) l μ k (ψ p) := by
      rw [← hgc.lower_christoffel hy l μ k]
      exact Finset.sum_congr rfl fun x _ => by rw [hs x l]; ring
    have t2 : ∑ x, christoffel (g.coordMetric x₀) x l k (ψ p) * g.coordMetric x₀ (ψ p) μ x =
        christoffelFirst (g.coordMetric x₀) μ l k (ψ p) := by
      rw [← hgc.lower_christoffel hy μ l k]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hpd := hgc.pd_eq_christoffelFirst hy k l μ
    rw [t1, t2, hF l μ k, hF μ l k, ← hpd]
    exact hind _ hy l μ
  intro v w
  have := congrArg (fun B' => B' v w) hB0
  simpa [hB] using this
end Lightlike

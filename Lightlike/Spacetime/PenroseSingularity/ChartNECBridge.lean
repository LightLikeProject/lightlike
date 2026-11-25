import Lightlike.Spacetime.PenroseSingularity.FocalChron
import Lightlike.Spacetime.PenroseSingularity.PenroseChron
import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.HypersurfaceConstraints

/-!
# The null energy condition in charts from the intrinsic Ricci curvature (G1-012)

For the Levi-Civita connection `cov` of `g`, the Ricci curvature `cov.ricciAt` of a null vector being
non-negative gives the chart statement `ChartNEC g`: in the chart at `x₀`, the Ricci tensor of the coordinate
metric is `ricciAt` of the coordinate fields (`ricciAt_coord`), and `ricciAt` is bilinear.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The **null convergence condition**: the Ricci curvature of the connection is non-negative on null vectors. -/
def NullConvergence (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) : Prop :=
  ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x), g.g x v v = 0 → 0 ≤ cov.ricciAt x v v

/-- **The null energy condition in charts from null convergence.** -/
theorem chartNEC_of_nullConvergence (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (hNC : NullConvergence g cov) : ChartNEC g := by
  classical
  intro x₀ z hsrc hnull
  obtain ⟨p, v⟩ := z
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ ψ.target, p = ψ.symm y :=
    ⟨ψ p, ψ.map_source hsrc, (ψ.left_inv hsrc).symm⟩
  have hp : ψ.symm y ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := symm_mem_chartTriv_baseSet x₀ hy
  -- the components of `v` and the expansion in coordinate fields
  set c : Fin n → ℝ := hv (E := Fin n → ℝ) x₀ (ψ.symm y) v with hc
  have hexp : v = ∑ a, c a • coordField x₀ a (ψ.symm y) := by
    set H := (tTriv (E := Fin n → ℝ) x₀).continuousLinearMapAt ℝ (ψ.symm y) with hH
    have hHv : ∀ u, H u = hv (E := Fin n → ℝ) x₀ (ψ.symm y) u := fun u => by
      rw [hH, Bundle.Trivialization.continuousLinearMapAt_apply, Bundle.Trivialization.linearMapAt_apply, ite_eq_left hp]
    have hcomp : hv (E := Fin n → ℝ) x₀ (ψ.symm y) (∑ a, c a • coordField x₀ a (ψ.symm y)) = c := by
      rw [← hHv]
      have h1 : H (∑ a, c a • coordField x₀ a (ψ.symm y)) = ∑ a, c a • H (coordField x₀ a (ψ.symm y)) := by
        simp [map_sum, map_smul]
      rw [h1]
      simp only [hHv, hv_coordField x₀ hp]
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have e1 := symmL_hv x₀ hp v
    have e2 := symmL_hv x₀ hp (∑ a, c a • coordField x₀ a (ψ.symm y))
    rw [hcomp] at e2
    exact e1.symm.trans e2
  have hbil := ricciAt_bilinear (E := Fin n → ℝ) cov (ψ.symm y)
  set B : TangentSpace 𝓘(ℝ, Fin n → ℝ) (ψ.symm y) →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) (ψ.symm y) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun Y Z => cov.ricciAt (ψ.symm y) Y Z) hbil.1 (fun r Y Z => hbil.2.1 r Y Z)
      hbil.2.2.1 (fun r Y Z => hbil.2.2.2 r Y Z) with hB
  have hnn := hNC _ v hnull
  have hrv : cov.ricciAt (ψ.symm y) v v = B v v := rfl
  have hsum : B v v = ∑ a, ∑ b, c a * c b * B (coordField x₀ a (ψ.symm y)) (coordField x₀ b (ψ.symm y)) := by
    conv_lhs => rw [hexp]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hent : ∀ a b, B (coordField x₀ a (ψ.symm y)) (coordField x₀ b (ψ.symm y)) =
      Lightlike.ricci (g.coordMetric x₀) b a y := fun a b => ricciAt_coord cov x₀ g.toNondegMetric hLC hy a b
  rw [hrv, hsum] at hnn
  have hψy : ψ (ψ.symm y) = y := ψ.right_inv hy
  show 0 ≤ ∑ a, ∑ b, Lightlike.ricci (g.coordMetric x₀) a b (ψ (ψ.symm y)) * c a * c b
  rw [hψy]
  simp only [hent] at hnn
  rw [Finset.sum_comm] at hnn
  refine le_of_le_of_eq hnn (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

/-- **Penrose's theorem for the Levi-Civita connection under null convergence, modulo `FocalImpliesChron`.** -/
theorem penrose_of_nullConvergence (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (hNC : NullConvergence g cov)
    (T : Causal.TimeOrientation g) (hGH : Causal.IsGloballyHyperbolic T) (hn : 3 ≤ n) {S : Set M}
    (hS : IsCompact S) (htrap : IsClosedTrappedSpacelikeSurface g cov T S) (Sig : Set M)
    (hCS : Causal.IsCauchySurface T Sig) [ConnectedSpace Sig] [NoncompactSpace Sig]
    (hKne : (frontier (Causal.causalFutureSet T S)).Nonempty) (hChron : FocalImpliesChron g T S) :
    NullGeodesicallyIncomplete g :=
  penrose_of_focal_chron g hLC T hGH hn hS htrap Sig hCS hKne hChron (chartNEC_of_nullConvergence g hLC hNC)

end Lightlike.Penrose

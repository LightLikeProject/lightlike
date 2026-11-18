import Lightlike.GR.Schwarzschild
import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.LeviCivitaSmooth

/-!
# The exterior Schwarzschild metric on the manifold layer

`schOpen M hM` is the open set `schU M = {2M < r, 0 < θ < π}` of `ℝ⁴` (coordinates `(t, r, θ, φ)`, index `0` is the time `t`)
as a manifold, and `schwarzschildMetric M hM` the smooth Lorentzian metric (`LorentzianMetric`, signature `−+++`) with the
components of the existing coordinate metric `schMetric M` (`Lightlike/GR/Schwarzschild.lean`):

* `schwarzschild_coordMetric` (**the bridge**): in every chart of the manifold the coordinate components of
  `schwarzschildMetric M hM` are `schMetric M`;
* `schwarzschild_satisfiesEinstein`: for the Levi-Civita connection of `schwarzschildMetric M hM` the vacuum Einstein
  equations hold (`Connection.lean`, `NondegMetric.SatisfiesEinstein` with `Λ = 0`);
* `schwarzschild_ricci_eq_zero`: its Ricci tensor vanishes.

Proof. The Einstein equations on a manifold are the coordinate vacuum equations in every chart
(`satisfiesEinstein_iff_chart_proved`); the charts of an open subset of `ℝ⁴` are restrictions of the identity, so the
coordinate components are `schMetric M` (`openMetric_coordMetric`) and the coordinate result `sch_isVacuumSolution` applies.

**The exterior region `r > 2M`.** All statements here are about the exterior region `r > 2M` only.

**Differences from the cited statement**, approved on 17 November 2026 (the comparison with the sources is pending: Carroll, *Spacetime and Geometry*, ch. 7, eq. (7.29),
and Wald, *General Relativity*, ch. 6, were not read at the cited locations): the manifold is the chart domain of the
coordinates `(t, r, θ, φ)` with `r > 2M` and `0 < θ < π` and **no condition on `φ ∈ ℝ`**, so it is a covering of the
exterior region with the axis removed, not `ℝ × (2M, ∞) × S²`; there is no extension across `r = 2M`; the coordinate
order is `(t, r, θ, φ)` with signature `−+++` (the convention of this library); the Einstein equations are those of
`Connection.lean` for the Levi-Civita connection, whose existence and uniqueness are `leviCivita_exists_unique_proved`;
`M > 0`. The theorems are for every `C^∞` Levi-Civita connection (`ContMDiffCovariantDerivative cov ∞`); such a connection
exists (`schwarzschild_exists_vacuum_connection`: `leviCivita g` is smooth by `contMDiffCovariantDerivative_leviCivita`).
-/

open Bundle Manifold Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

section Congr
variable {n : ℕ} {g₁ g₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- Two metrics that agree on an open set have the same Christoffel symbols there. -/
theorem christoffel_congr_on (hU : IsOpen U) (h : ∀ y ∈ U, g₁ y = g₂ y) {y : Fin n → ℝ} (hy : y ∈ U)
    (i j k : Fin n) : christoffel g₁ i j k y = christoffel g₂ i j k y := by
  have hev : ∀ a b : Fin n, (fun z => g₁ z a b) =ᶠ[nhds y] fun z => g₂ z a b := fun a b => by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [h z hz]
  simp only [christoffel, h y hy, pd_congr (hev _ _)]

/-- Two metrics that agree on an open set have the same Riemann tensor there. -/
theorem riemann_congr_on (hU : IsOpen U) (h : ∀ y ∈ U, g₁ y = g₂ y) {y : Fin n → ℝ} (hy : y ∈ U)
    (ρ σ μ ν : Fin n) : riemann g₁ ρ σ μ ν y = riemann g₂ ρ σ μ ν y := by
  have hev : ∀ a b c : Fin n, christoffel g₁ a b c =ᶠ[nhds y] christoffel g₂ a b c := fun a b c => by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact christoffel_congr_on hU h hz a b c
  simp only [riemann, pd_congr (hev _ _ _), christoffel_congr_on hU h hy]

/-- Two metrics that agree on an open set have the same Ricci tensor there. -/
theorem ricci_congr_on (hU : IsOpen U) (h : ∀ y ∈ U, g₁ y = g₂ y) {y : Fin n → ℝ} (hy : y ∈ U)
    (σ ν : Fin n) : ricci g₁ σ ν y = ricci g₂ σ ν y := by
  simp only [ricci, riemann_congr_on hU h hy]

/-- Two metrics that agree on an open set have the same scalar curvature there. -/
theorem scalarCurvature_congr_on (hU : IsOpen U) (h : ∀ y ∈ U, g₁ y = g₂ y) {y : Fin n → ℝ} (hy : y ∈ U) :
    scalarCurvature g₁ y = scalarCurvature g₂ y := by
  simp only [scalarCurvature, ricci_congr_on hU h hy, h y hy]

/-- Two metrics that agree on an open set have the same Einstein tensor there. -/
theorem einsteinTensor_congr_on (hU : IsOpen U) (h : ∀ y ∈ U, g₁ y = g₂ y) {y : Fin n → ℝ} (hy : y ∈ U)
    (μ ν : Fin n) : einsteinTensor g₁ μ ν y = einsteinTensor g₂ μ ν y := by
  simp only [einsteinTensor, ricci_congr_on hU h hy, scalarCurvature_congr_on hU h hy, h y hy]
end Congr

variable (M : ℝ) (hM : 0 < M)

/-- The exterior Schwarzschild domain `r > 2M`, `0 < θ < π` as an open subset of `ℝ⁴`. -/
def schOpen : Opens (Fin 4 → ℝ) := ⟨schU M, (isCoordMetric_sch M hM).isOpen⟩

/-- **The exterior Schwarzschild metric** as a smooth Lorentzian metric on the manifold `schOpen M hM`. -/
def schwarzschildMetric : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) (schOpen M hM) 4 :=
  openMetric (schOpen M hM) (schMetric M) (sch_isLorentzian M hM)

/-- **The bridge**: in every chart its coordinate components are the existing coordinate Schwarzschild metric. -/
theorem schwarzschild_coordMetric (x₀ : schOpen M hM) {y : Fin 4 → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).target) :
    (schwarzschildMetric M hM).coordMetric x₀ y = schMetric M y :=
  openMetric_coordMetric (schOpen M hM) (schMetric M) (sch_isLorentzian M hM) x₀ hy

/-- The chart target lies in the exterior domain. -/
theorem target_subset_schU (x₀ : schOpen M hM) :
    (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).target ⊆ schU M := fun y hy => by
  have h2 : (((extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).symm y : schOpen M hM) : Fin 4 → ℝ) ∈ schU M :=
    ((extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).symm y : schOpen M hM).2
  rwa [opens_extChartAt_symm (schOpen M hM) x₀ hy] at h2

variable (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (schOpen M hM))
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- In every chart the coordinate Einstein tensor of `schwarzschildMetric` vanishes. -/
theorem schwarzschild_coord_vacuum (x₀ : schOpen M hM) :
    IsVacuumSolution 0 ((schwarzschildMetric M hM).coordMetric x₀) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).target := by
  refine ⟨(schwarzschildMetric M hM).isCoordMetric_coordMetric x₀, fun y hy μ ν => ?_⟩
  have hcongr : ∀ z ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).target,
      (schwarzschildMetric M hM).coordMetric x₀ z = schMetric M z := fun z hz =>
    schwarzschild_coordMetric M hM x₀ hz
  rw [einsteinTensor_congr_on (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 4 → ℝ)) x₀) hcongr hy]
  simp [einstein_sch M (schU_subset M hM (target_subset_schU M hM x₀ hy)) μ ν]

/-- **Exterior Schwarzschild solves the vacuum Einstein equations on the manifold layer**: for the Levi-Civita
connection of `schwarzschildMetric M hM` the equations `Ric - (S/2) g = 0` hold at every point. -/
theorem schwarzschild_satisfiesEinstein (h : cov.IsLeviCivita (schwarzschildMetric M hM)) :
    (schwarzschildMetric M hM).SatisfiesEinstein cov 0 :=
  (satisfiesEinstein_iff_chart_proved cov (schwarzschildMetric M hM) h 0).2
    fun x₀ => schwarzschild_coord_vacuum M hM x₀

/-- **The Ricci tensor of exterior Schwarzschild vanishes** on the manifold layer. -/
theorem schwarzschild_ricci_eq_zero (h : cov.IsLeviCivita (schwarzschildMetric M hM)) (x : schOpen M hM)
    (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x) : cov.ricciAt x v w = 0 := by
  have hE := (schwarzschild_satisfiesEinstein M hM cov h).2 x v w
  have hzs : x ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x).source := mem_extChartAt_source x
  have hy : extChartAt 𝓘(ℝ, Fin 4 → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x).map_source hzs
  have hS := scalarCurvatureAt_coord cov x (schwarzschildMetric M hM) h hy
  rw [(extChartAt 𝓘(ℝ, Fin 4 → ℝ) x).left_inv hzs] at hS
  have hcongr : ∀ z ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x).target,
      (schwarzschildMetric M hM).coordMetric x z = schMetric M z := fun z hz =>
    schwarzschild_coordMetric M hM x hz
  have hy' := target_subset_schU M hM x hy
  have hS0 : scalarCurvature ((schwarzschildMetric M hM).coordMetric x) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x x) = 0 := by
    rw [scalarCurvature_congr_on (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 4 → ℝ)) x) hcongr hy]
    unfold scalarCurvature
    exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by
      rw [ricci_sch M (schU_subset M hM hy'), mul_zero]
  rw [hS, hS0] at hE
  linarith


/-- **Non-vacuity**: the Levi-Civita connection `leviCivita` of the exterior Schwarzschild metric is a smooth Levi-Civita
connection and satisfies the vacuum Einstein equations with vanishing Ricci tensor. -/
theorem schwarzschild_exists_vacuum_connection :
    ∃ cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (schOpen M hM),
      cov.IsLeviCivita (schwarzschildMetric M hM) ∧
        CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ∧
        (schwarzschildMetric M hM).SatisfiesEinstein cov 0 ∧
        ∀ (x : schOpen M hM) (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x), cov.ricciAt x v w = 0 := by
  have hLC : (leviCivita (schwarzschildMetric M hM)).IsLeviCivita (schwarzschildMetric M hM) :=
    ⟨leviCivita_torsion _, leviCivita_compat _⟩
  haveI := contMDiffCovariantDerivative_leviCivita (schwarzschildMetric M hM)
  exact ⟨leviCivita (schwarzschildMetric M hM), hLC, this,
    schwarzschild_satisfiesEinstein M hM _ hLC, schwarzschild_ricci_eq_zero M hM _ hLC⟩

end Lightlike

import Mathlib
import Lightlike.Geometry.HeatKernel.ChartParametrix

/-!
# The properties of the parametrix in a chart, bundled

`Lightlike.IsChartParametrix g U x N r u H Ω θ σ V` collects everything `Lightlike.exists_chart_parametrix` proves about
the cut-off parametrix `H(t, p, y) = θ(y − p) (4πt)^{-n/2} e^{-σ(p, y)/4t} Σ_{k ≤ N} tᵏ u_k(p, y)` of a Riemannian
coordinate metric `g` on `U` near `x`: the diagonal, the Gaussian and integral bounds, the heat error bound, the
structure (domain `Ω`, cutoff `θ`, world function `σ = g_p(V, V)`, coefficients `u_k`) and the expanded heat error.
`Lightlike.exists_isChartParametrix` restates the existence theorem in this form, so that later properties (the delta
property, derivative bounds of the heat error) can be proved from the bundle.
-/

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **The properties of the parametrix of order `N` in a chart**, near `x`. -/
structure IsChartParametrix (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (N : ℕ) (r : ℝ) (u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))) (θ : (Fin n → ℝ) → ℝ)
    (σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) : Prop where
  r_pos : 0 < r
  u_zero_diag : ∀ p, ‖p - x‖ < r → u 0 (p, p) = 1
  diag_eq : ∀ t > 0, ∀ p, ‖p - x‖ < r →
    H t p p = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ∑ k ∈ Finset.range (N + 1), t ^ k * u k (p, p)
  gauss_le : ∃ C a : ℝ, 0 < a ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y,
    |H t p y| ≤ C * t ^ (-(n : ℝ) / 2) * Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t)
  integral_abs_le : ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∫ y, |H t p y| ≤ C
  isOpen : IsOpen Ω
  center_mem : (x, x) ∈ Ω
  mem_of_lt : ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → (p, y) ∈ Ω
  snd_mem : ∀ q ∈ Ω, q.2 ∈ U
  V_smooth : ContDiffOn ℝ ∞ V Ω
  u_smooth : ∀ k, ContDiffOn ℝ ∞ (u k) Ω
  V_diag : ∀ p, (p, p) ∈ Ω → V (p, p) = 0 ∧
    HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p
  σ_eq : ∀ q ∈ Ω, σ q = Geodesic.pairing g q.1 (V q) (V q)
  θ_one : ∀ z, ‖z‖ < r / 2 → θ z = 1
  θ_zero : ∀ z, r ≤ ‖z‖ → θ z = 0
  θ_mem : ∀ z, θ z ∈ Icc (0 : ℝ) 1
  θ_smooth : ContDiff ℝ ∞ θ
  θ_tsupport : tsupport θ ⊆ ball 0 r
  θ_eventually_one : ∀ z, ‖z‖ < r / 2 → θ =ᶠ[𝓝 z] fun _ => 1
  H_cont : ∀ t p, ‖p - x‖ < r → Continuous (H t p)
  heatError_eq : ∀ t > 0, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → ∃ D, HasDerivAt (fun s => H s p y) D t ∧
    D + coordLaplacian g (H t p) y =
      θ (y - p) * (heatGaussian n (σ (p, y)) t * (t ^ N * coordLaplacian g (fun z => u N (p, z)) y)) +
        (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (gaussFactor t (σ (p, y)) * truncAnsatz (fun k y => u k (p, y)) N t y *
          coordLaplacian g (fun z => θ (z - p)) y - 2 * (gaussFactor t (σ (p, y)) *
            ((∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y) -
              truncAnsatz (fun k y => u k (p, y)) N t y *
                coordGradPair g (fun z => θ (z - p)) (fun z => σ (p, z)) y / (4 * t))))
  σ_lower : ∃ c : ℝ, 0 < c ∧ ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → c * ‖y - p‖ ^ 2 ≤ σ (p, y)
  ansatz_le : ∃ A : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r →
    |truncAnsatz (fun k y => u k (p, y)) N t y| ≤ A
  H_eq : ∀ t p y, H t p y = θ (y - p) * (heatGaussian n (σ (p, y)) t * truncAnsatz (fun k y => u k (p, y)) N t y)
  heatError_le : ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y, ∃ D, HasDerivAt (fun s => H s p y) D t ∧
    |D + coordLaplacian g (H t p) y| ≤ C * t ^ ((N : ℝ) - n / 2)

/-- **The parametrix in a chart exists**, with all its properties bundled. -/
theorem exists_isChartParametrix {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (N : ℕ) :
    ∃ r u H Ω θ σ V, IsChartParametrix g U x N r u H Ω θ σ V := by
  obtain ⟨r, u, H, hr, hu0, hHd, hGa, hL1, ⟨Ω, θ, σ, V, hΩo, hxΩ, hmem, hΩU, hVs, hus, hVd, hσV, hθ1, hθ0, hθr,
    hθc, hθsupp, hHc, hform, hσlow, hA, hH⟩, herr⟩ := exists_chart_parametrix hg hx N
  have hr' := hr
  refine ⟨r, u, H, Ω, θ, σ, V, ⟨hr, hu0, hHd, hGa, hL1, hΩo, hxΩ, hmem, hΩU, hVs, hus, hVd, hσV, hθ1, hθ0, hθr, hθc,
    hθsupp, fun z hz => ?_, hHc, hform, hσlow, hA, hH, herr⟩⟩
  have hev : ∀ᶠ w in 𝓝 z, ‖w‖ < r / 2 := (isOpen_lt continuous_norm continuous_const).mem_nhds hz
  filter_upwards [hev] with w hw using hθ1 w hw

end Lightlike

import Lightlike.Spacetime.PenroseSingularity.FocalData

/-!
# Components of the intrinsic Jacobi field in a chart (G1-012, step D4)

In the chart family `H (t, σ) = ψ (Γ (zS σ) t)`, the components of the intrinsic Jacobi field `jacV v t` and of the
velocity are `∂_v H` and `∂_t H`.
-/

open Set Filter Topology Manifold Bundle Matrix
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)}

/-- **The components of `jacV v t` in the chart at `x₀`.** -/
theorem comp_jacV (hF : FlowFamily g Γ zS Nz J Sg) {x₀ : M} {σ : Fin m → ℝ} (hσ : σ ∈ Sg) {t : ℝ} (ht : t ∈ J)
    (hsrc : Γ (zS σ) t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hHd : DifferentiableAt ℝ (chartH g Γ zS x₀) (t, σ)) (v : Fin m → ℝ) :
    comp x₀ (jacV g Γ zS σ v t) = fderiv ℝ (chartH g Γ zS x₀) (t, σ) (0, v) := by
  have hmd := hF.mdifferentiableAt_slice hσ ht
  have h1 := fderiv_coord x₀ hmd hsrc v
  have hc : HasFDerivAt (fun σ' : Fin m → ℝ => ((t, σ') : ℝ × (Fin m → ℝ)))
      ((0 : (Fin m → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin m → ℝ))) σ :=
    (hasFDerivAt_const t σ).prodMk (hasFDerivAt_id σ)
  have h2 := hHd.hasFDerivAt.comp σ hc
  have h3 : fderiv ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS σ') t)) σ v =
      fderiv ℝ (chartH g Γ zS x₀) (t, σ) (0, v) := by
    show fderiv ℝ (chartH g Γ zS x₀ ∘ Prod.mk t) σ v = _
    rw [h2.fderiv]
    simp
  rw [← h3, h1]
  rfl

end Lightlike.Penrose

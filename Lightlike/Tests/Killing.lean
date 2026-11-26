import Lightlike.Spacetime.SphereManifold
import Lightlike.Spacetime.CoordKilling

/-!
# Trust checks: a Killing field and a non-Killing field of the round 2-sphere

On the chart domain `0 < θ < π` of the round sphere of radius `r` (`roundSphereMetric`, metric
`r² dθ² + r² sin²θ dφ²`):

* `rotation_killing_S2`: the rotation field `∂_φ` is a Killing field at every point of the chart
  domain, for every Levi-Civita connection (from `coordField_killing`: the components of the metric
  do not depend on `φ`).
* `dilation_not_killing_S2`: the dilation `θ ∂_θ` of the polar coordinate is not Killing, at the
  point `θ = π/4`: `(L_X g)(∂_φ, ∂_φ) = (π/4) r² ≠ 0` there.

Only the second needs the Lie derivative (`lieDerivMetric`, with `[θ ∂_θ, ∂_φ] = 0`); the
wrong-model control is the dilation itself, and the rotation is the positive control.
-/

open Bundle Manifold Set TopologicalSpace Matrix VectorField
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Test

variable (r : ℝ) (hr : r ≠ 0)

/-- **The rotation field `∂_φ` is Killing** on the round 2-sphere (chart domain), for every
Levi-Civita connection of `roundSphereMetric r hr`. -/
theorem rotation_killing_S2 (cov : Connection 𝓘(ℝ, Fin 2 → ℝ) sphereOpen)
    (h : cov.IsLeviCivita (roundSphereMetric r hr)) (x₀ p : sphereOpen)
    (hp : p ∈ (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x₀).source) :
    IsKillingAt cov (roundSphereMetric r hr) (coordField x₀ 1) p := by
  refine coordField_killing (roundSphereMetric r hr) x₀ cov h 1 ?_ hp
  intro y hy a b
  have hev : (fun z => (roundSphereMetric r hr).coordMetric x₀ z a b) =ᶠ[nhds y]
      fun z => twoMetric (r ^ 2) (r ^ 2) z a b := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 2 → ℝ)) x₀).mem_nhds hy] with z hz
    rw [roundSphere_coordMetric r hr x₀ hz]
  unfold pd
  rw [hev.fderiv_eq]
  fin_cases a <;> fin_cases b
  · simp [twoMetric, twoD]
  · simp [twoMetric]
  · simp [twoMetric]
  · have := pd_twoD1 (r ^ 2) 1 y
    simpa [twoMetric, twoD, pd] using this

/-- The dilation `θ ∂_θ` of the polar coordinate in the chart at `x₀`. -/
def dilationField (x₀ : sphereOpen) : Π p : sphereOpen, TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p :=
  (fun p => (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x₀ p) 0) • coordField x₀ 0

/-- **The dilation `θ ∂_θ` is not a Killing field** of the round 2-sphere at the point `θ = π/4`
(chart centred there), for every Levi-Civita connection: `(L_X g)(∂_φ, ∂_φ) = (π/4) r² ≠ 0`. -/
theorem dilation_not_killing_S2 (cov : Connection 𝓘(ℝ, Fin 2 → ℝ) sphereOpen)
    (h : cov.IsLeviCivita (roundSphereMetric r hr)) (q : sphereOpen) (hq : q.1 0 = Real.pi / 4) :
    ¬ IsKillingAt cov (roundSphereMetric r hr) (dilationField q) q := by
  intro hK
  set ψ := extChartAt 𝓘(ℝ, Fin 2 → ℝ) q with hψ
  have hz : q ∈ ψ.source := mem_extChartAt_source q
  have hy : ψ q ∈ ψ.target := ψ.map_source hz
  have hp0 : q ∈ (chartTriv 2 q).baseSet := by
    simp
  have h1 : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (extChartAt 𝓘(ℝ, Fin 2 → ℝ) q) q :=
    mdifferentiableAt_extChartAt (mem_chart_source (Fin 2 → ℝ) q)
  have hf : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) (fun p : sphereOpen => (ψ p) 0) q := by
    have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).differentiableAt
      (x := ψ q) |>.comp_mdifferentiableAt h1
    exact h2
  have hV0 := mdiffAt_coordField q 0 hp0
  have hV := mdiffAt_coordField q 1 hp0
  have hX : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) (𝓘(ℝ, Fin 2 → ℝ).prod 𝓘(ℝ, Fin 2 → ℝ))
      (fun p : sphereOpen => (⟨p, dilationField q p⟩ : TangentBundle 𝓘(ℝ, Fin 2 → ℝ) sphereOpen)) q := by
    unfold dilationField
    exact MDifferentiableAt.smul_section hf hV0
  have key := (isKillingAt_iff_lieDerivMetric_eq_zero h hX).1 hK _ _ hV hV
  -- the symbols at the centre of the chart
  have hsy : ψ.symm (ψ q) = q := ψ.left_inv hz
  have hzs : ψ.symm (ψ q) ∈ ψ.source := ψ.map_target hy
  have hf' : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) (fun p : sphereOpen => (ψ p) 0) (ψ.symm (ψ q)) := by
    rw [hsy]; exact hf
  -- `d(θ)(∂_φ) = 0`
  have hdf0 : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) (fun p : sphereOpen => (ψ p) 0) (ψ.symm (ψ q))
      (coordField q 1 (ψ.symm (ψ q))) = 0 := by
    rw [mfderiv_eq_chart _ q _ hzs hf', mfderiv_chart_coordField (n := 2) q 1 hy, ψ.right_inv hy]
    have hev : ((fun p : sphereOpen => (ψ p) 0) ∘ ψ.symm) =ᶠ[nhds (ψ q)] fun z => z 0 := by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 2 → ℝ)) q).mem_nhds hy] with z hz'
      simp [ψ.right_inv hz']
    rw [hev.fderiv_eq]
    have hc : fderiv ℝ (fun z : Fin 2 → ℝ => z 0) (ψ q) =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).fderiv
    rw [hc]
    simp
    rfl
  have hdf : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) (fun p : sphereOpen => (ψ p) 0) q (coordField q 1 q) = 0 := by
    rw [hsy] at hdf0; exact hdf0
  have hbr : mlieBracket 𝓘(ℝ, Fin 2 → ℝ) (dilationField q) (coordField q 1) q = 0 := by
    unfold dilationField
    rw [mlieBracket_smul_left hf hV0]
    have hc := mlieBracket_coordField (n := 2) q 0 1 hy
    rw [hsy] at hc
    simp [hc]
    left; exact hdf
  unfold lieDerivMetric at key
  rw [hbr] at key
  simp only [map_zero, sub_zero] at key
  have hg0 := mvfderiv_gpair_coordField (roundSphereMetric r hr) q 1 1 0 hy
  rw [hsy] at hg0
  have hXq : dilationField q q = (ψ q 0) • coordField q 0 q := rfl
  rw [hXq, map_smul] at key
  have hψq : ψ q 0 = Real.pi / 4 := by
    rw [hψ, opens_extChartAt_apply]; exact hq
  have hev : (fun z => (roundSphereMetric r hr).coordMetric q z 1 1) =ᶠ[nhds (ψ q)]
      fun z => r ^ 2 * Real.sin (z 0) ^ 2 := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 2 → ℝ)) q).mem_nhds hy] with z hz'
    rw [roundSphere_coordMetric r hr q hz']
    simp [twoMetric, twoD]
  have hpd : pd 0 (fun z => (roundSphereMetric r hr).coordMetric q z 1 1) (ψ q) =
      r ^ 2 * (2 * Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4)) := by
    have := pd_twoD1 (r ^ 2) 0 (ψ q)
    unfold pd at this ⊢
    rw [hev.fderiv_eq]
    simpa [hψq] using this
  rw [hg0, hpd, hψq] at key
  have hs : Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) = 1 / 2 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have h2 : 2 * Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) = 1 := by linarith
  rw [h2] at key
  simp at key
  exact hr key


end Lightlike.Test

end

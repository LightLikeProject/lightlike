import Mathlib

/-!
# Growth equation: the scalar core (row G1-032)

Linear perturbation of a self-gravitating fluid in comoving coordinates (Bernardeau et al. 2002,
Section 2.3, source key `bernardeau-2002`), at a fixed comoving point and as functions of time `t`.
Write `a` for the scale factor, `H = a'/a`, `δ` for the density contrast, `D = ∇·u` for the
divergence of the peculiar velocity, `Lφ = Δφ` and `Lδ = Δδ` for the comoving Laplacians of the
potential and of `δ`. The linearized system is

* continuity `δ' = -D/a`,
* Euler (divergence) `D' = -H D - Δφ/a - c_s² Δδ/a`,
* Poisson `Δφ = 4πG a² ρ δ`.

`growth_core` eliminates `D`, `Δφ` and gives `δ'' + 2Hδ' - 4πGρδ = (c_s²/a²) Δδ`. This is the
purely algebraic step; the reduction from the vector fields lives in `Lightlike.Cosmology.GrowthEquation`
(later files).
-/

open Filter Topology

namespace Lightlike.Cosmology.GrowthEquation

/-- **Growth equation, scalar core.** With the linearized continuity equation `δ' = -D/a` near `t`,
the divergence of the linearized Euler equation `D' = -(a'/a) D - Δφ/a - c_s² Δδ/a` and the
Poisson equation `Δφ = 4πG a² ρ δ`, one has
`δ'' + 2 (a'/a) δ' - 4πG ρ δ - (c_s²/a²) Δδ = 0`. -/
theorem growth_core (a δ D Lφ Lδ ρ : ℝ → ℝ) (G cs t : ℝ)
    (ha : DifferentiableAt ℝ a t) (ha0 : a t ≠ 0) (hD : DifferentiableAt ℝ D t)
    (hcont : ∀ᶠ s in 𝓝 t, deriv δ s = -D s / a s)
    (heul : deriv D t = -(deriv a t / a t) * D t - Lφ t / a t - cs ^ 2 * Lδ t / a t)
    (hpois : Lφ t = 4 * Real.pi * G * a t ^ 2 * ρ t * δ t) :
    deriv (deriv δ) t + 2 * (deriv a t / a t) * deriv δ t - 4 * Real.pi * G * ρ t * δ t
      - cs ^ 2 / a t ^ 2 * Lδ t = 0 := by
  have h1 : deriv (deriv δ) t = deriv (fun s => -D s / a s) t :=
    Filter.EventuallyEq.deriv_eq hcont
  have h2 : HasDerivAt (fun s => -D s / a s)
      ((-(deriv D t) * a t - (-D t) * deriv a t) / a t ^ 2) t :=
    (hD.hasDerivAt.neg).div ha.hasDerivAt ha0
  rw [h1, h2.deriv, hcont.self_of_nhds, heul, hpois]
  field_simp
  ring

end Lightlike.Cosmology.GrowthEquation

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.growth_core := _root_.Lightlike.Cosmology.GrowthEquation.growth_core

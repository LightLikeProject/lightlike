import Lightlike.Spacetime.VariationIntegral
import Lightlike.Spacetime.EHManifold.FRVariation

/-!
# The first variation of the `f(R)` action over a compact set

`fR_variation`: for a smooth nondegenerate symmetric coordinate metric `g`, a smooth symmetric perturbation
`h`, a `C¹` function `f` and a compact set `T`,

`d/dt ∫_T √|g_t| f(R(g_t)) = ∫_T (-√|g| (f'(R) R^{αβ} - ½ f(R) g^{αβ}) h_{αβ} + f'(R) ∂_ρ (√|g| W^ρ))`

at `t = 0`. For `f(R) = R` this is the Einstein–Hilbert variation. The second term is not yet integrated by
parts, so this is not the form (6) of Sotiriou–Faraoni: the terms `-[∇_μ ∇_ν - g_{μν} □] f'(R)` are still
written as `f'(R)` times a divergence.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, eqs. (5), (6), p. 5.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)
include hg hh hdet

/-- The `f(R)` density family is `C¹` in `(t, x)` near `t = 0`. -/
theorem contDiffAt_fRDensity (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : Fin n → ℝ) :
    ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) := by
  have hx0 : (g x + (0 : ℝ) • h x).det ≠ 0 := by simpa using hdet x
  have hentry : ∀ i j, ContDiff ℝ 1 (fun p : ℝ × (Fin n → ℝ) => (g p.2 + p.1 • h p.2) i j) := by
    intro i j
    show ContDiff ℝ 1 (fun p : ℝ × (Fin n → ℝ) => g p.2 i j + p.1 * h p.2 i j)
    exact (((hg i j).of_le (by simp)).comp contDiff_snd).add
      (contDiff_fst.mul (((hh i j).of_le (by simp)).comp contDiff_snd))
  have hdetc : ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => (g p.2 + p.1 • h p.2).det) (0, x) :=
    (contDiff_det_of hentry).contDiffAt
  have hs : ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => √|(g p.2 + p.1 • h p.2).det|) (0, x) :=
    contDiffAt_sqrt_abs hdetc hx0
  have hs0 : √|(g x + (0 : ℝ) • h x).det| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 hx0)).ne'
  have hL := contDiffAt_lagDensity g h hg hh 0 0 x hx0
  have hquot : ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) =>
      lagDensity g h 0 p.1 p.2 / √|(g p.2 + p.1 • h p.2).det|) (0, x) := hL.div hs hs0
  have hcomp : ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => √|(g p.2 + p.1 • h p.2).det| *
      f (lagDensity g h 0 p.1 p.2 / √|(g p.2 + p.1 • h p.2).det|)) (0, x) :=
    hs.mul (hf.contDiffAt.comp _ hquot)
  refine hcomp.congr_of_eventuallyEq ?_
  have hne : ∀ᶠ p : ℝ × (Fin n → ℝ) in 𝓝 ((0 : ℝ), x), √|(g p.2 + p.1 • h p.2).det| ≠ 0 :=
    hs.continuousAt.eventually_ne hs0
  filter_upwards [hne] with p hp
  show fRDensity g h f p.1 p.2 = √|(g p.2 + p.1 • h p.2).det| *
    f (lagDensity g h 0 p.1 p.2 / √|(g p.2 + p.1 • h p.2).det|)
  have hq : lagDensity g h 0 p.1 p.2 / √|(g p.2 + p.1 • h p.2).det| =
      scalarCurvature (fun z => g z + p.1 • h z) p.2 := by
    unfold lagDensity
    field_simp
    ring
  rw [hq]
  rfl

include hgs hhs in
/-- **The first variation of the `f(R)` action over a compact set.** -/
theorem fR_variation (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {T : Set (Fin n → ℝ)} (hT : IsCompact T) :
    HasDerivAt (fun t : ℝ => ∫ x in T, fRDensity g h f t x)
      (∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        deriv f (scalarCurvature g x) * ehFluxDiv g h x)) 0 := by
  have hΦc : ∀ x, ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) :=
    fun x => contDiffAt_fRDensity g h hg hh hdet f hf x
  have hmain := hasDerivAt_integral_family (μ := (volume : Measure (Fin n → ℝ))) hT
    (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (fun x _ => hΦc x)
  have hder : ∀ x, fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) (1, 0) =
      -√|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        deriv f (scalarCurvature g x) * ehFluxDiv g h x := by
    intro x
    have h1 := hasDerivAt_fRDensity g h hg hh hgs hhs x (hdet x) f (deriv f (scalarCurvature g x))
      ((hf.differentiable (by simp)).differentiableAt.hasDerivAt)
    have h2 : HasDerivAt (fun t : ℝ => fRDensity g h f t x)
        (fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) (1, 0)) 0 := by
      have hd := ((hΦc x).differentiableAt (by simp)).hasFDerivAt
      have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Fin n → ℝ)) 0 :=
        (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
      exact hd.comp_hasDerivAt (0 : ℝ) hl
    exact h2.unique h1
  have hint : ∫ x in T, fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) (1, 0) =
      ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        deriv f (scalarCurvature g x) * ehFluxDiv g h x) :=
    setIntegral_congr_fun hT.isClosed.measurableSet fun x _ => hder x
  rw [hint] at hmain
  exact hmain

end Lightlike

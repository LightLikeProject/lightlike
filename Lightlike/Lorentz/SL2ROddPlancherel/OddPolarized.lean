import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.SphericalClean
import Lightlike.Lorentz.SL2RPlancherel.Linearity
import Lightlike.Lorentz.SL2ROddPlancherel.ComplexFourier

/-!
# The polarised spherical Plancherel identity

For `F`, `G` smooth with compact support and `F̂ = sphTransformH F`,

  `π² ∫_{v>1} conj(F) G dv = ¼ ∫_{ρ>0} ρ tanh(πρ) conj(F̂(ρ)) Ĝ(ρ) dρ`   (`sph_polarized`),

the sesquilinear form of `norm_sq_eq_sph`. It is derived by the polarisation identity
`4 conj(x) y = |x + y|² - |x - y|² - i |x + i y|² + i |x - i y|²` from the norm identity applied to `F ± G`,
`F ± iG` (`sphTransformH` is linear on smooth compactly supported functions); the weights
`ρ tanh(πρ) |Ĥ(ρ)|²` are integrable by the strip decay of `ComplexFourier.lean` (`integrable_sphWeight`).
It is used for the pair `(G, vG)` in the odd Plancherel identity
(`docs/notes/sl2r-odd-plancherel-route.md`).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2RPlancherel

/-- **Polarisation** for complex numbers (with the real squared norms cast to `ℂ`). -/
lemma polar_complex (x y : ℂ) :
    4 * (conj x * y) = ((‖x + y‖ ^ 2 : ℝ) : ℂ) - ((‖x + (-1 : ℂ) * y‖ ^ 2 : ℝ) : ℂ) -
      I * (((‖x + I * y‖ ^ 2 : ℝ) : ℂ) - ((‖x + (-I) * y‖ ^ 2 : ℝ) : ℂ)) := by
  apply Complex.ext <;>
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

/-- The weight `ρ tanh(πρ) ‖Ĥ(ρ)‖²` of the spherical Plancherel formula is integrable. -/
lemma integrable_sphWeight {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    Integrable fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH H ρ‖ ^ 2 := by
  have hg : ContDiff ℝ 2 (abelTransform H) := (contDiff_abelTransform H hH hc).of_le (by norm_cast)
  obtain ⟨C, hC0, hC⟩ := norm_ftC_le hg (hasCompactSupport_abelTransform H hc) 0
  have hcont : Continuous fun ρ : ℝ => sphTransformH H ρ := by
    have h := (differentiable_ftC (contDiff_abelTransform H hH hc).continuous
      (hasCompactSupport_abelTransform H hc)).continuous.comp Complex.continuous_ofReal
    exact h.congr fun ρ => by simp [ftC_ofReal]
  have htanh : Continuous fun ρ : ℝ => Real.tanh (Real.pi * ρ) := by
    have : (fun ρ : ℝ => Real.tanh (Real.pi * ρ)) =
        fun ρ => Real.sinh (Real.pi * ρ) / Real.cosh (Real.pi * ρ) := funext fun ρ => Real.tanh_eq_sinh_div_cosh _
    rw [this]
    exact (Real.continuous_sinh.comp (by fun_prop)).div (Real.continuous_cosh.comp (by fun_prop))
      fun ρ => (Real.cosh_pos _).ne'
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (C ^ 2))
    ((continuous_id.mul htanh).mul (hcont.norm.pow 2)).aestronglyMeasurable (Eventually.of_forall fun ρ => ?_)
  have hb : ‖sphTransformH H ρ‖ ≤ C / (1 + ρ ^ 2) := by
    have := hC ρ 0 (by simp)
    simpa [← ftC_ofReal] using this
  have hpos : 0 < 1 + ρ ^ 2 := by positivity
  have h1 : |ρ * Real.tanh (Real.pi * ρ)| ≤ |ρ| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_tanh_lt_one _).le
  have h2 : |ρ| ≤ 1 + ρ ^ 2 := by nlinarith [sq_abs ρ, abs_nonneg ρ, sq_nonneg (|ρ| - 1 / 2)]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖sphTransformH H ρ‖ ^ 2)]
  calc |ρ * Real.tanh (Real.pi * ρ)| * ‖sphTransformH H ρ‖ ^ 2
      ≤ |ρ| * (C / (1 + ρ ^ 2)) ^ 2 := by gcongr
    _ ≤ (1 + ρ ^ 2) * (C / (1 + ρ ^ 2)) ^ 2 := by gcongr
    _ = C ^ 2 * (1 + ρ ^ 2)⁻¹ := by field_simp

/-- `π² ∫_{v>1} ‖F + cG‖² = ¼ ∫_{ρ>0} ρ tanh(πρ) ‖F̂ + cĜ‖²` for a constant `c`. -/
lemma E_pair {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (c : ℂ) :
    Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), ‖F v + c * G v‖ ^ 2 =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) *
        ‖sphTransformH F ρ + c * sphTransformH G ρ‖ ^ 2 := by
  have hS : ContDiff ℝ ∞ (F + c • G) := hF.add (hG.const_smul c)
  have hcG : HasCompactSupport (c • G) :=
    hGc.comp_left (g := fun z : ℂ => c * z) (by simp)
  have hSc : HasCompactSupport (F + c • G) := hFc.add hcG
  have h := norm_sq_eq_sph (F + c • G) hS hSc
  have e1 : ∀ v, (F + c • G) v = F v + c * G v := fun v => by simp
  have e2 : ∀ ρ, sphTransformH (F + c • G) ρ = sphTransformH F ρ + c * sphTransformH G ρ := fun ρ => by
    show sphTransformH (F + fun y => c • G y) ρ = _
    rw [sphTransformH_add hF hFc (hG.const_smul c) hcG]
    exact congrArg (fun z => sphTransformH F ρ + z) (sphTransformH_smul c G ρ)
  simp only [e1, e2] at h
  exact h

/-- **Polarisation passes to integrals**: if `4 ψ = φ₁ - φ₂ - i (φ₃ - φ₄)` pointwise, with real integrable `φₖ`,
then `4 ∫ ψ = ∫ φ₁ - ∫ φ₂ - i (∫ φ₃ - ∫ φ₄)`. -/
lemma polar_integral {μ : Measure ℝ} {ψ : ℝ → ℂ} {φ₁ φ₂ φ₃ φ₄ : ℝ → ℝ} (h1 : Integrable φ₁ μ)
    (h2 : Integrable φ₂ μ) (h3 : Integrable φ₃ μ) (h4 : Integrable φ₄ μ)
    (hψ : ∀ x, 4 * ψ x = (φ₁ x : ℂ) - (φ₂ x : ℂ) - I * ((φ₃ x : ℂ) - (φ₄ x : ℂ))) :
    4 * ∫ x, ψ x ∂μ = ((∫ x, φ₁ x ∂μ : ℝ) : ℂ) - ((∫ x, φ₂ x ∂μ : ℝ) : ℂ) -
      I * (((∫ x, φ₃ x ∂μ : ℝ) : ℂ) - ((∫ x, φ₄ x ∂μ : ℝ) : ℂ)) := by
  have e : ∀ x, ψ x = (1 / 4 : ℂ) * ((φ₁ x : ℂ) - (φ₂ x : ℂ) - I * ((φ₃ x : ℂ) - (φ₄ x : ℂ))) := fun x => by
    rw [← hψ x]; ring
  have i1 := h1.ofReal (𝕜 := ℂ); have i2 := h2.ofReal (𝕜 := ℂ)
  have i3 := h3.ofReal (𝕜 := ℂ); have i4 := h4.ofReal (𝕜 := ℂ)
  have i12 : Integrable (fun a => (φ₁ a : ℂ) - (φ₂ a : ℂ)) μ := i1.sub i2
  have i34 : Integrable (fun a => I * ((φ₃ a : ℂ) - (φ₄ a : ℂ))) μ := (i3.sub i4).const_mul I
  have h12 : ∫ a, ((φ₁ a : ℂ) - (φ₂ a : ℂ)) ∂μ = ∫ a, (φ₁ a : ℂ) ∂μ - ∫ a, (φ₂ a : ℂ) ∂μ :=
    integral_sub i1 i2
  have h34 : ∫ a, ((φ₃ a : ℂ) - (φ₄ a : ℂ)) ∂μ = ∫ a, (φ₃ a : ℂ) ∂μ - ∫ a, (φ₄ a : ℂ) ∂μ :=
    integral_sub i3 i4
  have hall : ∫ a, ((φ₁ a : ℂ) - (φ₂ a : ℂ) - I * ((φ₃ a : ℂ) - (φ₄ a : ℂ))) ∂μ =
      (∫ a, ((φ₁ a : ℂ) - (φ₂ a : ℂ)) ∂μ) - ∫ a, I * ((φ₃ a : ℂ) - (φ₄ a : ℂ)) ∂μ :=
    integral_sub i12 i34
  simp_rw [e]
  rw [integral_const_mul, hall, h12, integral_const_mul, h34, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal]
  ring

/-- **The polarised spherical Plancherel identity**: for `F`, `G` smooth with compact support,
`π² ∫_{v>1} conj(F) G dv = ¼ ∫_{ρ>0} ρ tanh(πρ) conj(F̂(ρ)) Ĝ(ρ) dρ`. -/
theorem sph_polarized {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    (Real.pi : ℂ) ^ 2 * ∫ v in Ioi (1 : ℝ), conj (F v) * G v =
      (1 / 4 : ℂ) * ∫ ρ in Ioi (0 : ℝ), ((ρ * Real.tanh (Real.pi * ρ) : ℝ) : ℂ) *
        (conj (sphTransformH F ρ) * sphTransformH G ρ) := by
  -- integrability of the squared norms on both sides
  have hvint : ∀ c : ℂ, Integrable (fun v => ‖F v + c * G v‖ ^ 2) (volume.restrict (Ioi (1 : ℝ))) := by
    intro c
    have hcG : HasCompactSupport (c • G) := hGc.comp_left (g := fun z : ℂ => c * z) (by simp)
    have hcont : Continuous fun v => ‖F v + c * G v‖ ^ 2 :=
      ((hF.continuous.add (continuous_const.mul hG.continuous)).norm).pow 2
    have hcs : HasCompactSupport fun v => ‖F v + c * G v‖ ^ 2 := by
      have := (hFc.add hcG)
      have h2 : HasCompactSupport fun v => ‖(F + c • G) v‖ ^ 2 :=
        (this.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
      simpa using h2
    exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  have hρint : ∀ c : ℂ, Integrable (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) *
      ‖sphTransformH F ρ + c * sphTransformH G ρ‖ ^ 2) (volume.restrict (Ioi (0 : ℝ))) := by
    intro c
    have hcG : HasCompactSupport (c • G) := hGc.comp_left (g := fun z : ℂ => c * z) (by simp)
    have hS : ContDiff ℝ ∞ (F + c • G) := hF.add (hG.const_smul c)
    have hSc : HasCompactSupport (F + c • G) := hFc.add hcG
    have e2 : ∀ ρ, sphTransformH (F + c • G) ρ = sphTransformH F ρ + c * sphTransformH G ρ := fun ρ => by
      show sphTransformH (F + fun y => c • G y) ρ = _
      rw [sphTransformH_add hF hFc (hG.const_smul c) hcG]
      exact congrArg (fun z => sphTransformH F ρ + z) (sphTransformH_smul c G ρ)
    have := integrable_sphWeight hS hSc
    simp only [e2] at this
    exact this.integrableOn
  -- the four values `c = 1, -1, i, -i`
  have E1 := E_pair hF hFc hG hGc 1
  have E2 := E_pair hF hFc hG hGc (-1)
  have E3 := E_pair hF hFc hG hGc I
  have E4 := E_pair hF hFc hG hGc (-I)
  simp only [one_mul] at E1
  -- the polarised integrals
  have PV := polar_integral (μ := volume.restrict (Ioi (1 : ℝ)))
    (ψ := fun v => conj (F v) * G v) (by simpa using hvint 1) (hvint (-1)) (hvint I) (hvint (-I))
    (fun v => by
      have := polar_complex (F v) (G v)
      simpa using this)
  have PR := polar_integral (μ := volume.restrict (Ioi (0 : ℝ)))
    (ψ := fun ρ => ((ρ * Real.tanh (Real.pi * ρ) : ℝ) : ℂ) * (conj (sphTransformH F ρ) * sphTransformH G ρ))
    (by simpa using hρint 1) (hρint (-1)) (hρint I) (hρint (-I))
    (fun ρ => by
      have := polar_complex (sphTransformH F ρ) (sphTransformH G ρ)
      have h4 := congrArg (fun z => ((ρ * Real.tanh (Real.pi * ρ) : ℝ) : ℂ) * z) this
      push_cast at h4 ⊢
      simpa [mul_sub, mul_add, mul_left_comm, mul_assoc] using h4)
  have cast : ∀ {r s : ℝ}, Real.pi ^ 2 * r = (1 / 4 : ℝ) * s →
      (Real.pi : ℂ) ^ 2 * (r : ℂ) = (1 / 4 : ℂ) * (s : ℂ) := fun {r s} h => by
    have := congrArg (fun x : ℝ => (x : ℂ)) h
    simpa using this
  have E1c := cast E1
  have E2c := cast E2
  have E3c := cast E3
  have E4c := cast E4
  linear_combination (((Real.pi : ℂ) ^ 2) / 4) * PV - (1 / 16 : ℂ) * PR + (1 / 4 : ℂ) * E1c -
    (1 / 4 : ℂ) * E2c - (I / 4) * E3c + (I / 4) * E4c

end Lightlike.Lorentz.SL2ROddPlancherel

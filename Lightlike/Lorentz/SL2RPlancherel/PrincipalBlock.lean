import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalGroupCoeff
import Lightlike.Lorentz.SL2RPlancherel.KTypeBlockL2
import Lightlike.Lorentz.SL2RPlancherel.KKL2

/-!
# The block transforms are principal-series matrix coefficients

If the `K × K` component `(2r, -2l)` of a continuous compactly supported `f ∈ L²(SL(2,ℝ))` is the
ladder chain `Hc_{r,l} G` of a test function `G` on `(0, ∞)`, then `kkL2 f (2r, -2l) = π⁻¹ blockE r l G`
(`kkL2_eq_blockE`), and its block transform is, for almost every `ρ > 0`,
`|blockL2 r l (kkL2 f (2r, -2l))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |∫ f(g) ⟪e_r, π_{2ρ}(g) e_{-l}⟫ dg|²`
(`norm_sq_blockL2_kkL2`): the block isometry is the principal-series matrix coefficient weighted by
the Plancherel density `ρ tanh(πρ)`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (identification of the block transforms with
matrix coefficients), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- If the component `(2r, -2l)` of `f` is the chain `Hc_{r,l} G` on `(0, ∞)`, then
`kkL2 f (2r, -2l) = π⁻¹ blockE r l G`. -/
theorem kkL2_eq_blockE {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) (r l : ℕ)
    (G : smoothCS)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (r : ℤ), 2 * -(l : ℤ)] ξ = Hc r G l ξ) :
    kkL2 (hf.toLp f) ![2 * (r : ℤ), 2 * -(l : ℤ)] = ((Real.pi : ℂ))⁻¹ • blockE r l G := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine Lp.ext ?_
  have h1 := kkL2_toLp_ae hfc hf ![2 * (r : ℤ), 2 * -(l : ℤ)]
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (blockE r l G)
  have h3 : (blockE r l G : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] blockSrc r l G :=
    MemLp.coeFn_toLp (memLp_blockSrc r l G.2.1 G.2.2)
  filter_upwards [h1, h2, h3, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 e3 hξ
  rw [e1, e2, Pi.smul_apply, e3, kkSrc, blockSrc, h ξ hξ, smul_eq_mul, Complex.ofReal_mul]
  field_simp

lemma tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.2 hx) (Real.cosh_pos x).le

/-- **The block transform is the principal-series matrix coefficient**: for almost every `ρ > 0`,
`|blockL2 r l (kkL2 f (2r, -2l))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f r (-l)|²`. -/
theorem norm_sq_blockL2_kkL2 {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR)
    (hc : HasCompactSupport f) (r l : ℕ) (G : smoothCS)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (r : ℤ), 2 * -(l : ℤ)] ξ = Hc r G l ξ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2 r l (kkL2 (hf.toLp f) ![2 * (r : ℤ), 2 * -(l : ℤ)]) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f r (-l)‖ ^ 2 := by
  rw [kkL2_eq_blockE hfc hf r l G h, LinearIsometry.map_smul, blockL2_apply]
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (blockF r l G)
  have h3 : (blockF r l G : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] blockTgt r l G :=
    MemLp.coeFn_toLp (memLp_blockTgt r l G.2.1 G.2.2)
  filter_upwards [h2, h3, ae_restrict_mem measurableSet_Ioi] with ρ e2 e3 hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hnn : 0 ≤ ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ :=
    mul_nonneg (mul_nonneg (mul_nonneg hρ0.le (tanh_nonneg_of_nonneg (by positivity)))
      (wl_nonneg l ρ)) (wl_nonneg r ρ)
  rw [e2, Pi.smul_apply, e3, smul_eq_mul, norm_mul, mul_pow,
    norm_sq_piCoeff_eq ρ hfc hc r l G.2.1 G.2.2 h, blockTgt, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hnn, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  field_simp
  ring

/-- Non-vacuity: the chain hypothesis of `norm_sq_blockL2_kkL2` holds for `f = 0`, `G = 0`. -/
example (r l : ℕ) : ∀ ξ ∈ Ioi (0 : ℝ),
    kkCoeff (0 : SL2R → ℂ) ![2 * (r : ℤ), 2 * -(l : ℤ)] ξ = Hc r ((0 : smoothCS) : ℝ → ℂ) l ξ := by
  intro ξ _
  have h := Hc_smul r (0 : ℂ) (contDiff_const (c := (0 : ℂ))) l ξ
  simp only [zero_smul, zero_mul] at h
  simp only [ZeroMemClass.coe_zero, kkCoeff, kkProfile]
  simp [h]

end Lightlike.Lorentz.SL2RPlancherel

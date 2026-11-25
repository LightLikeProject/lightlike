import Mathlib
import Lightlike.Cosmology.FLRW
import Lightlike.Cosmology.GrowthEquation.Jeans

/-!
# Einstein–de Sitter check of the growth equation (row G1-032)

In the Einstein–de Sitter universe (`k = Λ = 0`, `a = t^{2/3}`) the first Friedmann equation gives
`H = 2/(3t)` and `4πGρ = 2/(3t²)`; the growth equation `d'' + 2H d' - 4πGρ d = 0` is then solved by
`d = t^{2/3} ∝ a` (growing mode `D₊`) and `d = t^{-1}` (decaying mode `D₋`)
(Bernardeau et al. 2002, Section 2.3, source key `bernardeau-2002`).
-/

namespace Lightlike.Cosmology.GrowthEquation

open Cosmology

private lemma deriv_rpow' {p t : ℝ} (ht : 0 < t) :
    deriv (fun s : ℝ => s ^ p) t = p * t ^ (p - 1) :=
  (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).deriv

private lemma deriv2_rpow' {p t : ℝ} (ht : 0 < t) :
    deriv (deriv fun s : ℝ => s ^ p) t = p * (p - 1) * t ^ (p - 1 - 1) := by
  have h : deriv (fun s : ℝ => s ^ p) =ᶠ[nhds t] fun s => p * s ^ (p - 1) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using deriv_rpow' (p := p) hs
  rw [h.deriv_eq]
  have := ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht.ne')).const_mul p).deriv
  rw [this]; ring

/-- In EdS, `H = a'/a = 2/(3t)` for `a = t^{2/3}`. -/
lemma eds_hubble {t : ℝ} (ht : 0 < t) :
    deriv (fun s : ℝ => s ^ (2 / 3 : ℝ)) t / t ^ (2 / 3 : ℝ) = 2 / (3 * t) := by
  rw [deriv_rpow' ht, Real.rpow_sub_one ht.ne']
  have : t ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  field_simp

/-- Friedmann with `k = Λ = 0` on `a = t^{2/3}` gives `4πGρ = 2/(3t²)`. -/
lemma eds_four_pi_G_rho {ρ : ℝ → ℝ} {Gn t : ℝ} (ht : 0 < t)
    (hF : FirstFriedmann (fun s : ℝ => s ^ (2 / 3 : ℝ)) ρ 0 0 Gn t) :
    4 * Real.pi * Gn * ρ t = 2 / (3 * t ^ 2) := by
  unfold FirstFriedmann at hF
  rw [eds_hubble ht] at hF
  simp only [zero_div, sub_zero, add_zero] at hF
  have h3 : (2 / (3 * t)) ^ 2 = 8 * Real.pi * Gn / 3 * ρ t := hF
  have : 4 * Real.pi * Gn * ρ t = 3 / 2 * (8 * Real.pi * Gn / 3 * ρ t) := by ring
  rw [this, ← h3]
  field_simp

/-- **EdS growth modes.** In the Einstein–de Sitter background (`a = t^{2/3}`, Friedmann with
`k = Λ = 0`), `d = t^p` solves `d'' + 2Hd' - 4πGρ d = 0` for `p = 2/3` (`D₊ ∝ a`) and `p = -1`
(`D₋ ∝ t⁻¹`), at every `t > 0`. -/
theorem eds_growth_ode {ρ : ℝ → ℝ} {Gn t p : ℝ} (ht : 0 < t)
    (hF : FirstFriedmann (fun s : ℝ => s ^ (2 / 3 : ℝ)) ρ 0 0 Gn t)
    (hp : p = 2 / 3 ∨ p = -1) :
    deriv (deriv fun s : ℝ => s ^ p) t
      + 2 * (deriv (fun s : ℝ => s ^ (2 / 3 : ℝ)) t / t ^ (2 / 3 : ℝ))
        * deriv (fun s : ℝ => s ^ p) t
      - 4 * Real.pi * Gn * ρ t * t ^ p = 0 := by
  rw [eds_hubble ht, eds_four_pi_G_rho ht hF, deriv2_rpow' (p := p) ht,
    deriv_rpow' (p := p) ht, Real.rpow_sub_one ht.ne' (p - 1), Real.rpow_sub_one ht.ne' p]
  have h0 : t ^ p ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hq : p * (p - 1) + 4 / 3 * p - 2 / 3 = 0 := by
    rcases hp with rfl | rfl <;> norm_num
  have e : p * (p - 1) * (t ^ p / t / t) + 2 * (2 / (3 * t)) * (p * (t ^ p / t))
      - 2 / (3 * t ^ 2) * t ^ p = t ^ p / t ^ 2 * (p * (p - 1) + 4 / 3 * p - 2 / 3) := by
    ring
  rw [e, hq, mul_zero]

end Lightlike.Cosmology.GrowthEquation

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.eds_four_pi_G_rho := _root_.Lightlike.Cosmology.GrowthEquation.eds_four_pi_G_rho
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.eds_growth_ode := _root_.Lightlike.Cosmology.GrowthEquation.eds_growth_ode
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.eds_hubble := _root_.Lightlike.Cosmology.GrowthEquation.eds_hubble

module

public import Mathlib
public import Lightlike.GR.AsymptoticSafetyFlow.Defs

/-!
# The Einstein–Hilbert ODE: partial derivatives of the vector field

Row G3-264 (task T-AS2). Explicit one-variable derivatives (`HasDerivAt`) of `EH.eta`,
`EH.betaG`, `EH.betaLam` in `g` and in `λ`, valid where `x = 1 − 2λ ≠ 0` and
`1 − g B₂(λ) ≠ 0`. They are the entries of the Jacobian of the ODE at a fixed point; the
evaluation at the non-Gaussian fixed point is in a later file.

Main results
* `EH.hasDerivAt_B1`, `EH.hasDerivAt_B2`: derivatives of the coefficient functions in `λ`.
* `EH.hasDerivAt_eta_g`, `EH.hasDerivAt_eta_lam`: partial derivatives of `η`.
* `EH.hasDerivAt_betaG_g`, `EH.hasDerivAt_betaG_lam`, `EH.hasDerivAt_betaLam_g`,
  `EH.hasDerivAt_betaLam_lam`: the four entries of the Jacobian of `EH.field`.
-/

@[expose] public section

noncomputable section

namespace Lightlike.AsymptoticSafety.EH

open Real

/-- `dB₁/dλ`. -/
def dB1 (lam : ℝ) : ℝ := (1 / (3 * π)) * (10 / denom lam ^ 2 - 36 / denom lam ^ 3)

/-- `dB₂/dλ`. -/
def dB2 (lam : ℝ) : ℝ := (1 / (12 * π)) * (24 / denom lam ^ 3 - 10 / denom lam ^ 2)

lemma hasDerivAt_denom (lam : ℝ) : HasDerivAt denom (-2) lam := by
  have h := ((hasDerivAt_id lam).const_mul (2 : ℝ)).const_sub 1
  have h' : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) lam := by simpa using h
  exact h'

lemma hasDerivAt_B1 {lam : ℝ} (hx : denom lam ≠ 0) : HasDerivAt B1 (dB1 lam) lam := by
  have hd := hasDerivAt_denom lam
  have h5 := (hasDerivAt_const lam (5 : ℝ)).div hd hx
  have h9 := (hasDerivAt_const lam (9 : ℝ)).div (hd.pow 2) (pow_ne_zero 2 hx)
  have h := ((h5.sub h9).sub_const 7).const_mul (1 / (3 * π))
  refine h.congr_deriv ?_
  unfold dB1
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_B2 {lam : ℝ} (hx : denom lam ≠ 0) : HasDerivAt B2 (dB2 lam) lam := by
  have hd := hasDerivAt_denom lam
  have h6 := (hasDerivAt_const lam (6 : ℝ)).div (hd.pow 2) (pow_ne_zero 2 hx)
  have h5 := (hasDerivAt_const lam (5 : ℝ)).div hd hx
  have h := (h6.sub h5).const_mul (1 / (12 * π))
  refine h.congr_deriv ?_
  unfold dB2
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- `∂η/∂g = B₁ / (1 − g B₂)²`. -/
def etaG (g lam : ℝ) : ℝ := B1 lam / (1 - g * B2 lam) ^ 2

/-- `∂η/∂λ = g (B₁' (1 − g B₂) + g B₁ B₂') / (1 − g B₂)²`. -/
def etaLam (g lam : ℝ) : ℝ :=
  g * (dB1 lam * (1 - g * B2 lam) + g * B1 lam * dB2 lam) / (1 - g * B2 lam) ^ 2

lemma hasDerivAt_eta_g {g lam : ℝ} (hD : 1 - g * B2 lam ≠ 0) :
    HasDerivAt (fun g => eta g lam) (etaG g lam) g := by
  have hn := (hasDerivAt_id g).mul_const (B1 lam)
  have hd := ((hasDerivAt_id g).mul_const (B2 lam)).const_sub 1
  have h := hn.div hd hD
  refine h.congr_deriv ?_
  unfold etaG
  simp only [id]
  field_simp
  ring

lemma hasDerivAt_eta_lam {g lam : ℝ} (hx : denom lam ≠ 0) (hD : 1 - g * B2 lam ≠ 0) :
    HasDerivAt (fun lam => eta g lam) (etaLam g lam) lam := by
  have hn := (hasDerivAt_B1 hx).const_mul g
  have hd := ((hasDerivAt_B2 hx).const_mul g).const_sub 1
  have h := hn.div hd hD
  refine h.congr_deriv ?_
  unfold etaLam
  field_simp
  ring

/-- `∂β_g/∂g = η_g g + 2 + η`. -/
def betaG_g (g lam : ℝ) : ℝ := etaG g lam * g + (2 + eta g lam)

/-- `∂β_g/∂λ = η_λ g`. -/
def betaG_lam (g lam : ℝ) : ℝ := etaLam g lam * g

/-- `∂β_λ/∂g`. -/
def betaLam_g (g lam : ℝ) : ℝ :=
  etaG g lam * lam + (1 / (4 * π)) * (10 / denom lam - 8 - (5 / 3) * eta g lam / denom lam)
    + g / (4 * π) * (-(5 / 3) * etaG g lam / denom lam)

/-- `∂β_λ/∂λ`. -/
def betaLam_lam (g lam : ℝ) : ℝ :=
  etaLam g lam * lam - (2 - eta g lam)
    + g / (4 * π) * (20 / denom lam ^ 2
      - (5 / 3) * (etaLam g lam / denom lam + 2 * eta g lam / denom lam ^ 2))

lemma hasDerivAt_betaG_g {g lam : ℝ} (hD : 1 - g * B2 lam ≠ 0) :
    HasDerivAt (fun g => betaG g lam) (betaG_g g lam) g := by
  have he := hasDerivAt_eta_g hD
  have h := (he.const_add 2).mul (hasDerivAt_id g)
  refine h.congr_deriv ?_
  unfold betaG_g
  simp only [id]
  ring

lemma hasDerivAt_betaG_lam {g lam : ℝ} (hx : denom lam ≠ 0) (hD : 1 - g * B2 lam ≠ 0) :
    HasDerivAt (fun lam => betaG g lam) (betaG_lam g lam) lam := by
  have he := hasDerivAt_eta_lam hx hD
  have h := (he.const_add 2).mul_const g
  refine h.congr_deriv ?_
  unfold betaG_lam
  ring

lemma hasDerivAt_betaLam_g {g lam : ℝ} (hx : denom lam ≠ 0) (hD : 1 - g * B2 lam ≠ 0) :
    HasDerivAt (fun g => betaLam g lam) (betaLam_g g lam) g := by
  have he := hasDerivAt_eta_g hD
  have h1 := (he.const_sub 2).neg.mul_const lam
  have h2 := (((he.const_mul (5 / 3)).div_const (denom lam)).const_sub (10 / denom lam - 8))
  have h3 := ((hasDerivAt_id g).div_const (4 * π)).mul h2
  have h := h1.add h3
  refine h.congr_deriv ?_
  unfold betaLam_g
  simp only [id]
  field_simp
  ring

lemma hasDerivAt_betaLam_lam {g lam : ℝ} (hx : denom lam ≠ 0) (hD : 1 - g * B2 lam ≠ 0) :
    HasDerivAt (fun lam => betaLam g lam) (betaLam_lam g lam) lam := by
  have he := hasDerivAt_eta_lam hx hD
  have hd := hasDerivAt_denom lam
  have h1 := (he.const_sub 2).neg.mul (hasDerivAt_id lam)
  have h2 := ((hasDerivAt_const lam (10 : ℝ)).div hd hx).sub_const 8
  have h3 := (he.const_mul (5 / 3)).div hd hx
  have h4 := (h2.sub h3).const_mul (g / (4 * π))
  have h := h1.add h4
  refine h.congr_deriv ?_
  unfold betaLam_lam
  simp only [id, Pi.neg_apply]
  field_simp
  ring

end Lightlike.AsymptoticSafety.EH

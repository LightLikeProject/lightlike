import Lightlike.Rows.G1_031.Tensor

/-!
# The linearized Einstein equations for tensor modes about conformal FLRW (row G1-031)

The field equation `G_{μν} + Λ g_{μν} = κ T_{μν}` with the perfect fluid `T_{μν} = (ρ+p) u_μ u_ν + p g_{μν}`,
`u_μ = -a δ_{μ0}` (the comoving observer; it stays unit for the tensor perturbation because
`h_{0μ} = 0`), is written `fieldEq`.

* `hasDerivAt_fieldEq_tPert` : the first variation of `fieldEq` along `confMetric a + ε tPert a f`.
* `dFieldEq_tPert_of_background` : once the background satisfies the spatial Einstein equation the
  variation is `dl μ ν cp μ · ½ (f_{00} + 2𝓗 f_0 - f_{33})`.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Rows.G1_031

open Lightlike Lightlike.Cosmology

/-- The comoving perfect-fluid stress tensor `(ρ+p) u_μ u_ν + p g_{μν}` with `u_μ = -a δ_{μ0}`. -/
def fluidT (ρ p : ℝ) (a : ℝ → ℝ) (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  (ρ + p) * a (x 0) ^ 2 * dl μ 0 * dl ν 0 + p * g x μ ν

/-- The field equation `G_{μν} + Λ g_{μν} - κ T_{μν}` (its vanishing is Einstein's equation). -/
def fieldEq (κ Λ ρ p : ℝ) (a : ℝ → ℝ) (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  einsteinTensor g μ ν x + Λ * g x μ ν - κ * fluidT ρ p a g μ ν x

variable {a : ℝ → ℝ} {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}

theorem contDiff_confMetric (hfa : ContDiff ℝ ∞ a) (l k : Fin 4) :
    ContDiff ℝ ∞ (fun y => confMetric a y l k) := by
  simp only [confMetric_apply]
  split_ifs
  · exact contDiff_const.mul ((hfa.comp (contDiff_pi.mp contDiff_id (0 : Fin 4))).pow 2)
  · exact contDiff_const

theorem contDiff_tPert (hfa : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (l k : Fin 4) :
    ContDiff ℝ ∞ (fun y => tPert a f y l k) := by
  simp only [tPert_apply]
  split_ifs
  · exact ((hfa.comp (contDiff_pi.mp contDiff_id (0 : Fin 4))).pow 2).mul (contDiff_const.mul hf)
  · exact contDiff_const

theorem det_confMetric_ne (hne : ∀ t, a t ≠ 0) : (confMetric a x).det ≠ 0 := by
  have hpos := hne (x 0)
  unfold confMetric
  rw [Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun μ _ => ?_
  unfold sgn; split_ifs <;> simp [hpos]

/-- **First variation of the field equation for the tensor perturbation.** -/
theorem hasDerivAt_fieldEq_tPert (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) (hf : ContDiff ℝ ∞ f)
    (h1 : pd 1 f = fun _ => 0) (h2 : pd 2 f = fun _ => 0) (κ Λ ρ p : ℝ) (μ ν : Fin 4) :
    HasDerivAt (fun t : ℝ => fieldEq κ Λ ρ p a (fun z => confMetric a z + t • tPert a f z) μ ν x)
      (dl μ ν * cp μ * ((1 / 2) * (pd 0 (pd 0 f) x + 2 * Hf a x * pd 0 f x - pd 3 (pd 3 f) x) +
        (-2 * dH a 0 x - Hf a x ^ 2 + a (x 0) ^ 2 * (Λ - κ * p)) * f x)) 0 := by
  have hg := contDiff_confMetric hfa
  have hh := contDiff_tPert hfa hf
  have hx := det_confMetric_ne (x := x) hne
  have hR := hasDerivAt_ricci (confMetric a) (tPert a f) hg hh x hx μ ν
  have hS := hasDerivAt_scalarCurvature (confMetric a) (tPert a f) hg hh x hx
  rw [dScalar_tPert hfa hne hf h1 h2] at hS
  have hm : HasDerivAt (fun t : ℝ => confMetric a x μ ν + t * tPert a f x μ ν)
      (tPert a f x μ ν) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (tPert a f x μ ν)).const_add (confMetric a x μ ν)
  have hT := ((hR.sub ((hS.mul hm).const_mul (1 / 2))).add (hm.const_mul Λ)).sub
    ((hm.const_mul p).const_add ((ρ + p) * a (x 0) ^ 2 * dl μ 0 * dl ν 0) |>.const_mul κ)
  unfold fieldEq fluidT einsteinTensor
  convert hT using 1
  · funext t; simp [mul_assoc]
  · simp only [zero_smul, add_zero, zero_mul]
    rw [dRicci_tPert hfa hne hf h1 h2, scalar_conf hfa hne, tPert_apply]
    have hpos := hne (x 0)
    fin_cases μ <;> fin_cases ν <;> simp [dl, cp] <;> field_simp <;> ring

end Lightlike.Rows.G1_031

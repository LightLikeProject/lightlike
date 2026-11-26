import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.NoInvariantForm

/-!
# No positive invariant form at the boundary `τ = 1` of the complementary series (HA3 trust check)

`NoInvariantForm.lean` shows that for the principal-series model `|cx+d|^{-τ-1}` with `|τ| > 1` no positive
definite sesquilinear form on smooth functions has `E, F, H` skew: the Casimir eigenvalue `(τ²-1)/4` on the
`K`-fixed vector `(1+x²)^{-(τ+1)/2}` is positive. At the boundary `τ = 1` (`σ = 1/2`, Casimir `0`) the
same computation gives `B(v, Ωv) = 0 = -B(Hv,Hv)/4 - B(Ev,Ev)`, so a positive definite skew form would
force `H v = 0`; but `H v (0) = 2`. So there is no positive definite invariant form on smooth functions at
`τ = 1` either.

* `eq_zero_of_casimir_zero`: the abstract step: if `B` is positive definite with `E, F, H` skew, `E v = F v`
  and `Ω v = 0`, then `H v = 0`.
* `no_invariant_form_smooth_boundary`: no positive definite form with `opE 1, opF, opH 1` skew on smooth
  functions.

**Limits.** Only `τ = 1`: at `τ = -1` the model is the action on functions on the projective line by
composition, where the constants are an invariant vector (`E v = F v = H v = 0`) and the `K`-fixed vector
gives no contradiction, so this argument does not decide that case. The statements are about the derived
action on smooth vectors (skewness of `E, F, H`), as in `NoInvariantForm.lean`, not about the group
representation.
-/

open Complex

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

open Lightlike.Lorentz.SL2R

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Casimir zero on a `K`-fixed vector forces `H v = 0`** for a positive definite form with `E, F, H` skew. -/
theorem eq_zero_of_casimir_zero (B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) (E F H : V →ₗ[ℂ] V)
    (hE : ∀ u w, B (E u) w + B u (E w) = 0) (hF : ∀ u w, B (F u) w + B u (F w) = 0)
    (hH : ∀ u w, B (H u) w + B u (H w) = 0) (hpos : ∀ u, u ≠ 0 → 0 < (B u u).re) (v : V)
    (hEF : E v = F v)
    (hΩ : (1 / 4 : ℂ) • H (H v) + (1 / 2 : ℂ) • (E (F v) + F (E v)) = 0) : H v = 0 := by
  have hnn : ∀ u, 0 ≤ (B u u).re := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · exact (hpos u hu).le
  have h1 : B v (H (H v)) = - B (H v) (H v) := by
    have := hH v (H v)
    linear_combination this
  have h2 : B v (E (F v)) = - B (E v) (E v) := by
    have := hE v (F v)
    have e : B (E v) (F v) = B (E v) (E v) := by rw [← hEF]
    linear_combination this - e
  have h3 : B v (F (E v)) = - B (E v) (E v) := by
    have := hF v (E v)
    have e : B (F v) (E v) = B (E v) (E v) := by rw [← hEF]
    linear_combination this - e
  have h4 : B v ((1 / 4 : ℂ) • H (H v) + (1 / 2 : ℂ) • (E (F v) + F (E v))) =
      -(1 / 4 : ℂ) * B (H v) (H v) - B (E v) (E v) := by
    rw [map_add, map_smul, map_smul, map_add, h1, h2, h3]
    simp only [smul_eq_mul]
    ring
  rw [hΩ, map_zero] at h4
  have hH0 : (B (H v) (H v)).re = 0 := by
    have a := hnn (H v)
    have b := hnn (E v)
    have hre := congrArg Complex.re h4
    simp only [Complex.zero_re, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im] at hre
    norm_num at hre
    linarith
  by_contra hne
  exact (lt_irrefl _ ((hpos (H v) hne).trans_eq hH0))

end Abstract

section Concrete

/-- **No positive invariant form at `τ = 1`, on smooth functions** (infinitesimal: `E, F, H` on smooth vectors, not
group-level; `τ = -1` is not decided). -/
theorem no_invariant_form_smooth_boundary
    (B : smoothFns →ₛₗ[starRingEnd ℂ] smoothFns →ₗ[ℂ] ℂ)
    (hBE : ∀ u w, B (opE 1 u) w + B u (opE 1 w) = 0) (hBF : ∀ u w, B (opF u) w + B u (opF w) = 0)
    (hBH : ∀ u w, B (opH 1 u) w + B u (opH 1 w) = 0) :
    ¬ ∀ u, u ≠ 0 → 0 < (B u u).re := by
  intro hpos
  set τ : ℝ := 1 with hτ
  set v : smoothFns := ⟨sphericalVec τ, contDiff_sphericalVec τ⟩ with hv
  have hvf : (v : ℝ → ℂ) = sphericalVec τ := rfl
  have hEF : opE τ v = opF v := by
    refine Subtype.ext (funext fun x => ?_)
    rw [opE_eq 0 τ, opF_eq 0 τ, hvf]
    exact upper_sub_lower_sphericalVec 0 τ x
  have hΩ : (1 / 4 : ℂ) • opH τ (opH τ v) + (1 / 2 : ℂ) • (opE τ (opF v) + opF (opE τ v)) = 0 := by
    refine Subtype.ext (funext fun x => ?_)
    obtain ⟨h1, h2⟩ : Differentiable ℝ (v : ℝ → ℂ) ∧ Differentiable ℝ (deriv (v : ℝ → ℂ)) := by
      have := contDiff_infty_iff_deriv.1 v.2
      exact ⟨this.1, ((contDiff_infty_iff_deriv.1 this.2).1)⟩
    have hc := casimir_principal (ε := 0) (ν := I * (τ : ℂ)) h1 h2 x
    have hcas : casimir (act 0 (I * (τ : ℂ))) (v : ℝ → ℂ) x = 0 := by
      rw [hc]
      have : (1 + (I * (τ : ℂ)) ^ 2 : ℂ) = 1 - (τ : ℂ) ^ 2 := by
        linear_combination (τ : ℂ) ^ 2 * Complex.I_sq
      rw [this, hτ]
      simp
    have e1 : ((((1 / 4 : ℂ) • opH τ (opH τ v) + (1 / 2 : ℂ) • (opE τ (opF v) + opF (opE τ v)) :
        smoothFns)) : ℝ → ℂ) x = casimir (act 0 (I * (τ : ℂ))) (v : ℝ → ℂ) x := by
      simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [opH_eq 0 τ (opH τ v), opH_eq 0 τ v, opE_eq 0 τ (opF v), opF_eq 0 τ v, opF_eq 0 τ (opE τ v),
        opE_eq 0 τ v, casimir]
      ring
    rw [e1, hcas]
    simp
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := congrFun (congrArg Subtype.val h) 0
    simp [hvf, sphericalVec] at h1
  have hH0 := eq_zero_of_casimir_zero B (opE τ) opF (opH τ) hBE hBF hBH hpos v hEF hΩ
  have h2 := congrFun (congrArg Subtype.val hH0) 0
  have h3 : (opH τ v : ℝ → ℂ) 0 = 2 := by
    rw [opH, smoothOp_apply, hvf]
    simp [sphericalVec, hτ]
    norm_num
  rw [h3] at h2
  simp at h2

end Concrete

end Lightlike.Lorentz.SL2RPlancherel

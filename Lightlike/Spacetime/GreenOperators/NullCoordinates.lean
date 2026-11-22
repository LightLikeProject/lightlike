import Mathlib
import Lightlike.Spacetime.GreenOperators.Triangle

/-!
# Klein–Gordon on 1+1 Minkowski: uniqueness for the Cauchy problem

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For `F : ℝ × ℝ → ℝ`, `F = F(t, x)`, of class `C²`, we write the Klein–Gordon operator
`P F = -∂ₜ² F + ∂ₓ² F - m² F` (`kgOp`).  In null coordinates `a = t - x`, `b = t + x` the equation
`P F = 0` reads `∂ₐ ∂_b v = -(m²/4) v` for `v a b = F ((a+b)/2, (b-a)/2)`, and the Cauchy-triangle
estimate `triangle_unique` gives uniqueness (finite propagation speed): a `C²` solution vanishing for
`t < T` vanishes for `t ≥ T` (`kg_vanishes_of_vanishes_before`) and hence everywhere
(`kg_eq_zero_of_vanishes_before`).

This is a supporting result; no catalogue entry.
-/

open Set

namespace Lightlike.GreenOperators

/-- The Klein–Gordon operator `-∂ₜ² F + ∂ₓ² F - m² F` on `ℝ × ℝ` with coordinates `(t, x)`. -/
noncomputable def kgOp (m : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -(fderiv ℝ (fderiv ℝ F) p (1, 0) (1, 0)) + fderiv ℝ (fderiv ℝ F) p (0, 1) (0, 1) - m ^ 2 * F p

/-- A continuous function with values in a normed space that vanishes for `t < T` vanishes
for `t ≤ T`. -/
lemma eq_zero_of_eq_zero_before {E : Type*} [NormedAddCommGroup E] {g : ℝ × ℝ → E}
    (hg : Continuous g) {T : ℝ} (h0 : ∀ p : ℝ × ℝ, p.1 < T → g p = 0) :
    ∀ p : ℝ × ℝ, p.1 ≤ T → g p = 0 := by
  have hclosed : IsClosed {q : ℝ × ℝ | g q = 0} := isClosed_eq hg continuous_const
  have hsub : closure (Prod.fst ⁻¹' Iio T : Set (ℝ × ℝ)) ⊆ {q | g q = 0} :=
    closure_minimal (fun q hq => h0 q hq) hclosed
  intro p hp
  apply hsub
  rw [← isOpenMap_fst.preimage_closure_eq_closure_preimage continuous_fst, closure_Iio]
  exact hp

variable (F : ℝ × ℝ → ℝ)

/-- The null-coordinate point `((a+b)/2, (b-a)/2)`, i.e. `t = (a+b)/2`, `x = (b-a)/2`. -/
noncomputable def nullPt (a b : ℝ) : ℝ × ℝ := ((a + b) / 2, (b - a) / 2)

/-- `∂_b v = w` for `v = F ∘ nullPt`, `w = DF(nullPt)(½, ½)`. -/
lemma hasDerivAt_null_b (hF : Differentiable ℝ F) (a b : ℝ) :
    HasDerivAt (fun b' => F (nullPt a b')) (fderiv ℝ F (nullPt a b) ((1 / 2 : ℝ), (1 / 2 : ℝ))) b := by
  have hl : HasFDerivAt F (fderiv ℝ F (nullPt a b)) (nullPt a b) := (hF _).hasFDerivAt
  have hf : HasDerivAt (fun b' => nullPt a b') ((1 / 2 : ℝ), (1 / 2 : ℝ)) b := by
    have h1 : HasDerivAt (fun b' : ℝ => (a + b') / 2) (1 / 2) b :=
      ((hasDerivAt_id b).const_add a).div_const 2
    have h2 : HasDerivAt (fun b' : ℝ => (b' - a) / 2) (1 / 2) b :=
      ((hasDerivAt_id b).sub_const a).div_const 2
    exact h1.prodMk h2
  exact hl.comp_hasDerivAt b hf

/-- `∂ₐ w = ¼ (F_tt - F_xx)` at `nullPt a b`, for `w = DF(nullPt)(½, ½)` and `F` of class `C²`. -/
lemma hasDerivAt_null_a (hF : ContDiff ℝ 2 F) (a b : ℝ) :
    HasDerivAt (fun a' => fderiv ℝ F (nullPt a' b) ((1 / 2 : ℝ), (1 / 2 : ℝ)))
      (fderiv ℝ (fderiv ℝ F) (nullPt a b) ((1 / 2 : ℝ), (-1 / 2 : ℝ)) ((1 / 2 : ℝ), (1 / 2 : ℝ)))
      a := by
  have hG : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hl : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (nullPt a b)) (nullPt a b) :=
    (hG _).hasFDerivAt
  have hf : HasDerivAt (fun a' => nullPt a' b) ((1 / 2 : ℝ), (-1 / 2 : ℝ)) a := by
    have h1 : HasDerivAt (fun a' : ℝ => (a' + b) / 2) (1 / 2) a :=
      ((hasDerivAt_id a).add_const b).div_const 2
    have h2 : HasDerivAt (fun a' : ℝ => (b - a') / 2) (-1 / 2) a := by
      simpa using ((hasDerivAt_id a).const_sub b).div_const 2
    exact h1.prodMk h2
  have h3 := (hl.comp_hasDerivAt a hf)
  have h4 := (ContinuousLinearMap.apply ℝ ℝ ((1 / 2 : ℝ), (1 / 2 : ℝ))
    : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt a h3
  exact h4

/-- **Finite propagation speed / uniqueness** for the Klein–Gordon equation on 1+1 Minkowski space:
a `C²` solution of `P F = 0` that vanishes for `t < T` vanishes for `t ≥ T`. -/
theorem kg_vanishes_of_vanishes_before (m T : ℝ) (hF : ContDiff ℝ 2 F)
    (hkg : ∀ p, kgOp m F p = 0) (h0 : ∀ p : ℝ × ℝ, p.1 < T → F p = 0) :
    ∀ p : ℝ × ℝ, T ≤ p.1 → F p = 0 := by
  have hFc : Continuous F := hF.continuous
  have hdF : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hF0 := eq_zero_of_eq_zero_before hFc h0
  have hD0 : ∀ p : ℝ × ℝ, p.1 < T → fderiv ℝ F p = 0 := by
    intro p hp
    have hev : F =ᶠ[nhds p] (fun _ => (0 : ℝ)) :=
      Filter.mem_of_superset ((isOpen_lt continuous_fst continuous_const).mem_nhds hp)
        (fun q hq => h0 q hq)
    simpa using hev.fderiv_eq
  have hD0' := eq_zero_of_eq_zero_before hdF hD0
  have hn : Continuous fun q : ℝ × ℝ => nullPt q.1 q.2 := by
    simp only [nullPt]; fun_prop
  intro p hp
  have hdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hwa : ∀ a b, HasDerivAt (fun a' => fderiv ℝ F (nullPt a' b) ((1 / 2 : ℝ), (1 / 2 : ℝ)))
      (-m ^ 2 / 4 * F (nullPt a b)) a := by
    intro a b
    refine (hasDerivAt_null_a F hF a b).congr_deriv ?_
    have hsym := (hF.contDiffAt (x := nullPt a b)).isSymmSndFDerivAt (n := 2)
      (by simp) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
    have hk := hkg (nullPt a b)
    unfold kgOp at hk
    have e1 : (((1 / 2 : ℝ), (-1 / 2 : ℝ)) : ℝ × ℝ)
        = (1 / 2 : ℝ) • ((1 : ℝ), (0 : ℝ)) + (-1 / 2 : ℝ) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    have e2 : (((1 / 2 : ℝ), (1 / 2 : ℝ)) : ℝ × ℝ)
        = (1 / 2 : ℝ) • ((1 : ℝ), (0 : ℝ)) + (1 / 2 : ℝ) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [e1, e2]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    linarith
  have hcv : Continuous (Function.uncurry fun a b => F (nullPt a b)) := hFc.comp hn
  have hcw : Continuous (Function.uncurry fun a b =>
      fderiv ℝ F (nullPt a b) ((1 / 2 : ℝ), (1 / 2 : ℝ))) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1 / 2 : ℝ), (1 / 2 : ℝ))).continuous.comp (hdF.comp hn)
  have hT : ∀ a, (nullPt a (2 * T - a)).1 ≤ T := fun a => by simp only [nullPt]; linarith
  have key := triangle_unique (-m ^ 2 / 4) T (fun a b => F (nullPt a b))
    (fun a b => fderiv ℝ F (nullPt a b) ((1 / 2 : ℝ), (1 / 2 : ℝ)))
    (fun a b => hasDerivAt_null_b F hdiff a b) hwa
    (fun a => hF0 _ (hT a))
    (fun a => by simp [hD0' _ (hT a)]) hcv hcw
    (a := p.1 - p.2) (b := p.1 + p.2) (by linarith)
  have hp' : nullPt (p.1 - p.2) (p.1 + p.2) = p := by
    ext <;> simp only [nullPt] <;> ring
  simpa [hp'] using key

/-- A `C²` solution of the Klein–Gordon equation on 1+1 Minkowski space that vanishes for `t < T`
vanishes identically. -/
theorem kg_eq_zero_of_vanishes_before (m T : ℝ) (hF : ContDiff ℝ 2 F)
    (hkg : ∀ p, kgOp m F p = 0) (h0 : ∀ p : ℝ × ℝ, p.1 < T → F p = 0) (p : ℝ × ℝ) :
    F p = 0 := by
  rcases lt_or_ge p.1 T with h | h
  · exact h0 p h
  · exact kg_vanishes_of_vanishes_before F m T hF hkg h0 p h

end Lightlike.GreenOperators

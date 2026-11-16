import Lightlike.Asymptotics.Lorentzian.ZStationary
import Lightlike.Asymptotics.Lorentzian.Bridge

/-!
# The derivative of the one-triangle action along a curve

`exp_triAction_eq_triFactor`: for `2k = n`, `e^{S}` of the power-form action is `triFactor`.
`differentiableAt_triAction` and `hasDerivAt_triAction_curve`: where the product of the overlaps is
off the cut of the logarithm, `triAction` is differentiable in both spinors, and its derivative
along a curve is the same source plus target coefficient as for `triFactor`
(`hasDerivAt_triFactor_curve`). The condition `∈ slitPlane` is a genuine hypothesis: at a critical
point the product of the overlaps is `r c` with `c` a phase, which may lie on the cut.
-/

open Complex
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian

/-- For `2k = n`, `exp (triAction)` is `triFactor` where the spinors and overlaps are nonzero. -/
theorem exp_triAction_eq_triFactor (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0)
    (hZ' : Z' ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    Complex.exp (triAction ((n : ℝ) / 2) p Z ξ Z' ξ') = triFactor n p Z ξ Z' ξ' := by
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  have hab : inner ℂ Z ξ * inner ℂ (jMap ξ') Z' ≠ 0 := mul_ne_zero h1 h2
  rw [exp_triAction_nat hZ hZ' h1 h2]
  unfold triFactor
  have hq : (((‖Z'‖ ^ 2 / ‖Z‖ ^ 2 : ℝ) : ℝ) : ℂ) ^ (I * p) =
      Complex.exp (I * p * (Real.log (‖Z'‖ ^ 2 / ‖Z‖ ^ 2) : ℝ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : ‖Z'‖ ^ 2 / ‖Z‖ ^ 2 ≠ 0))]
    rw [← Complex.ofReal_log (by positivity)]
    congr 1; ring
  have hr : (((‖Z‖ ^ 2 * ‖Z'‖ ^ 2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) =
      ((((‖Z‖ * ‖Z'‖) ^ n : ℝ) : ℂ))⁻¹ := by
    have : (‖Z‖ ^ 2 * ‖Z'‖ ^ 2 : ℝ) = (‖Z‖ * ‖Z'‖) ^ 2 := by ring
    rw [this, ← Real.rpow_natCast (‖Z‖ * ‖Z'‖) 2, ← Real.rpow_mul (by positivity)]
    have : ((2 : ℕ) : ℝ) * (-(n : ℝ) / 2) = -(n : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg (by positivity), Real.rpow_natCast]
    push_cast; rfl
  rw [hq, hr, div_eq_mul_inv]
  ring


/-- `triAction` is differentiable in both spinors where they are nonzero and the product of the
overlaps is off the cut of the logarithm (`slitPlane`). -/
theorem differentiableAt_triAction (k p : ℝ) (ξ ξ' : Spinor) {Z Z' : Spinor} (hZ : Z ≠ 0)
    (hZ' : Z' ≠ 0) (hP : inner ℂ Z ξ * inner ℂ (jMap ξ') Z' ∈ Complex.slitPlane) :
    DifferentiableAt ℝ (fun x : Spinor × Spinor => triAction k p x.1 ξ x.2 ξ') (Z, Z') := by
  unfold triAction
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  have hn1 : DifferentiableAt ℝ (fun x : Spinor × Spinor => ‖x.1‖) (Z, Z') :=
    differentiableAt_fst.norm ℝ (by simpa using hZ)
  have hn2 : DifferentiableAt ℝ (fun x : Spinor × Spinor => ‖x.2‖) (Z, Z') :=
    differentiableAt_snd.norm ℝ (by simpa using hZ')
  have hi1 : DifferentiableAt ℝ (fun x : Spinor × Spinor => inner ℂ x.1 ξ) (Z, Z') :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := fun x : Spinor => inner ℂ x ξ) (f := Prod.fst) (Z, Z')
      (differentiableAt_inner_left ξ Z) differentiableAt_fst
  have hi2 : DifferentiableAt ℝ (fun x : Spinor × Spinor => inner ℂ (jMap ξ') x.2) (Z, Z') :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := fun x : Spinor => inner ℂ (jMap ξ') x) (f := Prod.snd)
      (Z, Z') (differentiableAt_inner_right (jMap ξ') Z') differentiableAt_snd
  have hlogP : DifferentiableAt ℝ
      (fun x : Spinor × Spinor => Complex.log (inner ℂ x.1 ξ * inner ℂ (jMap ξ') x.2)) (Z, Z') :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := Complex.log) (f := fun x : Spinor × Spinor =>
      inner ℂ x.1 ξ * inner ℂ (jMap ξ') x.2) (Z, Z')
      (hasStrictFDerivAt_log_real hP).hasFDerivAt.differentiableAt (hi1.mul hi2)
  have hsq1 : DifferentiableAt ℝ (fun x : Spinor × Spinor => (((‖x.1‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    (Complex.ofRealCLM.differentiableAt).comp (Z, Z') (hn1.fun_pow 2)
  have hsq2 : DifferentiableAt ℝ (fun x : Spinor × Spinor => (((‖x.2‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    (Complex.ofRealCLM.differentiableAt).comp (Z, Z') (hn2.fun_pow 2)
  have hslit1 : (((‖Z‖ ^ 2 : ℝ) : ℂ)) * (((‖Z'‖ ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_mul]; exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hlog1 : DifferentiableAt ℝ (fun x : Spinor × Spinor =>
      Complex.log (((‖x.1‖ ^ 2 : ℝ) : ℂ) * ((‖x.2‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := Complex.log) (f := fun x : Spinor × Spinor =>
      ((‖x.1‖ ^ 2 : ℝ) : ℂ) * ((‖x.2‖ ^ 2 : ℝ) : ℂ)) (Z, Z')
      (hasStrictFDerivAt_log_real hslit1).hasFDerivAt.differentiableAt (hsq1.mul hsq2)
  have hslit2 : (((‖Z'‖ ^ 2 : ℝ) : ℂ)) / (((‖Z‖ ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_div]; exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hz0 : (((‖Z‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : ‖Z‖ ^ 2 ≠ 0)
  have hq : DifferentiableAt ℝ (fun x : Spinor × Spinor =>
      ((‖x.2‖ ^ 2 : ℝ) : ℂ) / ((‖x.1‖ ^ 2 : ℝ) : ℂ)) (Z, Z') := by
    simp only [div_eq_mul_inv]
    exact hsq2.mul (hsq1.inv hz0)
  have hlog2 : DifferentiableAt ℝ (fun x : Spinor × Spinor =>
      Complex.log (((‖x.2‖ ^ 2 : ℝ) : ℂ) / ((‖x.1‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := Complex.log) (f := fun x : Spinor × Spinor =>
      ((‖x.2‖ ^ 2 : ℝ) : ℂ) / ((‖x.1‖ ^ 2 : ℝ) : ℂ)) (Z, Z')
      (hasStrictFDerivAt_log_real hslit2).hasFDerivAt.differentiableAt hq
  exact (((differentiableAt_const _).mul hlogP).sub ((differentiableAt_const _).mul hlog1)).add
    ((differentiableAt_const _).mul hlog2)


/-- **The derivative of the action of one triangle along a curve in the two spinors** (`2k = n`),
at a point where the product of the overlaps is off the cut of the logarithm: the same
`(source coefficient) + (target coefficient)` as `hasDerivAt_triFactor_curve`. -/
theorem hasDerivAt_triAction_curve (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (W W' : Spinor)
    {Zc Z'c : ℝ → Spinor} (hZc : HasDerivAt Zc W 0) (hZ'c : HasDerivAt Z'c W' 0)
    (h0 : Zc 0 = Z) (h0' : Z'c 0 = Z')
    (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0)
    (hP : inner ℂ Z ξ * inner ℂ (jMap ξ') Z' ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => triAction ((n : ℝ) / 2) p (Zc t) ξ (Z'c t) ξ')
      (((n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) -
            ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ Z W).re / ‖Z‖ ^ 2 : ℝ) : ℂ)) +
          ((n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') Z') -
            ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ Z' W').re / ‖Z'‖ ^ 2 : ℝ) : ℂ))) 0 := by
  set f : Spinor × Spinor → ℂ := fun x => triAction ((n : ℝ) / 2) p x.1 ξ x.2 ξ' with hf
  have hF := (differentiableAt_triAction ((n : ℝ) / 2) p ξ ξ' hZ hZ' hP).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => (Zc t, Z'c t)) (W, W') 0 := hZc.prodMk hZ'c
  rw [← h0, ← h0'] at hF
  have hc := hF.comp_hasDerivAt (0 : ℝ) hcurve
  rw [h0, h0'] at hc
  set d : ℂ := fderiv ℝ f (Z, Z') (W, W') with hd
  have hS : HasDerivAt (fun t : ℝ => triAction ((n : ℝ) / 2) p (Zc t) ξ (Z'c t) ξ') d 0 := hc
  have hT := hasDerivAt_triFactor_curve n p W W' hZc hZ'c h0 h0' hZ hZ' h1 h2
  have hexp := hS.cexp
  have hcZ : ContinuousAt Zc 0 := hZc.continuousAt
  have hcZ' : ContinuousAt Z'c 0 := hZ'c.continuousAt
  have hev : ∀ᶠ t : ℝ in nhds 0, Zc t ≠ 0 ∧ Z'c t ≠ 0 ∧ inner ℂ (Zc t) ξ ≠ 0 ∧
      inner ℂ (jMap ξ') (Z'c t) ≠ 0 := by
    have e1 := hcZ.eventually_ne (by simpa [h0] using hZ)
    have e2 := hcZ'.eventually_ne (by simpa [h0'] using hZ')
    have e3 : ContinuousAt (fun t => inner ℂ (Zc t) ξ) 0 := hcZ.inner continuousAt_const
    have e4 : ContinuousAt (fun t => inner ℂ (jMap ξ') (Z'c t)) 0 :=
      continuousAt_const.inner hcZ'
    have e3' := e3.eventually_ne (by simpa [h0] using h1)
    have e4' := e4.eventually_ne (by simpa [h0'] using h2)
    exact e1.and (e2.and (e3'.and e4'))
  have heq : (fun t : ℝ => Complex.exp (triAction ((n : ℝ) / 2) p (Zc t) ξ (Z'c t) ξ')) =ᶠ[nhds 0]
      fun t : ℝ => triFactor n p (Zc t) ξ (Z'c t) ξ' := by
    filter_upwards [hev] with t ⟨a, b, c, e⟩
    exact exp_triAction_eq_triFactor n p a b c e
  have hT' := hT.congr_of_eventuallyEq heq
  have hu := hexp.unique hT'
  have hS0 : Complex.exp (triAction ((n : ℝ) / 2) p (Zc 0) ξ (Z'c 0) ξ') =
      triFactor n p Z ξ Z' ξ' := by
    rw [h0, h0']; exact exp_triAction_eq_triFactor n p hZ hZ' h1 h2
  rw [hS0] at hu
  have hd_eq := mul_left_cancel₀ (triFactor_ne_zero n p hZ hZ' h1 h2) hu
  rw [← hd_eq]
  exact hS

end Lightlike.Asymptotics.Lorentzian

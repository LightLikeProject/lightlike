import Lightlike.Asymptotics.Lorentzian.CriticalGradient
import Lightlike.Asymptotics.Lorentzian.TriActionDeriv
import Lightlike.Asymptotics.Lorentzian.SpinorPauli

/-!
# The Hessian block of one node of the Lorentzian vertex action

`hessXX_block`: at a critical configuration (`IsLorCritical`, critical spinors `critZ`), the second
derivative at `0` of `t ↦ lorAction` along `X_a Y(t)`, with `Y' = Y · genMat (β + iα)` (rotation
`α`, boost `β`, generators `J = iσ/2`, `K = σ/2`) and the other group elements and the spinors
fixed, is the sum over the ends at the node `a` of `endForm`: the closed form of the block
`H^{X_a X_a}` of BDFHP Appendix A, eq. (61).

## Main results

* `hasDerivAt_srcCoeff`, `hasDerivAt_tgtCoeff`: the derivative of the first-variation coefficients
  of one triangle along a one-parameter orbit.
* `hasDerivAt_srcCoeff_eval`, `hasDerivAt_tgtCoeff_eval`: their values in `α, β, m`.
* `hessXX_block`: the block, `Σ_{e ∋ a} endForm`.
* `re_hessRR_neg`: the real part of the rotation block is negative definite exactly when the normals
  are not all parallel (`sum_projForm_pos_iff`, Lagrange's identity `projForm_eq_minorSq`).

## Conventions

`m_e` is the spin vector of the spinor at the `a`-end of the edge `e`: `ξ_ab` at a source end and
`ξ_ba` at a target end (the vectors of the closure `Σ k m = 0`, BDFHP eq. (25)); `σ_e = +1` at a
source end and `-1` at a target end; `k_e = j e`, `p_e = γ k_e`.

## Implementation notes

The first derivative is computed at every `t` near `0` (`hasDerivAt_triAction_curve_at`) and
differentiated once more; the matrix exponential is not used (Mathlib has no `det exp = exp tr`):
the one-parameter subgroup enters through the ODE `Y' = Y L` of its entries. The target end is
reduced to the source end by the antiunitary `J` (`tgtCoeff_eq`), which sends `genMat d` to
`genMat (-conj d)`.

The result is `1/4` of BDFHP (61) for source ends, the printed blocks corresponding to the
generators `iσ` and `σ` (a factor `2` in `(α, β)`): measured, with those generators (61) is
reproduced to `5·10⁻⁷` at a node whose ends are all source ends. At a node with target ends no
variant of (61) agrees (relative residuals between `0.2` and `1.6`, depending on the
configuration, in `scripts/asymptotics/lorentzian_hessian_paper61_check.py`), while `endForm` agrees with
the independent `44 × 44` numerics of `scripts/asymptotics/lorentzian_hessian_check.py` to `2·10⁻¹⁹`
(`scripts/asymptotics/lorentzian_hessian_node_check.py`).

## References

* `bdfhp-2010`, Appendix A, eqs. (58)-(61).
-/

open Complex
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian


/-- Product rule for the complex inner product along real curves of spinors. -/
theorem hasDerivAt_inner_spinor {u v : ℝ → Spinor} {u' v' : Spinor} {t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => inner ℂ (u s) (v s)) (inner ℂ u' (v t) + inner ℂ (u t) v') t := by
  have hu' := hasDerivAt_spinor_iff.mp hu
  have hv' := hasDerivAt_spinor_iff.mp hv
  have h0 := ((hv' 0).mul (hu' 0).star).add ((hv' 1).mul (hu' 1).star)
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  refine h0.congr_deriv ?_
  simp [star_def]
  ring

/-- `hasDerivAt_spinAct` at an arbitrary parameter `t`. -/
theorem hasDerivAt_spinAct_at {M : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {M' : Matrix (Fin 2) (Fin 2) ℂ}
    {v : ℝ → Spinor} {v' : Spinor} {t : ℝ} (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => spinAct (M s) (v s)) (spinAct M' (v t) + spinAct (M t) v') t := by
  have hv' := hasDerivAt_spinor_iff.mp hv
  rw [hasDerivAt_spinor_iff]
  intro i
  fin_cases i
  · have := ((hM 0 0).mul (hv' 0)).add ((hM 0 1).mul (hv' 1))
    exact this.congr_deriv (by simp; ring)
  · have := ((hM 1 0).mul (hv' 0)).add ((hM 1 1).mul (hv' 1))
    exact this.congr_deriv (by simp; ring)

/-- The source-end coefficient of the first variation of the triangle action in the direction `W`
(`hasDerivAt_triAction_curve`, with the target fixed). -/
noncomputable def srcCoeff (n : ℕ) (p : ℝ) (ξ Z W : Spinor) : ℂ :=
  (n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) -
    ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ Z W).re / ‖Z‖ ^ 2 : ℝ) : ℂ)

/-- **Derivative of the source coefficient along a one-parameter orbit** `Z' = M Z`, at `Z(0) = ξ`
with `‖ξ‖ = 1`. -/
theorem hasDerivAt_srcCoeff (n : ℕ) (p : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) {ξ : Spinor}
    (hξ : ‖ξ‖ = 1) {Z : ℝ → Spinor} (hZ : ∀ t, HasDerivAt Z (spinAct M (Z t)) t) (hZ0 : Z 0 = ξ) :
    HasDerivAt (fun t => srcCoeff n p ξ (Z t) (spinAct M (Z t)))
      ((n : ℂ) * (inner ℂ (spinAct M (spinAct M ξ)) ξ - inner ℂ (spinAct M ξ) ξ ^ 2) -
        ((n : ℂ) + 2 * Complex.I * p) *
          ((‖spinAct M ξ‖ ^ 2 + (inner ℂ ξ (spinAct M (spinAct M ξ))).re -
            2 * (inner ℂ ξ (spinAct M ξ)).re ^ 2 : ℝ) : ℂ)) 0 := by
  have hW : ∀ t, HasDerivAt (fun s => spinAct M (Z s)) (spinAct M (spinAct M (Z t))) t := by
    intro t
    have := hasDerivAt_spinAct_at (M := fun _ : ℝ => M) (M' := 0) (t := t)
      (fun i j => by simpa using hasDerivAt_const t (M i j)) (hZ t)
    have h0 : spinAct (0 : Matrix (Fin 2) (Fin 2) ℂ) (Z t) = 0 := by
      ext i; fin_cases i <;> simp
    simpa [h0] using this
  have hc0 : (0 : Spinor) = 0 := rfl
  have hN := hasDerivAt_inner_spinor (hW 0) (hasDerivAt_const (0 : ℝ) ξ)
  have hD := hasDerivAt_inner_spinor (hZ 0) (hasDerivAt_const (0 : ℝ) ξ)
  have hR := hasDerivAt_inner_spinor (hZ 0) (hW 0)
  have hQ := hasDerivAt_inner_spinor (hZ 0) (hZ 0)
  rw [hZ0] at hN hD hR hQ
  have hRre : HasDerivAt (fun t => (inner ℂ (Z t) (spinAct M (Z t))).re)
      (inner ℂ (spinAct M ξ) (spinAct M ξ) + inner ℂ ξ (spinAct M (spinAct M ξ))).re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hR
    exact this
  have hQre : HasDerivAt (fun t => ‖Z t‖ ^ 2)
      (inner ℂ (spinAct M ξ) ξ + inner ℂ ξ (spinAct M ξ)).re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hQ
    have e : (fun t => (inner ℂ (Z t) (Z t)).re) = fun t => ‖Z t‖ ^ 2 := by
      funext t; rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [← e]
    exact this
  have hQ0 : ‖Z 0‖ ^ 2 = 1 := by rw [hZ0, hξ]; norm_num
  have hq := hRre.div hQre (by rw [hQ0]; norm_num)
  have hqC : HasDerivAt (fun t => (((inner ℂ (Z t) (spinAct M (Z t))).re / ‖Z t‖ ^ 2 : ℝ) : ℂ)) _ 0 :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  have hin : inner ℂ ξ ξ = 1 := by rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hnd := (hN.congr_deriv (by rw [inner_zero_right, add_zero])).div
    (hD.congr_deriv (by rw [inner_zero_right, add_zero])) (by rw [hZ0, hin]; exact one_ne_zero)
  have hfin := (hnd.const_mul (n : ℂ)).sub (hqC.const_mul ((n : ℂ) + 2 * Complex.I * p))
  refine hfin.congr_deriv ?_
  rw [hZ0, hin]
  have h1 : (inner ℂ (spinAct M ξ) (spinAct M ξ)).re = ‖spinAct M ξ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : (inner ℂ (spinAct M ξ) ξ).re = (inner ℂ ξ (spinAct M ξ)).re := by
    rw [← inner_conj_symm, Complex.conj_re]
  simp only [Complex.ofRealCLM_apply, Complex.add_re, h1, h2, hξ]
  push_cast
  ring



/-- `J` as a real-linear map has the derivative `J v'` along a curve. -/
theorem hasDerivAt_jMap {v : ℝ → Spinor} {v' : Spinor} {t : ℝ} (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => jMap (v s)) (jMap v') t := by
  have hv' := hasDerivAt_spinor_iff.mp hv
  rw [hasDerivAt_spinor_iff]
  intro i
  fin_cases i
  · have := ((hv' 1).star).neg
    simp only [jMap_zero_apply]
    exact this
  · have := (hv' 0).star
    simp only [jMap_one_apply]
    exact this

/-- `J` intertwines `genMat d` with `genMat (-conj d)`. -/
theorem jMap_spinAct_genMat (d : Fin 3 → ℂ) (ξ : Spinor) :
    jMap (spinAct (genMat d) ξ) = spinAct (genMat (fun i => -conj (d i))) (jMap ξ) := by
  rw [spinAct_genMat, spinAct_genMat, jMap_gen]


/-- The target-end coefficient of the first variation of the triangle action in the direction `W'`
(`hasDerivAt_triAction_curve`, with the source fixed). -/
noncomputable def tgtCoeff (n : ℕ) (p : ℝ) (ξ' Z' W' : Spinor) : ℂ :=
  (n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') Z') -
    ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ Z' W').re / ‖Z'‖ ^ 2 : ℝ) : ℂ)

/-- The target coefficient is the source coefficient of the `J`-conjugate with `p ↦ -p`. -/
theorem tgtCoeff_eq (n : ℕ) (p : ℝ) (ξ' Z' W' : Spinor) :
    tgtCoeff n p ξ' Z' W' = srcCoeff n (-p) ξ' (jMap Z') (jMap W') := by
  have e1 : ∀ Y : Spinor, inner ℂ (jMap ξ') Y = -inner ℂ (jMap Y) ξ' := by
    intro Y
    have : Y = -jMap (jMap Y) := by rw [jMap_jMap]; simp
    conv_lhs => rw [this]
    rw [inner_neg_right, inner_jMap_jMap, inner_conj_symm]
  unfold tgtCoeff srcCoeff
  rw [e1 W', e1 Z', inner_jMap_jMap, norm_jMap, Complex.conj_re]
  push_cast
  by_cases h : inner ℂ (jMap Z') ξ' = 0
  · simp [h]
    left; ring
  · field_simp
    ring

/-- `srcCoeff` is unchanged when `Z` and `W` are multiplied by the same nonzero complex number. -/
theorem srcCoeff_smul (n : ℕ) (p : ℝ) (ξ Z W : Spinor) {μ : ℂ} (hμ : μ ≠ 0) :
    srcCoeff n p ξ (μ • Z) (μ • W) = srcCoeff n p ξ Z W := by
  unfold srcCoeff
  have e1 : inner ℂ (μ • W) ξ = conj μ * inner ℂ W ξ := inner_smul_left _ _ _
  have e2 : inner ℂ (μ • Z) ξ = conj μ * inner ℂ Z ξ := inner_smul_left _ _ _
  have e3 : inner ℂ (μ • Z) (μ • W) = (conj μ * μ) * inner ℂ Z W := by
    rw [inner_smul_left, inner_smul_right]; ring
  have hc : conj μ ≠ 0 := by simpa using hμ
  have e4 : ‖μ • Z‖ ^ 2 = ‖μ‖ ^ 2 * ‖Z‖ ^ 2 := by rw [norm_smul]; ring
  have e5 : conj μ * μ = ((‖μ‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.conj_mul']; push_cast; ring
  have hn : (‖μ‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hA : inner ℂ (μ • W) ξ / inner ℂ (μ • Z) ξ = inner ℂ W ξ / inner ℂ Z ξ := by
    rw [e1, e2, mul_div_mul_left _ _ hc]
  have hB : (inner ℂ (μ • Z) (μ • W)).re / ‖μ • Z‖ ^ 2 = (inner ℂ Z W).re / ‖Z‖ ^ 2 := by
    rw [e3, e4, e5, Complex.re_ofReal_mul, mul_div_mul_left _ _ hn]
  rw [hA, hB]

/-- **Derivative of the target coefficient along a one-parameter orbit** `Z' = (genMat d) Z`, at
`Z(0) = lam · J ξ'` with `‖ξ'‖ = 1`, `lam ≠ 0`: the value of `hasDerivAt_srcCoeff` for the
`J`-conjugate matrix `genMat (-conj d)` and `-p`. -/
theorem hasDerivAt_tgtCoeff (n : ℕ) (p : ℝ) (d : Fin 3 → ℂ) {ξ' : Spinor} (hξ' : ‖ξ'‖ = 1)
    {lam : ℂ} (hlam : lam ≠ 0) {Z : ℝ → Spinor}
    (hZ : ∀ t, HasDerivAt Z (spinAct (genMat d) (Z t)) t) (hZ0 : Z 0 = lam • jMap ξ') :
    HasDerivAt (fun t => tgtCoeff n p ξ' (Z t) (spinAct (genMat d) (Z t)))
      ((n : ℂ) * (inner ℂ (spinAct (genMat fun i => -conj (d i)) (spinAct (genMat fun i => -conj (d i)) ξ')) ξ' -
          inner ℂ (spinAct (genMat fun i => -conj (d i)) ξ') ξ' ^ 2) -
        ((n : ℂ) + 2 * Complex.I * (-p : ℝ)) *
          ((‖spinAct (genMat fun i => -conj (d i)) ξ'‖ ^ 2 +
            (inner ℂ ξ' (spinAct (genMat fun i => -conj (d i)) (spinAct (genMat fun i => -conj (d i)) ξ'))).re -
            2 * (inner ℂ ξ' (spinAct (genMat fun i => -conj (d i)) ξ')).re ^ 2 : ℝ) : ℂ)) 0 := by
  set d' : Fin 3 → ℂ := fun i => -conj (d i) with hd'
  have hlc : (-(conj lam)) ≠ 0 := by simpa using hlam
  set μ : ℂ := (-(conj lam))⁻¹ with hμ
  have hμ0 : μ ≠ 0 := inv_ne_zero hlc
  have hY : ∀ t, HasDerivAt (fun s => μ • jMap (Z s)) (spinAct (genMat d') (μ • jMap (Z t))) t := by
    intro t
    have := (hasDerivAt_jMap (hZ t)).const_smul μ
    refine this.congr_deriv ?_
    rw [jMap_spinAct_genMat, spinAct_smul]
  have hY0 : μ • jMap (Z 0) = ξ' := by
    rw [hZ0]
    have : jMap (lam • jMap ξ') = (-(conj lam)) • ξ' := by
      ext i; fin_cases i <;> simp [jMap_zero_apply, jMap_one_apply]
    rw [this, smul_smul, hμ, inv_mul_cancel₀ hlc, one_smul]
  have h := hasDerivAt_srcCoeff n (-p) (genMat d') hξ' hY hY0
  have hfun : (fun t => tgtCoeff n p ξ' (Z t) (spinAct (genMat d) (Z t))) =
      fun t => srcCoeff n (-p) ξ' (μ • jMap (Z t)) (spinAct (genMat d') (μ • jMap (Z t))) := by
    funext t
    rw [tgtCoeff_eq, jMap_spinAct_genMat, spinAct_smul, srcCoeff_smul n (-p) ξ' _ _ hμ0]
  rw [hfun]
  exact h



/-- `hasDerivAt_triAction_curve` at an arbitrary parameter `t` (curves differentiable at `t`). -/
theorem hasDerivAt_triAction_curve_at (n : ℕ) (p : ℝ) {ξ ξ' : Spinor} (W W' : Spinor)
    {Zc Z'c : ℝ → Spinor} {t : ℝ} (hZc : HasDerivAt Zc W t) (hZ'c : HasDerivAt Z'c W' t)
    (hZ : Zc t ≠ 0) (hZ' : Z'c t ≠ 0) (h1 : inner ℂ (Zc t) ξ ≠ 0)
    (h2 : inner ℂ (jMap ξ') (Z'c t) ≠ 0)
    (hP : inner ℂ (Zc t) ξ * inner ℂ (jMap ξ') (Z'c t) ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => triAction ((n : ℝ) / 2) p (Zc s) ξ (Z'c s) ξ')
      (((n : ℂ) * (inner ℂ W ξ / inner ℂ (Zc t) ξ) -
            ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ (Zc t) W).re / ‖Zc t‖ ^ 2 : ℝ) : ℂ)) +
          ((n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') (Z'c t)) -
            ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ (Z'c t) W').re / ‖Z'c t‖ ^ 2 : ℝ) : ℂ))) t := by
  have h1' : HasDerivAt (fun s => Zc (t + s)) W 0 := by
    simpa using HasDerivAt.comp_const_add t 0 (by simpa using hZc)
  have h2' : HasDerivAt (fun s => Z'c (t + s)) W' 0 := by
    simpa using HasDerivAt.comp_const_add t 0 (by simpa using hZ'c)
  have := hasDerivAt_triAction_curve n p (ξ := ξ) (ξ' := ξ') W W' h1' h2' (by simp) (by simp)
    hZ hZ' h1 h2 hP
  have hG := this
  -- shift back
  have key := HasDerivAt.comp_add_const (f := fun s => triAction ((n : ℝ) / 2) p (Zc (t + s)) ξ (Z'c (t + s)) ξ') t (-t)
    (by simpa using hG)
  simpa using key


/-- **The source-end triangle action along a curve with the target fixed**: where the overlaps are
off the cut, `triAction` has derivative `srcCoeff` along `Z' = W`. -/
theorem hasDerivAt_edge_src (n : ℕ) (p : ℝ) {ξ ξ' Zp : Spinor} {Z : ℝ → Spinor} {W : Spinor} {t : ℝ}
    (hZc : HasDerivAt Z W t) (hZ : Z t ≠ 0) (hZp : Zp ≠ 0) (h1 : inner ℂ (Z t) ξ ≠ 0)
    (h2 : inner ℂ (jMap ξ') Zp ≠ 0)
    (hP : inner ℂ (Z t) ξ * inner ℂ (jMap ξ') Zp ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => triAction ((n : ℝ) / 2) p (Z s) ξ Zp ξ')
      (srcCoeff n p ξ (Z t) W) t := by
  have := hasDerivAt_triAction_curve_at n p (ξ := ξ) (ξ' := ξ') W 0 hZc
    (hasDerivAt_const t Zp) hZ hZp h1 h2 hP
  refine this.congr_deriv ?_
  simp [srcCoeff]

/-- **The target-end triangle action along a curve with the source fixed.** -/
theorem hasDerivAt_edge_tgt (n : ℕ) (p : ℝ) {ξ ξ' Zs : Spinor} {Z' : ℝ → Spinor} {W' : Spinor}
    {t : ℝ} (hZ'c : HasDerivAt Z' W' t) (hZs : Zs ≠ 0) (hZ' : Z' t ≠ 0)
    (h1 : inner ℂ Zs ξ ≠ 0) (h2 : inner ℂ (jMap ξ') (Z' t) ≠ 0)
    (hP : inner ℂ Zs ξ * inner ℂ (jMap ξ') (Z' t) ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => triAction ((n : ℝ) / 2) p Zs ξ (Z' s) ξ')
      (tgtCoeff n p ξ' (Z' t) W') t := by
  have := hasDerivAt_triAction_curve_at n p (ξ := ξ) (ξ' := ξ') 0 W' (hasDerivAt_const t Zs)
    hZ'c hZs hZ' h1 h2 hP
  refine this.congr_deriv ?_
  simp [tgtCoeff]

/-- The end formula `k (-½ (α,α) + i σ (α,β) + σ m·(α×β)) - (k/2 + i σ p) (β,β)` of one end of a node
(`σ = 1` at a source end, `-1` at a target end). -/
noncomputable def endForm (k p σ : ℝ) (m α β : Fin 3 → ℝ) : ℂ :=
  (k : ℂ) * (-(1 / 2 : ℂ) * (projForm m α α : ℝ) + Complex.I * σ * (projForm m α β : ℝ) +
      σ * (tripleForm m α β : ℝ)) -
    ((k : ℂ) / 2 + Complex.I * σ * p) * (projForm m β β : ℝ)

/-- **Source end, evaluated**: along an orbit `Z' = (genMat (β - iα)) Z` with `Z(0) = ξ`, the source
coefficient has derivative `endForm (n/2) p 1 + i p m·(α×β)`. -/
theorem hasDerivAt_srcCoeff_eval (n : ℕ) (p : ℝ) (α β : Fin 3 → ℝ) {ξ : Spinor} (hξ : ‖ξ‖ = 1)
    {Z : ℝ → Spinor}
    (hZ : ∀ t, HasDerivAt Z (spinAct (genMat fun i => (β i : ℂ) - Complex.I * α i) (Z t)) t)
    (hZ0 : Z 0 = ξ) :
    HasDerivAt (fun t => srcCoeff n p ξ (Z t)
        (spinAct (genMat fun i => (β i : ℂ) - Complex.I * α i) (Z t)))
      (endForm ((n : ℝ) / 2) p 1 (spinVec ξ) α β +
        Complex.I * p * (tripleForm (spinVec ξ) α β : ℝ)) 0 := by
  have h := hasDerivAt_srcCoeff n p (genMat fun i => (β i : ℂ) - Complex.I * α i) hξ hZ hZ0
  refine h.congr_deriv ?_
  have := srcValue_eval n p α β hξ
  simp only at this
  rw [this]
  simp only [endForm]
  push_cast
  ring

/-- **Target end, evaluated**: along an orbit `Z' = (genMat (β - iα)) Z` with `Z(0) = λ J ξ'`, the
target coefficient has derivative `endForm (n/2) p (-1) + i p m·(α×β)`. -/
theorem hasDerivAt_tgtCoeff_eval (n : ℕ) (p : ℝ) (α β : Fin 3 → ℝ) {ξ' : Spinor} (hξ' : ‖ξ'‖ = 1)
    {lam : ℂ} (hlam : lam ≠ 0) {Z : ℝ → Spinor}
    (hZ : ∀ t, HasDerivAt Z (spinAct (genMat fun i => (β i : ℂ) - Complex.I * α i) (Z t)) t)
    (hZ0 : Z 0 = lam • jMap ξ') :
    HasDerivAt (fun t => tgtCoeff n p ξ' (Z t)
        (spinAct (genMat fun i => (β i : ℂ) - Complex.I * α i) (Z t)))
      (endForm ((n : ℝ) / 2) p (-1) (spinVec ξ') α β +
        Complex.I * p * (tripleForm (spinVec ξ') α β : ℝ)) 0 := by
  have h := hasDerivAt_tgtCoeff n p (fun i => (β i : ℂ) - Complex.I * α i) hξ' hlam hZ hZ0
  refine h.congr_deriv ?_
  have hd : (fun i => -conj (((β i : ℂ) - Complex.I * α i))) = fun i => (((-β) i : ℝ) : ℂ) - Complex.I * α i := by
    funext i; simp [Complex.conj_ofReal, Complex.conj_I]; ring
  rw [hd]
  have := srcValue_eval n (-p) α (-β) hξ'
  simp only at this
  rw [this]
  simp only [endForm, projForm, tripleForm, Pi.neg_apply, Fin.sum_univ_three]
  push_cast
  ring

/-- **The orbit of a spinor under the conjugate transpose of a one-parameter subgroup**:
if `Y' = Y · L` (entrywise) then `s ↦ (Y s)† v` has derivative `L† ((Y t)† v)`. -/
theorem hasDerivAt_orbit (L : Matrix (Fin 2) (Fin 2) ℂ) (Y : ℝ → SL2C)
    (hY : ∀ t i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
      (((Y t : Matrix (Fin 2) (Fin 2) ℂ) * L) i k) t) (v : Spinor) (t : ℝ) :
    HasDerivAt (fun s => spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v)
      (spinAct Lᴴ (spinAct (Y t : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v)) t := by
  have hc : ∀ i k, HasDerivAt (fun s => ((Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) i k)
      ((((Y t : Matrix (Fin 2) (Fin 2) ℂ) * L)ᴴ) i k) t := by
    intro i k
    have := (hY t k i).star
    simpa [Matrix.conjTranspose_apply] using this
  have := hasDerivAt_spinAct_at (M := fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
    (M' := ((Y t : Matrix (Fin 2) (Fin 2) ℂ) * L)ᴴ) (v := fun _ => v) (v' := 0) (t := t) hc
    (hasDerivAt_const t v)
  refine this.congr_deriv ?_
  have h0 : spinAct ((Y t : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) (0 : Spinor) = 0 := by
    ext i; fin_cases i <;> simp
  rw [h0, add_zero, Matrix.conjTranspose_mul, spinAct_mul]

/-- The spin vector of the end at node `a` (the vector of the closure). -/
noncomputable def endVec (g : BdryData) (e : Fin 10) (a : Fin 5) : Fin 3 → ℝ :=
  if edgeSrc e = a then spinVec (firstCol (g e 0)) else spinVec (firstCol (g e 1))

/-- `+1` if `a` is the source of `e`, `-1` otherwise. -/
def endSign (e : Fin 10) (a : Fin 5) : ℝ := if edgeSrc e = a then 1 else -1

/-- **The Hessian block `H^{X_a X_a}` of the vertex action at a critical configuration** (BDFHP
Appendix A, eq. (61), in the normalisation of the generators `J = iσ/2`, `K = σ/2`).

Hypotheses: `X₀` satisfies the z-eliminated critical equations (`IsLorCritical`) and the spinors are
the critical ones (`critZ`); the boundary spinors `ξ_ab = firstCol (g e 0)` and `ξ_ba = firstCol
(g e 1)` have norm one; `j e = n e / 2` and `p e = γ j e` (BDFHP eq. (24)); on every edge the product
of the overlaps `⟨Z,ξ⟩⟨Jξ',Z'⟩ = r c` at the critical point is off the cut of the logarithm
(`∈ slitPlane`); the vector closure `Σ_e j e m_e = 0` holds at the node `a`, with `m_e` the spin vector
of the spinor at the `a`-end of `e` (BDFHP eq. (25)); `Y : ℝ → SL(2,ℂ)` has `Y 0 = 1` and entrywise
`Y' = Y · genMat (β + iα)`.

Conclusion: the second derivative at `0` of `t ↦ lorAction j p g (X₀ with X₀ a replaced by X₀ a * Y t)
(critZ g X₀)` equals `Σ_{e ∋ a} endForm (j e) (p e) σ_e m_e α β`, with `σ_e = 1` at a source end and
`-1` at a target end. The first derivative is not assumed to vanish: it vanishes by closure
(`hasDerivAt_lorAction_critical`), which is not needed here. -/
theorem hessXX_block {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ} {γ : ℝ}
    (hj : ∀ e, j e = (n e : ℝ) / 2) (hp : ∀ e, p e = γ * j e) {g : BdryData} {X₀ : Fin 5 → SL2C}
    (hcrit : IsLorCritical g X₀) (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1)
    (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (hslit : ∀ e, inner ℂ (spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e))
        (firstCol (g e 0)) *
      inner ℂ (jMap (firstCol (g e 1)))
        (spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e)) ∈
        Complex.slitPlane)
    (a : Fin 5) (hk : ∀ i, ∑ e, ((if edgeSrc e = a then j e * spinVec (firstCol (g e 0)) i else 0) +
        (if edgeTgt e = a then j e * spinVec (firstCol (g e 1)) i else 0)) = 0)
    (α β : Fin 3 → ℝ) (Y : ℝ → SL2C) (hY0 : Y 0 = 1)
    (hY : ∀ t i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
      (((Y t : Matrix (Fin 2) (Fin 2) ℂ) *
        genMat (fun m => (β m : ℂ) + Complex.I * α m)) i k) t) :
    deriv (fun s => deriv (fun t => lorAction j p g (Function.update X₀ a (X₀ a * Y t))
        (critZ g X₀)) s) 0 =
      ∑ e, if edgeSrc e = a ∨ edgeTgt e = a then
        endForm (j e) (p e) (endSign e a) (endVec g e a) α β else 0 := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := genMat (fun i => (β i : ℂ) - Complex.I * α i) with hM
  have hMd : (genMat (fun m => (β m : ℂ) + Complex.I * α m))ᴴ = M := by
    rw [genMat_conjTranspose, hM]; congr 1; funext i; simp [Complex.conj_ofReal, Complex.conj_I]; ring
  -- the end curves
  set Xt : ℝ → Fin 5 → SL2C := fun t => Function.update X₀ a (X₀ a * Y t) with hXt
  set Zs : Fin 10 → ℝ → Spinor := fun e t =>
    spinAct (Xt t (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e) with hZs
  set Zt : Fin 10 → ℝ → Spinor := fun e t =>
    spinAct (Xt t (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e) with hZt
  choose r hr c hc h20 h21 using hcrit
  have hL : ∀ t i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
      (((Y t : Matrix (Fin 2) (Fin 2) ℂ) * genMat (fun m => (β m : ℂ) + Complex.I * α m)) i k) t := hY
  have horb := hasDerivAt_orbit (genMat (fun m => (β m : ℂ) + Complex.I * α m)) Y hY
  rw [hMd] at horb
  have hne : ∀ e : Fin 10, edgeSrc e ≠ edgeTgt e := fun e => edgeSrc_ne_edgeTgt e
  -- the source end of an edge
  have hZs : ∀ e t, HasDerivAt (Zs e)
      (if edgeSrc e = a then spinAct M (Zs e t) else 0) t := by
    intro e t
    by_cases h : edgeSrc e = a
    · have hfun : Zs e = fun s => spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (firstCol (g e 0)) := by
        funext s
        simp only [hZs, hXt, h, Function.update_self, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.conjTranspose_mul, spinAct_mul]
        have := critZ_src g X₀ e
        rw [h] at this
        rw [this]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact horb (firstCol (g e 0)) t
    · have hfun : Zs e = fun _ => spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e) := by
        funext s
        simp only [hZs, hXt, Function.update_of_ne h]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact hasDerivAt_const t _
  have hZt : ∀ e t, HasDerivAt (Zt e)
      (if edgeTgt e = a then spinAct M (Zt e t) else 0) t := by
    intro e t
    by_cases h : edgeTgt e = a
    · have hfun : Zt e = fun s => spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          (spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e)) := by
        funext s
        simp only [hZt, hXt, h, Function.update_self, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.conjTranspose_mul, spinAct_mul]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact horb _ t
    · have hfun : Zt e = fun _ => spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e) := by
        funext s
        simp only [hZt, hXt, Function.update_of_ne h]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact hasDerivAt_const t _
  -- the first derivative of the action, edge by edge
  set Ws : Fin 10 → ℝ → Spinor := fun e t => if edgeSrc e = a then spinAct M (Zs e t) else 0 with hWs
  set Wt : Fin 10 → ℝ → Spinor := fun e t => if edgeTgt e = a then spinAct M (Zt e t) else 0 with hWt
  set D : Fin 10 → ℝ → ℂ := fun e t =>
    srcCoeff (n e) (p e) (firstCol (g e 0)) (Zs e t) (Ws e t) +
      tgtCoeff (n e) (p e) (firstCol (g e 1)) (Zt e t) (Wt e t) with hD
  have hZ0s : ∀ e, Zs e 0 = spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e) := by
    intro e
    have hx : Xt 0 = X₀ := by simp only [hXt, hY0, mul_one, Function.update_eq_self]
    show spinAct (Xt 0 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ _ = _
    rw [hx]
  have hZ0t : ∀ e, Zt e 0 = spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e) := by
    intro e
    have hx : Xt 0 = X₀ := by simp only [hXt, hY0, mul_one, Function.update_eq_self]
    show spinAct (Xt 0 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ _ = _
    rw [hx]
  have hev : ∀ e, ∀ᶠ t : ℝ in nhds 0, HasDerivAt
      (fun s => triAction (j e) (p e) (Zs e s) (firstCol (g e 0)) (Zt e s) (firstCol (g e 1)))
      (D e t) t := by
    intro e
    have hcs : ContinuousAt (Zs e) 0 := (hZs e 0).continuousAt
    have hct : ContinuousAt (Zt e) 0 := (hZt e 0).continuousAt
    have hpr : ContinuousAt (fun t => inner ℂ (Zs e t) (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1))) (Zt e t)) 0 :=
      (hcs.inner continuousAt_const).mul (continuousAt_const.inner hct)
    have hmem : inner ℂ (Zs e 0) (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1))) (Zt e 0) ∈ Complex.slitPlane := by
      rw [hZ0s, hZ0t]; exact hslit e
    filter_upwards [hpr.eventually (Complex.isOpen_slitPlane.mem_nhds hmem)] with t ht
    have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
    have hne0 : inner ℂ (Zs e t) (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1))) (Zt e t) ≠ 0 := fun h => h0 (h ▸ ht)
    have h1 := left_ne_zero_of_mul hne0
    have h2 := right_ne_zero_of_mul hne0
    have hz : Zs e t ≠ 0 := fun h => h1 (by rw [h]; simp)
    have hz' : Zt e t ≠ 0 := fun h => h2 (by rw [h]; simp)
    rw [hj e]
    exact hasDerivAt_triAction_curve_at (n e) (p e) (Ws e t) (Wt e t)
      (by simpa [hWs] using hZs e t) (by simpa [hWt] using hZt e t) hz hz' h1 h2 ht
  set V : Fin 10 → ℂ := fun e =>
    if edgeSrc e = a then endForm (j e) (p e) 1 (spinVec (firstCol (g e 0))) α β +
      Complex.I * p e * (tripleForm (spinVec (firstCol (g e 0))) α β : ℝ)
    else if edgeTgt e = a then endForm (j e) (p e) (-1) (spinVec (firstCol (g e 1))) α β +
      Complex.I * p e * (tripleForm (spinVec (firstCol (g e 1))) α β : ℝ)
    else 0 with hV
  have hDV : ∀ e, HasDerivAt (D e) (V e) 0 := by
    intro e
    by_cases hs : edgeSrc e = a
    · have hnt : edgeTgt e ≠ a := fun h => hne e (hs.trans h.symm)
      have hfun : D e = fun t => srcCoeff (n e) (p e) (firstCol (g e 0)) (Zs e t)
          (spinAct M (Zs e t)) := by
        funext t
        simp [hD, hWs, hWt, hs, hnt, tgtCoeff]
      rw [hfun]
      have h0 : Zs e 0 = firstCol (g e 0) := by rw [hZ0s]; exact critZ_src g X₀ e
      have := hasDerivAt_srcCoeff_eval (n e) (p e) α β (hξ e)
        (Z := Zs e) (fun t => by simpa [hs] using hZs e t) h0
      simp only [hV, hs, ↓reduceIte, ← hj e] at this ⊢
      exact this
    · by_cases ht : edgeTgt e = a
      · have hfun : D e = fun t => tgtCoeff (n e) (p e) (firstCol (g e 1)) (Zt e t)
            (spinAct M (Zt e t)) := by
          funext t
          simp [hD, hWs, hWt, hs, ht, srcCoeff]
        rw [hfun]
        have hr0 : ((r e : ℂ) * c e) ≠ 0 := by
          have : (r e : ℂ) ≠ 0 := by exact_mod_cast (hr e).ne'
          have : c e ≠ 0 := by intro h; have := hc e; rw [h] at this; simp at this
          exact mul_ne_zero ‹(r e : ℂ) ≠ 0› this
        have h0 : Zt e 0 = ((r e : ℂ) * c e) • jMap (firstCol (g e 1)) := by
          rw [hZ0t]; exact critZ_tgt g X₀ e (r e) (c e) (h20 e)
        have := hasDerivAt_tgtCoeff_eval (n e) (p e) α β (hξ' e) hr0
          (Z := Zt e) (fun t => by simpa [ht] using hZt e t) h0
        simp only [hV, hs, ht, ↓reduceIte, ← hj e] at this ⊢
        exact this
      · have hfun : D e = fun _ => (0 : ℂ) := by
          funext t
          simp [hD, hWs, hWt, hs, ht, srcCoeff, tgtCoeff]
        rw [hfun]
        simp only [hV, hs, ht, ↓reduceIte]
        exact hasDerivAt_const _ _
  -- the derivative of the derivative
  have hall : ∀ᶠ t : ℝ in nhds 0, ∀ e, HasDerivAt
      (fun s => triAction (j e) (p e) (Zs e s) (firstCol (g e 0)) (Zt e s) (firstCol (g e 1)))
      (D e t) t := Filter.eventually_all.2 hev
  have hEq : (fun s => deriv (fun t => lorAction j p g (Function.update X₀ a (X₀ a * Y t))
      (critZ g X₀)) s) =ᶠ[nhds 0] fun t => ∑ e, D e t := by
    filter_upwards [hall] with t ht
    exact (HasDerivAt.fun_sum (u := Finset.univ) (fun e _ => ht e)).deriv
  have hDsum : HasDerivAt (fun t => ∑ e, D e t) (∑ e, V e) 0 :=
    HasDerivAt.fun_sum (fun e _ => hDV e)
  have hd2 := (hDsum.congr_of_eventuallyEq hEq).deriv
  rw [hd2]
  set Xend : Fin 10 → ℝ := fun e =>
    if edgeSrc e = a then tripleForm (spinVec (firstCol (g e 0))) α β
    else if edgeTgt e = a then tripleForm (spinVec (firstCol (g e 1))) α β else 0 with hXend
  have hV' : ∀ e, V e = (if edgeSrc e = a ∨ edgeTgt e = a then
      endForm (j e) (p e) (endSign e a) (endVec g e a) α β else 0) +
      Complex.I * p e * ((Xend e : ℝ) : ℂ) := by
    intro e
    by_cases hs : edgeSrc e = a
    · simp [hV, hXend, hs, endVec, endSign]
    · by_cases ht : edgeTgt e = a
      · simp [hV, hXend, hs, ht, endVec, endSign]
      · simp [hV, hXend, hs, ht]
  have hzero : ∑ e, j e * Xend e = 0 := by
    have hterm : ∀ e, j e * Xend e =
        (α 1 * β 2 - α 2 * β 1) * ((if edgeSrc e = a then j e * spinVec (firstCol (g e 0)) 0 else 0) +
          (if edgeTgt e = a then j e * spinVec (firstCol (g e 1)) 0 else 0)) +
        (α 2 * β 0 - α 0 * β 2) * ((if edgeSrc e = a then j e * spinVec (firstCol (g e 0)) 1 else 0) +
          (if edgeTgt e = a then j e * spinVec (firstCol (g e 1)) 1 else 0)) +
        (α 0 * β 1 - α 1 * β 0) * ((if edgeSrc e = a then j e * spinVec (firstCol (g e 0)) 2 else 0) +
          (if edgeTgt e = a then j e * spinVec (firstCol (g e 1)) 2 else 0)) := by
      intro e
      by_cases hs : edgeSrc e = a
      · have : ¬ edgeTgt e = a := fun h => hne e (hs.trans h.symm)
        simp [hXend, hs, this, tripleForm]; ring
      · by_cases ht : edgeTgt e = a
        · simp [hXend, hs, ht, tripleForm]; ring
        · simp [hXend, hs, ht]
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hk 0, hk 1, hk 2]
    ring
  have hpz : ∑ e, p e * Xend e = 0 := by
    simp only [hp, mul_assoc, ← Finset.mul_sum, hzero, mul_zero]
  calc ∑ e, V e = ∑ e, ((if edgeSrc e = a ∨ edgeTgt e = a then
        endForm (j e) (p e) (endSign e a) (endVec g e a) α β else 0) +
        Complex.I * p e * ((Xend e : ℝ) : ℂ)) := Finset.sum_congr rfl fun e _ => hV' e
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have : ∑ e, Complex.I * (p e : ℂ) * ((Xend e : ℝ) : ℂ) = 0 := by
        have := congrArg (fun x : ℝ => (x : ℂ)) hpz
        simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero] at this
        simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero]
      rw [this, add_zero]

/-- The minors `α_i m_j - α_j m_i` of the pair `(α, m)`: they all vanish exactly when `α` and `m` are
parallel. -/
def minorSq (m α : Fin 3 → ℝ) : ℝ :=
  (α 0 * m 1 - α 1 * m 0) ^ 2 + (α 0 * m 2 - α 2 * m 0) ^ 2 + (α 1 * m 2 - α 2 * m 1) ^ 2

/-- **Lagrange's identity for a unit vector**: `(α,α)_m = |α|² - (m·α)²` is the sum of the squares of
the minors of `(α, m)`, hence `≥ 0`, and `= 0` exactly when `α ∥ m`. -/
theorem projForm_eq_minorSq {m : Fin 3 → ℝ} (hm : ∑ i, m i ^ 2 = 1) (α : Fin 3 → ℝ) :
    projForm m α α = minorSq m α := by
  simp only [projForm, minorSq, Fin.sum_univ_three] at *
  nlinarith [hm]

theorem minorSq_nonneg (m α : Fin 3 → ℝ) : 0 ≤ minorSq m α := by
  unfold minorSq; positivity

theorem minorSq_eq_zero_iff (m α : Fin 3 → ℝ) :
    minorSq m α = 0 ↔ α 0 * m 1 - α 1 * m 0 = 0 ∧ α 0 * m 2 - α 2 * m 0 = 0 ∧
      α 1 * m 2 - α 2 * m 1 = 0 := by
  unfold minorSq
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (α 0 * m 1 - α 1 * m 0),
      sq_nonneg (α 0 * m 2 - α 2 * m 0), sq_nonneg (α 1 * m 2 - α 2 * m 1)]
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]; norm_num

/-- **The rotation block of the Hessian is negative definite exactly when the normals are not all
parallel to `α`**: for positive `k_e` and unit `m_e`, `Σ_e k_e (α,α)_e ≥ 0`, with equality iff every
`m_e` is parallel to `α` (all minors of `(α, m_e)` vanish). Combined with `Re endForm (β = 0) =
-½ k (α,α)` this is the statement that `Re H^RR` is negative definite iff the normals are not all
parallel (BDFHP App. A, eq. (61), `H^{RR} = -2 Σ k (δ - n n)` in their generators). -/
theorem sum_projForm_pos_iff {ι : Type*} [Fintype ι] (k : ι → ℝ) (m : ι → Fin 3 → ℝ)
    (hk : ∀ e, 0 < k e) (hm : ∀ e, ∑ i, m e i ^ 2 = 1) (α : Fin 3 → ℝ) :
    0 ≤ ∑ e, k e * projForm (m e) α α ∧
      (∑ e, k e * projForm (m e) α α = 0 ↔ ∀ e, minorSq (m e) α = 0) := by
  have hterm : ∀ e, k e * projForm (m e) α α = k e * minorSq (m e) α := fun e => by
    rw [projForm_eq_minorSq (hm e)]
  simp only [hterm]
  refine ⟨Finset.sum_nonneg fun e _ => mul_nonneg (hk e).le (minorSq_nonneg _ _), ?_⟩
  constructor
  · intro h e
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun e _ => mul_nonneg (hk e).le (minorSq_nonneg (m e) α)).mp h e
      (Finset.mem_univ e)
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 (hk e).ne'
    · exact h0
  · intro h
    exact Finset.sum_eq_zero fun e _ => by rw [h e, mul_zero]

/-- **Strict negativity of the rotation block**: if some normal is not parallel to `α` (some minor of
`(α, m_e)` is nonzero), `Σ_e k_e (α,α)_e > 0`. -/
theorem sum_projForm_pos {ι : Type*} [Fintype ι] (k : ι → ℝ) (m : ι → Fin 3 → ℝ)
    (hk : ∀ e, 0 < k e) (hm : ∀ e, ∑ i, m e i ^ 2 = 1) (α : Fin 3 → ℝ)
    (hnp : ∃ e, minorSq (m e) α ≠ 0) : 0 < ∑ e, k e * projForm (m e) α α := by
  obtain ⟨h0, h1⟩ := sum_projForm_pos_iff k m hk hm α
  refine lt_of_le_of_ne h0 fun h => ?_
  obtain ⟨e, he⟩ := hnp
  exact he ((h1.mp h.symm) e)


/-- **The rotation part of `endForm` has real part `-½ k (α,α)`**: with `β = 0`, the form of one end is
`k (-½ (α,α) + i σ·0 + σ m·(α × 0)) - 0 = -½ k (α,α)`. -/
theorem re_endForm_beta_zero (k p σ : ℝ) (m α : Fin 3 → ℝ) :
    (endForm k p σ m α 0).re = -(1 / 2) * k * projForm m α α := by
  simp [endForm, projForm, tripleForm]
  ring

/-- **The rotation block of the Hessian is negative definite exactly when the normals are not all
parallel.** Sign convention: `H` is the Hessian matrix of `hessXX_block`, `Q(v) = vᵀ H v` the second
derivative along `X_a exp(t (α J + β K))`; at `β = 0` the real part of the sum of the end formulas is
`Re Q(α, 0) = Σ_e Re endForm = -½ Σ_e k_e (α,α)_e`, i.e. `Re H^{RR}(α, α) = -½ Σ_e k_e (α,α)_e`.
For `k_e > 0` and unit `m_e`, `Re H^{RR}(α, α) < 0` for every `α ≠ 0` iff for no `α ≠ 0` are all the
`m_e` parallel to `α` (`sum_projForm_pos`): the quadratic form is definite precisely when the normals
are not all parallel (BDFHP App. A eq. (61), `H^{RR} = -2 Σ k (δ - n n)` in their generators, four times
this). Cross-checked numerically by a numpy certificate (regular tetrahedron and seeded random closed
configurations; the all-parallel control is degenerate). -/
theorem re_hessRR_neg {ι : Type*} [Fintype ι] (k p σ : ι → ℝ) (m : ι → Fin 3 → ℝ)
    (hk : ∀ e, 0 < k e) (hm : ∀ e, ∑ i, m e i ^ 2 = 1) (α : Fin 3 → ℝ)
    (hnp : ∃ e, minorSq (m e) α ≠ 0) :
    (∑ e, endForm (k e) (p e) (σ e) (m e) α 0).re < 0 := by
  have h := sum_projForm_pos k m hk hm α hnp
  have : (∑ e, endForm (k e) (p e) (σ e) (m e) α 0).re =
      ∑ e, -(1 / 2) * (k e * projForm (m e) α α) := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [re_endForm_beta_zero]; ring
  rw [this, ← Finset.mul_sum]
  linarith

end Lightlike.Asymptotics.Lorentzian

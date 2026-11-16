import Lightlike.Asymptotics.Lorentzian.HessianAssembly

/-!
# A critical configuration has closure; no critical configuration without closure

The converse of the gradient link of `CriticalGradient`: at a configuration with `Re S = 0` (the maximum of the real
part, BDFHP Sec. 4.2.1, eqs. (18), (19)) every edge is aligned, `Z_ab = λ ξ_ab`, `Z_ba = μ J ξ_ba`
(`aligned_of_re_lorAction_eq_zero`); there the first derivative of the vertex action along a curve `X_a Y(t)` is the sum
over the ends at `a` of the logarithmic derivative (`hasDerivAt_lorAction_aligned`, whatever the scalings `λ`, `μ`),
so stationarity along every such curve gives the closure `Σ_e n_e n̂_e = 0` of BDFHP eq. (25)
(`closure_of_stationary`, `critical_configuration_closure`), and for boundary data without closure at some node there
is no critical configuration (`no_critical_without_closure`). `exists_sl2_curve` gives, for every direction `c` of
`sl(2, ℂ)`, a Cayley curve in `SL(2, ℂ)` with that velocity.

This is the statement on the configuration space. The suppression of the integral for such data (BDFHP Sec. 6.4,
eq. (56), the sub-case without closure) needs it in a chart together with the non-stationary phase bound
(`Lightlike/Oscillatory/Localisation.lean`) for an action smooth only on an open set; that step is not done here.
-/

open Complex
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian

/-- The first variation of the source coefficient along `(genMat c)†` at `Z = λ ξ`, `λ ≠ 0`, `‖ξ‖ = 1`: the
logarithmic derivative (the coefficient is invariant under scaling `Z`, `W` by the same number). -/
theorem srcCoeff_adj_gen_smul (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) {ξ : Spinor} (hξ : ‖ξ‖ = 1) {lam : ℂ}
    (hlam : lam ≠ 0) :
    srcCoeff n p ξ (lam • ξ) (spinAct (genMat c)ᴴ (lam • ξ)) = logDeriv n p c ξ := by
  rw [spinAct_smul, srcCoeff_smul n p ξ _ _ hlam]
  exact srcCoeff_adj_gen n p c hξ

/-- **The one-triangle action along curves in the two spinors, at an aligned edge** (`Z = λ ξ`, `Z' = μ J ξ'`,
`λ μ ≠ 0`, the overlap product off the cut): the derivative at `0` is `srcCoeff + tgtCoeff` at the aligned
spinors. -/
theorem hasDerivAt_edge_aligned (n : ℕ) (p : ℝ) {ξ ξ' : Spinor} (hξ : ‖ξ‖ = 1) {Zc Z'c : ℝ → Spinor}
    {lam mu : ℂ} (h0 : Zc 0 = lam • ξ) (h0' : Z'c 0 = mu • jMap ξ')
    {W W' : Spinor} (hZc : HasDerivAt Zc W 0) (hZ'c : HasDerivAt Z'c W' 0)
    (hP : inner ℂ (Zc 0) ξ * inner ℂ (jMap ξ') (Z'c 0) ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => triAction ((n : ℝ) / 2) p (Zc s) ξ (Z'c s) ξ')
      (srcCoeff n p ξ (lam • ξ) W + tgtCoeff n p ξ' (mu • jMap ξ') W') 0 := by
  have hξ0 : ξ ≠ 0 := by intro h; rw [h] at hξ; simp at hξ
  have h0ne : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
  have hne0 : inner ℂ (Zc 0) ξ * inner ℂ (jMap ξ') (Z'c 0) ≠ 0 := fun h => h0ne (h ▸ hP)
  have h1 := left_ne_zero_of_mul hne0
  have h2 := right_ne_zero_of_mul hne0
  have hz : Zc 0 ≠ 0 := fun h => h1 (by rw [h]; simp)
  have hz' : Z'c 0 ≠ 0 := fun h => h2 (by rw [h]; simp)
  have := hasDerivAt_triAction_curve_at n p (ξ := ξ) (ξ' := ξ') W W' hZc hZ'c hz hz' h1 h2 hP
  rw [h0, h0'] at this
  refine this.congr_deriv ?_
  simp [srcCoeff, tgtCoeff]

/-- **The first derivative of the vertex action along a curve in one group element, at an aligned
configuration**: if `X₀_a† z_e = λ_e ξ_ab` at every source end and `X₀_b† z_e = μ_e J ξ_ba` at every target end
(`λ_e μ_e ≠ 0`, unit boundary spinors, overlap products off the cut), then along `X_a Y(t)` with `Y 0 = 1` and
`Y' 0 = genMat c` the derivative of `lorAction` at `0` is the sum over the ends at `a` of the logarithmic
derivative `logDeriv n p c ξ`. The scalings `λ_e`, `μ_e` do not matter. -/
theorem hasDerivAt_lorAction_aligned {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ}
    (hj : ∀ e, j e = (n e : ℝ) / 2) {g : BdryData} {X₀ : Fin 5 → SL2C} {z₀ : Fin 10 → Spinor}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1) (lam mu : Fin 10 → ℂ)
    (hlam : ∀ e, lam e ≠ 0) (hmu : ∀ e, mu e ≠ 0)
    (hsrc : ∀ e, spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = lam e • firstCol (g e 0))
    (htgt : ∀ e, spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = mu e • jMap (firstCol (g e 1)))
    (hslit : ∀ e, inner ℂ (spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e)) (firstCol (g e 0)) *
      inner ℂ (jMap (firstCol (g e 1))) (spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e)) ∈
        Complex.slitPlane)
    (a : Fin 5) (c : Fin 3 → ℂ) (Y : ℝ → SL2C) (hY0 : Y 0 = 1)
    (hY : ∀ i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
      (((Y 0 : Matrix (Fin 2) (Fin 2) ℂ) * genMat c) i k) 0) :
    HasDerivAt (fun t => lorAction j p g (Function.update X₀ a (X₀ a * Y t)) z₀)
      (∑ e, ((if edgeSrc e = a then logDeriv (n e) (p e) c (firstCol (g e 0)) else 0) +
        (if edgeTgt e = a then logDeriv (n e) (p e) c (firstCol (g e 1)) else 0))) 0 := by
  have hne : ∀ e : Fin 10, edgeSrc e ≠ edgeTgt e := fun e => edgeSrc_ne_edgeTgt e
  have hY1 : (Y 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by rw [hY0]; rfl
  have horb : ∀ v : Spinor, HasDerivAt (fun s => spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v)
      (spinAct (genMat c)ᴴ v) 0 := by
    intro v
    have := hasDerivAt_orbit_pt (genMat c) Y 0 hY v
    simpa [hY1, spinAct_one] using this
  have hedge : ∀ e, HasDerivAt (fun s => triAction (j e) (p e)
      (spinAct (Function.update X₀ a (X₀ a * Y s) (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e))
      (firstCol (g e 0))
      (spinAct (Function.update X₀ a (X₀ a * Y s) (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e))
      (firstCol (g e 1)))
      ((if edgeSrc e = a then logDeriv (n e) (p e) c (firstCol (g e 0)) else 0) +
        (if edgeTgt e = a then logDeriv (n e) (p e) c (firstCol (g e 1)) else 0)) 0 := by
    intro e
    have hP := hslit e
    rw [hsrc e, htgt e] at hP
    -- the curves of the two ends, pointwise
    have hSa : ∀ s, edgeSrc e = a → spinAct (Function.update X₀ a (X₀ a * Y s) (edgeSrc e) :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lam e • firstCol (g e 0)) := by
      intro s hs
      simp only [hs, Function.update_self, Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul, spinAct_mul]
      have := hsrc e
      rw [hs] at this
      rw [this]
    have hSn : ∀ s, edgeSrc e ≠ a → spinAct (Function.update X₀ a (X₀ a * Y s) (edgeSrc e) :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = lam e • firstCol (g e 0) := by
      intro s hs
      rw [Function.update_of_ne hs]
      exact hsrc e
    have hTa : ∀ s, edgeTgt e = a → spinAct (Function.update X₀ a (X₀ a * Y s) (edgeTgt e) :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (mu e • jMap (firstCol (g e 1))) := by
      intro s ht
      simp only [ht, Function.update_self, Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul, spinAct_mul]
      have := htgt e
      rw [ht] at this
      rw [this]
    have hTn : ∀ s, edgeTgt e ≠ a → spinAct (Function.update X₀ a (X₀ a * Y s) (edgeTgt e) :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = mu e • jMap (firstCol (g e 1)) := by
      intro s ht
      rw [Function.update_of_ne ht]
      exact htgt e
    rw [hj e]
    by_cases hs : edgeSrc e = a
    · have hnt : edgeTgt e ≠ a := fun h => hne e (hs.trans h.symm)
      simp only [eq_true hs, eq_false hnt, ↓reduceIte]
      simp only [hSa _ hs, hTn _ hnt]
      have key := hasDerivAt_edge_aligned (n e) (p e) (ξ' := firstCol (g e 1)) (lam := lam e) (mu := mu e) (hξ e) (Zc := fun s =>
        spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lam e • firstCol (g e 0)))
        (Z'c := fun _ => mu e • jMap (firstCol (g e 1)))
        (by simp [hY1, spinAct_one]) rfl (horb _) (hasDerivAt_const 0 _) (by simpa [hY1, spinAct_one] using hP)
      refine key.congr_deriv ?_
      rw [srcCoeff_adj_gen_smul (n e) (p e) c (hξ e) (hlam e), tgtCoeff_zero_dir, add_zero]
    · by_cases ht : edgeTgt e = a
      · simp only [eq_false hs, eq_true ht, ↓reduceIte]
        simp only [hSn _ hs, hTa _ ht]
        have key := hasDerivAt_edge_aligned (n e) (p e) (ξ' := firstCol (g e 1)) (lam := lam e) (mu := mu e) (hξ e)
          (Zc := fun _ => lam e • firstCol (g e 0))
          (Z'c := fun s => spinAct (Y s : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (mu e • jMap (firstCol (g e 1))))
          rfl (by simp [hY1, spinAct_one]) (hasDerivAt_const 0 _) (horb _) (by simpa [hY1, spinAct_one] using hP)
        refine key.congr_deriv ?_
        rw [tgtCoeff_adj_gen (n e) (p e) c (hξ' e) (hmu e), srcCoeff_zero_dir, zero_add]
      · simp only [eq_false hs, eq_false ht, ↓reduceIte]
        simp only [hSn _ hs, hTn _ ht]
        have key := hasDerivAt_edge_aligned (n e) (p e) (ξ' := firstCol (g e 1)) (lam := lam e) (mu := mu e) (hξ e)
          (Zc := fun _ => lam e • firstCol (g e 0)) (Z'c := fun _ => mu e • jMap (firstCol (g e 1)))
          rfl rfl (hasDerivAt_const 0 _) (hasDerivAt_const 0 _) hP
        refine key.congr_deriv ?_
        rw [srcCoeff_zero_dir, tgtCoeff_zero_dir, add_zero]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun e _ => hedge e)
  exact hs

/-- `s(t) = t² (c·c) / 16`. -/
noncomputable def curveS (c : Fin 3 → ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ 2 * (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) / 16

/-- The Cayley transform of `t · genMat c` as an explicit matrix: `((1 + s) 1 + t M) / (1 - s)`. -/
noncomputable def curveMat (c : Fin 3 → ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 - curveS c t)⁻¹ • ((1 + curveS c t) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (t : ℂ) • genMat c)

/-- `det ((1 + s) 1 + t M) = (1 - s)²` for the traceless `M = genMat c`. -/
theorem det_curveMat_num (c : Fin 3 → ℂ) (t : ℝ) :
    ((1 + curveS c t) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (t : ℂ) • genMat c).det = (1 - curveS c t) ^ 2 := by
  simp only [curveS, genMat, Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Where `s ≠ 1`, `curveMat c t` has determinant one. -/
theorem det_curveMat {c : Fin 3 → ℂ} {t : ℝ} (h : curveS c t ≠ 1) : (curveMat c t).det = 1 := by
  have h1 : (1 - curveS c t) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold curveMat
  rw [Matrix.det_smul, det_curveMat_num]
  simp only [Fintype.card_fin]
  field_simp

/-- A curve in `SL(2, ℂ)`: `curveMat c t` where `s ≠ 1`, the identity elsewhere. -/
noncomputable def slCurve (c : Fin 3 → ℂ) (t : ℝ) : SL2C :=
  if h : curveS c t ≠ 1 then ⟨curveMat c t, det_curveMat h⟩ else 1

/-- **A curve through the identity with a prescribed velocity**: for every `c` there is a curve `Y` in
`SL(2, ℂ)` with `Y 0 = 1` and entrywise derivative `genMat c` at `0` (a Cayley curve). -/
theorem exists_sl2_curve (c : Fin 3 → ℂ) :
    ∃ Y : ℝ → SL2C, Y 0 = 1 ∧ ∀ i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
      (((Y 0 : Matrix (Fin 2) (Fin 2) ℂ) * genMat c) i k) 0 := by
  refine ⟨slCurve c, ?_, ?_⟩
  · have h : curveS c 0 ≠ 1 := by simp [curveS]
    apply Subtype.ext
    simp [slCurve, curveMat, curveS]
  · intro i k
    have h0 : slCurve c 0 = 1 := by
      have h : curveS c 0 ≠ 1 := by simp [curveS]
      apply Subtype.ext
      simp [slCurve, curveMat, curveS]
    rw [h0]
    have hev : ∀ᶠ t : ℝ in nhds 0, curveS c t ≠ 1 := by
      have hc : Continuous fun t : ℝ => curveS c t := by unfold curveS; fun_prop
      exact hc.continuousAt.eventually_ne (by simp [curveS])
    have hf : (fun t : ℝ => (slCurve c t : Matrix (Fin 2) (Fin 2) ℂ) i k) =ᶠ[nhds 0]
        fun t : ℝ => (1 - curveS c t)⁻¹ * ((1 + curveS c t) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i k +
          (t : ℂ) * genMat c i k) := by
      filter_upwards [hev] with t ht
      simp [slCurve, ht, curveMat, Matrix.smul_apply, Matrix.add_apply]
      ring
    refine HasDerivAt.congr_of_eventuallyEq ?_ hf
    have hs : HasDerivAt (fun t : ℝ => curveS c t) 0 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
      have h2 := (h1.pow 2).mul_const (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) |>.div_const 16
      refine h2.congr_deriv ?_
      simp
    have hden : HasDerivAt (fun t : ℝ => (1 : ℂ) - curveS c t) (0 - 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (1 : ℂ)).sub hs
    rw [sub_zero] at hden
    have hinv := hden.inv (by simp [curveS])
    have hnum : HasDerivAt (fun t : ℝ => (1 + curveS c t) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i k +
        (t : ℂ) * genMat c i k) (genMat c i k) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
      have := (((hasDerivAt_const (0 : ℝ) (1 : ℂ)).add hs).mul_const ((1 : Matrix (Fin 2) (Fin 2) ℂ) i k)).add
        (h1.mul_const (genMat c i k))
      refine this.congr_deriv ?_
      simp
    have := hinv.mul hnum
    refine this.congr_deriv ?_
    simp [curveS]

/-- **Closure from stationarity** (BDFHP Sec. 4.2.2, eq. (25)): at an aligned configuration (`X₀_a† z_e = λ_e ξ_ab`
at the source ends, `X₀_b† z_e = μ_e J ξ_ba` at the target ends, unit boundary spinors, overlap products off the
cut), if the vertex action is stationary along every curve `X_a Y(t)` with `Y 0 = 1`, then at every node `a` the
normals close: `Σ_e n_e n̂_e = 0`, summing the spin vectors of the ends at `a`. -/
theorem closure_of_stationary {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ}
    (hj : ∀ e, j e = (n e : ℝ) / 2) {g : BdryData} {X₀ : Fin 5 → SL2C} {z₀ : Fin 10 → Spinor}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1) (lam mu : Fin 10 → ℂ)
    (hlam : ∀ e, lam e ≠ 0) (hmu : ∀ e, mu e ≠ 0)
    (hsrc : ∀ e, spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = lam e • firstCol (g e 0))
    (htgt : ∀ e, spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e) = mu e • jMap (firstCol (g e 1)))
    (hslit : ∀ e, inner ℂ (spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e)) (firstCol (g e 0)) *
      inner ℂ (jMap (firstCol (g e 1))) (spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z₀ e)) ∈
        Complex.slitPlane)
    (hstat : ∀ (a : Fin 5) (c : Fin 3 → ℂ) (Y : ℝ → SL2C), Y 0 = 1 →
      (∀ i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
        (((Y 0 : Matrix (Fin 2) (Fin 2) ℂ) * genMat c) i k) 0) →
      HasDerivAt (fun t => lorAction j p g (Function.update X₀ a (X₀ a * Y t)) z₀) 0 0)
    (a : Fin 5) (i : Fin 3) :
    ∑ e, ((if edgeSrc e = a then (n e : ℝ) * spinVec (firstCol (g e 0)) i else 0) +
      (if edgeTgt e = a then (n e : ℝ) * spinVec (firstCol (g e 1)) i else 0)) = 0 := by
  set c : Fin 3 → ℂ := fun m => if m = i then Complex.I else 0 with hc
  obtain ⟨Y, hY0, hY⟩ := exists_sl2_curve c
  have h1 := hasDerivAt_lorAction_aligned (p := p) hj hξ hξ' lam mu hlam hmu hsrc htgt hslit a c Y hY0 hY
  have h2 := hstat a c Y hY0 hY
  have h3 := h1.unique h2
  have key : ∀ (e : Fin 10) (ξ : Spinor), logDeriv (n e) (p e) c ξ =
      Complex.I * ((((n e : ℝ) / 2 * spinVec ξ i : ℝ)) : ℂ) := by
    intro e ξ
    have him : ∀ x : Fin 3, (c x).im = if x = i then 1 else 0 := fun x => by
      simp only [hc]; split_ifs <;> simp
    have hre : ∀ x : Fin 3, (c x).re = 0 := fun x => by
      simp only [hc]; split_ifs <;> simp
    rw [logDeriv_eq]
    simp only [him, hre, zero_mul, Finset.sum_const_zero]
    simp [Finset.sum_ite_eq']
  have hsum : ∑ e, ((if edgeSrc e = a then logDeriv (n e) (p e) c (firstCol (g e 0)) else 0) +
      (if edgeTgt e = a then logDeriv (n e) (p e) c (firstCol (g e 1)) else 0)) =
      Complex.I * (((1 / 2 * ∑ e, ((if edgeSrc e = a then (n e : ℝ) * spinVec (firstCol (g e 0)) i else 0) +
        (if edgeTgt e = a then (n e : ℝ) * spinVec (firstCol (g e 1)) i else 0)) : ℝ)) : ℂ) := by
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [key]
    split_ifs <;> push_cast <;> ring
  rw [hsum] at h3
  have h4 := (mul_eq_zero.mp h3).resolve_left Complex.I_ne_zero
  have h5 : (1 / 2 * ∑ e, ((if edgeSrc e = a then (n e : ℝ) * spinVec (firstCol (g e 0)) i else 0) +
        (if edgeTgt e = a then (n e : ℝ) * spinVec (firstCol (g e 1)) i else 0)) : ℝ) = 0 := by
    exact_mod_cast h4
  linarith

/-- **`Re S = 0` forces the alignment of every edge** (BDFHP Sec. 4.2.1, eqs. (18), (19)): for positive spin
parameters, unit boundary spinors and nonvanishing overlaps, if the real part of the vertex action is `0` (its
maximum), then on every edge `Z_ab = λ ξ_ab` and `Z_ba = μ J ξ_ba` with `λ μ ≠ 0`. -/
theorem aligned_of_re_lorAction_eq_zero {j p : Fin 10 → ℝ} (hj : ∀ e, 0 < j e) {g : BdryData}
    {X : Fin 5 → SL2C} {z : Fin 10 → Spinor}
    (hZ : ∀ e, spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (hZ' : ∀ e, spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (h1 : ∀ e, inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0)) ≠ 0)
    (h2 : ∀ e, inner ℂ (jMap (firstCol (g e 1)))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) ≠ 0)
    (hRe : (lorAction j p g X z).re = 0) :
    ∀ e, ∃ lam mu : ℂ, lam ≠ 0 ∧ mu ≠ 0 ∧
      spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) = lam • firstCol (g e 0) ∧
      spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) = mu • jMap (firstCol (g e 1)) := by
  have hle : ∀ e, (triAction (j e) (p e)
      (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 1))).re ≤ 0 := fun e =>
    re_triAction_le_zero (hj e).le (hZ e) (hZ' e) (hξ e) (hξ' e) (h1 e) (h2 e)
  have hsum : ∑ e, (triAction (j e) (p e)
      (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 1))).re = 0 := by
    rw [← Complex.re_sum]; exact hRe
  have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun e _ => hle e)).mp hsum
  intro e
  have h0 := hz e (Finset.mem_univ e)
  have hn := norm_exp_triAction (k := j e) (p := p e) (hZ e) (hZ' e) (h1 e) (h2 e)
  rw [Complex.norm_exp, h0, Real.exp_zero] at hn
  have hw := (triWeight_eq_one_iff (hj e) (hZ e) (hZ' e) (hξ e) (hξ' e)).mp hn.symm
  obtain ⟨⟨r, hr, hrξ⟩, ⟨s, hs, hsξ⟩⟩ := hw
  refine ⟨r⁻¹, s, inv_ne_zero hr, hs, ?_, hsξ⟩
  rw [hrξ, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- **A critical configuration has closure at every node** (BDFHP Sec. 4.2, eqs. (18)–(20) and (25)): for positive
spin parameters (`j e = n e / 2`), unit boundary spinors, nonvanishing overlaps whose products are off the cut, a
configuration `(X, z)` with `Re S = 0` at which the vertex action is stationary along every curve `X_a Y(t)`
(`Y 0 = 1`) has `Σ_e n_e n̂_e = 0` at every node, where `n̂_e` is the spin vector of the boundary spinor of the
end of `e` at the node. -/
theorem critical_configuration_closure {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ}
    (hj : ∀ e, j e = (n e : ℝ) / 2) (hjpos : ∀ e, 0 < j e) {g : BdryData} {X : Fin 5 → SL2C}
    {z : Fin 10 → Spinor}
    (hZ : ∀ e, spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (hZ' : ∀ e, spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (h1 : ∀ e, inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0)) ≠ 0)
    (h2 : ∀ e, inner ℂ (jMap (firstCol (g e 1)))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) ≠ 0)
    (hslit : ∀ e, inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0)) *
      inner ℂ (jMap (firstCol (g e 1))) (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) ∈
        Complex.slitPlane)
    (hRe : (lorAction j p g X z).re = 0)
    (hstat : ∀ (a : Fin 5) (c : Fin 3 → ℂ) (Y : ℝ → SL2C), Y 0 = 1 →
      (∀ i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
        (((Y 0 : Matrix (Fin 2) (Fin 2) ℂ) * genMat c) i k) 0) →
      HasDerivAt (fun t => lorAction j p g (Function.update X a (X a * Y t)) z) 0 0)
    (a : Fin 5) (i : Fin 3) :
    ∑ e, ((if edgeSrc e = a then (n e : ℝ) * spinVec (firstCol (g e 0)) i else 0) +
      (if edgeTgt e = a then (n e : ℝ) * spinVec (firstCol (g e 1)) i else 0)) = 0 := by
  have hal := aligned_of_re_lorAction_eq_zero hjpos hZ hZ' hξ hξ' h1 h2 hRe
  choose lam mu hlam hmu hsrc htgt using hal
  exact closure_of_stationary hj hξ hξ' lam mu hlam hmu hsrc htgt hslit hstat a i

/-- **No critical configuration without closure** (the contrapositive): if at some node the normals do not close,
no configuration satisfying the hypotheses of `critical_configuration_closure` has `Re S = 0` and is stationary
along the curves `X_a Y(t)`. -/
theorem no_critical_without_closure {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ}
    (hj : ∀ e, j e = (n e : ℝ) / 2) (hjpos : ∀ e, 0 < j e) {g : BdryData}
    (hnc : ∃ (a : Fin 5) (i : Fin 3), ∑ e, ((if edgeSrc e = a then (n e : ℝ) * spinVec (firstCol (g e 0)) i else 0) +
      (if edgeTgt e = a then (n e : ℝ) * spinVec (firstCol (g e 1)) i else 0)) ≠ 0)
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    {X : Fin 5 → SL2C} {z : Fin 10 → Spinor}
    (hZ : ∀ e, spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (hZ' : ∀ e, spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (h1 : ∀ e, inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0)) ≠ 0)
    (h2 : ∀ e, inner ℂ (jMap (firstCol (g e 1)))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) ≠ 0)
    (hslit : ∀ e, inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0)) *
      inner ℂ (jMap (firstCol (g e 1))) (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) ∈
        Complex.slitPlane) :
    ¬ ((lorAction j p g X z).re = 0 ∧ ∀ (a : Fin 5) (c : Fin 3 → ℂ) (Y : ℝ → SL2C), Y 0 = 1 →
      (∀ i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
        (((Y 0 : Matrix (Fin 2) (Fin 2) ℂ) * genMat c) i k) 0) →
      HasDerivAt (fun t => lorAction j p g (Function.update X a (X a * Y t)) z) 0 0) := by
  rintro ⟨hRe, hstat⟩
  obtain ⟨a, i, hne⟩ := hnc
  exact hne (critical_configuration_closure hj hjpos hZ hZ' hξ hξ' h1 h2 hslit hRe hstat a i)

end Lightlike.Asymptotics.Lorentzian

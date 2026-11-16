import Lightlike.Asymptotics.Lorentzian.TriActionDeriv
import Lightlike.Asymptotics.Lorentzian.CriticalSpinors
import Lightlike.Asymptotics.Lorentzian.ZStationary

/-!
# Stationarity of the vertex action along chart curves at a critical configuration

`hasDerivAt_lorAction_critical`: at a configuration satisfying the z-eliminated critical equations
(`IsLorCritical`) with the critical spinors `critZ`, the derivative of `lorAction` along any curve
`(X(t), z(t))` through it vanishes, when the closure of the normals holds at every node and the
product of the overlaps is off the cut of the logarithm on every edge. The curve in `SL(2,ℂ)` is
given by the entrywise derivative `X₀ · genMat c` of each `X_a`, which is the tangent space at `X₀`.

Not here: a chart of `SL(2,ℂ)^5 × (ℂ²)^10` (the construction of the curves; `Matrix` has no
`det exp = exp tr` in Mathlib), and the identification of this line derivative with the Fréchet
derivative of the pulled-back action `lorChartAction`. Support lemmas: the coordinates of a spinor
curve (`hasDerivAt_spinor_iff`), the product rule `hasDerivAt_spinAct`, and the matrix
`genMat c` of `gen c`.
-/

open Complex
open scoped ComplexConjugate Matrix

open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- A curve of spinors is differentiable exactly when its two coordinates are. -/
theorem hasDerivAt_spinor_iff {v : ℝ → Spinor} {v' : Spinor} {t : ℝ} :
    HasDerivAt v v' t ↔ ∀ i, HasDerivAt (fun s => v s i) (v' i) t := by
  constructor
  · intro h i
    have hl : HasFDerivAt (fun x : Spinor => x i) ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)
        (v t) := ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).hasFDerivAt
    exact hl.comp_hasDerivAt t h
  · intro h
    have hp : HasDerivAt (fun s => (WithLp.ofLp (v s) : Fin 2 → ℂ)) (WithLp.ofLp v') t :=
      hasDerivAt_pi.mpr h
    let L : (Fin 2 → ℂ) →L[ℝ] Spinor :=
      ((EuclideanSpace.equiv (Fin 2) ℂ).symm.toContinuousLinearMap).restrictScalars ℝ
    have hl : HasFDerivAt (fun x : Fin 2 → ℂ => L x) L (WithLp.ofLp (v t)) := L.hasFDerivAt
    exact hl.comp_hasDerivAt t hp

/-- **Product rule for the action of a matrix curve on a spinor curve**, with the matrix derivative
given entrywise (the matrices carry no global norm). -/
theorem hasDerivAt_spinAct {M : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {M' : Matrix (Fin 2) (Fin 2) ℂ}
    {v : ℝ → Spinor} {v' : Spinor} (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0)
    (hv : HasDerivAt v v' 0) :
    HasDerivAt (fun t => spinAct (M t) (v t)) (spinAct M' (v 0) + spinAct (M 0) v') 0 := by
  have hv' := hasDerivAt_spinor_iff.mp hv
  rw [hasDerivAt_spinor_iff]
  intro i
  fin_cases i
  · have := ((hM 0 0).mul (hv' 0)).add ((hM 0 1).mul (hv' 1))
    exact this.congr_deriv (by simp; ring)
  · have := ((hM 1 0).mul (hv' 0)).add ((hM 1 1).mul (hv' 1))
    exact this.congr_deriv (by simp; ring)

/-- The entries of the conjugate transpose of a differentiable matrix curve. -/
theorem hasDerivAt_conjTranspose_entry {M : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    {M' : Matrix (Fin 2) (Fin 2) ℂ} (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0)
    (i j : Fin 2) :
    HasDerivAt (fun t => (M t)ᴴ i j) (M'ᴴ i j) 0 := by
  have := (hM j i).star
  simpa [Matrix.conjTranspose_apply] using this

/-- The matrix `½ Σ c_i σ_i` of `gen c` (`sl₂(ℂ)`, traceless). -/
noncomputable def genMat (c : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![c 2 / 2, (c 0 - Complex.I * c 1) / 2; (c 0 + Complex.I * c 1) / 2, -(c 2) / 2]

/-- `genMat c` acts as `gen c`. -/
theorem spinAct_genMat (c : Fin 3 → ℂ) (ξ : Spinor) : spinAct (genMat c) ξ = gen c ξ := by
  ext i; fin_cases i <;> simp [genMat, gen_apply_zero, gen_apply_one]

/-- `genMat c` is traceless. -/
theorem trace_genMat (c : Fin 3 → ℂ) : (genMat c).trace = 0 := by
  simp [genMat, Matrix.trace_fin_two]; ring

/-- The conjugate transpose of `genMat c` is `genMat (conj c)`. -/
theorem genMat_conjTranspose (c : Fin 3 → ℂ) : (genMat c)ᴴ = genMat (fun i => conj (c i)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [genMat, Matrix.conjTranspose_apply] <;> ring

/-- The adjoint of `gen c` is the action of `(genMat c)ᴴ`. -/
theorem spinAct_genMat_conjTranspose (c : Fin 3 → ℂ) (ξ : Spinor) :
    spinAct (genMat c)ᴴ ξ = LinearMap.adjoint (gen c) ξ := by
  rw [genMat_conjTranspose, spinAct_genMat, adjoint_gen]

/-- **Stationarity of the vertex action along chart curves at the critical point** (BDFHP Sec. 4.2.2,
the gradient of the action): let `(X₀, z₀)` be a critical configuration (`IsLorCritical`, with the
critical spinors `critZ`), `j e = n e / 2`, and let `(X(t), z(t))` be a curve through it with
`X_a(t)` of derivative `X₀_a · (½ Σ c_i σ_i)` (the tangent space of `SL(2,ℂ)` at `X₀_a`, entrywise)
and `z_e(t)` differentiable. If the product of the overlaps is off the cut of the logarithm on every
edge, and the closure `Σ n_e n̂_e = 0` and `Σ p_e n̂_e = 0` holds at every node in the form
`hcl`, then `t ↦ lorAction j p g (X t) (z t)` has derivative `0` at `0`. -/
theorem hasDerivAt_lorAction_critical {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ}
    (hj : ∀ e, j e = (n e : ℝ) / 2) {g : BdryData} {X₀ : Fin 5 → SL2C}
    (hcrit : IsLorCritical g X₀) (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1)
    (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (hslit : ∀ e, inner ℂ (spinAct (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e))
        (firstCol (g e 0)) *
      inner ℂ (jMap (firstCol (g e 1)))
        (spinAct (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X₀ e)) ∈
        Complex.slitPlane)
    (ca : Fin 5 → Fin 3 → ℂ) (δz : Fin 10 → Spinor)
    (Xc : ℝ → Fin 5 → SL2C) (zc : ℝ → Fin 10 → Spinor)
    (hX0 : Xc 0 = X₀) (hz0 : zc 0 = critZ g X₀)
    (hX : ∀ a i j, HasDerivAt (fun t => (Xc t a : Matrix (Fin 2) (Fin 2) ℂ) i j)
      ((X₀ a * genMat (ca a) : Matrix (Fin 2) (Fin 2) ℂ) i j) 0)
    (hz : ∀ e, HasDerivAt (fun t => zc t e) (δz e) 0)
    (hcl : ∀ (a : Fin 5) (c : Fin 3 → ℂ), ∑ e, ((if edgeSrc e = a then
        logDeriv (n e) (p e) c (firstCol (g e 0)) else 0) +
        (if edgeTgt e = a then logDeriv (n e) (p e) c (firstCol (g e 1)) else 0)) = 0) :
    HasDerivAt (fun t => lorAction j p g (Xc t) (zc t)) 0 0 := by
  have key : ∀ e : Fin 10, HasDerivAt (fun t : ℝ => triAction (j e) (p e)
      (spinAct (Xc t (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (zc t e)) (firstCol (g e 0))
      (spinAct (Xc t (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (zc t e)) (firstCol (g e 1)))
      (logDeriv (n e) (p e) (ca (edgeSrc e)) (firstCol (g e 0)) +
        logDeriv (n e) (p e) (ca (edgeTgt e)) (firstCol (g e 1))) 0 := by
    intro e
    obtain ⟨r, hr, c, hc, h20, h21⟩ := hcrit e
    set M : Matrix (Fin 2) (Fin 2) ℂ := (X₀ (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) with hM
    set N : Matrix (Fin 2) (Fin 2) ℂ := (X₀ (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) with hN
    set ξ := firstCol (g e 0) with hξdef
    set ξ' := firstCol (g e 1) with hξ'def
    have hsrc := critZ_src g X₀ e
    have htgt := critZ_tgt g X₀ e r c h20
    have hZc : HasDerivAt (fun t : ℝ => spinAct (Xc t (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (zc t e))
        (spinAct (M * genMat (ca (edgeSrc e)))ᴴ (zc 0 e) + spinAct (Xc 0 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (δz e)) 0 :=
      hasDerivAt_spinAct (fun i j => hasDerivAt_conjTranspose_entry (hX (edgeSrc e)) i j) (hz e)
    have hZ'c : HasDerivAt (fun t : ℝ => spinAct (Xc t (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (zc t e))
        (spinAct (N * genMat (ca (edgeTgt e)))ᴴ (zc 0 e) + spinAct (Xc 0 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (δz e)) 0 :=
      hasDerivAt_spinAct (fun i j => hasDerivAt_conjTranspose_entry (hX (edgeTgt e)) i j) (hz e)
    have hz0e : zc 0 e = critZ g X₀ e := by rw [hz0]
    rw [hz0e, hX0] at hZc hZ'c
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
    have hξ0 : ξ ≠ 0 := by intro h; have := hξ e; rw [← hξdef, h] at this; simp at this
    have hξ'0 : ξ' ≠ 0 := by intro h; have := hξ' e; rw [← hξ'def, h] at this; simp at this
    have hjξ' : jMap ξ' ≠ 0 := jMap_ne_zero hξ'0
    have hW : spinAct (M * genMat (ca (edgeSrc e)))ᴴ (critZ g X₀ e) =
        LinearMap.adjoint (gen (ca (edgeSrc e))) ξ := by
      rw [Matrix.conjTranspose_mul, spinAct_mul, hsrc, spinAct_genMat_conjTranspose]
    have hW' : spinAct (N * genMat (ca (edgeTgt e)))ᴴ (critZ g X₀ e) =
        LinearMap.adjoint (gen (ca (edgeTgt e))) (((r : ℂ) * c) • jMap ξ') := by
      rw [Matrix.conjTranspose_mul, spinAct_mul, htgt, spinAct_genMat_conjTranspose]
    rw [hW] at hZc
    rw [hW'] at hZ'c
    have hin : inner ℂ ξ ξ = 1 := by rw [inner_self_eq_norm_sq_to_K, hξ e]; simp
    have hjin : inner ℂ (jMap ξ') (jMap ξ') = 1 := by
      rw [inner_self_eq_norm_sq_to_K, norm_jMap, hξ' e]; simp
    have h2 : inner ℂ (jMap ξ') (((r : ℂ) * c) • jMap ξ') = (r : ℂ) * c := by
      rw [inner_smul_right, hjin, mul_one]
    have hP : inner ℂ ξ ξ * inner ℂ (jMap ξ') (((r : ℂ) * c) • jMap ξ') ∈ Complex.slitPlane := by
      have := hslit e
      rw [hsrc, htgt] at this
      exact this
    have hcur := hasDerivAt_triAction_curve (n e) (p e) (Z := ξ) (ξ := ξ) (Z' := ((r : ℂ) * c) • jMap ξ')
      (ξ' := ξ') _ _ hZc hZ'c (by rw [hX0, hz0e]; exact hsrc) (by rw [hX0, hz0e]; exact htgt) hξ0
      (smul_ne_zero (mul_ne_zero hr0 hc0) hjξ') (by rw [hin]; exact one_ne_zero)
      (by rw [h2]; exact mul_ne_zero hr0 hc0) hP
    rw [hj e]
    refine hcur.congr_deriv ?_
    have hev := edge_variation (n e) (p e) r c (ca (edgeSrc e)) (ca (edgeTgt e)) M N ξ ξ' (δz e) hr hc
      (hξ e) (hξ' e) h21
    exact hev
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun e _ => key e)
  have h0 := sum_logDeriv_nodes (E := Fin 10) (V := Fin 5) edgeSrc edgeTgt n p
    (fun e => firstCol (g e 0)) (fun e => firstCol (g e 1)) ca hcl
  rw [h0] at hs
  exact hs

end Lightlike.Asymptotics.Lorentzian

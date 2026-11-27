import Mathlib
import Lightlike.Dirac.SphereTransition
import Lightlike.Dirac.ConformalDirac
import Lightlike.Dirac.ModeSphere

/-!
# From a `V`-valued eigenspinor of the sphere to the complex pair of the mode equations

For a `Cl₂`-module `V` of real dimension `4` (the spinor module `ℂ² ≅ ℍ`) and a nonzero vector `v`, the
four vectors `v, Jv, γ₀v, γ₀Jv` form a basis (quaternion norm identity, `phiMap_injective`), so
`(c₁, c₂) ↦ Lv c₁ + γ₀ Lv c₂` is a continuous linear equivalence `ℂ × ℂ ≃L[ℝ] V` (`phiEquiv`).

An eigenspinor `f` of the Dirac operator of the unit 2-sphere in the stereographic chart (`D f = λ f`)
corresponds to `g = h^{-1/2} f`, which solves the flat equation `h D₀ g = λ g`
(`diracF_stereo_conformal_eigen_iff`); its coordinates `(c₁, c₂) = Φ⁻¹ g` give the pair
`(g₁, g₂) = (c₂, -i c₁)` solving the system of `chart_eigenspinor_quantized` (`eigen_pair`).
A bound `‖f‖ ≤ B` gives the decay `‖g_i x‖ ≤ C/‖x‖` of that system (`pair_decay`).
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The real-linear map `(c₁, c₂) ↦ Lv c₁ + γ₀ Lv c₂` from `ℂ × ℂ` to the spinor module. -/
noncomputable def phiMap (ρ : CliffordRep 2 V) (v : V) : ℂ × ℂ →L[ℝ] V :=
  (Lv ρ v).coprod ((gam ρ 0).comp (Lv ρ v))

lemma phiMap_apply (ρ : CliffordRep 2 V) (v : V) (c : ℂ × ℂ) :
    phiMap ρ v c = Lv ρ v c.1 + gam ρ 0 (Lv ρ v c.2) := by
  simp [phiMap]

/-- **Independence of `v, Jv, γ₀v, γ₀Jv`.** The quaternion norm identity `q q̄ = |q|²` for
`q = a + b J + a' γ₀ + b' γ₀J` shows that `phiMap` is injective for `v ≠ 0`. -/
lemma phiMap_injective (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0) :
    Function.Injective (phiMap ρ v) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨c₁, c₂⟩ h
  rw [phiMap_apply] at h
  dsimp only at h
  rw [Lv_apply, Lv_apply] at h
  have key : (c₁.re ^ 2 + c₁.im ^ 2 + c₂.re ^ 2 + c₂.im ^ 2) • v = 0 := by
    have := congrArg (fun x => c₁.re • x - c₁.im • Jop ρ x - c₂.re • gam ρ 0 x -
      c₂.im • gam ρ 0 (Jop ρ x)) h
    simp only [map_add, map_smul, map_zero, smul_zero, smul_add, smul_sub, map_sub, map_neg,
      Jop_gam0, Jop_sq, gam_sq ρ 0, smul_neg, neg_neg] at this
    linear_combination (norm := module) this
  have h0 := (smul_eq_zero.mp key).resolve_right hv
  have ha : c₁.re = 0 := by nlinarith [sq_nonneg c₁.re, sq_nonneg c₁.im, sq_nonneg c₂.re, sq_nonneg c₂.im]
  have hb : c₁.im = 0 := by nlinarith [sq_nonneg c₁.re, sq_nonneg c₁.im, sq_nonneg c₂.re, sq_nonneg c₂.im]
  have hc : c₂.re = 0 := by nlinarith [sq_nonneg c₁.re, sq_nonneg c₁.im, sq_nonneg c₂.re, sq_nonneg c₂.im]
  have hd : c₂.im = 0 := by nlinarith [sq_nonneg c₁.re, sq_nonneg c₁.im, sq_nonneg c₂.re, sq_nonneg c₂.im]
  exact Prod.ext (Complex.ext (by simpa using ha) (by simpa using hb))
    (Complex.ext (by simpa using hc) (by simpa using hd))

/-- The coordinates of a spinor in the basis `v, Jv, γ₀v, γ₀Jv`: a continuous linear equivalence
`ℂ × ℂ ≃L[ℝ] V` when `dim V = 4`. -/
noncomputable def phiEquiv [FiniteDimensional ℝ V] (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0)
    (hV : Module.finrank ℝ V = 4) : (ℂ × ℂ) ≃L[ℝ] V :=
  (LinearMap.linearEquivOfInjective (phiMap ρ v : ℂ × ℂ →ₗ[ℝ] V) (phiMap_injective ρ hv)
    (by rw [hV, Module.finrank_prod, Complex.finrank_real_complex])).toContinuousLinearEquiv

lemma phiEquiv_apply [FiniteDimensional ℝ V] (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0)
    (hV : Module.finrank ℝ V = 4) (c : ℂ × ℂ) : phiEquiv ρ hv hV c = phiMap ρ v c := rfl

local notation "hE" => ((((2 : ℕ) : ℝ) - 1) / 2)

/-- The rescaled spinor `g = h^{-1/2} f` (the flat form of a sphere spinor). -/
noncomputable def rescale (f : E 2 → V) : E 2 → V := fun y => (stereoH y ^ hE)⁻¹ • f y

lemma stereoH_rpow_pos (y : E 2) : 0 < stereoH y ^ hE := Real.rpow_pos_of_pos (stereoH_pos y) _

lemma contDiff_stereoH_rpow : ContDiff ℝ 1 (fun y : E 2 => stereoH y ^ hE) :=
  ((contDiff_stereoH (n := 2)).of_le (by norm_num)).rpow_const_of_ne (fun x => (stereoH_pos x).ne')

lemma rescale_contDiff {f : E 2 → V} (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (rescale f) :=
  (contDiff_stereoH_rpow.inv (fun x => (stereoH_rpow_pos x).ne')).smul hf

lemma rescale_eq (f : E 2 → V) : f = fun y => stereoH y ^ hE • rescale f y := by
  funext y
  unfold rescale
  rw [smul_inv_smul₀ (stereoH_rpow_pos y).ne']

/-- The flat form of the eigenvalue equation: `h D₀ g = λ g` for `g = h^{-1/2} f`. -/
lemma rescale_flat {f : E 2 → V} (hf : ContDiff ℝ 1 f) {lam : ℝ} (ρ : CliffordRep 2 V)
    (heig : ∀ x, diracF ρ stereoF stereoOmega f x = lam • f x) (x : E 2) :
    stereoH x • dirac ρ (rescale f) x = lam • rescale f x := by
  have hg := rescale_contDiff hf
  refine (diracF_stereo_conformal_eigen_iff ρ x ((hg.differentiable (by norm_num)) x) lam).1 ?_
  have h1 := heig x
  have h2 := rescale_eq f
  rw [h2] at h1
  simpa using h1

/-- **The complex pair of an eigenspinor.**  For `D f = λ f`, the coordinates `c = Φ⁻¹ (h^{-1/2} f)` give the
`C¹` pair `(g₁, g₂) = (c₂, -i c₁)` of the mode equations of `chart_eigenspinor_quantized`. -/
theorem eigen_pair [FiniteDimensional ℝ V] (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0)
    (hV : Module.finrank ℝ V = 4) {lam : ℝ} {f : E 2 → V} (hf : ContDiff ℝ 1 f)
    (heig : ∀ x, diracF ρ stereoF stereoOmega f x = lam • f x) :
    ContDiff ℝ 1 (fun x => ((phiEquiv ρ hv hV).symm (rescale f x)).2) ∧
    ContDiff ℝ 1 (fun x => -(Complex.I * ((phiEquiv ρ hv hV).symm (rescale f x)).1)) ∧
    (∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ (fun x => ((phiEquiv ρ hv hV).symm (rescale f x)).2) x (e (0 : Fin 2)) +
        Complex.I * fderiv ℝ (fun x => ((phiEquiv ρ hv hV).symm (rescale f x)).2) x (e (1 : Fin 2))) =
      2 * (lam : ℂ) * (-(Complex.I * ((phiEquiv ρ hv hV).symm (rescale f x)).1))) ∧
    (∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ (fun x => -(Complex.I * ((phiEquiv ρ hv hV).symm (rescale f x)).1)) x (e (0 : Fin 2)) -
        Complex.I * fderiv ℝ (fun x => -(Complex.I * ((phiEquiv ρ hv hV).symm (rescale f x)).1)) x
          (e (1 : Fin 2))) =
      2 * (lam : ℂ) * ((phiEquiv ρ hv hV).symm (rescale f x)).2) := by
  set Φ := phiEquiv ρ hv hV with hΦ
  set c : E 2 → ℂ × ℂ := fun x => Φ.symm (rescale f x) with hc
  have hg := rescale_contDiff hf
  have hcd : ContDiff ℝ 1 c := Φ.symm.contDiff.comp hg
  have hc1 : ContDiff ℝ 1 (fun x => (c x).1) := contDiff_fst.comp hcd
  have hc2 : ContDiff ℝ 1 (fun x => (c x).2) := contDiff_snd.comp hcd
  -- the pointwise equations
  have key : ∀ x : E 2,
      -((stereoH x : ℂ) * (fderiv ℝ (fun x => (c x).2) x (e 0) + Complex.I * fderiv ℝ (fun x => (c x).2) x (e 1))) =
        (lam : ℂ) * (c x).1 ∧
      (stereoH x : ℂ) * (fderiv ℝ (fun x => (c x).1) x (e 0) - Complex.I * fderiv ℝ (fun x => (c x).1) x (e 1)) =
        (lam : ℂ) * (c x).2 := by
    intro x
    have hflat := rescale_flat hf ρ heig x
    have hgc : rescale f = angSpinor ρ v (fun x => (c x).1) (fun x => (c x).2) := by
      funext y
      have : Φ (c y) = rescale f y := Φ.apply_symm_apply _
      rw [← this, hΦ, phiEquiv_apply, phiMap_apply]
      rfl
    rw [hgc] at hflat
    rw [dirac_angular ρ v ((hc1.differentiable (by norm_num) x).hasFDerivAt)
      ((hc2.differentiable (by norm_num) x).hasFDerivAt)] at hflat
    have hLv : ∀ (r : ℝ) (z : ℂ), Lv ρ v ((r : ℂ) * z) = r • Lv ρ v z := fun r z => by
      rw [← Complex.real_smul, map_smul]
    have heq : phiMap ρ v (-((stereoH x : ℂ) * (fderiv ℝ (fun x => (c x).2) x (e 0) +
          Complex.I * fderiv ℝ (fun x => (c x).2) x (e 1))),
        (stereoH x : ℂ) * (fderiv ℝ (fun x => (c x).1) x (e 0) - Complex.I * fderiv ℝ (fun x => (c x).1) x (e 1))) =
        phiMap ρ v ((lam : ℂ) * (c x).1, (lam : ℂ) * (c x).2) := by
      rw [phiMap_apply, phiMap_apply]
      dsimp only
      simp only [map_neg, hLv, map_smul]
      simp only [angSpinor, Pi.smul_apply, hLv, map_smul] at hflat
      linear_combination (norm := module) hflat
    have hinj := phiMap_injective ρ hv heq
    exact ⟨(Prod.ext_iff.mp hinj).1, (Prod.ext_iff.mp hinj).2⟩
  refine ⟨hc2, (contDiff_const.mul hc1).neg, ?_, ?_⟩
  · intro x
    have hh : (1 + ((‖x‖ ^ 2 : ℝ) : ℂ)) = 2 * (stereoH x : ℂ) := by unfold stereoH; push_cast; ring
    rw [hh]
    linear_combination (-2 * Complex.I) * (key x).1
  · intro x
    have hh : (1 + ((‖x‖ ^ 2 : ℝ) : ℂ)) = 2 * (stereoH x : ℂ) := by unfold stereoH; push_cast; ring
    have hd : ∀ i : Fin 2, fderiv ℝ (fun x => -(Complex.I * (c x).1)) x (e i) =
        -(Complex.I * fderiv ℝ (fun x => (c x).1) x (e i)) := by
      intro i
      have h1 := ((hc1.differentiable (by norm_num) x).hasFDerivAt.const_mul Complex.I).neg
      have h2 : fderiv ℝ (fun x => -(Complex.I * (c x).1)) x =
          -(Complex.I • fderiv ℝ (fun x => (c x).1) x) := h1.fderiv
      rw [h2]
      simp
    rw [hh, hd 0, hd 1]
    linear_combination 2 * (key x).2 +
      (-(2 * (stereoH x : ℂ) * (fderiv ℝ (fun x => (c x).1) x (e 0) -
        Complex.I * fderiv ℝ (fun x => (c x).1) x (e 1)))) * Complex.I_sq

/-- **Decay of the pair.** A bound `‖f x‖ ≤ B` gives `‖c_i x‖ ≤ C / ‖x‖` for `‖x‖ ≥ 1`. -/
lemma pair_decay [FiniteDimensional ℝ V] (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0)
    (hV : Module.finrank ℝ V = 4) {f : E 2 → V} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    ∃ C : ℝ, ∀ x : E 2, 1 ≤ ‖x‖ →
      ‖((phiEquiv ρ hv hV).symm (rescale f x)).1‖ ≤ C / ‖x‖ ∧
      ‖((phiEquiv ρ hv hV).symm (rescale f x)).2‖ ≤ C / ‖x‖ := by
  refine ⟨‖(phiEquiv ρ hv hV).symm.toContinuousLinearMap‖ * B * Real.sqrt 2, fun x hx => ?_⟩
  have hx0 : 0 < ‖x‖ := by linarith
  have hs2 : 0 < Real.sqrt 2 := by positivity
  -- `h^{1/2} ≥ ‖x‖ / √2`
  have hh : ‖x‖ / Real.sqrt 2 ≤ stereoH x ^ hE := by
    have e1 : hE = (1 / 2 : ℝ) := by norm_num
    rw [e1, ← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    unfold stereoH
    nlinarith [sq_nonneg ‖x‖]
  have hinv : (stereoH x ^ hE)⁻¹ ≤ Real.sqrt 2 / ‖x‖ := by
    have := inv_anti₀ (by positivity) hh
    simpa [inv_div] using this
  have hg : ‖rescale f x‖ ≤ B * (Real.sqrt 2 / ‖x‖) := by
    unfold rescale
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (stereoH_rpow_pos x).le]
    calc (stereoH x ^ hE)⁻¹ * ‖f x‖ ≤ (Real.sqrt 2 / ‖x‖) * B :=
          mul_le_mul hinv (hB x) (norm_nonneg _) (by positivity)
      _ = B * (Real.sqrt 2 / ‖x‖) := by ring
  have hc : ‖(phiEquiv ρ hv hV).symm (rescale f x)‖ ≤
      ‖(phiEquiv ρ hv hV).symm.toContinuousLinearMap‖ * ‖rescale f x‖ :=
    (phiEquiv ρ hv hV).symm.toContinuousLinearMap.le_opNorm _
  have hN : 0 ≤ ‖(phiEquiv ρ hv hV).symm.toContinuousLinearMap‖ := norm_nonneg _
  have hfin : ‖(phiEquiv ρ hv hV).symm (rescale f x)‖ ≤
      ‖(phiEquiv ρ hv hV).symm.toContinuousLinearMap‖ * B * Real.sqrt 2 / ‖x‖ := by
    calc _ ≤ _ := hc
      _ ≤ ‖(phiEquiv ρ hv hV).symm.toContinuousLinearMap‖ * (B * (Real.sqrt 2 / ‖x‖)) :=
          mul_le_mul_of_nonneg_left hg hN
      _ = _ := by ring
  exact ⟨(norm_fst_le _).trans hfin, (norm_snd_le _).trans hfin⟩

end Lightlike.Dirac

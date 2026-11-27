import Mathlib
import Lightlike.Dirac.SphereDirac
import Lightlike.Dirac.SpinorLichnerowicz
import Lightlike.Dirac.SphereSpectrum

/-!
# The Dirac spectrum on the spinor sections of the 2-sphere

The smooth sections of the spinor bundle of `sphereSpinStructure` (`Lightlike/Dirac/SphereSpin.lean`) and their
Dirac operator `SpinorSection.dirac` (`Lightlike/Dirac/SpinorBundle.lean`). This file relates the eigensections
`D σ = λ σ` to the chart eigenspinors of the two-chart spectrum theorem (`SphereEigenspace`,
`Lightlike/Dirac/SphereSpectrum.lean`) through the north chart (work in progress).

## This layer

* `northRep σ`: the representation of `σ` in the north frame, read in the north chart;
* `SpinorSection.eq_zero_of_north`: a smooth section vanishing on `S2 ∖ {N}` vanishes.
-/

open Bundle Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Dirac

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ρ : CliffordRep 2 V}

lemma stereoS_zero_pc : pc (stereoS 0) 2 = 1 := by
  rw [(pc_stereoS 0).2.2]; simp [nsq]

lemma stereoS_ne_north {y : Fin 2 → ℝ} (hy : y ≠ 0) : pc (stereoS y) 2 ≠ 1 := by
  rw [(pc_stereoS y).2.2]
  have hq : 0 < nsq y := by
    unfold nsq
    by_contra h
    push_neg at h
    have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact hy (funext fun i => by fin_cases i <;> simp [h0, h1])
  intro h
  rw [div_eq_one_iff_eq (by positivity)] at h
  linarith

lemma pc_stereoS_ne_south (y : Fin 2 → ℝ) : pc (stereoS y) 2 ≠ -1 := by
  rw [(pc_stereoS y).2.2]
  have hq := nsq_nonneg y
  intro h
  rw [div_eq_iff (by positivity)] at h
  linarith

/-- **A smooth spinor section vanishing away from the north pole vanishes.** -/
theorem SpinorSection.eq_zero_of_north (σ : SpinorSection sphereSpinStructure ρ)
    (h : ∀ p : S2, pc p 2 ≠ 1 → σ p = 0) : σ = 0 := by
  ext p
  by_cases hp : pc p 2 = 1
  · -- `p` is the north pole `stereoS 0`; read `σ` in the south frame along `stereoS`
    have hS : p = stereoS 0 := by
      have hs := pc_sq_sum p
      have h01 : pc p 0 = 0 ∧ pc p 1 = 0 := by
        constructor <;> nlinarith [sq_nonneg (pc p 0), sq_nonneg (pc p 1)]
      apply Subtype.ext
      ext i
      obtain ⟨h0, h1, h2⟩ := pc_stereoS 0
      fin_cases i
      · exact h01.1.trans (by rw [show (0 : Fin (2 + 1)) = 0 from rfl] at h0; simpa [nsq] using h0.symm)
      · exact h01.2.trans (by simpa [nsq] using h1.symm)
      · exact hp.trans (by simpa [nsq] using h2.symm)
    subst hS
    set g : (Fin 2 → ℝ) → V := fun y => σ.toField.rep false (stereoS y)
    have hdom : ∀ y, stereoS y ∈ sphereSpinStructure.dom false := fun y => pc_stereoS_ne_south y
    have hg : ContinuousAt g 0 :=
      ((σ.toField_isSmooth false (stereoS 0) (hdom 0)).continuousAt).comp
        (contMDiff_stereoS 0).continuousAt
    have hg0 : ∀ y, y ≠ 0 → g y = 0 := fun y hy => by
      show σ.toField.rep false (stereoS y) = 0
      rw [show σ.toField.rep false (stereoS y) = σ.rep false (stereoS y) from rfl,
        σ.rep_of_mem (hdom y), h _ (stereoS_ne_north hy)]
      erw [map_zero]
    have hlim : Tendsto g (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hg0 y hy).symm)
    have hg00 : g 0 = 0 := tendsto_nhds_unique (hg.tendsto.mono_left nhdsWithin_le_nhds) hlim
    apply SpinStructure.coordChange_injective (ρ := ρ) (hdom 0)
    simp only
    rw [show ((0 : SpinorSection sphereSpinStructure ρ) (stereoS 0)) = 0 from rfl]
    erw [map_zero, ← σ.rep_of_mem (hdom 0)]
    exact hg00
  · exact h p hp

/-! ## The north representation -/

lemma stereoN_mem_dom (y : Fin 2 → ℝ) : stereoN y ∈ sphereSpinStructure.dom true := pc_stereoN_ne y

lemma pc_ne_one_iff_dom {p : S2} : p ∈ sphereSpinStructure.dom true ↔ pc p 2 ≠ 1 := Iff.rfl

/-- The representation of `σ` in the north frame, read in the north chart (on `E 2`). -/
def northRep (σ : SpinorSection sphereSpinStructure ρ) (x : E 2) : V :=
  σ.toField.rep true (stereoN (modelEquiv2 x))

lemma rep_add (σ τ : SpinorSection sphereSpinStructure ρ) {i : Bool} {p : S2}
    (hp : p ∈ sphereSpinStructure.dom i) :
    (σ + τ).toField.rep i p = σ.toField.rep i p + τ.toField.rep i p := by
  change (σ + τ).rep i p = σ.rep i p + τ.rep i p
  rw [(σ + τ).rep_of_mem hp, σ.rep_of_mem hp, τ.rep_of_mem hp]
  erw [map_add]

lemma rep_smul (c : ℝ) (σ : SpinorSection sphereSpinStructure ρ) {i : Bool} {p : S2}
    (hp : p ∈ sphereSpinStructure.dom i) :
    (c • σ).toField.rep i p = c • σ.toField.rep i p := by
  change (c • σ).rep i p = c • σ.rep i p
  rw [(c • σ).rep_of_mem hp, σ.rep_of_mem hp]
  erw [map_smul]

/-- The north representation as a linear map. -/
def northMap : SpinorSection sphereSpinStructure ρ →ₗ[ℝ] (E 2 → V) where
  toFun := northRep
  map_add' σ τ := funext fun x => rep_add σ τ (stereoN_mem_dom _)
  map_smul' c σ := funext fun x => rep_smul c σ (stereoN_mem_dom _)

/-- A section is determined by its north representation. -/
theorem northMap_injective : Function.Injective (northMap (ρ := ρ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro σ hσ
  refine σ.eq_zero_of_north fun p hp => ?_
  have hx := congrFun hσ (modelEquiv2.symm (invN p))
  simp only [northMap, LinearMap.coe_mk, AddHom.coe_mk, northRep, ContinuousLinearEquiv.apply_symm_apply,
    stereoN_invN hp, Pi.zero_apply] at hx
  apply SpinStructure.coordChange_injective (ρ := ρ) (show p ∈ sphereSpinStructure.dom true from hp)
  simp only
  erw [map_zero, ← σ.rep_of_mem (show p ∈ sphereSpinStructure.dom true from hp)]
  exact hx

/-- **The eigen-equation from the chart.** If the north representation of a smooth section satisfies the chart
eigen-equation `diracF f = λ f`, then `D σ = λ σ`. -/
theorem dirac_eq_of_north (σ : SpinorSection sphereSpinStructure ρ) (lam : ℝ)
    (h : ∀ x, diracF ρ stereoF stereoOmega (northRep σ) x = lam • northRep σ x) :
    σ.dirac = lam • σ := by
  rw [← sub_eq_zero]
  refine (σ.dirac - lam • σ).eq_zero_of_north fun p hp => ?_
  have hd : p ∈ sphereSpinStructure.dom true := hp
  set x := modelEquiv2.symm (invN p)
  have hpx : stereoN (modelEquiv2 x) = p := by
    simp only [x, ContinuousLinearEquiv.apply_symm_apply]; exact stereoN_invN hp
  have hdiff : MDifferentiableAt I2 𝓘(ℝ, V) (σ.toField.rep true) (stereoN (modelEquiv2 x)) := by
    rw [hpx]; exact (σ.toField_isSmooth true p hd).mdifferentiableAt (by simp)
  have key := dirac_sphere_north ρ hdiff
  rw [show (σ.toField.rep true ∘ stereoN ∘ modelEquiv2) = northRep σ from rfl, h x] at key
  rw [hpx] at key
  -- the north representation of `D σ - λ σ` vanishes at `p`
  have h1 : (σ.dirac - lam • σ).toField.rep true p = 0 := by
    rw [sub_eq_add_neg, rep_add _ _ hd, ← neg_smul, rep_smul _ _ hd, σ.toField_dirac hd]
    change sphereSpinStructure.dirac ρ true (σ.toField.rep true) p + _ = 0
    rw [key, neg_smul, show northRep σ x = σ.toField.rep true p by
      simp only [northRep]; rw [hpx]]
    abel
  apply SpinStructure.coordChange_injective (ρ := ρ) hd
  simp only
  erw [map_zero, ← (σ.dirac - lam • σ).rep_of_mem hd]
  exact h1

lemma contDiff_northRep (σ : SpinorSection sphereSpinStructure ρ) : ContDiff ℝ ∞ (northRep σ) := by
  rw [← contMDiff_iff_contDiff]
  intro x
  have h1 := σ.toField_isSmooth true (stereoN (modelEquiv2 x)) (stereoN_mem_dom _)
  have h2 : ContMDiffAt 𝓘(ℝ, E 2) I2 ∞ (fun x : E 2 => stereoN (modelEquiv2 x)) x :=
    (contMDiff_stereoN (modelEquiv2 x)).comp x
      ((modelEquiv2 : E 2 →L[ℝ] Fin 2 → ℝ).contDiff.contMDiff.contMDiffAt)
  exact h1.comp x h2

/-- **The chart eigen-equation from the section.** If `D σ = λ σ`, the north representation satisfies
`diracF ρ stereoF stereoOmega f = λ f` on the whole chart. -/
theorem north_eq_of_dirac {σ : SpinorSection sphereSpinStructure ρ} {lam : ℝ} (h : σ.dirac = lam • σ)
    (x : E 2) : diracF ρ stereoF stereoOmega (northRep σ) x = lam • northRep σ x := by
  have hd := stereoN_mem_dom (modelEquiv2 x)
  have hdiff : MDifferentiableAt I2 𝓘(ℝ, V) (σ.toField.rep true) (stereoN (modelEquiv2 x)) :=
    (σ.toField_isSmooth true _ hd).mdifferentiableAt (by simp)
  have key := dirac_sphere_north ρ hdiff
  rw [show (σ.toField.rep true ∘ stereoN ∘ modelEquiv2) = northRep σ from rfl] at key
  rw [← key]
  change sphereSpinStructure.dirac ρ true (σ.toField.rep true) _ = lam • σ.toField.rep true _
  have e1 : sphereSpinStructure.dirac ρ true (σ.toField.rep true) (stereoN (modelEquiv2 x)) =
      σ.dirac.toField.rep true (stereoN (modelEquiv2 x)) := (σ.toField_dirac hd).symm
  rw [e1, h, rep_smul _ _ hd]

/-! ## The south side -/

section South

open CliffordAlgebra

lemma rho_ι_apply (u : E 2) (v : V) : ρ (ι (Qneg 2) u) v = cliffV ρ u v := by
  have hu : u = u 0 • e 0 + u 1 • e 1 := by
    ext i; fin_cases i <;> simp [e]
  conv_lhs => rw [hu]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, cliffV, gam]

lemma unitE_eq (y : Fin 2 → ℝ) : unitE y = (√(nsq y))⁻¹ • modelEquiv2.symm y := rfl

lemma cliffV_smul_left (c : ℝ) (u : E 2) (v : V) : cliffV ρ (c • u) v = c • cliffV ρ u v := by
  simp only [cliffV, PiLp.smul_apply, smul_eq_mul, mul_smul, smul_add]

/-- The lift of the frame change acts by `|y|⁻¹ (y₀γ₀ + y₁γ₁) γ₁`. -/
lemma rho_liftNS (y : Fin 2 → ℝ) (v : V) :
    ρ (liftNS y) v = (√(nsq y))⁻¹ • cliffV ρ (modelEquiv2.symm y) (gam ρ 1 v) := by
  rw [liftNS, map_mul]
  change ρ (ι (Qneg 2) (unitE y)) (ρ (ι (Qneg 2) (e 1)) v) = _
  rw [rho_ι_apply, unitE_eq, cliffV_smul_left]
  rfl

/-- The reflection `(y₀, y₁) ↦ (y₀, -y₁)` of the chart. -/
def reflY (z : Fin 2 → ℝ) : Fin 2 → ℝ := ![z 0, -z 1]

lemma norm_modelEquiv2_symm (y : Fin 2 → ℝ) : ‖modelEquiv2.symm y‖ = √(nsq y) := by
  rw [← norm_sq_modelEquiv2_symm, Real.sqrt_sq (norm_nonneg _)]

/-- **The transfer identity**: if `f = |y|⁻¹ c(y) γ₁ g` (the north–south relation of a section), then
`−γ₀ g = |y|⁻¹ c(y) J f` (#950's transfer `sphereT`). -/
lemma transfer_identity (w : E 2) (hw : w ≠ 0) (g : V) :
    -(gam ρ 0 g) = sphereT ρ w (‖w‖⁻¹ • cliffV ρ w (gam ρ 1 g)) := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hJ : Jop ρ (gam ρ 1 g) = -(gam ρ 0 g) := by
    simp only [Jop, ContinuousLinearMap.comp_apply, gam_sq, map_neg]
  unfold sphereT
  have h1 : ‖w‖⁻¹ * (‖w‖⁻¹ * ‖w‖ ^ 2) = 1 := by field_simp
  rw [map_smul, cliffV_smul, Jop_cliffV, cliffV_neg, cliffV_cliffV, hJ]
  simp only [smul_neg, neg_smul, neg_neg, smul_smul, h1, one_smul]

end South

section Membership

lemma pc_stereoN_ne_south {y : Fin 2 → ℝ} (hy : y ≠ 0) : pc (stereoN y) 2 ≠ -1 := by
  rw [(pc_stereoN y).2.2]
  have hq : 0 < nsq y := by
    unfold nsq
    by_contra h
    push_neg at h
    have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact hy (funext fun i => by fin_cases i <;> simp [h0, h1])
  intro h
  rw [div_eq_iff (by positivity)] at h
  linarith

lemma reflY_inv2 (w : E 2) : reflY (modelEquiv2 (inv2 w)) = tau (modelEquiv2 w) := by
  have hn : ‖w‖ ^ 2 = nsq (modelEquiv2 w) := by
    rw [← norm_sq_modelEquiv2_symm, ContinuousLinearEquiv.symm_apply_apply]
  ext i
  fin_cases i <;> simp [reflY, tau, inv2, hn, modelEquiv2_symm_apply] <;> ring

lemma stereoS_tau {y : Fin 2 → ℝ} (hy : y ≠ 0) : stereoS (tau y) = stereoN y := by
  have h1 := stereoN_mem_dom y
  have h2 := pc_stereoN_ne_south hy
  have h3 : invS (stereoN y) = tau y := by rw [invS_eq_tau h1 h2, invN_stereoN]
  rw [← h3, stereoS_invS h2]

/-- The south chart function of a section in #950's convention: `fS(w) = −γ₀ f_S(stereoS (R w))`. -/
def southRep (σ : SpinorSection sphereSpinStructure ρ) (w : E 2) : V :=
  -(gam ρ 0 (σ.toField.rep false (stereoS (reflY (modelEquiv2 w)))))

lemma contDiff_southRep (σ : SpinorSection sphereSpinStructure ρ) : ContDiff ℝ ∞ (southRep σ) := by
  have hR : ContDiff ℝ ∞ (fun w : E 2 => reflY (modelEquiv2 w)) := by
    set L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun i =>
      if i = 0 then ContinuousLinearMap.proj 0 else -ContinuousLinearMap.proj 1
    have hL : (fun w : E 2 => reflY (modelEquiv2 w)) = L.comp (modelEquiv2 : E 2 →L[ℝ] Fin 2 → ℝ) := by
      funext w; ext i; fin_cases i <;> simp [reflY, L]
    rw [hL]; exact (L.comp _).contDiff
  rw [← contMDiff_iff_contDiff]
  intro w
  have h1 := σ.toField_isSmooth false (stereoS (reflY (modelEquiv2 w))) (pc_stereoS_ne_south _)
  have h2 : ContMDiffAt 𝓘(ℝ, E 2) I2 ∞ (fun w : E 2 => stereoS (reflY (modelEquiv2 w))) w :=
    (contMDiff_stereoS _).comp w (hR.contMDiff.contMDiffAt)
  exact ((gam ρ 0).contDiff.contMDiff.contMDiffAt.comp w (h1.comp w h2)).neg

/-- **The north representation of an eigensection is a two-chart eigenspinor** (`SphereEigenspace`). -/
theorem northMap_mem {σ : SpinorSection sphereSpinStructure ρ} {lam : ℝ} (h : σ.dirac = lam • σ) :
    northMap σ ∈ SphereEigenspace ρ lam := by
  refine ⟨contDiff_northRep σ, north_eq_of_dirac h, southRep σ, contDiff_southRep σ, fun w hw => ?_⟩
  set y := modelEquiv2 w
  have hy : y ≠ 0 := fun h0 => hw (by simpa [y] using congrArg modelEquiv2.symm h0)
  have hN := stereoN_mem_dom y
  have hS : stereoN y ∈ sphereSpinStructure.dom false := pc_stereoN_ne_south hy
  unfold southRep
  rw [reflY_inv2, stereoS_tau hy]
  have htr := σ.toField.transform true false (stereoN y) hN hS
  change northRep σ w = _ at htr
  simp only [northMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [htr]
  change _ = sphereT ρ w (ρ (liftNS (invN (stereoN y))) _)
  rw [invN_stereoN, rho_liftNS, show modelEquiv2.symm y = w by simp [y],
    show √(nsq y) = ‖w‖ by rw [← norm_modelEquiv2_symm]; simp [y]]
  exact transfer_identity w hw _

end Membership

section Surjective

/-- The inverse transfer: `v = |w|⁻¹ c(w) γ₁ γ₀ (|w|⁻¹ c(w) J v)`. -/
lemma inverse_identity (w : E 2) (hw : w ≠ 0) (v : V) :
    ‖w‖⁻¹ • cliffV ρ w (gam ρ 1 (gam ρ 0 (sphereT ρ w v))) = v := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have h10 : ∀ x : V, gam ρ 1 (gam ρ 0 x) = -Jop ρ x := fun x => by
    have := gam_anticomm ρ (show (0 : Fin 2) ≠ 1 by decide) x
    rw [eq_neg_iff_add_eq_zero, add_comm]
    simpa [Jop] using this
  have h1 : ‖w‖⁻¹ * (‖w‖⁻¹ * ‖w‖ ^ 2) = 1 := by field_simp
  simp only [sphereT, map_smul, h10, Jop_cliffV, map_neg, Jop_sq, cliffV_neg, cliffV_smul, cliffV_cliffV,
    neg_neg, smul_neg, neg_smul, smul_smul, h1, one_smul]

lemma reflY_reflY (z : Fin 2 → ℝ) : reflY (reflY z) = z := by
  ext i; fin_cases i <;> simp [reflY]

open Classical in
/-- The smooth pair of a two-chart eigenspinor `(f, fS)`. -/
def pairOf (f fS : E 2 → V) : (S2 → V) × (S2 → V) :=
  (fun p => if pc p 2 ≠ 1 then f (modelEquiv2.symm (invN p)) else 0,
   fun p => if pc p 2 ≠ -1 then gam ρ 0 (fS (modelEquiv2.symm (reflY (invS p)))) else 0)

lemma contDiff_reflY : ContDiff ℝ ∞ reflY := by
  set L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun i =>
    if i = 0 then ContinuousLinearMap.proj 0 else -ContinuousLinearMap.proj 1
  have hL : reflY = L := by funext z; ext i; fin_cases i <;> simp [reflY, L]
  rw [hL]; exact L.contDiff

/-- The smooth pair of a two-chart eigenspinor. -/
def smoothPairOf {f fS : E 2 → V} (hf : ContDiff ℝ ∞ f) (hfS : ContDiff ℝ ∞ fS)
    (htr : ∀ y : E 2, y ≠ 0 → fS (inv2 y) = sphereT ρ y (f y)) : sphereSpinStructure.SmoothPair ρ :=
  ⟨pairOf (ρ := ρ) f fS, by
    refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p h1 h2 => ?_⟩
    · have hp' : pc p 2 ≠ 1 := hp
      have hc : ContMDiffAt I2 𝓘(ℝ, V) ∞ (fun q => f (modelEquiv2.symm (invN q))) p :=
        ((hf.comp (modelEquiv2.symm : (Fin 2 → ℝ) →L[ℝ] E 2).contDiff).contMDiff.contMDiffAt).comp p
          (contMDiffAt_invN hp')
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_pc_ne 1).mem_nhds hp'] with q hq
      simp [pairOf, hq]
    · have hp' : pc p 2 ≠ -1 := hp
      have hc : ContMDiffAt I2 𝓘(ℝ, V) ∞ (fun q => gam ρ 0 (fS (modelEquiv2.symm (reflY (invS q))))) p :=
        (((gam ρ 0).contDiff.comp ((hfS.comp (modelEquiv2.symm : (Fin 2 → ℝ) →L[ℝ] E 2).contDiff).comp
          contDiff_reflY)).contMDiff.contMDiffAt).comp p (contMDiffAt_invS hp')
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_pc_ne (-1)).mem_nhds hp'] with q hq
      simp [pairOf, hq]
    · have : ¬ (pc p 2 ≠ 1) := hp
      simp [pairOf, this]
    · have : ¬ (pc p 2 ≠ -1) := hp
      simp [pairOf, this]
    · have hp1 : pc p 2 ≠ 1 := h1
      have hp2 : pc p 2 ≠ -1 := h2
      simp only [pairOf, if_pos hp1, if_pos hp2]
      set y := invN p
      set w := modelEquiv2.symm y
      have hy : y ≠ 0 := by
        intro h0
        have := nsq_invN_ne_zero hp1 hp2
        rw [show nsq (invN p) = nsq y from rfl, h0] at this
        simp [nsq] at this
      have hw : w ≠ 0 := fun h0 => hy (by simpa [w] using congrArg modelEquiv2 h0)
      have hR : modelEquiv2.symm (reflY (invS p)) = inv2 w := by
        rw [invS_eq_tau hp1 hp2, ← show reflY (modelEquiv2 (inv2 w)) = tau y by
          rw [reflY_inv2]; simp [w, y], reflY_reflY]
        simp
      rw [hR, htr w hw]
      change f w = ρ (liftNS (invN p)) _
      rw [rho_liftNS, show modelEquiv2.symm (invN p) = w from rfl,
        show √(nsq (invN p)) = ‖w‖ by rw [← norm_modelEquiv2_symm]]
      exact (inverse_identity w hw (f w)).symm⟩

end Surjective

end Lightlike.Dirac

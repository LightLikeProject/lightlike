module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.LadderComplete

/-!
# The adjoint of a ladder step, for functionals

A functional `Λ` on the smooth functions with compact support in `(0, ∞)`, linear there, with
`Λ (ladUp l r F) = ⟨F, χ⟩` for every such `F` (`χ` continuous on `(0, ∞)`, the inner product of
`L²((0, ∞), sinh ξ dξ)`) is itself integration against an explicit function:
`Λ G = ⟨G, ladKer l r · (c - ∫_{x₀}^ξ ladFactor l r · sinh · χ)⟩` for some constant `c`
(`exists_eq_inner_of_comp_ladUp`).  The proof writes `G = g · ladFactor l r`, so that
`ladUp l r G = g' · ladFactor l r`, and applies the lemma of du Bois-Reymond for functionals
(`exists_eq_const_mul_integral_of_deriv_eq_zero`).  Iterated along a chain of ladders, this
identifies the vectors orthogonal to all chain images with the kernel of the adjoint chain, a finite
dimensional space of explicit smooth functions; no a priori regularity of the vector is needed,
because each intermediate stage is a functional (a distribution), not a function.  Layer 2c-v of
the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The smooth functions with compact support in `(0, ∞)`, complex valued. -/
def IsTestPos (F : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ioi 0

/-- A real test function times `ladFactor l r`, as a complex test function. -/
lemma isTestPos_mul_ladFactor (l r : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgsub : tsupport g ⊆ Ioi 0) :
    IsTestPos (fun x => ((g x * ladFactor l r x : ℝ) : ℂ)) := by
  have hsupp : tsupport (fun x => ((g x * ladFactor l r x : ℝ) : ℂ)) ⊆ tsupport g := by
    refine closure_mono fun x hx => ?_
    intro hgx
    apply hx
    simp [hgx]
  refine ⟨Complex.ofRealCLM.contDiff.comp
    (contDiff_mul_of_tsupport_subset isOpen_Ioi hg hgsub (contDiffOn_ladFactor l r)),
    hgc.mono' ((subset_tsupport _).trans hsupp), hsupp.trans hgsub⟩

/-- `ladUp l r (g · ladFactor l r) = g' · ladFactor l r` as functions, for a real test function `g`
with support in `(0, ∞)`. -/
lemma ladUp_mul_ladFactor_eq (l r : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgsub : tsupport g ⊆ Ioi 0) :
    ladUp l r (fun x => ((g x * ladFactor l r x : ℝ) : ℂ)) =
      fun x => ((deriv g x * ladFactor l r x : ℝ) : ℂ) := by
  funext x
  by_cases hx : 0 < x
  · exact ladUp_mul_ladFactor l r hx ((hg.differentiable (by simp)) x)
  · have hxs : x ∉ tsupport g := fun h => hx (hgsub h)
    have hev : (fun x => ((g x * ladFactor l r x : ℝ) : ℂ)) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
      simp [hy]
    have hd : deriv g x = 0 := by
      by_contra hne
      exact hxs (support_deriv_subset hne)
    rw [ladUp, hev.deriv_eq]
    simp [hd, image_eq_zero_of_notMem_tsupport hxs]

/-- On a real test function with support in `(0, ∞)` the integral over `(0, ∞)` is the integral over
`ℝ`. -/
lemma setIntegral_Ioi_smul_eq {g : ℝ → ℝ} (hgsub : tsupport g ⊆ Ioi 0) (f : ℝ → ℂ) :
    ∫ x in Ioi (0 : ℝ), g x • f x = ∫ x, g x • f x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  have : x ∉ tsupport g := fun h => hx (hgsub h)
  simp [image_eq_zero_of_notMem_tsupport this]

/-- **The adjoint of a ladder step, for functionals.**  If `Λ` is linear on the complex test
functions of `(0, ∞)` and `Λ (ladUp l r F) = ⟨F, χ⟩` for all of them, with `χ` continuous on
`(0, ∞)`, then for any `x₀ > 0` there is a constant `c` with
`Λ G = ⟨G, ladKer l r · (c - ∫_{x₀}^ξ ladFactor l r · sinh · χ)⟩` for every test function `G`. -/
theorem exists_eq_inner_of_comp_ladUp (l r : ℝ) (Λ : (ℝ → ℂ) → ℂ)
    (hlin : ∀ F G : ℝ → ℂ, IsTestPos F → IsTestPos G → ∀ a : ℂ,
      Λ (fun x => F x + a * G x) = Λ F + a * Λ G)
    {χ : ℝ → ℂ} (hχ : ContinuousOn χ (Ioi 0)) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hstep : ∀ F, IsTestPos F →
      Λ (ladUp l r F) = ∫ ξ in Ioi (0 : ℝ), F ξ * (starRingEnd ℂ) (χ ξ) * (Real.sinh ξ : ℂ)) :
    ∃ c : ℂ, ∀ G, IsTestPos G → Λ G = ∫ ξ in Ioi (0 : ℝ), G ξ * (starRingEnd ℂ)
      ((ladKer l r ξ : ℂ) * (c - ∫ t in x₀..ξ, (ladFactor l r t * Real.sinh t : ℝ) * χ t)) *
        (Real.sinh ξ : ℂ) := by
  set w : ℝ → ℂ := fun ξ => ((ladFactor l r ξ * Real.sinh ξ : ℝ) : ℂ) with hw
  set q : ℝ → ℂ := fun ξ => -(w ξ * (starRingEnd ℂ) (χ ξ)) with hq
  set Q : ℝ → ℂ := fun x => ∫ t in x₀..x, q t with hQ
  have hwc : ContinuousOn w (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((contDiffOn_ladFactor l r).continuousOn.mul Real.continuous_sinh.continuousOn)
  have hqc : ContinuousOn q (Ioi 0) :=
    (hwc.mul (Complex.continuous_conj.comp_continuousOn hχ)).neg
  have hQd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt Q (q x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right
      ((hqc.mono (ordConnected_Ioi.uIcc_subset (mem_Ioi.2 hx₀) hx)).intervalIntegrable)
      (hqc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hqc.continuousAt (isOpen_Ioi.mem_nhds hx))
  have hQc : ContinuousOn Q (Ioi 0) := fun x hx => (hQd x hx).continuousAt.continuousWithinAt
  have hint : ∀ (f : ℝ → ℂ), ContinuousOn f (Ioi 0) → ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
      HasCompactSupport g → tsupport g ⊆ Ioi 0 → Integrable (fun x => g x • f x) :=
    fun f hf g hg hgc hgsub =>
      (continuous_smul_of_tsupport_subset isOpen_Ioi hg.continuous hgsub hf).integrable_of_hasCompactSupport
        hgc.smul_right
  -- the functional on real test functions
  set L : (ℝ → ℝ) → ℂ := fun g =>
    Λ (fun x => ((g x * ladFactor l r x : ℝ) : ℂ)) - ∫ x, g x • Q x with hL
  have hLlin : ∀ g h : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
      ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ Ioi 0 → ∀ a : ℝ,
        L (fun x => g x - a * h x) = L g - a * L h := by
    intro g h hg hgc hgsub hh hhc hhsub a
    have e1 : (fun x => (((g x - a * h x) * ladFactor l r x : ℝ) : ℂ)) =
        fun x => ((g x * ladFactor l r x : ℝ) : ℂ) + (-(a : ℂ)) * ((h x * ladFactor l r x : ℝ) : ℂ) := by
      funext x; push_cast; ring
    have e2 := hlin _ _ (isTestPos_mul_ladFactor l r hg hgc hgsub)
      (isTestPos_mul_ladFactor l r hh hhc hhsub) (-(a : ℂ))
    have e3 : (fun x => (g x - a * h x) • Q x) = fun x => g x • Q x - a • (h x • Q x) := by
      funext x; rw [sub_smul, mul_smul]
    have hi3 : Integrable (fun x => a • (h x • Q x)) := (hint Q hQc h hh hhc hhsub).smul a
    simp only [hL]
    rw [e1, e2, e3, integral_sub (hint Q hQc g hg hgc hgsub) hi3,
      integral_smul, Complex.real_smul]
    ring
  have hd : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
      L (deriv g) = 0 := by
    intro g hg hgc hgsub
    simp only [hL]
    rw [← ladUp_mul_ladFactor_eq l r hg hgsub, hstep _ (isTestPos_mul_ladFactor l r hg hgc hgsub),
      integral_deriv_smul_eq_neg isOpen_Ioi hQd hqc hg hgc hgsub, ← setIntegral_Ioi_smul_eq hgsub q,
      sub_neg_eq_add, ← integral_add]
    · refine setIntegral_eq_zero_of_forall_eq_zero fun x _ => ?_
      simp only [hq, hw, Complex.real_smul]
      push_cast
      ring
    · have hc : ContinuousOn (fun x => w x * (starRingEnd ℂ) (χ x)) (Ioi 0) :=
        hwc.mul (Complex.continuous_conj.comp_continuousOn hχ)
      refine (hint _ hc g hg hgc hgsub).integrableOn.congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only [hw, Complex.real_smul]
      push_cast
      ring
    · exact (hint q hqc g hg hgc hgsub).integrableOn
  obtain ⟨c', hc'⟩ := exists_eq_const_mul_integral_of_deriv_eq_zero isOpen_Ioi ordConnected_Ioi
    ⟨1, by norm_num⟩ L hLlin hd
  -- on real test functions
  have hreal : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
      Λ (fun x => ((g x * ladFactor l r x : ℝ) : ℂ)) = ∫ x, g x • (Q x + c') := by
    intro g hg hgc hgsub
    have h1 := hc' g hg hgc hgsub
    simp only [hL, sub_eq_iff_eq_add] at h1
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    have e : (fun x => g x • (Q x + c')) = fun x => g x • Q x + g x • c' := by
      funext x; rw [smul_add]
    rw [h1, e, integral_add (hint Q hQc g hg hgc hgsub) (hgi.smul_const c'), integral_smul_const,
      Complex.real_smul]
    ring
  refine ⟨(starRingEnd ℂ) c', fun G hG => ?_⟩
  obtain ⟨hGs, hGc, hGsub⟩ := hG
  -- `G = (g₁ + i g₂) · ladFactor l r` with real test functions `g₁, g₂`
  have hinv : ContDiffOn ℝ ∞ (fun x => (((ladFactor l r x)⁻¹ : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_ladFactor l r).inv fun x _ => (ladFactor_pos l r x).ne')
  set Gi : ℝ → ℂ := fun x => G x * (((ladFactor l r x)⁻¹ : ℝ) : ℂ) with hGi
  have hGis : ContDiff ℝ ∞ Gi := contDiff_mul_of_tsupport_subset isOpen_Ioi hGs hGsub hinv
  set g₁ : ℝ → ℝ := fun x => (Gi x).re with hg₁
  set g₂ : ℝ → ℝ := fun x => (Gi x).im with hg₂
  have hsupp : ∀ g : ℝ → ℝ, (∀ x, G x = 0 → g x = 0) → tsupport g ⊆ tsupport G := fun g hg =>
    closure_mono fun x hx hGx => hx (hg x hGx)
  have hs₁ : tsupport g₁ ⊆ tsupport G := hsupp g₁ fun x hx => by simp [hg₁, hGi, hx]
  have hs₂ : tsupport g₂ ⊆ tsupport G := hsupp g₂ fun x hx => by simp [hg₂, hGi, hx]
  have hg₁s : ContDiff ℝ ∞ g₁ := Complex.reCLM.contDiff.comp hGis
  have hg₂s : ContDiff ℝ ∞ g₂ := Complex.imCLM.contDiff.comp hGis
  have hg₁c : HasCompactSupport g₁ := hGc.mono' ((subset_tsupport _).trans hs₁)
  have hg₂c : HasCompactSupport g₂ := hGc.mono' ((subset_tsupport _).trans hs₂)
  have hGfun : G = fun x => ((g₁ x * ladFactor l r x : ℝ) : ℂ) +
      Complex.I * ((g₂ x * ladFactor l r x : ℝ) : ℂ) := by
    funext x
    have he : ((ladFactor l r x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ladFactor_pos l r x).ne'
    have hGx : G x = Gi x * ((ladFactor l r x : ℝ) : ℂ) := by
      simp only [hGi]; push_cast; field_simp
    conv_lhs => rw [hGx, ← Complex.re_add_im (Gi x)]
    simp only [hg₁, hg₂]
    push_cast
    ring
  rw [hGfun, hlin _ _ (isTestPos_mul_ladFactor l r hg₁s hg₁c (hs₁.trans hGsub))
    (isTestPos_mul_ladFactor l r hg₂s hg₂c (hs₂.trans hGsub)),
    hreal g₁ hg₁s hg₁c (hs₁.trans hGsub), hreal g₂ hg₂s hg₂c (hs₂.trans hGsub)]
  have hQc' : ContinuousOn (fun x => Q x + c') (Ioi 0) := hQc.add continuousOn_const
  have hi₁ := hint _ hQc' g₁ hg₁s hg₁c (hs₁.trans hGsub)
  have hi₂ := hint _ hQc' g₂ hg₂s hg₂c (hs₂.trans hGsub)
  rw [← setIntegral_Ioi_smul_eq (hs₁.trans hGsub) (fun x => Q x + c'),
    ← setIntegral_Ioi_smul_eq (hs₂.trans hGsub) (fun x => Q x + c'),
    ← integral_const_mul, ← integral_add hi₁.integrableOn (hi₂.integrableOn.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
  have he := ladFactor_pos l r x
  have hconj : (starRingEnd ℂ) (∫ t in x₀..x, (ladFactor l r t * Real.sinh t : ℝ) * χ t) = -Q x := by
    rw [← intervalIntegral_conj, hQ, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hq, hw, map_mul, Complex.conj_ofReal, neg_neg]
  have hGx : G x = (((g₁ x : ℝ) : ℂ) + Complex.I * ((g₂ x : ℝ) : ℂ)) * ((ladFactor l r x : ℝ) : ℂ) := by
    rw [hGfun]; push_cast; ring
  rw [map_mul, map_sub, hconj, Complex.conj_conj, Complex.conj_ofReal, ladKer]
  simp only [Complex.real_smul]
  have hsC : Complex.sinh (x : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sinh]; exact_mod_cast hs.ne'
  have heC : ((ladFactor l r x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast
  field_simp
  ring

/-- Non-vacuity: the zero functional with `χ = 0` satisfies the hypotheses of
`exists_eq_inner_of_comp_ladUp`. -/
example (l r : ℝ) : ∃ c : ℂ, ∀ G, IsTestPos G → (0 : ℂ) = ∫ ξ in Ioi (0 : ℝ), G ξ *
    (starRingEnd ℂ) ((ladKer l r ξ : ℂ) * (c - ∫ t in (1 : ℝ)..ξ,
      (ladFactor l r t * Real.sinh t : ℝ) * (0 : ℂ))) * (Real.sinh ξ : ℂ) :=
  exists_eq_inner_of_comp_ladUp l r (fun _ => 0) (fun _ _ _ _ _ => by simp) continuousOn_const
    one_pos fun _ _ => by simp

end Lightlike.Lorentz.SL2RPlancherel

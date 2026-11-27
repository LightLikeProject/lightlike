import Mathlib
import Lightlike.Dirac.SphereSpectrumBridge
import Lightlike.Dirac.SphereSpectrumModes

/-!
# The multiplicity bound for the Dirac eigenspinors of the sphere chart

`ChartEigen ρ λ` is the real vector space of `C¹` spinors `f : ℝ² → V` of bounded norm with `D f = λ f` for the Dirac
operator of the unit 2-sphere in the stereographic chart (`diracF ρ stereoF stereoOmega`).  For a spinor module of real
dimension `4`:

* it is zero unless `λ = ±k` with `k ≥ 1` an integer (`chartEigen_eq_bot`, including `λ = 0`);
* for `λ = ±k` it has real dimension at most `4k` (`chartEigen_finrank_le`): the Fourier mode of angular index `m` at
  radius `1` is a vector `(a_m(1), b_m(1)) ∈ ℂ²` that determines the whole mode (`mode_sol_zero`), the Wronskian of two modes
  with the same `m` vanishes (so one coordinate determines the vector), and only the `2k` indices `-k ≤ m ≤ k-1`
  occur (`mode_range`).
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma dirac_add_fn (ρ : CliffordRep 2 V) {f g : E 2 → V} {x : E 2}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirac ρ (f + g) x = dirac ρ f x + dirac ρ g x := by
  have hd : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x := (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  simp only [dirac, hd, ContinuousLinearMap.add_apply, map_add, Finset.sum_add_distrib]

lemma dirac_smul_fn (ρ : CliffordRep 2 V) (a : ℝ) {f : E 2 → V} {x : E 2} (hf : DifferentiableAt ℝ f x) :
    dirac ρ (a • f) x = a • dirac ρ f x := by
  have hd : fderiv ℝ (a • f) x = a • fderiv ℝ f x := (hf.hasFDerivAt.const_smul a).fderiv
  simp only [dirac, hd, ContinuousLinearMap.smul_apply, map_smul, Finset.smul_sum]

lemma diracF_add (ρ : CliffordRep 2 V) {f g : E 2 → V} {x : E 2}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    diracF ρ stereoF stereoOmega (f + g) x =
      diracF ρ stereoF stereoOmega f x + diracF ρ stereoF stereoOmega g x := by
  rw [diracF_stereo, diracF_stereo, diracF_stereo, dirac_add_fn ρ hf hg, Pi.add_apply, map_add]
  module

lemma diracF_smul (ρ : CliffordRep 2 V) (a : ℝ) {f : E 2 → V} {x : E 2} (hf : DifferentiableAt ℝ f x) :
    diracF ρ stereoF stereoOmega (a • f) x = a • diracF ρ stereoF stereoOmega f x := by
  rw [diracF_stereo, diracF_stereo, dirac_smul_fn ρ a hf, Pi.smul_apply, map_smul]
  module

lemma diracF_zero (ρ : CliffordRep 2 V) (x : E 2) :
    diracF ρ stereoF stereoOmega (0 : E 2 → V) x = 0 := by
  have h := diracF_smul ρ (0 : ℝ) (f := (0 : E 2 → V)) (x := x) (differentiableAt_const (0 : V))
  simpa using h

/-- **The chart eigenspinors.** `C¹` spinors of bounded norm on the plane with `D f = λ f` for the Dirac operator of
the unit 2-sphere in the stereographic chart. -/
noncomputable def ChartEigen (ρ : CliffordRep 2 V) (lam : ℝ) : Submodule ℝ (E 2 → V) where
  carrier := {f | ContDiff ℝ 1 f ∧ (∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) ∧
    ∀ x, diracF ρ stereoF stereoOmega f x = lam • f x}
  add_mem' := by
    rintro f g ⟨hf, ⟨B, hB⟩, hfe⟩ ⟨hg, ⟨B', hB'⟩, hge⟩
    refine ⟨hf.add hg, ⟨B + B', fun x => (norm_add_le _ _).trans (add_le_add (hB x) (hB' x))⟩, fun x => ?_⟩
    rw [diracF_add ρ (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x), hfe, hge,
      Pi.add_apply, smul_add]
  zero_mem' := by
    refine ⟨contDiff_const, ⟨0, fun x => by simp⟩, fun x => ?_⟩
    simp [diracF_zero]
  smul_mem' := by
    rintro a f ⟨hf, ⟨B, hB⟩, hfe⟩
    refine ⟨hf.const_smul a, ⟨‖a‖ * B, fun x => ?_⟩, fun x => ?_⟩
    · calc ‖(a • f) x‖ = ‖a‖ * ‖f x‖ := by simp [norm_smul]
        _ ≤ ‖a‖ * B := mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    · rw [diracF_smul ρ a (hf.differentiable (by norm_num) x), hfe, Pi.smul_apply, smul_comm]

lemma chartEigen_contDiff {ρ : CliffordRep 2 V} {lam : ℝ} (f : ChartEigen ρ lam) : ContDiff ℝ 1 f.1 := f.2.1

lemma rescale_add (f g : E 2 → V) : rescale (f + g) = rescale f + rescale g := by
  funext y; simp [rescale, smul_add]

lemma rescale_smul (a : ℝ) (f : E 2 → V) : rescale (a • f) = a • rescale f := by
  funext y; simp [rescale, smul_comm a]

section Count

variable [FiniteDimensional ℝ V] (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0)
  (hV : Module.finrank ℝ V = 4)

/-- The first function of the complex pair of a spinor. -/
noncomputable def pairA (f : E 2 → V) : E 2 → ℂ := fun x => ((phiEquiv ρ hv hV).symm (rescale f x)).2

/-- The second function of the complex pair of a spinor. -/
noncomputable def pairB (f : E 2 → V) : E 2 → ℂ :=
  fun x => -(Complex.I * ((phiEquiv ρ hv hV).symm (rescale f x)).1)

lemma pairA_add (f g : E 2 → V) : pairA ρ hv hV (f + g) = pairA ρ hv hV f + pairA ρ hv hV g := by
  funext x; simp [pairA, rescale_add]

lemma pairB_add (f g : E 2 → V) : pairB ρ hv hV (f + g) = pairB ρ hv hV f + pairB ρ hv hV g := by
  funext x; simp [pairB, rescale_add, mul_add]; ring

lemma pairA_smul (a : ℝ) (f : E 2 → V) : pairA ρ hv hV (a • f) = a • pairA ρ hv hV f := by
  funext x; simp [pairA, rescale_smul]

lemma pairB_smul (a : ℝ) (f : E 2 → V) : pairB ρ hv hV (a • f) = a • pairB ρ hv hV f := by
  funext x
  simp only [pairB, rescale_smul, Pi.smul_apply, map_smul, Prod.smul_fst, Complex.real_smul]
  ring

lemma pairA_continuous {f : E 2 → V} (hf : ContDiff ℝ 1 f) : Continuous (pairA ρ hv hV f) :=
  continuous_snd.comp ((phiEquiv ρ hv hV).symm.continuous.comp (rescale_contDiff hf).continuous)

lemma pairB_continuous {f : E 2 → V} (hf : ContDiff ℝ 1 f) : Continuous (pairB ρ hv hV f) :=
  (continuous_const.mul (continuous_fst.comp
    ((phiEquiv ρ hv hV).symm.continuous.comp (rescale_contDiff hf).continuous))).neg

/-- The Fourier coefficient of a sum of continuous functions. -/
lemma fcoef_polar_add {G H : E 2 → ℂ} (hG : Continuous G) (hH : Continuous H) (m : ℤ) (r : ℝ) :
    fcoef (polarFn (G + H)) m r = fcoef (polarFn G) m r + fcoef (polarFn H) m r := by
  have hc : ∀ F : E 2 → ℂ, Continuous F →
      Continuous fun θ : ℝ => Complex.exp (-(m : ℂ) * θ * Complex.I) * polarFn F r θ := by
    intro F hF
    have h1 : Continuous fun θ : ℝ => polarFn F r θ :=
      hF.comp (polarPt_continuous.comp (continuous_const.prodMk continuous_id))
    have h2 : Continuous fun θ : ℝ => Complex.exp (-(m : ℂ) * θ * Complex.I) := by fun_prop
    exact h2.mul h1
  unfold fcoef
  rw [← intervalIntegral.integral_add ((hc G hG).intervalIntegrable _ _) ((hc H hH).intervalIntegrable _ _)]
  congr 1
  funext θ
  simp [polarFn, mul_add]

/-- The Fourier coefficient of a real multiple. -/
lemma fcoef_polar_smul (a : ℝ) (G : E 2 → ℂ) (m : ℤ) (r : ℝ) :
    fcoef (polarFn (a • G)) m r = a • fcoef (polarFn G) m r := by
  unfold fcoef polarFn
  simp only [Pi.smul_apply, mul_smul_comm, intervalIntegral.integral_smul]

/-- The mode vector `(a_m(1), b_m(1))` of a chart spinor. -/
noncomputable def modeVec (m : ℤ) (f : E 2 → V) : ℂ × ℂ :=
  (fcoef (polarFn (pairA ρ hv hV f)) m 1, fcoef (polarFn (pairB ρ hv hV f)) (m + 1) 1)

/-- The mode vector is real-linear on the chart eigenspinors. -/
noncomputable def modeLin (lam : ℝ) (m : ℤ) : ChartEigen ρ lam →ₗ[ℝ] ℂ × ℂ where
  toFun f := modeVec ρ hv hV m f.1
  map_add' f g := by
    simp only [Submodule.coe_add, modeVec, pairA_add, pairB_add]
    rw [fcoef_polar_add (pairA_continuous ρ hv hV (chartEigen_contDiff f)) (pairA_continuous ρ hv hV (chartEigen_contDiff g)),
      fcoef_polar_add (pairB_continuous ρ hv hV (chartEigen_contDiff f)) (pairB_continuous ρ hv hV (chartEigen_contDiff g))]
    rfl
  map_smul' a f := by
    simp only [Submodule.coe_smul, modeVec, pairA_smul, pairB_smul, fcoef_polar_smul, RingHom.id_apply]
    rfl

lemma modeLin_apply (lam : ℝ) (m : ℤ) (f : ChartEigen ρ lam) :
    modeLin ρ hv hV lam m f = modeVec ρ hv hV m f.1 := rfl

include hv hV

/-- The modes of a chart eigenspinor: radial system, boundedness at `0`, decay at `∞`. -/
lemma chart_mode_data (lam : ℝ) (f : ChartEigen ρ lam) (m : ℤ) :
    IsModeSol (2 * (lam : ℂ) / Complex.I) m (fun r => fcoef (polarFn (pairA ρ hv hV f.1)) m r)
        (fun r => fcoef (polarFn (pairB ρ hv hV f.1)) (m + 1) r) ∧
      (∃ C₀ : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
        ‖fcoef (polarFn (pairA ρ hv hV f.1)) m r‖ ≤ C₀ ∧
          ‖fcoef (polarFn (pairB ρ hv hV f.1)) (m + 1) r‖ ≤ C₀) ∧
      (∃ C₁ : ℝ, ∀ r : ℝ, 1 ≤ r →
        ‖fcoef (polarFn (pairA ρ hv hV f.1)) m r‖ ≤ C₁ / r ∧
          ‖fcoef (polarFn (pairB ρ hv hV f.1)) (m + 1) r‖ ≤ C₁ / r) := by
  obtain ⟨hf, ⟨B, hB⟩, heig⟩ := f.2
  obtain ⟨h₁, h₂, hA, hB'⟩ := eigen_pair ρ hv hV hf heig
  obtain ⟨C, hC⟩ := pair_decay ρ hv hV hB
  have hdec : ∀ x : E 2, 1 ≤ ‖x‖ →
      ‖pairA ρ hv hV f.1 x‖ ≤ C / ‖x‖ ∧ ‖pairB ρ hv hV f.1 x‖ ≤ C / ‖x‖ := by
    intro x hx
    obtain ⟨c1, c2⟩ := hC x hx
    refine ⟨c2, ?_⟩
    have : ‖pairB ρ hv hV f.1 x‖ = ‖((phiEquiv ρ hv hV).symm (rescale f.1 x)).1‖ := by
      simp [pairB]
    rw [this]; exact c1
  obtain ⟨hsol, hbd, hdc⟩ := pair_mode_data (g₁ := pairA ρ hv hV f.1) (g₂ := pairB ρ hv hV f.1) h₁ h₂ hA hB' hdec m
  exact ⟨hsol, hbd, ⟨C * (2 * Real.pi), hdc⟩⟩

/-- The Wronskian of two modes with the same angular index vanishes: the mode vectors are parallel. -/
lemma mode_wronskian_vec (lam : ℝ) (f g : ChartEigen ρ lam) (m : ℤ) :
    (modeVec ρ hv hV m f.1).1 * (modeVec ρ hv hV m g.1).2 =
      (modeVec ρ hv hV m g.1).1 * (modeVec ρ hv hV m f.1).2 := by
  obtain ⟨hsf, ⟨Cf, hbf⟩, -⟩ := chart_mode_data ρ hv hV lam f m
  obtain ⟨hsg, ⟨Cg, hbg⟩, -⟩ := chart_mode_data ρ hv hV lam g m
  have := mode_wronskian_zero_of_bounded hsf hsg (C := max Cf Cg)
    (fun r hr hr1 => ⟨(hbf r hr hr1).1.trans (le_max_left _ _), (hbf r hr hr1).2.trans (le_max_left _ _),
      (hbg r hr hr1).1.trans (le_max_right _ _), (hbg r hr hr1).2.trans (le_max_right _ _)⟩) 1 one_pos
  simp only [modeVec]
  linear_combination this

/-- A nonzero mode vector forces `-k ≤ m ≤ k - 1`. -/
lemma modeVec_eq_zero_of_out {k : ℕ} (hk : 1 ≤ k) {lam : ℝ} (hlam : lam = k ∨ lam = -(k : ℝ))
    (f : ChartEigen ρ lam) (m : ℤ) (hm : ¬(-(k : ℤ) ≤ m ∧ m ≤ (k : ℤ) - 1)) :
    modeVec ρ hv hV m f.1 = 0 := by
  by_contra hne
  obtain ⟨hsol, ⟨C₀, hbd⟩, ⟨C₁, hdc⟩⟩ := chart_mode_data ρ hv hV lam f m
  have hnz : fcoef (polarFn (pairA ρ hv hV f.1)) m 1 ≠ 0 ∨ fcoef (polarFn (pairB ρ hv hV f.1)) (m + 1) 1 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Prod.ext h.1 h.2)
  have hlamC : (lam : ℂ) = (k : ℂ) ∨ (lam : ℂ) = -(k : ℂ) := by
    rcases hlam with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  exact hm (mode_range hk hlamC m hsol one_pos hnz hbd hdc)

/-- A chart eigenspinor all of whose mode vectors vanish is zero. -/
lemma eq_zero_of_modeVec (lam : ℝ) (f : ChartEigen ρ lam) (h : ∀ m : ℤ, modeVec ρ hv hV m f.1 = 0) : f = 0 := by
  have hz : ∀ m : ℤ, ∀ r : ℝ, 0 < r →
      fcoef (polarFn (pairA ρ hv hV f.1)) m r = 0 ∧ fcoef (polarFn (pairB ρ hv hV f.1)) (m + 1) r = 0 := by
    intro m r hr
    obtain ⟨hsol, -, -⟩ := chart_mode_data ρ hv hV lam f m
    have h0 := h m
    simp only [modeVec, Prod.mk_eq_zero] at h0
    exact mode_sol_zero hsol one_pos h0.1 h0.2 r hr
  have hf := chartEigen_contDiff f
  have z1 : pairA ρ hv hV f.1 = 0 :=
    eq_zero_of_fcoef_polar_pos (pairA_continuous ρ hv hV hf) fun m r hr => (hz m r hr).1
  have z2 : pairB ρ hv hV f.1 = 0 := by
    refine eq_zero_of_fcoef_polar_pos (pairB_continuous ρ hv hV hf) fun m r hr => ?_
    have := (hz (m - 1) r hr).2
    simpa using this
  apply Subtype.ext
  funext x
  have h1 : ((phiEquiv ρ hv hV).symm (rescale f.1 x)).2 = 0 := congrFun z1 x
  have h2 : ((phiEquiv ρ hv hV).symm (rescale f.1 x)).1 = 0 := by
    have := congrFun z2 x
    simp only [pairB, Pi.zero_apply, neg_eq_zero, mul_eq_zero] at this
    exact this.resolve_left Complex.I_ne_zero
  have h3 : (phiEquiv ρ hv hV).symm (rescale f.1 x) = 0 := Prod.ext h2 h1
  have h4 : rescale f.1 x = 0 := by
    have := congrArg (phiEquiv ρ hv hV) h3
    simpa using this
  have h5 := congrFun (rescale_eq f.1) x
  simp only [h4, smul_zero] at h5
  simpa using h5

/-- **An injection into `ℂ^{2k}`.** For `λ = ±k` (`k ≥ 1`) the mode vectors, one coordinate for each of the `2k`
angular indices `-k ≤ m ≤ k-1`, embed the chart eigenspinors into `ℂ^{2k}`. -/
theorem chartEigen_embed {k : ℕ} (hk : 1 ≤ k) {lam : ℝ} (hlam : lam = k ∨ lam = -(k : ℝ)) :
    ∃ S : ChartEigen ρ lam →ₗ[ℝ] (Fin (2 * k) → ℂ), Function.Injective S := by
  classical
  -- for every `m` a coordinate that determines the mode vector
  have hex : ∀ m : ℤ, ∃ p : ℂ × ℂ →ₗ[ℝ] ℂ, ∀ f : ChartEigen ρ lam,
      p (modeVec ρ hv hV m f.1) = 0 → modeVec ρ hv hV m f.1 = 0 := by
    intro m
    by_cases h : ∃ f₀ : ChartEigen ρ lam, (modeVec ρ hv hV m f₀.1).1 ≠ 0
    · obtain ⟨f₀, hf₀⟩ := h
      refine ⟨LinearMap.fst ℝ ℂ ℂ, fun f hf => ?_⟩
      have hf' : (modeVec ρ hv hV m f.1).1 = 0 := hf
      have hw := mode_wronskian_vec ρ hv hV lam f f₀ m
      rw [hf', zero_mul] at hw
      have hb : (modeVec ρ hv hV m f.1).2 = 0 := (mul_eq_zero.mp hw.symm).resolve_left hf₀
      exact Prod.ext hf' hb
    · push_neg at h
      exact ⟨LinearMap.snd ℝ ℂ ℂ, fun f hf => Prod.ext (h f) hf⟩
  choose p hp using hex
  let mi : Fin (2 * k) → ℤ := fun i => (i : ℤ) - k
  refine ⟨LinearMap.pi fun i => (p (mi i)).comp (modeLin ρ hv hV lam (mi i)), ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine eq_zero_of_modeVec ρ hv hV lam f fun m => ?_
  by_cases hm : -(k : ℤ) ≤ m ∧ m ≤ (k : ℤ) - 1
  · have hi : (m + k).toNat < 2 * k := by omega
    have := congrFun hf ⟨(m + k).toNat, hi⟩
    have hmi : mi ⟨(m + k).toNat, hi⟩ = m := by simp only [mi]; omega
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, Pi.zero_apply, hmi, modeLin_apply] at this
    exact hp m f this
  · exact modeVec_eq_zero_of_out ρ hv hV hk hlam f m hm

/-- The chart eigenspinors form a finite-dimensional space for `λ = ±k`. -/
theorem chartEigen_finite {k : ℕ} (hk : 1 ≤ k) {lam : ℝ} (hlam : lam = k ∨ lam = -(k : ℝ)) :
    Module.Finite ℝ (ChartEigen ρ lam) := by
  obtain ⟨S, hS⟩ := chartEigen_embed ρ hv hV hk hlam
  exact Module.Finite.of_injective S hS

/-- **The multiplicity bound.** For `λ = ±k` (`k ≥ 1`) the chart eigenspinors have real dimension at most `4k`. -/
theorem chartEigen_finrank_le {k : ℕ} (hk : 1 ≤ k) {lam : ℝ} (hlam : lam = k ∨ lam = -(k : ℝ)) :
    Module.finrank ℝ (ChartEigen ρ lam) ≤ 4 * k := by
  obtain ⟨S, hS⟩ := chartEigen_embed ρ hv hV hk hlam
  have h1 := LinearMap.finrank_le_finrank_of_injective hS
  have h2 : Module.finrank ℝ (Fin (2 * k) → ℂ) = 4 * k := by
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  omega

/-- The mode vectors of an eigenspinor with `λ = 0` vanish. -/
lemma modeVec_eq_zero_of_zero (f : ChartEigen ρ 0) (m : ℤ) : modeVec ρ hv hV m f.1 = 0 := by
  obtain ⟨hsol, ⟨C₀, hbd⟩, ⟨C₁, hdc⟩⟩ := chart_mode_data ρ hv hV 0 f m
  have hs0 : (2 * ((0 : ℝ) : ℂ) / Complex.I) = 0 := by simp
  rw [hs0] at hsol
  have ha := power_sol_zero m (a := fun r => fcoef (polarFn (pairA ρ hv hV f.1)) m r)
    (fun r hr => (hsol r hr).1.congr_deriv (by simp)) (fun r hr hr1 => (hbd r hr hr1).1)
    (fun r hr => (hdc r hr).1)
  have hb := power_sol_zero (-(m + 1)) (a := fun r => fcoef (polarFn (pairB ρ hv hV f.1)) (m + 1) r)
    (fun r hr => (hsol r hr).2.congr_deriv (by push_cast; simp only [zero_div, zero_mul, add_zero]; ring))
    (fun r hr hr1 => (hbd r hr hr1).2) (fun r hr => (hdc r hr).2)
  exact Prod.ext (ha 1 one_pos) (hb 1 one_pos)

/-- **No other eigenvalue.** The chart eigenspinors vanish unless `λ = ±k` for an integer `k ≥ 1`. -/
theorem chartEigen_eq_bot {lam : ℝ} (hnot : ∀ k : ℕ, 1 ≤ k → lam ≠ k ∧ lam ≠ -(k : ℝ)) :
    ChartEigen ρ lam = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have h : (⟨f, hf⟩ : ChartEigen ρ lam) = 0 := by
    refine eq_zero_of_modeVec ρ hv hV lam ⟨f, hf⟩ fun m => ?_
    by_cases hl : lam = 0
    · subst hl; exact modeVec_eq_zero_of_zero ρ hv hV ⟨f, hf⟩ m
    · by_contra hne
      obtain ⟨hsol, ⟨C₀, hbd⟩, ⟨C₁, hdc⟩⟩ := chart_mode_data ρ hv hV lam ⟨f, hf⟩ m
      have hnz : fcoef (polarFn (pairA ρ hv hV f)) m 1 ≠ 0 ∨ fcoef (polarFn (pairB ρ hv hV f)) (m + 1) 1 ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (Prod.ext h.1 h.2)
      have hlC : (lam : ℂ) ≠ 0 := by exact_mod_cast hl
      have hν0 : 2 * (lam : ℂ) / Complex.I ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hlC) Complex.I_ne_zero
      obtain ⟨k, hk, hkk⟩ := mode_decay_quantized_int hν0 m hsol one_pos hnz hbd hdc
      have hα : Complex.I * (2 * (lam : ℂ) / Complex.I) / 2 = lam := by field_simp
      rw [hα] at hkk
      rcases hkk with h1 | h1
      · exact (hnot k hk).1 (by exact_mod_cast h1)
      · exact (hnot k hk).2 (by exact_mod_cast h1)
  exact congrArg Subtype.val h

end Count

end Lightlike.Dirac

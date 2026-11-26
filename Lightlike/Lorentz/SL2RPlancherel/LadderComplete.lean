module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.Ladder
public import Lightlike.Lorentz.SL2RPlancherel.WeakDeriv

/-!
# What is orthogonal to every ladder image is a multiple of the kernel of the adjoint ladder

The raising operator `ladUp l r F = F' - (l coth ξ + r / sinh ξ) F` has the integrating factor
`ladFactor l r ξ = sinh ξ ^ l · tanh (ξ/2) ^ r` (`hasDerivAt_ladFactor`): for `F = g · ladFactor l r`
one gets `ladUp l r F = g' · ladFactor l r` (`ladUp_mul_ladFactor`).  The kernel of the adjoint
ladder `ladDown (l+1) r` on `(0, ∞)` is spanned by
`ladKer l r ξ = 1 / (ladFactor l r ξ · sinh ξ) = sinh ξ ^ (-(l+1)) · tanh (ξ/2) ^ (-r)`
(`ladDown_ladKer`).

**Completeness of the ladder images** (`ae_eq_const_mul_ladKer_of_orth`): a function `ψ`, locally
integrable on `(0, ∞)`, that is orthogonal in the weight `sinh ξ dξ` to `ladUp l r F` for every
smooth `F` with compact support in `(0, ∞)` is almost everywhere a constant multiple of `ladKer l r`.
Proof: the orthogonality says `∫ g' · (ladFactor · sinh · conj ψ) = 0` for every test function `g`,
so `ladFactor · sinh · conj ψ` is almost everywhere constant (du Bois-Reymond,
`exists_ae_eq_const_of_weak_deriv_zero`).  Together with `ladUp_orth_ker` (the ladder images are
orthogonal to `ladKer l r`) this identifies the orthocomplement of the ladder images: it is
`ℂ · ladKer l r` intersected with the space, which is zero unless `ladKer l r` is square integrable
in the weight `sinh ξ dξ` (the discrete part).  The same argument with a right-hand side, via
`exists_ae_eq_primitive_of_weak_deriv`, solves the lowered ladder equation `ladDown (l+1) r ψ = χ`
weakly by variation of constants (`ae_eq_ladKer_mul_of_weak_ladDown`); iterated, this handles the
chains of ladder images of the radial generators.  Layer 2c-iv of the Plancherel formula on `SL(2,ℝ)`,
milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The integrating factor of the raising operator** `ladUp l r`: for `ξ > 0` it is
`sinh ξ ^ l · tanh (ξ/2) ^ r`, written as `exp (l log sinh ξ + r (log sinh (ξ/2) - log cosh (ξ/2)))`. -/
def ladFactor (l r : ℝ) (ξ : ℝ) : ℝ :=
  Real.exp (l * Real.log (Real.sinh ξ) +
    r * (Real.log (Real.sinh (ξ / 2)) - Real.log (Real.cosh (ξ / 2))))

lemma ladFactor_pos (l r ξ : ℝ) : 0 < ladFactor l r ξ := Real.exp_pos _

/-- `1 / sinh ξ` is the derivative of `log tanh (ξ/2)`, in the form used here. -/
lemma inv_sinh_eq_half_log_tanh_deriv {ξ : ℝ} (hξ : 0 < ξ) :
    Real.cosh (ξ / 2) * (1 / 2) / Real.sinh (ξ / 2) - Real.sinh (ξ / 2) * (1 / 2) / Real.cosh (ξ / 2) =
      1 / Real.sinh ξ := by
  have hs2 : 0 < Real.sinh (ξ / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hc2 : 0 < Real.cosh (ξ / 2) := Real.cosh_pos _
  have hsx : Real.sinh ξ = 2 * Real.sinh (ξ / 2) * Real.cosh (ξ / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have hcs := Real.cosh_sq_sub_sinh_sq (ξ / 2)
  rw [hsx]
  field_simp
  linear_combination hcs

/-- The factor `ladFactor l r` solves `e' = ladCoeff l r · e` on `(0, ∞)`. -/
lemma hasDerivAt_ladFactor (l r : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (ladFactor l r) (ladFactor l r ξ * ladCoeff l r ξ) ξ := by
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hξ
  have hs2 : 0 < Real.sinh (ξ / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hc2 : 0 < Real.cosh (ξ / 2) := Real.cosh_pos _
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) ξ := (hasDerivAt_id ξ).div_const 2
  have h1 : HasDerivAt (fun x => Real.log (Real.sinh x)) (Real.cosh ξ / Real.sinh ξ) ξ :=
    (Real.hasDerivAt_sinh ξ).log hs.ne'
  have hsd : HasDerivAt (fun x => Real.sinh (x / 2)) (Real.cosh (ξ / 2) * (1 / 2)) ξ :=
    hhalf.sinh
  have hcd : HasDerivAt (fun x => Real.cosh (x / 2)) (Real.sinh (ξ / 2) * (1 / 2)) ξ :=
    hhalf.cosh
  have h2 : HasDerivAt (fun x => Real.log (Real.sinh (x / 2)))
      (Real.cosh (ξ / 2) * (1 / 2) / Real.sinh (ξ / 2)) ξ := hsd.log hs2.ne'
  have h3 : HasDerivAt (fun x => Real.log (Real.cosh (x / 2)))
      (Real.sinh (ξ / 2) * (1 / 2) / Real.cosh (ξ / 2)) ξ := hcd.log hc2.ne'
  have hE := ((h1.const_mul l).add ((h2.sub h3).const_mul r)).exp
  refine HasDerivAt.congr_deriv (f := ladFactor l r) hE ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [inv_sinh_eq_half_log_tanh_deriv hξ, ladFactor, ladCoeff]
  ring

/-- `ladFactor l r` is smooth on `(0, ∞)`. -/
lemma contDiffOn_ladFactor (l r : ℝ) : ContDiffOn ℝ ∞ (ladFactor l r) (Ioi 0) := by
  have hs : ContDiffOn ℝ ∞ (fun x => Real.log (Real.sinh x)) (Ioi 0) :=
    Real.contDiff_sinh.contDiffOn.log fun x hx => (Real.sinh_pos_iff.2 hx).ne'
  have hs2 : ContDiffOn ℝ ∞ (fun x : ℝ => Real.log (Real.sinh (x / 2))) (Ioi 0) :=
    (Real.contDiff_sinh.comp (contDiff_id.div_const 2)).contDiffOn.log fun x hx =>
      (Real.sinh_pos_iff.2 (by simp only [mem_Ioi] at hx; simp only [id]; linarith)).ne'
  have hc2 : ContDiffOn ℝ ∞ (fun x : ℝ => Real.log (Real.cosh (x / 2))) (Ioi 0) :=
    (Real.contDiff_cosh.comp (contDiff_id.div_const 2)).contDiffOn.log fun x _ =>
      (Real.cosh_pos _).ne'
  exact ((contDiffOn_const.mul hs).add (contDiffOn_const.mul (hs2.sub hc2))).exp

/-- **The kernel of the adjoint ladder** `ladDown (l+1) r` on `(0, ∞)`:
`ladKer l r ξ = 1 / (ladFactor l r ξ · sinh ξ) = sinh ξ ^ (-(l+1)) · tanh (ξ/2) ^ (-r)`. -/
def ladKer (l r : ℝ) (ξ : ℝ) : ℝ := 1 / (ladFactor l r ξ * Real.sinh ξ)

/-- `ladKer l r` is differentiable on `(0, ∞)`, with `ladKer' = -ladCoeff (l+1) r · ladKer`. -/
lemma hasDerivAt_ladKer (l r : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (ladKer l r) (-(ladCoeff (l + 1) r ξ * ladKer l r ξ)) ξ := by
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hξ
  have he := ladFactor_pos l r ξ
  have hp : HasDerivAt (fun x => ladFactor l r x * Real.sinh x)
      (ladFactor l r ξ * ladCoeff l r ξ * Real.sinh ξ + ladFactor l r ξ * Real.cosh ξ) ξ :=
    (hasDerivAt_ladFactor l r hξ).mul (Real.hasDerivAt_sinh ξ)
  have hk := (hasDerivAt_const ξ (1 : ℝ)).div hp (by positivity)
  have hfun : ladKer l r = fun x => 1 / (ladFactor l r x * Real.sinh x) := rfl
  rw [hfun]
  convert hk using 1
  simp only [ladCoeff]
  field_simp
  ring

/-- `ladKer l r` solves `ladDown (l+1) r G = 0` on `(0, ∞)`, so it is the function `G` of
`ladUp_orth_ker`. -/
theorem ladDown_ladKer (l r : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladDown (l + 1) r (fun x => (ladKer l r x : ℂ)) ξ = 0 := by
  have hd : HasDerivAt (fun x => (ladKer l r x : ℂ)) (((-(ladCoeff (l + 1) r ξ * ladKer l r ξ)) : ℝ) : ℂ) ξ :=
    (hasDerivAt_ladKer l r hξ).ofReal_comp
  rw [ladDown, hd.deriv]
  push_cast
  ring

/-- A smooth function with compact support in an open set `U`, times a function smooth on `U`, is
smooth. -/
lemma contDiff_mul_of_tsupport_subset {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {U : Set ℝ} (hU : IsOpen U) {g e : ℝ → 𝔸}
    (hg : ContDiff ℝ ∞ g) (hsub : tsupport g ⊆ U) (he : ContDiffOn ℝ ∞ e U) :
    ContDiff ℝ ∞ (fun x => g x * e x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport g
  · exact (hg.contDiffAt.mul (he.contDiffAt (hU.mem_nhds (hsub hx))))
  · have hev : (fun x => g x * e x) =ᶠ[𝓝 x] fun _ => (0 : 𝔸) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **The integrating factor turns the raising operator into a derivative**: for `g` differentiable
at `ξ > 0`, `ladUp l r (g · ladFactor l r) ξ = g' ξ · ladFactor l r ξ`. -/
theorem ladUp_mul_ladFactor (l r : ℝ) {g : ℝ → ℝ} {ξ : ℝ} (hξ : 0 < ξ) (hg : DifferentiableAt ℝ g ξ) :
    ladUp l r (fun x => ((g x * ladFactor l r x : ℝ) : ℂ)) ξ =
      ((deriv g ξ * ladFactor l r ξ : ℝ) : ℂ) := by
  have hd : HasDerivAt (fun x => g x * ladFactor l r x)
      (deriv g ξ * ladFactor l r ξ + g ξ * (ladFactor l r ξ * ladCoeff l r ξ)) ξ :=
    hg.hasDerivAt.mul (hasDerivAt_ladFactor l r hξ)
  rw [ladUp, hd.ofReal_comp.deriv]
  push_cast
  ring

/-- The complex conjugate of a locally integrable function is locally integrable. -/
lemma locallyIntegrableOn_conj {s : Set ℝ} {ψ : ℝ → ℂ} (hψ : LocallyIntegrableOn ψ s) :
    LocallyIntegrableOn (fun x => (starRingEnd ℂ) (ψ x)) s := by
  intro x hx
  obtain ⟨t, ht, hint⟩ := hψ x hx
  exact ⟨t, ht, (Complex.conjLIE.integrable_comp_iff).2 hint⟩

/-- **Completeness of the ladder images.** A function `ψ`, locally integrable on `(0, ∞)`, that is
orthogonal in `L²((0, ∞), sinh ξ dξ)` to every ladder image `ladUp l r F` of a smooth `F` with
compact support in `(0, ∞)` is almost everywhere on `(0, ∞)` a constant multiple of `ladKer l r`. -/
theorem ae_eq_const_mul_ladKer_of_orth (l r : ℝ) {ψ : ℝ → ℂ} (hψ : LocallyIntegrableOn ψ (Ioi 0))
    (horth : ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ Ioi 0 →
      ∫ ξ in Ioi (0 : ℝ), ladUp l r F ξ * (starRingEnd ℂ) (ψ ξ) * (Real.sinh ξ : ℂ) = 0) :
    ∃ c : ℂ, ∀ᵐ ξ, ξ ∈ Ioi (0 : ℝ) → ψ ξ = c * (ladKer l r ξ : ℂ) := by
  set φ : ℝ → ℂ := fun ξ =>
    ((ladFactor l r ξ * Real.sinh ξ : ℝ) : ℂ) * (starRingEnd ℂ) (ψ ξ) with hφ
  have hcont : ContinuousOn (fun ξ => ((ladFactor l r ξ * Real.sinh ξ : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((contDiffOn_ladFactor l r).continuousOn.mul Real.continuous_sinh.continuousOn)
  have hφi : LocallyIntegrableOn φ (Ioi 0) :=
    (locallyIntegrableOn_conj hψ).continuousOn_mul hcont isOpen_Ioi.isLocallyClosed
  have hweak : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
      ∫ x, deriv g x • φ x = 0 := by
    intro g hg hgc hgsub
    have hgd : ∀ x, DifferentiableAt ℝ g x := fun x => (hg.differentiable (by simp)) x
    set F : ℝ → ℂ := fun x => ((g x * ladFactor l r x : ℝ) : ℂ) with hF
    have hFs : ContDiff ℝ ∞ F :=
      Complex.ofRealCLM.contDiff.comp
        (contDiff_mul_of_tsupport_subset isOpen_Ioi hg hgsub (contDiffOn_ladFactor l r))
    have hFsupp : tsupport F ⊆ tsupport g := by
      refine closure_mono fun x hx => ?_
      intro hgx
      apply hx
      simp [hF, hgx]
    have hFc : HasCompactSupport F := hgc.mono' ((subset_tsupport F).trans hFsupp)
    have h := horth F hFs hFc (hFsupp.trans hgsub)
    have hzero : ∀ x, x ∉ Ioi (0 : ℝ) → deriv g x • φ x = 0 := by
      intro x hx
      have : x ∉ tsupport g := fun h' => hx (hgsub h')
      have hd : deriv g x = 0 := by
        by_contra hne
        exact this (support_deriv_subset hne)
      simp [hd]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [hF, hφ]
    rw [ladUp_mul_ladFactor l r hx (hgd x)]
    simp only [Complex.real_smul]
    push_cast
    ring
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_weak_deriv_zero isOpen_Ioi ordConnected_Ioi
    ⟨1, by norm_num⟩ hφi hweak
  refine ⟨(starRingEnd ℂ) c, ?_⟩
  filter_upwards [hc] with ξ hξ hmem
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hmem
  have he := ladFactor_pos l r ξ
  have h := hξ hmem
  simp only [hφ] at h
  have hne : ((ladFactor l r ξ * Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos he hs).ne'
  have h' : (starRingEnd ℂ) (ψ ξ) = c / ((ladFactor l r ξ * Real.sinh ξ : ℝ) : ℂ) := by
    rw [eq_div_iff hne, mul_comm, h]
  have h'' := congrArg (starRingEnd ℂ) h'
  rw [Complex.conj_conj] at h''
  rw [h'', ladKer, map_div₀, Complex.conj_ofReal]
  push_cast
  ring

/-- The conjugate of an interval integral. -/
lemma intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ t in a..b, (starRingEnd ℂ) (f t) = (starRingEnd ℂ) (∫ t in a..b, f t) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-- **Weak solutions of the lowered ladder equation** (variation of constants): if `ψ` is locally
integrable on `(0, ∞)`, `χ` is continuous on `(0, ∞)` and `ψ` solves `ladDown (l+1) r ψ = χ` weakly,
i.e. `⟨ladUp l r F, ψ⟩ = ⟨F, χ⟩` in `L²((0, ∞), sinh ξ dξ)` for every smooth `F` with compact
support in `(0, ∞)`, then for any `x₀ > 0` there is a constant `c` with
`ψ ξ = ladKer l r ξ · (c - ∫_{x₀}^ξ ladFactor l r t · sinh t · χ t dt)` for almost every `ξ > 0`. -/
theorem ae_eq_ladKer_mul_of_weak_ladDown (l r : ℝ) {ψ χ : ℝ → ℂ}
    (hψ : LocallyIntegrableOn ψ (Ioi 0)) (hχ : ContinuousOn χ (Ioi 0)) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hweak : ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ Ioi 0 →
      ∫ ξ in Ioi (0 : ℝ), ladUp l r F ξ * (starRingEnd ℂ) (ψ ξ) * (Real.sinh ξ : ℂ) =
        ∫ ξ in Ioi (0 : ℝ), F ξ * (starRingEnd ℂ) (χ ξ) * (Real.sinh ξ : ℂ)) :
    ∃ c : ℂ, ∀ᵐ ξ, ξ ∈ Ioi (0 : ℝ) → ψ ξ = (ladKer l r ξ : ℂ) *
      (c - ∫ t in x₀..ξ, (ladFactor l r t * Real.sinh t : ℝ) * χ t) := by
  set w : ℝ → ℂ := fun ξ => ((ladFactor l r ξ * Real.sinh ξ : ℝ) : ℂ) with hw
  set φ : ℝ → ℂ := fun ξ => w ξ * (starRingEnd ℂ) (ψ ξ) with hφ
  set h : ℝ → ℂ := fun ξ => -(w ξ * (starRingEnd ℂ) (χ ξ)) with hh
  have hwc : ContinuousOn w (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((contDiffOn_ladFactor l r).continuousOn.mul Real.continuous_sinh.continuousOn)
  have hφi : LocallyIntegrableOn φ (Ioi 0) :=
    (locallyIntegrableOn_conj hψ).continuousOn_mul hwc isOpen_Ioi.isLocallyClosed
  have hhc : ContinuousOn h (Ioi 0) :=
    (hwc.mul (Complex.continuous_conj.comp_continuousOn hχ)).neg
  have hw' : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
      ∫ x, deriv g x • φ x = -∫ x, g x • h x := by
    intro g hg hgc hgsub
    have hgd : ∀ x, DifferentiableAt ℝ g x := fun x => (hg.differentiable (by simp)) x
    set F : ℝ → ℂ := fun x => ((g x * ladFactor l r x : ℝ) : ℂ) with hF
    have hFs : ContDiff ℝ ∞ F :=
      Complex.ofRealCLM.contDiff.comp
        (contDiff_mul_of_tsupport_subset isOpen_Ioi hg hgsub (contDiffOn_ladFactor l r))
    have hFsupp : tsupport F ⊆ tsupport g := by
      refine closure_mono fun x hx => ?_
      intro hgx
      apply hx
      simp [hF, hgx]
    have hFc : HasCompactSupport F := hgc.mono' ((subset_tsupport F).trans hFsupp)
    have hE := hweak F hFs hFc (hFsupp.trans hgsub)
    have hzero1 : ∀ x, x ∉ Ioi (0 : ℝ) → deriv g x • φ x = 0 := by
      intro x hx
      have : x ∉ tsupport g := fun h' => hx (hgsub h')
      have hd : deriv g x = 0 := by
        by_contra hne
        exact this (support_deriv_subset hne)
      simp [hd]
    have hzero2 : ∀ x, x ∉ Ioi (0 : ℝ) → g x • h x = 0 := by
      intro x hx
      have : x ∉ tsupport g := fun h' => hx (hgsub h')
      simp [image_eq_zero_of_notMem_tsupport this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero2, ← integral_neg]
    have e1 : ∫ x in Ioi (0 : ℝ), deriv g x • φ x =
        ∫ ξ in Ioi (0 : ℝ), ladUp l r F ξ * (starRingEnd ℂ) (ψ ξ) * (Real.sinh ξ : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [hF, hφ, hw]
      rw [ladUp_mul_ladFactor l r hx (hgd x)]
      simp only [Complex.real_smul]
      push_cast
      ring
    have e2 : ∫ x in Ioi (0 : ℝ), -(g x • h x) =
        ∫ ξ in Ioi (0 : ℝ), F ξ * (starRingEnd ℂ) (χ ξ) * (Real.sinh ξ : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [hF, hh, hw, Complex.real_smul]
      push_cast
      ring
    rw [e1, e2, hE]
  obtain ⟨c, hc⟩ := exists_ae_eq_primitive_of_weak_deriv isOpen_Ioi ordConnected_Ioi
    (mem_Ioi.2 hx₀) hφi hhc hw'
  refine ⟨(starRingEnd ℂ) c, ?_⟩
  filter_upwards [hc] with ξ hξ hmem
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hmem
  have he := ladFactor_pos l r ξ
  have hφξ := hξ hmem
  have hne : w ξ ≠ 0 := by
    simp only [hw]; exact_mod_cast (mul_pos he hs).ne'
  -- the conjugate of the primitive
  have hprim : (starRingEnd ℂ) (∫ t in x₀..ξ, h t) =
      -∫ t in x₀..ξ, (ladFactor l r t * Real.sinh t : ℝ) * χ t := by
    rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hh, hw, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  have h1 : (starRingEnd ℂ) (ψ ξ) = (c + ∫ t in x₀..ξ, h t) / w ξ := by
    rw [eq_div_iff hne, ← hφξ]
    simp only [hφ]
    ring
  have h2 := congrArg (starRingEnd ℂ) h1
  rw [Complex.conj_conj, map_div₀, map_add, hprim] at h2
  rw [h2, ladKer]
  simp only [hw, Complex.conj_ofReal]
  push_cast
  ring

/-! ### Trust checks and non-vacuity -/

/-- Trust check: for `(l, r) = (1, 0)` the factor is `sinh ξ`. -/
lemma ladFactor_one_zero {ξ : ℝ} (hξ : 0 < ξ) : ladFactor 1 0 ξ = Real.sinh ξ := by
  simp [ladFactor, Real.exp_log (Real.sinh_pos_iff.2 hξ)]

/-- Trust check: for `(l, r) = (0, 1)` the factor is `tanh (ξ/2)`. -/
lemma ladFactor_zero_one {ξ : ℝ} (hξ : 0 < ξ) : ladFactor 0 1 ξ = Real.tanh (ξ / 2) := by
  have hs2 : 0 < Real.sinh (ξ / 2) := Real.sinh_pos_iff.2 (by linarith)
  rw [ladFactor, zero_mul, zero_add, one_mul, Real.exp_sub, Real.exp_log hs2,
    Real.exp_log (Real.cosh_pos _), Real.tanh_eq_sinh_div_cosh]

/-- Trust check: for `(l, r) = (0, 0)` the kernel of `ladDown 1 0` is `1 / sinh ξ`. -/
lemma ladKer_zero_zero (ξ : ℝ) : ladKer 0 0 ξ = 1 / Real.sinh ξ := by
  simp [ladKer, ladFactor]

/-- `ladKer l r` is continuous on `(0, ∞)`. -/
lemma continuousOn_ladKer (l r : ℝ) : ContinuousOn (ladKer l r) (Ioi 0) := fun _ hx =>
  (hasDerivAt_ladKer l r hx).continuousAt.continuousWithinAt

/-- **The ladder images are orthogonal to `ladKer l r`** (the hypothesis of
`ae_eq_const_mul_ladKer_of_orth` holds for `ψ = ladKer l r`): for `F` smooth with compact support
in `(0, ∞)`, `ladUp l r F · ladKer l r · sinh = (F / ladFactor l r)'`, whose integral vanishes. -/
theorem integral_ladUp_mul_ladKer (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ Ioi 0) :
    ∫ ξ in Ioi (0 : ℝ), ladUp l r F ξ * (starRingEnd ℂ) (ladKer l r ξ : ℂ) * (Real.sinh ξ : ℂ) = 0 := by
  set h : ℝ → ℂ := fun x => F x * (((ladFactor l r x)⁻¹ : ℝ) : ℂ) with hh
  have hinv : ContDiffOn ℝ ∞ (fun x => (((ladFactor l r x)⁻¹ : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_ladFactor l r).inv fun x _ => (ladFactor_pos l r x).ne')
  have hhs : ContDiff ℝ ∞ h := contDiff_mul_of_tsupport_subset isOpen_Ioi hF hFs hinv
  have hhsupp : tsupport h ⊆ tsupport F :=
    closure_mono (Function.support_mul_subset_left _ _)
  have hhc : HasCompactSupport h := hFc.mono' ((subset_tsupport h).trans hhsupp)
  have hdiff : Differentiable ℝ h := hhs.differentiable (by simp)
  -- the derivative of `h` is the integrand on `(0, ∞)`
  have hder : ∀ ξ, 0 < ξ →
      deriv h ξ = ladUp l r F ξ * (starRingEnd ℂ) (ladKer l r ξ : ℂ) * (Real.sinh ξ : ℂ) := by
    intro ξ hξ
    have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hξ
    have he := ladFactor_pos l r ξ
    have hi : HasDerivAt (fun x => (ladFactor l r x)⁻¹)
        (-(ladFactor l r ξ * ladCoeff l r ξ) / ladFactor l r ξ ^ 2) ξ :=
      (hasDerivAt_ladFactor l r hξ).inv he.ne'
    have hFd : HasDerivAt F (deriv F ξ) ξ :=
      ((hF.differentiable (by simp)) ξ).hasDerivAt
    have hd := hFd.mul hi.ofReal_comp
    have hsC : Complex.sinh (ξ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sinh]; exact_mod_cast hs.ne'
    rw [show deriv h ξ = _ from hd.deriv, ladUp, Complex.conj_ofReal, ladKer]
    have heC : ((ladFactor l r ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast he.ne'
    push_cast
    field_simp
    ring
  have hzero : ∀ x, x ∉ Ioi (0 : ℝ) → deriv h x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hFs (hhsupp (support_deriv_subset hne)))
  rw [← setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => hder ξ hξ,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hdc : Continuous (deriv h) := hhs.continuous_deriv (by simp)
  exact integral_eq_zero_of_hasDerivAt_of_integrable (fun x => (hdiff x).hasDerivAt)
    (hdc.integrable_of_hasCompactSupport hhc.deriv)
    (hhs.continuous.integrable_of_hasCompactSupport hhc)

/-- Non-vacuity: `ψ = ladKer l r` satisfies the hypotheses of `ae_eq_const_mul_ladKer_of_orth`. -/
example (l r : ℝ) : ∃ c : ℂ, ∀ᵐ ξ, ξ ∈ Ioi (0 : ℝ) → (ladKer l r ξ : ℂ) = c * (ladKer l r ξ : ℂ) :=
  ae_eq_const_mul_ladKer_of_orth l r
    ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_ladKer l r)).locallyIntegrableOn
      measurableSet_Ioi)
    fun _ hF hFc hFs => integral_ladUp_mul_ladKer l r hF hFc hFs

end Lightlike.Lorentz.SL2RPlancherel

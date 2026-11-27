module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileLadderForm
public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileDecay

/-!
# The radial profiles of the antiholomorphic discrete series are orthogonal to the ladder images

For `ν ≥ 1`, `j, k ∈ ℕ` and a test function `F` (smooth with compact support in `(0, ∞)`), the `(ν + k)`-fold raising
chain `ladUpChain (-(ν + j)) (ν + k) F` of the `K`-type `(0, -(ν + j))` is orthogonal in `L²((0, ∞), sinh ξ dξ)` to the
radial profile `ψ_{jk}` of the antiholomorphic series `D_{2ν}⁻` of `K`-type `(ν + k, -(ν + j))`
(`integral_ladUpChain_mul_profile`, and the same for the complex conjugate profile): each step is adjoint to the
lowering operator (`integral_ladUp_mul_conj`), which maps `ψ_{jk}` to a multiple of `ψ_{j,k-1}` and kills `ψ_{j0}`
(`ladDown_profileFun_succ_minus`, `ladDown_profileFun_zero_minus`).
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Adjointness of the ladders with boundary terms** on `[a, b] ⊂ (0, ∞)`. -/
theorem ladder_adjoint_on_Ioi (l r : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {F G : ℝ → ℂ}
    (hF : ContDiffOn ℝ 1 F (Ioi 0)) (hG : ContDiffOn ℝ 1 G (Ioi 0)) :
    ∫ ξ in a..b, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      (F b * (starRingEnd ℂ) (G b) * (Real.sinh b : ℂ) - F a * (starRingEnd ℂ) (G a) * (Real.sinh a : ℂ)) +
      ∫ ξ in a..b, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hFd : ∀ ξ, 0 < ξ → HasDerivAt F (deriv F ξ) ξ := fun ξ hξ =>
    ((hF.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hξ)).hasDerivAt
  have hGd : ∀ ξ, 0 < ξ → HasDerivAt G (deriv G ξ) ξ := fun ξ hξ =>
    ((hG.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hξ)).hasDerivAt
  set P : ℝ → ℂ := fun ξ => F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) with hP
  have hpt : ∀ ξ, 0 < ξ → HasDerivAt P
      (ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) -
        F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) ξ := by
    intro ξ hξ
    have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
    have h1 := (hFd ξ hξ).mul ((hGd ξ hξ).star)
    have h2 := h1.mul ((Real.hasDerivAt_sinh ξ).ofReal_comp)
    refine HasDerivAt.congr_deriv h2 ?_
    have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hcs : (starRingEnd ℂ) (Complex.sinh (ξ : ℂ)) = Complex.sinh ξ := by
      rw [← Complex.ofReal_sinh, Complex.conj_ofReal]
    have hcc : (starRingEnd ℂ) (Complex.cosh (ξ : ℂ)) = Complex.cosh ξ := by
      rw [← Complex.ofReal_cosh, Complex.conj_ofReal]
    have hs'' : Complex.sinh (ξ : ℂ) ≠ 0 := by rw [← Complex.ofReal_sinh]; exact_mod_cast hs
    simp [ladUp, ladDown, ladCoeff, Complex.conj_ofReal, hcs, hcc]
    field_simp
    ring
  have hFc : ContinuousOn F (uIcc a b) := (hF.continuousOn).mono fun x hx => hpos x hx
  have hGc : ContinuousOn G (uIcc a b) := (hG.continuousOn).mono fun x hx => hpos x hx
  have hF'c : ContinuousOn (deriv F) (uIcc a b) :=
    (hF.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono fun x hx => hpos x hx
  have hG'c : ContinuousOn (deriv G) (uIcc a b) :=
    (hG.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono fun x hx => hpos x hx
  have hκc : ContinuousOn (fun ξ => (ladCoeff l r ξ : ℂ)) (uIcc a b) := by
    have : ContinuousOn (ladCoeff l r) (uIcc a b) := fun x hx =>
      (hasDerivAt_ladCoeff l r (hpos x hx)).continuousAt.continuousWithinAt
    exact Complex.continuous_ofReal.comp_continuousOn this
  have hκc1 : ContinuousOn (fun ξ => (ladCoeff (l + 1) r ξ : ℂ)) (uIcc a b) := by
    have : ContinuousOn (ladCoeff (l + 1) r) (uIcc a b) := fun x hx =>
      (hasDerivAt_ladCoeff (l + 1) r (hpos x hx)).continuousAt.continuousWithinAt
    exact Complex.continuous_ofReal.comp_continuousOn this
  have hsc : Continuous fun ξ : ℝ => (Real.sinh ξ : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_sinh
  have hL : ContinuousOn (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ)) (uIcc a b) := by
    unfold ladUp
    exact ((hF'c.sub (hκc.mul hFc)).mul
      (Complex.continuous_conj.comp_continuousOn hGc)).mul hsc.continuousOn
  have hR : ContinuousOn (fun ξ => F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) (uIcc a b) := by
    unfold ladDown
    exact (hFc.mul (Complex.continuous_conj.comp_continuousOn
      ((hG'c.neg).sub (hκc1.mul hGc)))).mul hsc.continuousOn
  have hLi : IntervalIntegrable (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ))
      volume a b := hL.intervalIntegrable
  have hRi : IntervalIntegrable (fun ξ => F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ))
      volume a b := hR.intervalIntegrable
  have hder : ∀ x ∈ uIcc a b, HasDerivAt P
      (ladUp l r F x * (starRingEnd ℂ) (G x) * (Real.sinh x : ℂ) -
        F x * (starRingEnd ℂ) (ladDown (l + 1) r G x) * (Real.sinh x : ℂ)) x :=
    fun x hx => hpt x (hpos x hx)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hLi.sub hRi)
  rw [intervalIntegral.integral_sub hLi hRi] at key
  have : ∫ ξ in a..b, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      P b - P a + ∫ ξ in a..b, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
    linear_combination key
  exact this

/-- **The chain of raising operators** `ladUp (k - 1) r ∘ ⋯ ∘ ladUp 0 r`, of the `K`-types `(0, r) ↦ (k, r)`. -/
def ladUpChain (r : ℝ) : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, F => F
  | k + 1, F => ladUp (k : ℝ) r (ladUpChain r k F)

/-- **Test functions**: smooth on `(0, ∞)` with compact support in `(0, ∞)`. -/
def IsTestFn (F : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ F (Ioi 0) ∧ IsCompact (tsupport F) ∧ tsupport F ⊆ Ioi 0

lemma contDiffOn_ladCoeff (l r : ℝ) : ContDiffOn ℝ ∞ (ladCoeff l r) (Ioi 0) := by
  have hs : ContDiffOn ℝ ∞ Real.sinh (Ioi 0) := Real.contDiff_sinh.contDiffOn
  have hc : ContDiffOn ℝ ∞ Real.cosh (Ioi 0) := Real.contDiff_cosh.contDiffOn
  have hne : ∀ x ∈ Ioi (0 : ℝ), Real.sinh x ≠ 0 := fun x hx => (Real.sinh_pos_iff.2 hx).ne'
  unfold ladCoeff
  exact ((hc.div hs hne).const_smul l |>.congr (fun x _ => by simp [smul_eq_mul])).add
    ((contDiffOn_const).div hs hne)

lemma isTestFn_ladUp {F : ℝ → ℂ} (hF : IsTestFn F) (l r : ℝ) : IsTestFn (ladUp l r F) := by
  obtain ⟨h1, h2, h3⟩ := hF
  have hd : ContDiffOn ℝ ∞ (deriv F) (Ioi 0) := ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 h1).2
  have hk : ContDiffOn ℝ ∞ (fun ξ => (ladCoeff l r ξ : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_ladCoeff l r)
  have hsub : tsupport (ladUp l r F) ⊆ tsupport F := by
    refine closure_minimal (fun ξ hξ => ?_) (isClosed_tsupport F)
    by_contra hξF
    have h0 : F =ᶠ[𝓝 ξ] 0 := notMem_tsupport_iff_eventuallyEq.1 hξF
    apply hξ
    simp [ladUp, h0.deriv_eq, h0.self_of_nhds]
  refine ⟨?_, h2.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans h3⟩
  unfold ladUp
  exact hd.sub (hk.mul h1)

lemma isTestFn_ladUpChain {F : ℝ → ℂ} (hF : IsTestFn F) (r : ℝ) : ∀ k, IsTestFn (ladUpChain r k F)
  | 0 => hF
  | k + 1 => isTestFn_ladUp (isTestFn_ladUpChain hF r k) _ _

/-- **Integration by parts on `(0, ∞)`**: the lowering operator is adjoint to the raising operator, for test
functions. -/
theorem integral_ladUp_mul_conj (l r : ℝ) {F G : ℝ → ℂ} (hF : IsTestFn F) (hG : ContDiffOn ℝ 1 G (Ioi 0)) :
    ∫ ξ in Ioi (0 : ℝ), ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in Ioi (0 : ℝ), F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := hF
  rcases (tsupport F).eq_empty_or_nonempty with hE | hne
  · have hF0 : F = 0 := by
      ext ξ
      by_contra h
      have : ξ ∈ tsupport F := subset_tsupport F h
      rw [hE] at this; exact this
    subst hF0
    have hl : ∀ ξ, ladUp l r (0 : ℝ → ℂ) ξ = 0 := fun ξ => by simp [ladUp]
    simp [hl]
  obtain ⟨x₀, hx₀, hmin⟩ := h2.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨x₁, hx₁, hmax⟩ := h2.exists_isMaxOn hne continuous_id.continuousOn
  have hx₀pos : 0 < x₀ := h3 hx₀
  have hx₁pos : 0 < x₁ := h3 hx₁
  set a : ℝ := x₀ / 2 with ha
  set b : ℝ := 2 * x₁ with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by
    have : x₀ ≤ x₁ := hmax hx₀
    simp only [ha, hb]; linarith
  have hFout : ∀ ξ, ξ ∉ Icc x₀ x₁ → F ξ = 0 := by
    intro ξ hξ
    by_contra h
    have hmem : ξ ∈ tsupport F := subset_tsupport F h
    exact hξ ⟨hmin hmem, hmax hmem⟩
  have hFa : F a = 0 := hFout a (by rw [mem_Icc]; intro h; linarith [h.1, ha])
  have hFb : F b = 0 := hFout b (by rw [mem_Icc]; intro h; linarith [h.2, hb])
  have hF1 : ContDiffOn ℝ 1 F (Ioi 0) := h1.of_le (by norm_cast)
  have hadj := ladder_adjoint_on_Ioi l r ha0 hab hF1 hG
  rw [hFa, hFb] at hadj
  simp only [zero_mul, sub_zero, zero_add] at hadj
  have hLzero : ∀ ξ ∈ Ioi (0 : ℝ) \ Ioc a b,
      ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) = 0 := by
    intro ξ hξ
    have hξ' : ξ ∉ Icc x₀ x₁ := by
      intro hh
      apply hξ.2
      refine ⟨?_, ?_⟩ <;> simp only [ha, hb] <;> linarith [hh.1, hh.2, hξ.1]
    have : ladUp l r F ξ = 0 := by
      have hmem : ξ ∉ tsupport F := fun hm => hξ' ⟨hmin hm, hmax hm⟩
      have h0 : F =ᶠ[𝓝 ξ] 0 := notMem_tsupport_iff_eventuallyEq.1 hmem
      simp [ladUp, h0.deriv_eq, h0.self_of_nhds]
    simp [this]
  have hRzero : ∀ ξ ∈ Ioi (0 : ℝ) \ Ioc a b,
      F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) = 0 := by
    intro ξ hξ
    have hξ' : ξ ∉ Icc x₀ x₁ := by
      intro hh
      apply hξ.2
      refine ⟨?_, ?_⟩ <;> simp only [ha, hb] <;> linarith [hh.1, hh.2, hξ.1]
    simp [hFout ξ hξ']
  have hsub : Ioc a b ⊆ Ioi 0 := fun x hx => lt_trans ha0 hx.1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hLzero,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hRzero,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact hadj

lemma contDiffOn_one_of_deriv_eq {G : ℝ → ℂ} (hd : ∀ ξ, 0 < ξ → DifferentiableAt ℝ G ξ)
    (hc : ContinuousOn (deriv G) (Ioi 0)) : ContDiffOn ℝ 1 G (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun ξ hξ => (hd ξ hξ).differentiableWithinAt, by simp, ?_⟩
  exact contDiffOn_zero.2 hc

lemma ladDown_conj (l r : ℝ) {G : ℝ → ℂ} {ξ : ℝ} (hG : DifferentiableAt ℝ G ξ) :
    ladDown l r (fun x => (starRingEnd ℂ) (G x)) ξ = (starRingEnd ℂ) (ladDown l r G ξ) := by
  have h : deriv (fun x => (starRingEnd ℂ) (G x)) ξ = (starRingEnd ℂ) (deriv G ξ) := by
    have := hG.hasDerivAt.star
    simpa [Complex.star_def] using this.deriv
  simp only [ladDown, h, map_sub, map_neg, map_mul, Complex.conj_ofReal]

/-- **The raising chain is orthogonal to a family `G_k` of functions with `ladDown (ν + k + 1) r G_{k+1} = c_k G_k`
and `ladDown ν r G_0 = 0`.** -/
theorem integral_ladUpChain_mul_conj_eq_zero (r : ℝ) (ν : ℕ) (hν : 1 ≤ ν) {G : ℕ → ℝ → ℂ} (c : ℕ → ℝ)
    (hG : ∀ k, ContDiffOn ℝ 1 (G k) (Ioi 0))
    (h0 : ∀ ξ : ℝ, 0 < ξ → ladDown (ν : ℝ) r (G 0) ξ = 0)
    (hs : ∀ (k : ℕ) (ξ : ℝ), 0 < ξ → ladDown ((ν + k + 1 : ℕ) : ℝ) r (G (k + 1)) ξ = (c k : ℂ) * G k ξ)
    {F : ℝ → ℂ} (hF : IsTestFn F) :
    ∀ k : ℕ, ∫ ξ in Ioi (0 : ℝ), ladUpChain r (ν + k) F ξ * (starRingEnd ℂ) (G k ξ) * (Real.sinh ξ : ℂ) = 0 := by
  obtain ⟨ν', rfl⟩ : ∃ ν', ν = ν' + 1 := ⟨ν - 1, by omega⟩
  intro k
  induction k with
  | zero =>
    have e : ladUpChain r (ν' + 1 + 0) F = ladUp (ν' : ℝ) r (ladUpChain r ν' F) := rfl
    rw [e, integral_ladUp_mul_conj _ _ (isTestFn_ladUpChain hF r ν') (hG 0)]
    have : ∀ ξ ∈ Ioi (0 : ℝ), ladUpChain r ν' F ξ * (starRingEnd ℂ) (ladDown ((ν' : ℝ) + 1) r (G 0) ξ) *
        (Real.sinh ξ : ℂ) = 0 := by
      intro ξ hξ
      have := h0 ξ hξ
      push_cast at this ⊢
      simp [this]
    rw [setIntegral_congr_fun measurableSet_Ioi this]; simp
  | succ k ih =>
    have e : ladUpChain r (ν' + 1 + (k + 1)) F = ladUp ((ν' + 1 + k : ℕ) : ℝ) r (ladUpChain r (ν' + 1 + k) F) := rfl
    rw [e, integral_ladUp_mul_conj _ _ (isTestFn_ladUpChain hF r _) (hG (k + 1))]
    have : ∀ ξ ∈ Ioi (0 : ℝ), ladUpChain r (ν' + 1 + k) F ξ *
        (starRingEnd ℂ) (ladDown (((ν' + 1 + k : ℕ) : ℝ) + 1) r (G (k + 1)) ξ) * (Real.sinh ξ : ℂ) =
        (c k : ℂ) * (ladUpChain r (ν' + 1 + k) F ξ * (starRingEnd ℂ) (G k ξ) * (Real.sinh ξ : ℂ)) := by
      intro ξ hξ
      have h1 := hs k ξ hξ
      have h2 : (((ν' + 1 + k : ℕ) : ℝ) + 1) = ((ν' + 1 + k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h2, h1]
      simp only [map_mul, Complex.conj_ofReal]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul, ih]; simp

lemma continuousOn_ladB (n j l : ℕ) : ContinuousOn (ladB n j l) (Ioi 0) := by
  unfold ladB
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => ?_)
  have := Real.sinh_pos_iff.2 (show 0 < x from hx)
  positivity

lemma contDiffOn_profileFun (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) : ContDiffOn ℝ 1 (profileFun n l j κ) (Ioi 0) := by
  refine contDiffOn_one_of_deriv_eq (fun ξ _ => (hasDerivAt_profileFun n l j hn κ ξ).differentiableAt) ?_
  have hc : ContinuousOn (fun ξ => (ladB n j l ξ : ℂ) * profileFun n l j κ ξ -
      ((n + l : ℕ) : ℂ) * profileFun n (l + 1) j κ ξ) (Ioi 0) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (Complex.continuous_ofReal.comp_continuousOn (continuousOn_ladB n j l)).mul
        (continuous_profileFun n l j hn κ).continuousOn
    · exact continuousOn_const.mul (continuous_profileFun n (l + 1) j hn κ).continuousOn
  refine hc.congr (fun ξ hξ => ?_)
  have := profileFun_down n l j hn κ hξ
  linear_combination this

/-- **The radial profile of the antiholomorphic series `D_{2ν}⁻` is orthogonal to every raising chain image**:
for a test function `F`, `∫_0^∞ (ladUpChain (-(ν + j)) (ν + k) F) conj(ψ_{jk}) sinh ξ dξ = 0`. -/
theorem integral_ladUpChain_mul_profile (ν j k : ℕ) (hν : 1 ≤ ν) (κ : ℂ) {F : ℝ → ℂ} (hF : IsTestFn F) :
    ∫ ξ in Ioi (0 : ℝ), ladUpChain (-((ν + j : ℕ) : ℝ)) (ν + k) F ξ *
      (starRingEnd ℂ) (profileFun (2 * ν) k j κ ξ) * (Real.sinh ξ : ℂ) = 0 := by
  have hn : 1 ≤ 2 * ν := by omega
  refine integral_ladUpChain_mul_conj_eq_zero (-((ν + j : ℕ) : ℝ)) ν hν (G := fun k => profileFun (2 * ν) k j κ)
    (fun k => -((k + 1 : ℕ) : ℝ)) (fun k => contDiffOn_profileFun (2 * ν) k j hn κ) ?_ ?_ hF k
  · intro ξ hξ
    have h := ladDown_profileFun_zero_minus (2 * ν) j hn κ hξ
    have e1 : (((2 * ν + 2 * 0 : ℕ) : ℝ) / 2) = (ν : ℝ) := by push_cast; ring
    have e2 : (-((2 * ν + 2 * j : ℕ) : ℝ) / 2) = -((ν + j : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    exact h
  · intro k ξ hξ
    have h := ladDown_profileFun_succ_minus (2 * ν) k j hn κ hξ
    have e1 : (((2 * ν + 2 * (k + 1) : ℕ) : ℝ) / 2) = ((ν + k + 1 : ℕ) : ℝ) := by push_cast; ring
    have e2 : (-((2 * ν + 2 * j : ℕ) : ℝ) / 2) = -((ν + j : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    rw [h]; push_cast; ring

/-- The same for the complex conjugate profile: `∫ (chain image) ψ_{jk} sinh = 0`. -/
theorem integral_ladUpChain_mul_profile_conj (ν j k : ℕ) (hν : 1 ≤ ν) (κ : ℂ) {F : ℝ → ℂ} (hF : IsTestFn F) :
    ∫ ξ in Ioi (0 : ℝ), ladUpChain (-((ν + j : ℕ) : ℝ)) (ν + k) F ξ *
      profileFun (2 * ν) k j κ ξ * (Real.sinh ξ : ℂ) = 0 := by
  have hn : 1 ≤ 2 * ν := by omega
  have key := integral_ladUpChain_mul_conj_eq_zero (-((ν + j : ℕ) : ℝ)) ν hν
    (G := fun k ξ => (starRingEnd ℂ) (profileFun (2 * ν) k j κ ξ)) (fun k => -((k + 1 : ℕ) : ℝ))
    (fun k => (Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_profileFun (2 * ν) k j hn κ)))
    ?_ ?_ hF k
  · simpa using key
  · intro ξ hξ
    have h := ladDown_profileFun_zero_minus (2 * ν) j hn κ hξ
    have e1 : (((2 * ν + 2 * 0 : ℕ) : ℝ) / 2) = (ν : ℝ) := by push_cast; ring
    have e2 : (-((2 * ν + 2 * j : ℕ) : ℝ) / 2) = -((ν + j : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    rw [ladDown_conj _ _ ((hasDerivAt_profileFun (2 * ν) 0 j hn κ ξ).differentiableAt), h]; simp
  · intro k ξ hξ
    have h := ladDown_profileFun_succ_minus (2 * ν) k j hn κ hξ
    have e1 : (((2 * ν + 2 * (k + 1) : ℕ) : ℝ) / 2) = ((ν + k + 1 : ℕ) : ℝ) := by push_cast; ring
    have e2 : (-((2 * ν + 2 * j : ℕ) : ℝ) / 2) = -((ν + j : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    rw [ladDown_conj _ _ ((hasDerivAt_profileFun (2 * ν) (k + 1) j hn κ ξ).differentiableAt), h]
    simp only [map_mul, map_neg, map_natCast]
    push_cast; ring

end Lightlike.Lorentz.SL2RPlancherel

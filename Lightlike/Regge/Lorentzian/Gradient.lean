import Lightlike.Regge.Lorentzian.ReggeEquations

/-!
# The gradient of the Lorentzian Regge action

The Lorentzian counterpart of `Lightlike/Regge/D4/Gradient.lean`. `hasDerivAt_lorReggeAction_grad`
(`Lightlike/Regge/Lorentzian/ReggeEquations.lean`) differentiates the complex Lorentzian Regge action along
every line `L + τ v` of signed squared lengths. For a finite vertex set this file proves the
stronger statement that the action is (Fréchet) differentiable on the finite-dimensional space
`Finset V → ℝ` of squared-length assignments, with derivative `v ↦ Σ_e v_e ∂S/∂L_e`.

The branches of Sorkin's angle (`arcosh`, `−arcosh(−·)`, `arsinh`) and of the timelike dihedral
angle (`arccos(−·)`) are differentiable where they are used, and the branch, the number of light
rays and the causal factor `Z_t` are locally constant in a neighbourhood of non-degenerate
Lorentzian squared lengths, not only along lines.

## Main results

* `differentiableAt_sorkinAngle`: Sorkin's angle of differentiable Gram data with `a b ≠ 0` and
  `a b < m²` is differentiable.
* `differentiableAt_lorDihedral4`: the Lorentzian dihedral angle is differentiable in the squared
  lengths at a non-null hinge of a Lorentzian 4-simplex with non-null tetrahedra.
* `differentiableAt_lorReggeAction`: the Lorentzian Regge action is differentiable at
  non-degenerate Lorentzian squared lengths.
* `hasFDerivAt_lorReggeAction` (**the Lorentzian Regge equations, gradient form**): its derivative
  is `lorReggeGradient K L`, the real-linear functional `v ↦ Σ_e v_e ∂S/∂L_e` with complex values.
-/

open Real Finset Filter Topology

namespace Lightlike.ReggeLor

open Lightlike.FourD (Complex4)
open Lightlike.FourD.Complex4 (mem_faces)
open Lightlike.Regge4 (det3 lineL exists_label4 intTris4 bdryTris4)

/-! ## Sorkin's angle on a normed space -/

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b m : F → ℝ} {x : F}

/-- The ratio `m / √(c a b)` is differentiable where `c a b > 0`. -/
theorem differentiableAt_ratio (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hm : DifferentiableAt ℝ m x) {c : ℝ} (hc : 0 < c * (a x * b x)) :
    DifferentiableAt ℝ (fun y => m y / √(c * (a y * b y))) x := by
  have hs := ((ha.fun_mul hb).const_mul c).sqrt hc.ne'
  simpa only [div_eq_mul_inv] using hm.fun_mul (hs.fun_inv (Real.sqrt_pos.mpr hc).ne')

/-- **The boost part is differentiable** for differentiable Gram data with `a b ≠ 0` and
`a b < m²`. -/
theorem differentiableAt_boostPart (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hm : DifferentiableAt ℝ m x) (hP : a x * b x ≠ 0) (hgap : a x * b x < m x ^ 2) :
    DifferentiableAt ℝ (fun y => boostPart (a y) (b y) (m y)) x := by
  have hc : ContinuousAt (fun y => a y * b y) x := ha.continuousAt.mul hb.continuousAt
  rcases hP.lt_or_gt with hn | hp
  · have hK := differentiableAt_ratio ha hb hm (c := -1) (by linarith)
    simp only [neg_one_mul] at hK
    refine hK.arsinh.congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually (gt_mem_nhds hn)] with y h1
    have h1' : a y * b y < 0 := h1
    simp only [boostPart, not_lt.mpr h1'.le, h1', ↓reduceIte]
  · have hK := differentiableAt_ratio ha hb hm (c := 1) (by simpa using hp)
    simp only [one_mul] at hK
    have hsP : 0 < √(a x * b x) := Real.sqrt_pos.mpr hp
    have hm0 : m x ≠ 0 := fun h => by
      have := hp.trans hgap
      simp [h] at this
    rcases hm0.lt_or_gt with hmn | hmp
    · have hκ : 1 < -m x / √(a x * b x) := by
        rw [one_lt_div hsP, Real.sqrt_lt' (by linarith), neg_sq]
        exact hgap
      have hK' : DifferentiableAt ℝ (fun y => -m y / √(a y * b y)) x := by
        simpa only [neg_div] using hK.fun_neg
      refine ((hasDerivAt_arcosh hκ).differentiableAt.comp x hK').neg.congr_of_eventuallyEq ?_
      filter_upwards [hc.eventually (lt_mem_nhds hp),
        hm.continuousAt.eventually (gt_mem_nhds hmn)] with y h1 h2
      have h1' : 0 < a y * b y := h1
      simp only [boostPart, h1', not_lt.mpr h2.le, ↓reduceIte, Function.comp_apply, Pi.neg_apply]
    · have hκ : 1 < m x / √(a x * b x) := by
        rw [one_lt_div hsP, Real.sqrt_lt' hmp]
        exact hgap
      refine ((hasDerivAt_arcosh hκ).differentiableAt.comp x hK).congr_of_eventuallyEq ?_
      filter_upwards [hc.eventually (lt_mem_nhds hp),
        hm.continuousAt.eventually (lt_mem_nhds hmp)] with y h1 h2
      have h1' : 0 < a y * b y := h1
      simp only [boostPart, h1', h2, ↓reduceIte, Function.comp_apply]

omit [NormedSpace ℝ F] in
/-- The number of light rays in the wedge is locally constant for continuous Gram data of two
non-null vectors (`a b ≠ 0`) that are not orthogonal when of the same causal type. -/
theorem eventually_lightRays_nhds (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hm : ContinuousAt m x) (hP : a x * b x ≠ 0) (hm0 : 0 < a x * b x → m x ≠ 0) :
    ∀ᶠ y in 𝓝 x, lightRays (a y) (b y) (m y) = lightRays (a x) (b x) (m x) := by
  have hc : ContinuousAt (fun y => a y * b y) x := ha.mul hb
  have hd : ContinuousAt (fun y => a y * m y) x := ha.mul hm
  rcases hP.lt_or_gt with hn | hp
  · filter_upwards [hc.eventually (gt_mem_nhds hn)] with y h1
    have h1' : a y * b y < 0 := h1
    simp only [lightRays, h1', hn, not_lt.mpr h1'.le, not_lt.mpr hn.le, ↓reduceIte]
  · have hd0 : a x * m x ≠ 0 := mul_ne_zero (left_ne_zero_of_mul hp.ne') (hm0 hp)
    rcases hd0.lt_or_gt with hdn | hdp
    · filter_upwards [hc.eventually (lt_mem_nhds hp), hd.eventually (gt_mem_nhds hdn)]
        with y h1 h2
      have h1' : 0 < a y * b y := h1
      have h2' : a y * m y < 0 := h2
      simp only [lightRays, h1', hp, not_lt.mpr h2'.le, not_lt.mpr hdn.le, ↓reduceIte]
    · filter_upwards [hc.eventually (lt_mem_nhds hp), hd.eventually (lt_mem_nhds hdp)]
        with y h1 h2
      have h1' : 0 < a y * b y := h1
      have h2' : 0 < a y * m y := h2
      simp only [lightRays, h1', hp, h2', hdp, ↓reduceIte]

/-- **Sorkin's angle is differentiable** for differentiable Gram data with `a b ≠ 0` and
`a b < m²`: its imaginary part is locally constant. -/
theorem differentiableAt_sorkinAngle (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hm : DifferentiableAt ℝ m x) (hP : a x * b x ≠ 0) (hgap : a x * b x < m x ^ 2) :
    DifferentiableAt ℝ (fun y => sorkinAngle (a y) (b y) (m y)) x := by
  have hm0 : 0 < a x * b x → m x ≠ 0 := fun hp h => by
    have := hp.trans hgap
    simp [h] at this
  have hL := eventually_lightRays_nhds ha.continuousAt hb.continuousAt hm.continuousAt hP hm0
  have hB := Complex.ofRealCLM.differentiableAt.comp x (differentiableAt_boostPart ha hb hm hP hgap)
  refine (hB.sub_const (((π / 2 * (lightRays (a x) (b x) (m x) : ℝ) : ℝ) : ℂ) *
    Complex.I)).congr_of_eventuallyEq ?_
  filter_upwards [hL] with y hy
  simp only [sorkinAngle, hy, Function.comp, Complex.ofRealCLM_apply]

end Calculus

/-! ## Differentiability in the squared lengths -/

section Lengths

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Signed squared lengths are differentiable functions of the squared-length assignment. -/
@[fun_prop] theorem differentiable_sqL (a b : V) :
    Differentiable ℝ fun m : Finset V → ℝ => sqL m a b := by
  by_cases h : a = b
  · subst h
    simp only [sqL_self]
    fun_prop
  · simp only [sqL_of_ne _ h]
    fun_prop

/-- **The Lorentzian dihedral angle is differentiable in the squared lengths** at a Lorentzian
4-simplex (`gram4L < 0`) with a non-null hinge `pqr` and non-null tetrahedra `pqrs`, `pqru`, for
both causal types of the hinge. -/
theorem differentiableAt_lorDihedral4 {L : Finset V → ℝ} {p q r s u : V}
    (hs : gram3L L p q r s ≠ 0) (hu : gram3L L p q r u ≠ 0) (h2 : gram2L L p q r ≠ 0)
    (h4 : gram4L L p q r s u < 0) :
    DifferentiableAt ℝ (fun m => lorDihedral4 m p q r s u) L := by
  have hM : Differentiable ℝ (fun m : Finset V → ℝ => mixedL m p q r s u) := by
    unfold mixedL det3 ipL
    fun_prop
  have hGs : Differentiable ℝ (fun m : Finset V → ℝ => gram3L m p q r s) := by
    unfold gram3L det3 ipL
    fun_prop
  have hGu : Differentiable ℝ (fun m : Finset V → ℝ => gram3L m p q r u) := by
    unfold gram3L det3 ipL
    fun_prop
  have hc : ContinuousAt (fun m : Finset V → ℝ => gram2L m p q r) L := by
    have : Differentiable ℝ (fun m : Finset V → ℝ => gram2L m p q r) := by
      unfold gram2L ipL
      fun_prop
    exact this.continuous.continuousAt
  have hdj := desnanot_jacobiL L p q r s u
  rcases h2.lt_or_gt with h2n | h2p
  · -- a timelike hinge: the Euclidean angle `arccos (−M / √(G_s G_u))`
    have hpos := mul_pos_of_neg_of_neg h2n h4
    have hgap : mixedL L p q r s u ^ 2 < gram3L L p q r s * gram3L L p q r u := by linarith
    have hP : 0 < gram3L L p q r s * gram3L L p q r u := lt_of_le_of_lt (sq_nonneg _) hgap
    have hK := differentiableAt_ratio (hGs L) (hGu L) (hM L).fun_neg (c := 1) (by simpa using hP)
    simp only [one_mul] at hK
    have hsq1 : (-mixedL L p q r s u / √(gram3L L p q r s * gram3L L p q r u)) ^ 2 < 1 := by
      rw [div_pow, Real.sq_sqrt hP.le, div_lt_one hP, neg_sq]
      exact hgap
    have hbd := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hsq1)
    have hA := (Real.differentiableAt_arccos.mpr ⟨hbd.1.ne', hbd.2.ne⟩).comp L hK
    refine (Complex.ofRealCLM.differentiableAt.comp L hA).congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually (gt_mem_nhds h2n)] with m hm
    have hm' : gram2L m p q r < 0 := hm
    simp only [lorDihedral4, hm', not_lt.mpr hm'.le, ↓reduceIte, Function.comp,
      Complex.ofRealCLM_apply]
  · -- a spacelike hinge: Sorkin's angle
    have hneg := mul_neg_of_pos_of_neg h2p h4
    refine (differentiableAt_sorkinAngle (hGs L) (hGu L) (hM L) (mul_ne_zero hs hu)
      (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually (lt_mem_nhds h2p)] with m hm
    have hm' : 0 < gram2L m p q r := hm
    simp only [lorDihedral4, hm', ↓reduceIte]

omit [DecidableEq V] in
/-- Areas are differentiable in the squared lengths at a non-null triangle. -/
theorem differentiableAt_lorArea {L : Finset V → ℝ} {t : Finset V} (h : triHL L t ≠ 0) :
    DifferentiableAt ℝ (fun m => lorArea m t) L := by
  have hH : DifferentiableAt ℝ (fun m : Finset V → ℝ => triHL m t) L := by
    unfold triHL
    fun_prop
  simpa only [lorArea, div_eq_mul_inv] using ((hH.abs h).sqrt (abs_pos.mpr h).ne').mul_const (4 : ℝ)⁻¹

omit [DecidableEq V] in
/-- The causal type of a non-null triangle is locally constant in the squared lengths. -/
theorem eventually_causalZ_nhds {L : Finset V → ℝ} {t : Finset V} (h : triHL L t ≠ 0) :
    ∀ᶠ m in 𝓝 L, causalZ m t = causalZ L t := by
  have hc : ContinuousAt (fun m : Finset V → ℝ => triHL m t) L := by
    have : Differentiable ℝ (fun m : Finset V → ℝ => triHL m t) := by
      unfold triHL
      fun_prop
    exact this.continuous.continuousAt
  rcases lt_or_gt_of_ne h with hn | hp
  · filter_upwards [hc.eventually (gt_mem_nhds hn)] with m hm
    have hm' : triHL m t < 0 := hm
    simp only [causalZ, lt_asymm hm', lt_asymm hn, ↓reduceIte]
  · filter_upwards [hc.eventually (lt_mem_nhds hp)] with m hm
    have hm' : 0 < triHL m t := hm
    simp only [causalZ, hm', hp, ↓reduceIte]

omit [DecidableEq V] in
/-- `A_t Z_t` is differentiable in the squared lengths at a non-null triangle. -/
theorem differentiableAt_area_causalZ {L : Finset V → ℝ} {t : Finset V} (h : triHL L t ≠ 0) :
    DifferentiableAt ℝ (fun m => (lorArea m t : ℂ) * causalZ m t) L := by
  refine ((Complex.ofRealCLM.differentiableAt.comp L (differentiableAt_lorArea h)).mul_const
    (causalZ L t)).congr_of_eventuallyEq ?_
  filter_upwards [eventually_causalZ_nhds h] with m hm
  simp only [hm, Function.comp, Complex.ofRealCLM_apply]

/-- One 4-simplex's area-weighted sum of Lorentzian dihedral angles is differentiable in the
squared lengths. -/
theorem differentiableAt_lorSimpSum4 {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) {σ : Finset V} (hσ : σ ∈ K.simps) :
    DifferentiableAt ℝ (fun m => ∑ t ∈ σ.powersetCard 3,
      (lorArea m t : ℂ) * lorDihedralAt m σ t) L := by
  refine DifferentiableAt.fun_sum fun t ht => ?_
  obtain ⟨hts, ht3⟩ := mem_powersetCard.mp ht
  refine (Complex.ofRealCLM.differentiableAt.comp L
    (differentiableAt_lorArea (hK.tri t (mem_faces.mpr ⟨σ, hσ, hts, ht3⟩)))).mul ?_
  obtain ⟨a, b, c, x, y, hab, hac, hax, hay, hbc, hbx, hby, hcx, hcy, hxy, rfl, rfl⟩ :=
    exists_label4 (K.card_eq σ hσ) ht3 hts
  have hfun : (fun m => lorDihedralAt m {a, b, c, x, y} {a, b, c}) =
      fun m => lorDihedral4 m a b c x y :=
    funext fun m => lorDihedralAt_eq m hab hac hax hay hbc hbx hby hcx hcy hxy
  have hnd := hK.lorNondeg4 hab hac hax hay hbc hbx hby hcx hcy hxy hσ
  rw [hfun]
  exact differentiableAt_lorDihedral4 hnd.f_u hnd.f_s hnd.t₁ hnd.g4

/-- **The Lorentzian Regge action is differentiable** at non-degenerate Lorentzian squared
lengths, as a function on the finite-dimensional space of squared-length assignments. -/
theorem differentiableAt_lorReggeAction {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) : DifferentiableAt ℝ (lorReggeAction K) L := by
  have : lorReggeAction K = fun m =>
      ∑ t ∈ intTris4 K, 2 * π * ((lorArea m t : ℂ) * causalZ m t) +
      ∑ t ∈ bdryTris4 K, π * ((lorArea m t : ℂ) * causalZ m t) -
      ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, (lorArea m t : ℂ) * lorDihedralAt m σ t :=
    funext (lorReggeAction_eq_sum_simps K)
  rw [this]
  exact ((DifferentiableAt.fun_sum fun t ht =>
      (differentiableAt_area_causalZ (hK.tri t (mem_filter.mp ht).1)).const_mul
        (2 * π : ℂ)).add
    (DifferentiableAt.fun_sum fun t ht =>
      (differentiableAt_area_causalZ (hK.tri t (mem_filter.mp ht).1)).const_mul (π : ℂ))).sub
    (DifferentiableAt.fun_sum fun σ hσ => differentiableAt_lorSimpSum4 hK hσ)

/-- The gradient of the Lorentzian Regge action at the squared lengths `L`: the real-linear
functional `v ↦ Σ_e v_e ∂S/∂L_e`, with complex values, on variations of the squared lengths. -/
noncomputable def lorReggeGradient (K : Complex4 V) (L : Finset V → ℝ) :
    (Finset V → ℝ) →L[ℝ] ℂ :=
  ∑ e ∈ K.edges, (ContinuousLinearMap.proj e : (Finset V → ℝ) →L[ℝ] ℝ).smulRight
    (lorReggePartial K L e)

omit [Fintype V] in
/-- The gradient applied to a variation `v`. -/
theorem lorReggeGradient_apply [Fintype V] (K : Complex4 V) (L v : Finset V → ℝ) :
    lorReggeGradient K L v = ∑ e ∈ K.edges, (v e : ℂ) * lorReggePartial K L e := by
  simp [lorReggeGradient, Complex.real_smul]

/-- **The Lorentzian Regge equations, gradient form.** At non-degenerate Lorentzian squared
lengths the complex Lorentzian Regge action is differentiable on the space of squared-length
assignments, and its derivative is `lorReggeGradient`:
`∂S/∂L_e = Σ_{t ∋ e} (∂A_t/∂L_e) (ε_t or π Z_t − Σ θ)`. -/
theorem hasFDerivAt_lorReggeAction {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) :
    HasFDerivAt (lorReggeAction K) (lorReggeGradient K L) L := by
  have hd := (differentiableAt_lorReggeAction hK).hasFDerivAt
  convert hd using 1
  refine ContinuousLinearMap.ext fun v => ?_
  have hline : HasDerivAt (fun τ : ℝ => L + τ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add L
  have h1 := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have h2 := hasDerivAt_lorReggeAction_grad hK v
  have hfun : (lorReggeAction K ∘ fun τ : ℝ => L + τ • v) =
      fun τ => lorReggeAction K (lineL L v τ) := by
    funext τ
    simp only [Function.comp]
    congr 1
  rw [hfun] at h1
  rw [lorReggeGradient_apply, h2.unique h1]

end Lengths

end Lightlike.ReggeLor

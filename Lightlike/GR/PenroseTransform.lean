import Lightlike.GR.ZeroRestMass

/-!
# The Penrose transform by contour integrals

A point `x` of complexified Minkowski space is a line `X ≅ CP¹` of twistor space, on which
`μ^{α̇} = x^{βα̇} λ_β` (Adamo (3.28)). Along a section `λ(z)` of `X` over a circle `C(c, R)` the
Penrose transform of a twistor function `f(μ, λ)` is the contour integral
`φ_{α₁⋯α_{n+1}}(x) = ∮ ⟨λ dλ⟩ λ_{α₁} ⋯ λ_{α_{n+1}} f(μ(x, λ), λ)` (helicity `h = -(n + 1)/2`, Adamo (3.40)),
`φ(x) = ∮ ⟨λ dλ⟩ f(μ(x, λ), λ)` (helicity `0`, (3.41)), and
`φ̃_{α̇₁⋯α̇_{n+1}}(x) = ∮ ⟨λ dλ⟩ ∂^{n+1} f/∂μ^{α̇₁} ⋯ ∂μ^{α̇_{n+1}}` (helicity `(n + 1)/2`, (3.42)).

* `hasFDerivAt_circleIntegral_twistorPt`, `pd_circleIntegral_twistorPt`: differentiation under the
  contour integral, for `f` holomorphic (`C¹`) on an open set containing the twistor points of the
  contour: `∂_{γδ̇} ∮ w f(μ(x, λ), λ) = ∮ w λ_γ ∂f/∂μ^{δ̇}`.
* **The transform is a z.r.m. field** (`penroseNeg_isZrmNeg`, `penroseScalar_isZrmScalar`,
  `penrosePos_isZrmPos`): the integrand computation (3.30), `∂^{α₁α̇} (λ_{α₁} ⋯ f) = λ^{α₁} λ_{α₁} (⋯) = 0`,
  under the integral sign; for `h > 0`, `∂^{βα̇₁} ∂_{μ^{α̇₁}} ⋯ f = λ^β ε^{α̇₁δ̇} ∂_{μ^{δ̇}} ∂_{μ^{α̇₁}} ⋯ f = 0`
  because holomorphic derivatives commute (`iteratedFDeriv_cons_swap`).
* **Helicity ↔ homogeneity** (`penroseNeg_integrand_rescale`, `penroseScalar_integrand_rescale`,
  `penrosePos_integrand_rescale`, and `penroseNeg_rescale`, `penroseScalar_rescale`, `penrosePos_rescale`):
  rescaling the section, `λ ↦ s λ`, multiplies the integrand by `s ^ (2 + (n + 1) + d)`, `s ^ (2 + d)`,
  `s ^ (2 + d - (n + 1))` for `f` homogeneous of degree `d`; for `d = 2h - 2` the transform does not
  depend on the section.

Helicity follows Adamo (3.15), p. 25: `h < 0` fields carry undotted indices, `h > 0` dotted ones.
Twistor functions are functions of `(μ, λ) ∈ ℂ² × ℂ²` (non-projective twistor space); "holomorphic" is
`C¹` (`h ≤ 0`, Mathlib's complex `C¹`) or analytic (`h > 0`, for the symmetry of iterated derivatives).

## References

* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196: helicity conventions (3.15), p. 25
  (`h < 0`: undotted indices); §3.2, pp. 27–30: the integral formula (3.26)–(3.29), the measure
  `⟨λ dλ⟩` "of projective weight +2", the weight `-2s - 2` of `f` (3.27), the restriction (3.28), the
  computation (3.30), the transform (3.39) with weight `2h - 2` and the integral formulae (3.40)–(3.42);
  `⟨κ ω⟩ = κ^α ω_α` (1.10), p. 6.
* M. Atiyah, M. Dunajski, L. Mason, *Twistor theory at fifty*, arXiv:1704.07464: the contour integral
  formula (1.1), p. 3 ("the most elementary of Penrose's series of twistor integral formulae for
  massless fields"), and its twistor reading, §2.3, pp. 8–9 (`f` homogeneous of degree `-2` restricted
  to the line `L_p` and integrated along a contour `Γ ⊂ L_p`).
* M. Wolf, *A First Course on Twistors, Integrability and Gluon Scattering Amplitudes*,
  arXiv:1001.3871v2, §2.1: the contour formulae (2.1)–(2.2) (`h = 0`), p. 11, and (2.3)–(2.6) (`h ≠ 0`),
  p. 12; Exercise 2.1, p. 12 (`f = 1/(z¹z²)` gives the elementary solution, `penroseScalar_elementary`).

Convention (against Wolf): Wolf's twistor `(z^α, λ_α̇)`, `z^α = x^{αβ̇} λ_β̇`, has the chirality opposite
to Adamo's `(μ^{α̇}, λ_α)`; exchanging dotted and undotted indices, Wolf's (2.3) is `penroseNeg` and
(2.5) is `penrosePos`, and Wolf's helicity `h` is `-h` here (helicity as Adamo (3.15)); the homogeneities
agree, `-2h - 2 = 2(-h) - 2`. Wolf's normalisation `-1/(2πi)` is omitted.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Spinor

/-- A point `Z = (μ^{α̇}, λ_α)` of (non-projective) twistor space. -/
abbrev TwistorPair := (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- The incidence relation `μ^{α̇} = x^{βα̇} λ_β` (Adamo (3.28)). -/
def incid (x : SpinorCoord) (l : Fin 2 → ℂ) : Fin 2 → ℂ := fun α' => ∑ β, x β α' * l β

/-- `x ↦ μ(x, λ)` as a continuous linear map. -/
def incidL (l : Fin 2 → ℂ) : SpinorCoord →L[ℂ] (Fin 2 → ℂ) :=
  ∑ β, l β • (ContinuousLinearMap.proj β : SpinorCoord →L[ℂ] (Fin 2 → ℂ))

lemma incidL_apply (l : Fin 2 → ℂ) (x : SpinorCoord) : incidL l x = incid x l := by
  funext α'
  simp [incidL, incid, mul_comm]

lemma continuous_incidL : Continuous incidL :=
  continuous_finsetSum _ fun β _ => (continuous_apply β).smul continuous_const

lemma incidL_coordVec (l : Fin 2 → ℂ) (γ δ' : Fin 2) :
    incidL l (coordVec γ δ') = l γ • (Pi.single δ' (1 : ℂ) : Fin 2 → ℂ) := by
  rw [incidL_apply]
  funext α'
  fin_cases γ <;> fin_cases δ' <;> fin_cases α' <;>
    simp [incid, coordVec, Fin.sum_univ_two, Pi.single_apply]

lemma incid_smul (x : SpinorCoord) (s : ℂ) (l : Fin 2 → ℂ) : incid x (s • l) = s • incid x l := by
  funext α'
  simp only [incid, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

/-- `⟨κ ν⟩ = κ^α ν_α = ε^{αβ} κ_β ν_α` (Adamo (1.7), (1.10)). -/
def angle (κ ν : Fin 2 → ℂ) : ℂ := ∑ α, ∑ β, eps α β * κ β * ν α

lemma angle_smul_add (s t : ℂ) (κ ν : Fin 2 → ℂ) :
    angle (s • κ) (s • ν + t • κ) = s ^ 2 * angle κ ν := by
  simp only [angle, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The twistor point `(μ(x, λ(z)), λ(z))` over `x` and `z`. -/
def twistorPt (l : ℂ → Fin 2 → ℂ) (x : SpinorCoord) (z : ℂ) : TwistorPair := (incid x (l z), l z)

lemma twistorPt_eq (l : ℂ → Fin 2 → ℂ) (z : ℂ) :
    (fun x => twistorPt l x z) = fun x => (incidL (l z) x, l z) := by
  funext x
  simp [twistorPt, incidL_apply]

lemma continuousOn_twistorPt {l : ℂ → Fin 2 → ℂ} {S : Set ℂ} (hl : ContinuousOn l S) :
    ContinuousOn (fun p : SpinorCoord × ℂ => twistorPt l p.1 p.2) (univ ×ˢ S) := by
  have h : ContinuousOn (fun p : SpinorCoord × ℂ => l p.2) (univ ×ˢ S) :=
    hl.comp continuousOn_snd fun p hp => hp.2
  have e : (fun p : SpinorCoord × ℂ => twistorPt l p.1 p.2) =
      fun p => (incidL (l p.2) p.1, l p.2) := by
    funext p; simp [twistorPt, incidL_apply]
  rw [e]
  exact ((continuous_incidL.comp_continuousOn h).clm_apply continuousOn_fst).prodMk h

lemma circleIntegral_clm_apply {L : ℂ → SpinorCoord →L[ℂ] ℂ} {c : ℂ} {R : ℝ}
    (hL : CircleIntegrable L c R) (v : SpinorCoord) :
    (∮ z in C(c, R), L z) v = ∮ z in C(c, R), L z v := by
  simp only [circleIntegral]
  rw [ContinuousLinearMap.intervalIntegral_apply ((circleIntegrable_iff R).1 hL)]
  rfl

lemma circleIntegral_finset_sum_mul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (A : ι → ℂ → ℂ)
    {c : ℂ} {R : ℝ} (hA : ∀ i ∈ s, ContinuousOn (A i) (sphere c |R|)) :
    ∑ i ∈ s, a i * ∮ z in C(c, R), A i z = ∮ z in C(c, R), ∑ i ∈ s, a i * A i z := by
  rw [circleIntegral.integral_fun_sum (f := fun i z => a i * A i z)
    fun i hi => (continuousOn_const.mul (hA i hi)).circleIntegrable']
  simp only [circleIntegral.integral_const_mul]

section Differentiation

variable {G : TwistorPair → ℂ} {W : Set TwistorPair} {w : ℂ → ℂ} {l : ℂ → Fin 2 → ℂ} {c : ℂ}
  {R : ℝ} {U : Set SpinorCoord}

/-- The derivative in `x` of the integrand `w(z) G(μ(x, λ(z)), λ(z))`. -/
def integrandDeriv (G : TwistorPair → ℂ) (w : ℂ → ℂ) (l : ℂ → Fin 2 → ℂ) (x : SpinorCoord) (z : ℂ) :
    SpinorCoord →L[ℂ] ℂ :=
  w z • (fderiv ℂ G (twistorPt l x z)).comp
    ((ContinuousLinearMap.inl ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).comp (incidL (l z)))

lemma continuousOn_integrand (hG : ContDiffOn ℂ 1 G W) (hw : ContinuousOn w (sphere c |R|))
    (hl : ContinuousOn l (sphere c |R|))
    (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W) :
    ContinuousOn (fun p : SpinorCoord × ℂ => w p.2 * G (twistorPt l p.1 p.2))
      (U ×ˢ sphere c |R|) :=
  (hw.comp continuousOn_snd fun _ hp => hp.2).mul
    (hG.continuousOn.comp ((continuousOn_twistorPt hl).mono (prod_mono (subset_univ _) le_rfl))
      fun p hp => hUW p.1 hp.1 p.2 hp.2)

lemma continuousOn_integrandDeriv (hW : IsOpen W) (hG : ContDiffOn ℂ 1 G W)
    (hw : ContinuousOn w (sphere c |R|)) (hl : ContinuousOn l (sphere c |R|))
    (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W) :
    ContinuousOn (fun p : SpinorCoord × ℂ => integrandDeriv G w l p.1 p.2) (U ×ˢ sphere c |R|) := by
  have hG' : ContinuousOn (fderiv ℂ G) W := hG.continuousOn_fderiv_of_isOpen hW le_rfl
  have hl' : ContinuousOn (fun p : SpinorCoord × ℂ => l p.2) (U ×ˢ sphere c |R|) :=
    hl.comp continuousOn_snd fun p hp => hp.2
  exact (hw.comp continuousOn_snd fun p hp => hp.2).smul
    ((hG'.comp ((continuousOn_twistorPt hl).mono (prod_mono (subset_univ _) le_rfl))
      fun p hp => hUW p.1 hp.1 p.2 hp.2).clm_comp
      (continuousOn_const.clm_comp (continuous_incidL.comp_continuousOn hl')))

lemma hasFDerivAt_integrand (hW : IsOpen W) (hG : ContDiffOn ℂ 1 G W) {x : SpinorCoord} {z : ℂ}
    (hxz : twistorPt l x z ∈ W) :
    HasFDerivAt (fun x => w z * G (twistorPt l x z)) (integrandDeriv G w l x z) x := by
  have hd : DifferentiableAt ℂ G (twistorPt l x z) :=
    (hG.differentiableOn one_ne_zero).differentiableAt (hW.mem_nhds hxz)
  have hΦ : HasFDerivAt (fun x => twistorPt l x z)
      ((ContinuousLinearMap.inl ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).comp (incidL (l z))) x := by
    rw [twistorPt_eq]
    exact ((incidL (l z)).hasFDerivAt.prodMk (hasFDerivAt_const (l z) x)).congr_fderiv
      (by ext v <;> simp)
  exact (hd.hasFDerivAt.comp x hΦ).const_mul (w z)

/-- **Differentiation under the contour integral**: for `G` holomorphic (`C¹`) on an open set `W`
containing the twistor points `(μ(x, λ(z)), λ(z))` of `x ∈ U` and `z` on the circle. -/
theorem hasFDerivAt_circleIntegral_twistorPt (hW : IsOpen W) (hG : ContDiffOn ℂ 1 G W)
    (hw : ContinuousOn w (sphere c |R|)) (hl : ContinuousOn l (sphere c |R|)) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W) {x₀ : SpinorCoord} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∮ z in C(c, R), w z * G (twistorPt l x z))
      (∮ z in C(c, R), integrandDeriv G w l x₀ z) x₀ := by
  have hg := continuousOn_integrand hG hw hl hUW
  have hg' := continuousOn_integrandDeriv hW hG hw hl hUW
  have hs1 : ∀ x ∈ U, ContinuousOn (fun z => w z * G (twistorPt l x z)) (sphere c |R|) :=
    fun x hx => hg.comp (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨hx, hz⟩
  have hs2 : ContinuousOn (fun z => integrandDeriv G w l x₀ z) (sphere c |R|) :=
    hg'.comp (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨hx₀, hz⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hKU : closedBall x₀ (r / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ (r / 2)).prod (isCompact_sphere c |R|)).exists_bound_of_continuousOn
    (hg'.mono (prod_mono hKU le_rfl))
  refine hasFDerivAt_circleIntegral_of_dominated_of_fderiv_le (s := ball x₀ (r / 2))
    (bound := fun _ => C) (ball_mem_nhds x₀ (half_pos hr)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.eventually_of_mem (hU.mem_nhds hx₀) fun x hx =>
      ((hs1 x hx).comp_continuous (continuous_circleMap c R)
        fun θ => circleMap_mem_sphere' c R θ).aestronglyMeasurable
  · exact (hs1 x₀ hx₀).circleIntegrable'
  · exact (hs2.comp_continuous (continuous_circleMap c R)
      fun θ => circleMap_mem_sphere' c R θ).aestronglyMeasurable
  · exact fun z hz x hx => hC (x, z) ⟨ball_subset_closedBall hx, hz⟩
  · exact continuousOn_const.circleIntegrable'
  · exact fun z hz x hx => hasFDerivAt_integrand hW hG
      (hUW x (hKU (ball_subset_closedBall hx)) z hz)

lemma integrandDeriv_coordVec (G : TwistorPair → ℂ) (w : ℂ → ℂ) (l : ℂ → Fin 2 → ℂ)
    (x : SpinorCoord) (z : ℂ) (γ δ' : Fin 2) :
    integrandDeriv G w l x z (coordVec γ δ') =
      (w z * l z γ) * fderiv ℂ G (twistorPt l x z) (Pi.single δ' 1, 0) := by
  have e : (l z γ • (Pi.single δ' (1 : ℂ) : Fin 2 → ℂ), (0 : Fin 2 → ℂ)) =
      l z γ • ((Pi.single δ' (1 : ℂ) : Fin 2 → ℂ), (0 : Fin 2 → ℂ)) := by simp
  change w z * fderiv ℂ G (twistorPt l x z) (incidL (l z) (coordVec γ δ'), 0) = _
  rw [incidL_coordVec, e, map_smul, smul_eq_mul]
  ring

/-- `∂_{γδ̇} ∮ w G(μ(x, λ), λ) = ∮ (w λ_γ) ∂G/∂μ^{δ̇}`. -/
theorem pd_circleIntegral_twistorPt (hW : IsOpen W) (hG : ContDiffOn ℂ 1 G W)
    (hw : ContinuousOn w (sphere c |R|)) (hl : ContinuousOn l (sphere c |R|)) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W) {x₀ : SpinorCoord} (hx₀ : x₀ ∈ U)
    (γ δ' : Fin 2) :
    pd (fun x => ∮ z in C(c, R), w z * G (twistorPt l x z)) γ δ' x₀ =
      ∮ z in C(c, R), (w z * l z γ) * fderiv ℂ G (twistorPt l x₀ z) (Pi.single δ' 1, 0) := by
  have hint : CircleIntegrable (integrandDeriv G w l x₀) c R :=
    ((continuousOn_integrandDeriv hW hG hw hl hUW).comp
      (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨hx₀, hz⟩).circleIntegrable'
  rw [pd, (hasFDerivAt_circleIntegral_twistorPt hW hG hw hl hU hUW hx₀).fderiv,
    circleIntegral_clm_apply hint]
  simp only [integrandDeriv_coordVec]

lemma contDiffOn_dmu {n : ℕ} {F : TwistorPair → ℂ} (hW : IsOpen W) (hF : ContDiffOn ℂ (n + 1) F W)
    (v : TwistorPair) : ContDiffOn ℂ n (fun p => fderiv ℂ F p v) W :=
  (hF.fderiv_of_isOpen hW le_rfl).clm_apply contDiffOn_const

end Differentiation

/-! ## The transform -/

/-- **The Penrose transform, helicity `-(n + 1)/2`** (Adamo (3.40); the contour form is Wolf (2.3),
with the chirality exchanged and without `-1/(2πi)`), along the section `λ(z)` over
`C(c, R)`: `φ_{α₁⋯α_{n+1}}(x) = ∮ ⟨λ dλ⟩ λ_{α₁} ⋯ λ_{α_{n+1}} f(μ(x, λ), λ)`. -/
def penroseNeg (n : ℕ) (F : TwistorPair → ℂ) (l : ℂ → Fin 2 → ℂ) (c : ℂ) (R : ℝ) :
    (Fin (n + 1) → Fin 2) → SpinorCoord → ℂ := fun i x =>
  ∮ z in C(c, R), (angle (l z) (deriv l z) * ∏ k, l z (i k)) * F (twistorPt l x z)

/-- **The Penrose transform, helicity `0`** (Adamo (3.41); ADM (1.1); Wolf (2.1)):
`φ(x) = ∮ ⟨λ dλ⟩ f(μ(x, λ), λ)`. -/
def penroseScalar (F : TwistorPair → ℂ) (l : ℂ → Fin 2 → ℂ) (c : ℂ) (R : ℝ) (x : SpinorCoord) : ℂ :=
  ∮ z in C(c, R), angle (l z) (deriv l z) * F (twistorPt l x z)

lemma continuousOn_angle {l : ℂ → Fin 2 → ℂ} (hl : ContDiff ℂ 1 l) (S : Set ℂ) :
    ContinuousOn (fun z => angle (l z) (deriv l z)) S := by
  have h1 : Continuous l := hl.continuous
  have h2 : Continuous (deriv l) := hl.continuous_deriv le_rfl
  refine Continuous.continuousOn ?_
  simp only [angle]
  fun_prop

lemma continuousOn_prod_l {l : ℂ → Fin 2 → ℂ} (hl : ContDiff ℂ 1 l) {m : ℕ} (i : Fin m → Fin 2)
    (S : Set ℂ) : ContinuousOn (fun z => ∏ k, l z (i k)) S := by
  have h1 : Continuous l := hl.continuous
  exact Continuous.continuousOn (continuous_finsetProd _ fun k _ => (continuous_apply _).comp h1)

lemma pd_penroseNeg {n : ℕ} {F : TwistorPair → ℂ} {W : Set TwistorPair} (hW : IsOpen W)
    (hF : ContDiffOn ℂ 1 F W) {l : ℂ → Fin 2 → ℂ} (hl : ContDiff ℂ 1 l) {c : ℂ} {R : ℝ}
    {U : Set SpinorCoord} (hU : IsOpen U) (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W)
    (j : Fin (n + 1) → Fin 2) {x : SpinorCoord} (hx : x ∈ U) (γ δ' : Fin 2) :
    pd (penroseNeg n F l c R j) γ δ' x =
      ∮ z in C(c, R), ((angle (l z) (deriv l z) * ∏ k, l z (j k)) * l z γ) *
        fderiv ℂ F (twistorPt l x z) (Pi.single δ' 1, 0) :=
  pd_circleIntegral_twistorPt (w := fun z => angle (l z) (deriv l z) * ∏ k, l z (j k)) hW hF
    ((continuousOn_angle hl _).mul (continuousOn_prod_l hl j _)) hl.continuous.continuousOn hU hUW
    hx γ δ'

/-- **The contour integral of helicity `-(n + 1)/2` is a z.r.m. field** (Adamo (3.30), (3.40)): for
`f` holomorphic (`C¹`) on an open set `W` containing the twistor points of the contour over `U`. -/
theorem penroseNeg_isZrmNeg (n : ℕ) {F : TwistorPair → ℂ} {W : Set TwistorPair} (hW : IsOpen W)
    (hF : ContDiffOn ℂ 1 F W) {l : ℂ → Fin 2 → ℂ} (hl : ContDiff ℂ 1 l) (c : ℂ) (R : ℝ)
    {U : Set SpinorCoord} (hU : IsOpen U) (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W) :
    IsZrmNeg n U (penroseNeg n F l c R) where
  symm σ i := by
    funext x
    simp only [penroseNeg, Function.comp_apply]
    exact congrArg (fun f : ℂ → ℂ => ∮ z in C(c, R), f z)
      (funext fun z => by rw [Equiv.prod_comp σ (fun k => l z (i k))])
  eqn β' i x hx := by
    have hw : ∀ j : Fin (n + 1) → Fin 2,
        ContinuousOn (fun z => angle (l z) (deriv l z) * ∏ k, l z (j k)) (sphere c |R|) := fun j =>
      (continuousOn_angle hl _).mul (continuousOn_prod_l hl j _)
    have hpd := fun (α γ δ' : Fin 2) => pd_penroseNeg hW hF hl hU hUW (Fin.cons α i) hx γ δ'
    have hcont : ∀ p : Fin 2 × Fin 2 × Fin 2, ContinuousOn (fun z =>
        ((angle (l z) (deriv l z) * ∏ k, l z ((Fin.cons p.1 i : Fin (n + 1) → Fin 2) k)) * l z p.2.1) *
          fderiv ℂ F (twistorPt l x z) (Pi.single p.2.2 1, 0)) (sphere c |R|) := by
      intro p
      have hF' : ContinuousOn (fun z => fderiv ℂ F (twistorPt l x z)) (sphere c |R|) :=
        (hF.continuousOn_fderiv_of_isOpen hW le_rfl).comp
          (((continuousOn_twistorPt hl.continuous.continuousOn).comp
            (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨mem_univ x, hz⟩))
          fun z hz => hUW x hx z hz
      exact ((hw _).mul ((continuous_apply p.2.1).comp hl.continuous).continuousOn).mul
        (hF'.clm_apply continuousOn_const)
    calc ∑ α, ∑ γ, ∑ δ', eps α γ * eps β' δ' * pd (penroseNeg n F l c R (Fin.cons α i)) γ δ' x
        = ∑ p : Fin 2 × Fin 2 × Fin 2, eps p.1 p.2.1 * eps β' p.2.2 * ∮ z in C(c, R),
            ((angle (l z) (deriv l z) * ∏ k, l z ((Fin.cons p.1 i : Fin (n + 1) → Fin 2) k)) * l z p.2.1) *
              fderiv ℂ F (twistorPt l x z) (Pi.single p.2.2 1, 0) := by
          simp only [Fintype.sum_prod_type, hpd]
      _ = ∮ z in C(c, R), ∑ p : Fin 2 × Fin 2 × Fin 2, eps p.1 p.2.1 * eps β' p.2.2 *
            (((angle (l z) (deriv l z) * ∏ k, l z ((Fin.cons p.1 i : Fin (n + 1) → Fin 2) k)) * l z p.2.1) *
              fderiv ℂ F (twistorPt l x z) (Pi.single p.2.2 1, 0)) :=
          circleIntegral_finset_sum_mul _ _ _ fun p _ => hcont p
      _ = ∮ z in C(c, R), (0 : ℂ) := congrArg (fun f : ℂ → ℂ => ∮ z in C(c, R), f z)
          (funext fun z => by
            simp only [Fintype.sum_prod_type, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
              Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11]
            ring)
      _ = 0 := by simp [circleIntegral]

/-- **The contour integral of helicity `0` solves the wave equation** (Adamo (3.41); ADM (1.1)–(1.2)):
for `f` holomorphic (`C²`) on an open set `W` containing the twistor points of the contour over `U`. -/
theorem penroseScalar_isZrmScalar {F : TwistorPair → ℂ} {W : Set TwistorPair} (hW : IsOpen W)
    (hF : ContDiffOn ℂ 2 F W) {l : ℂ → Fin 2 → ℂ} (hl : ContDiff ℂ 1 l) (c : ℂ) (R : ℝ)
    {U : Set SpinorCoord} (hU : IsOpen U) (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W) :
    IsZrmScalar U (penroseScalar F l c R) := by
  intro x hx
  have hl0 : ContinuousOn l (sphere c |R|) := hl.continuous.continuousOn
  have hF1 : ContDiffOn ℂ 1 F W := hF.of_le (by norm_num)
  have hw : ContinuousOn (fun z => angle (l z) (deriv l z)) (sphere c |R|) := continuousOn_angle hl _
  have hw2 : ∀ α, ContinuousOn (fun z => angle (l z) (deriv l z) * l z α) (sphere c |R|) := fun α =>
    hw.mul ((continuous_apply α).comp hl.continuous).continuousOn
  have hG2 : ∀ α', ContDiffOn ℂ 1 (fun p => fderiv ℂ F p (Pi.single α' 1, 0)) W := fun α' =>
    contDiffOn_dmu (n := 1) hW hF _
  -- the first derivatives, on `U`
  have h1 : ∀ α α', pd (penroseScalar F l c R) α α' =ᶠ[𝓝 x] fun y =>
      ∮ z in C(c, R), (angle (l z) (deriv l z) * l z α) *
        (fun p => fderiv ℂ F p (Pi.single α' 1, 0)) (twistorPt l y z) := fun α α' =>
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy =>
      pd_circleIntegral_twistorPt hW hF1 hw hl0 hU hUW hy α α'
  have h2 : ∀ α α' β β', pd (pd (penroseScalar F l c R) α α') β β' x =
      ∮ z in C(c, R), ((angle (l z) (deriv l z) * l z α) * l z β) *
        fderiv ℂ (fun p => fderiv ℂ F p (Pi.single α' 1, 0)) (twistorPt l x z) (Pi.single β' 1, 0) := by
    intro α α' β β'
    rw [pd, (h1 α α').fderiv_eq, ← pd]
    exact pd_circleIntegral_twistorPt hW (hG2 α') (hw2 α) hl0 hU hUW hx β β'
  have hcont : ∀ p : Fin 2 × Fin 2 × Fin 2 × Fin 2, ContinuousOn (fun z =>
      ((angle (l z) (deriv l z) * l z p.1) * l z p.2.2.1) *
        fderiv ℂ (fun q => fderiv ℂ F q (Pi.single p.2.1 1, 0)) (twistorPt l x z)
          (Pi.single p.2.2.2 1, 0)) (sphere c |R|) := by
    intro p
    have hF' : ContinuousOn (fun z => fderiv ℂ (fun q => fderiv ℂ F q (Pi.single p.2.1 1, 0))
        (twistorPt l x z)) (sphere c |R|) :=
      ((hG2 p.2.1).continuousOn_fderiv_of_isOpen hW le_rfl).comp
        (((continuousOn_twistorPt hl0).comp
          (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨mem_univ x, hz⟩))
        fun z hz => hUW x hx z hz
    exact ((hw2 _).mul ((continuous_apply p.2.2.1).comp hl.continuous).continuousOn).mul
      (hF'.clm_apply continuousOn_const)
  calc box (penroseScalar F l c R) x
      = ∑ p : Fin 2 × Fin 2 × Fin 2 × Fin 2, eps p.1 p.2.2.1 * eps p.2.1 p.2.2.2 *
          ∮ z in C(c, R), ((angle (l z) (deriv l z) * l z p.1) * l z p.2.2.1) *
            fderiv ℂ (fun q => fderiv ℂ F q (Pi.single p.2.1 1, 0)) (twistorPt l x z)
              (Pi.single p.2.2.2 1, 0) := by
        simp only [box, Fintype.sum_prod_type, h2, Fin.sum_univ_two]
        ring
    _ = ∮ z in C(c, R), ∑ p : Fin 2 × Fin 2 × Fin 2 × Fin 2, eps p.1 p.2.2.1 * eps p.2.1 p.2.2.2 *
          (((angle (l z) (deriv l z) * l z p.1) * l z p.2.2.1) *
            fderiv ℂ (fun q => fderiv ℂ F q (Pi.single p.2.1 1, 0)) (twistorPt l x z)
              (Pi.single p.2.2.2 1, 0)) :=
        circleIntegral_finset_sum_mul _ _ _ fun p _ => hcont p
    _ = ∮ z in C(c, R), (0 : ℂ) := congrArg (fun f : ℂ → ℂ => ∮ z in C(c, R), f z)
        (funext fun z => by
          simp only [Fintype.sum_prod_type, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11]
          ring)
    _ = 0 := by simp [circleIntegral]

/-! ## Helicity and homogeneity -/

lemma prod_smul_l {m : ℕ} (s : ℂ) (l : Fin 2 → ℂ) (i : Fin m → Fin 2) :
    ∏ k, (s • l) (i k) = s ^ m * ∏ k, l (i k) := by
  simp [Finset.prod_mul_distrib, Finset.prod_const]

lemma twistorPt_smul (s : ℂ → ℂ) (l : ℂ → Fin 2 → ℂ) (x : SpinorCoord) (z : ℂ) :
    twistorPt (fun z => s z • l z) x z = s z • twistorPt l x z := by
  simp [twistorPt, incid_smul]

/-- **The homogeneity count of the integrand**: for `f` homogeneous of degree `d` and the section
rescaled to `s λ`, the integrand of `penroseNeg` is multiplied by `s ^ ((n + 1) + d + 2)` (`⟨λ dλ⟩`
has weight `2`, Adamo p. 27). -/
theorem penroseNeg_integrand_rescale {n : ℕ} {F : TwistorPair → ℂ} {d : ℤ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ d * F p) {s : ℂ → ℂ}
    {l : ℂ → Fin 2 → ℂ} {z : ℂ} (hs : s z ≠ 0) (hsd : DifferentiableAt ℂ s z)
    (hld : DifferentiableAt ℂ l z) (i : Fin (n + 1) → Fin 2) (x : SpinorCoord) :
    (angle ((fun z => s z • l z) z) (deriv (fun z => s z • l z) z) *
        ∏ k, (fun z => s z • l z) z (i k)) * F (twistorPt (fun z => s z • l z) x z) =
      s z ^ (((n : ℤ) + 1) + d + 2) *
        ((angle (l z) (deriv l z) * ∏ k, l z (i k)) * F (twistorPt l x z)) := by
  rw [deriv_fun_smul hsd hld, twistorPt_smul, hF _ _ hs, angle_smul_add, prod_smul_l]
  rw [zpow_add₀ hs, zpow_add₀ hs, zpow_add₀ hs]
  simp only [zpow_one, zpow_natCast, zpow_two]
  ring

/-- **Helicity ↔ homogeneity** (Adamo (3.27), (3.39)–(3.40)): for `f` homogeneous of degree
`2h - 2 = -(n + 1) - 2`, the transform of helicity `h = -(n + 1)/2` does not depend on the section:
rescaling `λ(z)` by a nonvanishing `s(z)` leaves it unchanged. -/
theorem penroseNeg_rescale {n : ℕ} {F : TwistorPair → ℂ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ (-((n : ℤ) + 1) - 2) * F p)
    {s : ℂ → ℂ} {l : ℂ → Fin 2 → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z ∈ sphere c R, s z ≠ 0) (hsd : ∀ z ∈ sphere c R, DifferentiableAt ℂ s z)
    (hld : ∀ z ∈ sphere c R, DifferentiableAt ℂ l z) :
    penroseNeg n F (fun z => s z • l z) c R = penroseNeg n F l c R := by
  funext i x
  refine circleIntegral.integral_congr hR fun z hz => ?_
  rw [penroseNeg_integrand_rescale hF (hs z hz) (hsd z hz) (hld z hz),
    show ((n : ℤ) + 1 + (-((n : ℤ) + 1) - 2) + 2) = 0 by ring, zpow_zero, one_mul]

/-- The homogeneity count for helicity `0`: the integrand is multiplied by `s ^ (d + 2)`. -/
theorem penroseScalar_integrand_rescale {F : TwistorPair → ℂ} {d : ℤ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ d * F p) {s : ℂ → ℂ}
    {l : ℂ → Fin 2 → ℂ} {z : ℂ} (hs : s z ≠ 0) (hsd : DifferentiableAt ℂ s z)
    (hld : DifferentiableAt ℂ l z) (x : SpinorCoord) :
    angle ((fun z => s z • l z) z) (deriv (fun z => s z • l z) z) *
        F (twistorPt (fun z => s z • l z) x z) =
      s z ^ (d + 2) * (angle (l z) (deriv l z) * F (twistorPt l x z)) := by
  rw [deriv_fun_smul hsd hld, twistorPt_smul, hF _ _ hs, angle_smul_add, zpow_add₀ hs]
  simp only [zpow_two]
  ring

/-- **Helicity `0` ↔ homogeneity `-2`** (Adamo (3.41); ADM §2.3, pp. 8–9): for `f` homogeneous of degree
`-2`, the scalar transform does not depend on the section. -/
theorem penroseScalar_rescale {F : TwistorPair → ℂ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ (-2 : ℤ) * F p)
    {s : ℂ → ℂ} {l : ℂ → Fin 2 → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z ∈ sphere c R, s z ≠ 0) (hsd : ∀ z ∈ sphere c R, DifferentiableAt ℂ s z)
    (hld : ∀ z ∈ sphere c R, DifferentiableAt ℂ l z) :
    penroseScalar F (fun z => s z • l z) c R = penroseScalar F l c R := by
  funext x
  refine circleIntegral.integral_congr hR fun z hz => ?_
  rw [penroseScalar_integrand_rescale hF (hs z hz) (hsd z hz) (hld z hz),
    show ((-2 : ℤ) + 2) = 0 by norm_num, zpow_zero, one_mul]

/-! ## Positive helicity -/

/-- `∂/∂μ^{α̇}` as a vector of twistor space. -/
def muVec (a : Fin 2) : TwistorPair := ((Pi.single a (1 : ℂ) : Fin 2 → ℂ), 0)

/-- `∂^m f/∂μ^{α̇₁} ⋯ ∂μ^{α̇ₘ}`, the derivatives taken in increasing order of the indices; for `f`
holomorphic the order does not matter (`dmuIter_eq`). -/
def dmuIter {m : ℕ} (F : TwistorPair → ℂ) (j : Fin m → Fin 2) (p : TwistorPair) : ℂ :=
  iteratedFDeriv ℂ m F p (fun k => muVec (j (Tuple.sort j k)))

lemma dmuIter_perm {m : ℕ} (F : TwistorPair → ℂ) (j : Fin m → Fin 2) (σ : Equiv.Perm (Fin m)) :
    dmuIter F (j ∘ σ) = dmuIter F j := by
  funext p
  have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := j) (σ := σ)
  simp only [dmuIter]
  congr 1
  funext k
  exact congrArg muVec (congrFun h k)

lemma dmuIter_eq {m : ℕ} {F : TwistorPair → ℂ} {p : TwistorPair} (hF : ContDiffAt ℂ ω F p)
    (j : Fin m → Fin 2) : dmuIter F j p = iteratedFDeriv ℂ m F p (fun k => muVec (j k)) :=
  hF.iteratedFDeriv_comp_perm (fun k => muVec (j k)) (Tuple.sort j)

lemma contDiffAt_iteratedFDeriv_apply {m : ℕ} {F : TwistorPair → ℂ} {p : TwistorPair}
    (hF : ContDiffAt ℂ ω F p) (u : Fin m → TwistorPair) :
    ContDiffAt ℂ 1 (fun q => iteratedFDeriv ℂ m F q u) p :=
  (ContinuousMultilinearMap.apply ℂ (fun _ : Fin m => TwistorPair) ℂ u).contDiff.contDiffAt.comp p
    (hF.iteratedFDeriv_right le_top)

lemma fderiv_iteratedFDeriv_apply {m : ℕ} {F : TwistorPair → ℂ} {p : TwistorPair}
    (hF : ContDiffAt ℂ ω F p) (u : Fin m → TwistorPair) (e : TwistorPair) :
    fderiv ℂ (fun q => iteratedFDeriv ℂ m F q u) p e =
      iteratedFDeriv ℂ (m + 1) F p (Fin.cons e u) := by
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ m F) p :=
    (hF.iteratedFDeriv_right (m := 1) le_top).differentiableAt one_ne_zero
  rw [fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_cons]

/-- Mixed holomorphic derivatives commute: the first two slots of `∂^{m+2} f` can be exchanged. -/
lemma iteratedFDeriv_cons_swap {m : ℕ} {F : TwistorPair → ℂ} {p : TwistorPair}
    (hF : ContDiffAt ℂ ω F p) (a b : TwistorPair) (u : Fin m → TwistorPair) :
    iteratedFDeriv ℂ (m + 2) F p (Fin.cons a (Fin.cons b u)) =
      iteratedFDeriv ℂ (m + 2) F p (Fin.cons b (Fin.cons a u)) := by
  rw [← hF.iteratedFDeriv_comp_perm (Fin.cons b (Fin.cons a u)) (Equiv.swap 0 1)]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp
  · simp
  · have h0 : (Fin.succ (Fin.succ k) : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero _
    have h1 : (Fin.succ (Fin.succ k) : Fin (m + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [Equiv.swap_apply_of_ne_of_ne h0 h1]

lemma muVec_cons {n : ℕ} (a : Fin 2) (i : Fin n → Fin 2) :
    (fun k => muVec ((Fin.cons a i : Fin (n + 1) → Fin 2) k)) =
      Fin.cons (muVec a) (fun k => muVec (i k)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp

/-- **The Penrose transform, helicity `(n + 1)/2`** (Adamo (3.42); the contour form is Wolf (2.5), with
the chirality exchanged and without `-1/(2πi)`):
`φ̃_{α̇₁⋯α̇_{n+1}}(x) = ∮ ⟨λ dλ⟩ ∂^{n+1} f/∂μ^{α̇₁} ⋯ ∂μ^{α̇_{n+1}} (μ(x, λ), λ)`. -/
def penrosePos (n : ℕ) (F : TwistorPair → ℂ) (l : ℂ → Fin 2 → ℂ) (c : ℂ) (R : ℝ) :
    (Fin (n + 1) → Fin 2) → SpinorCoord → ℂ := fun j x =>
  ∮ z in C(c, R), angle (l z) (deriv l z) * dmuIter F j (twistorPt l x z)

/-- **The contour integral of helicity `(n + 1)/2` is a z.r.m. field** (Adamo (3.42), "You can
readily check that the `h ≥ 0` integral formulae obey the z.r.m. equations by using holomorphicity and
the incidence relations"): for `f` holomorphic (analytic) on an open set `W` containing the twistor
points of the contour over `U`. -/
theorem penrosePos_isZrmPos (n : ℕ) {F : TwistorPair → ℂ} {W : Set TwistorPair} (hW : IsOpen W)
    (hF : ContDiffOn ℂ ω F W) {l : ℂ → Fin 2 → ℂ} (hl : ContDiff ℂ 1 l) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    {U : Set SpinorCoord} (hU : IsOpen U) (hUW : ∀ x ∈ U, ∀ z ∈ sphere c |R|, twistorPt l x z ∈ W) :
    IsZrmPos n U (penrosePos n F l c R) where
  symm σ j := by
    funext x
    simp only [penrosePos, dmuIter_perm]
  eqn β i x hx := by
    have hS : sphere c |R| = sphere c R := by rw [abs_of_nonneg hR]
    have hFa : ∀ p ∈ W, ContDiffAt ℂ ω F p := fun p hp => hF.contDiffAt (hW.mem_nhds hp)
    have hl0 : ContinuousOn l (sphere c |R|) := hl.continuous.continuousOn
    have hw : ContinuousOn (fun z => angle (l z) (deriv l z)) (sphere c |R|) :=
      continuousOn_angle hl _
    have hGu : ∀ u : Fin (n + 1) → TwistorPair,
        ContDiffOn ℂ 1 (fun q => iteratedFDeriv ℂ (n + 1) F q u) W := fun u p hp =>
      (contDiffAt_iteratedFDeriv_apply (hFa p hp) u).contDiffWithinAt
    have hpd : ∀ (a γ δ' : Fin 2), pd (penrosePos n F l c R (Fin.cons a i)) γ δ' x =
        ∮ z in C(c, R), (angle (l z) (deriv l z) * l z γ) *
          iteratedFDeriv ℂ (n + 2) F (twistorPt l x z)
            (Fin.cons (muVec δ') (Fin.cons (muVec a) fun k => muVec (i k))) := by
      intro a γ δ'
      have hev : penrosePos n F l c R (Fin.cons a i) =ᶠ[𝓝 x] fun y =>
          ∮ z in C(c, R), angle (l z) (deriv l z) *
            (fun q => iteratedFDeriv ℂ (n + 1) F q
              (fun k => muVec ((Fin.cons a i : Fin (n + 1) → Fin 2) k))) (twistorPt l y z) :=
        Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy =>
          circleIntegral.integral_congr hR fun z hz => by
            rw [dmuIter_eq (hFa _ (hUW y hy z (hS ▸ hz)))]
      rw [pd, hev.fderiv_eq, ← pd, pd_circleIntegral_twistorPt hW (hGu _) hw hl0 hU hUW hx]
      refine circleIntegral.integral_congr hR fun z hz => ?_
      rw [show ((Pi.single δ' (1 : ℂ) : Fin 2 → ℂ), (0 : Fin 2 → ℂ)) = muVec δ' from rfl,
        fderiv_iteratedFDeriv_apply (hFa _ (hUW x hx z (hS ▸ hz))), muVec_cons]
    have hcont : ∀ q : Fin 2 × Fin 2 × Fin 2, ContinuousOn (fun z =>
        (angle (l z) (deriv l z) * l z q.2.1) * iteratedFDeriv ℂ (n + 2) F (twistorPt l x z)
          (Fin.cons (muVec q.2.2) (Fin.cons (muVec q.1) fun k => muVec (i k)))) (sphere c |R|) := by
      intro q
      have hDW : ContinuousOn (fun z => iteratedFDerivWithin ℂ (n + 2) F W (twistorPt l x z))
          (sphere c |R|) :=
        (hF.continuousOn_iteratedFDerivWithin le_top hW.uniqueDiffOn).comp
          ((continuousOn_twistorPt hl0).comp (continuousOn_const.prodMk continuousOn_id)
            fun z hz => ⟨mem_univ x, hz⟩) fun z hz => hUW x hx z hz
      have hD : ContinuousOn (fun z => iteratedFDeriv ℂ (n + 2) F (twistorPt l x z)) (sphere c |R|) :=
        hDW.congr fun z hz => (iteratedFDerivWithin_of_isOpen _ hW (hUW x hx z hz)).symm
      exact (hw.mul ((continuous_apply q.2.1).comp hl.continuous).continuousOn).mul
        ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n + 2) => TwistorPair) ℂ _).continuous.comp_continuousOn hD)
    calc ∑ α', ∑ γ, ∑ δ', eps β γ * eps α' δ' * pd (penrosePos n F l c R (Fin.cons α' i)) γ δ' x
        = ∑ q : Fin 2 × Fin 2 × Fin 2, eps β q.2.1 * eps q.1 q.2.2 * ∮ z in C(c, R),
            (angle (l z) (deriv l z) * l z q.2.1) * iteratedFDeriv ℂ (n + 2) F (twistorPt l x z)
              (Fin.cons (muVec q.2.2) (Fin.cons (muVec q.1) fun k => muVec (i k))) := by
          simp only [Fintype.sum_prod_type, hpd]
      _ = ∮ z in C(c, R), ∑ q : Fin 2 × Fin 2 × Fin 2, eps β q.2.1 * eps q.1 q.2.2 *
            ((angle (l z) (deriv l z) * l z q.2.1) * iteratedFDeriv ℂ (n + 2) F (twistorPt l x z)
              (Fin.cons (muVec q.2.2) (Fin.cons (muVec q.1) fun k => muVec (i k)))) :=
          circleIntegral_finset_sum_mul _ _ _ fun q _ => hcont q
      _ = ∮ z in C(c, R), (0 : ℂ) := circleIntegral.integral_congr hR fun z hz => by
          have hsym := iteratedFDeriv_cons_swap (hFa _ (hUW x hx z (hS ▸ hz))) (muVec 1) (muVec 0)
            (fun k => muVec (i k))
          simp only [Fintype.sum_prod_type, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11, hsym]
          ring
      _ = 0 := by simp [circleIntegral]

/-- **Homogeneity of iterated derivatives**: for `f` homogeneous of degree `d`, `∂^m f` is homogeneous
of degree `d - m`. -/
lemma iteratedFDeriv_smul_of_homogeneous {m : ℕ} {F : TwistorPair → ℂ} {d : ℤ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ d * F p) {r : ℂ} (hr : r ≠ 0)
    (p : TwistorPair) (u : Fin m → TwistorPair) :
    iteratedFDeriv ℂ m F (r • p) u = r ^ (d - m) * iteratedFDeriv ℂ m F p u := by
  set g : TwistorPair ≃L[ℂ] TwistorPair :=
    (LinearEquiv.smulOfNeZero ℂ TwistorPair r hr).toContinuousLinearEquiv
  set h : ℂ ≃L[ℂ] ℂ := (LinearEquiv.smulOfNeZero ℂ ℂ (r ^ d) (zpow_ne_zero d hr)).toContinuousLinearEquiv
  have hFg : F ∘ g = h ∘ F := by
    funext q
    simp [g, h, hF r q hr]
  have h1 := g.iteratedFDerivWithin_comp_right F uniqueDiffOn_univ (mem_univ (g p)) m
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, hFg,
    h.iteratedFDeriv_comp_left] at h1
  have h2 := congrArg (fun L => L u) h1
  change r ^ d • iteratedFDeriv ℂ m F p u = iteratedFDeriv ℂ m F (r • p) (fun i => r • u i) at h2
  rw [ContinuousMultilinearMap.map_smul_univ] at h2
  simp only [smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  rw [zpow_sub₀ hr, zpow_natCast, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero m hr)]
  linear_combination (-1 : ℂ) * h2

lemma dmuIter_smul_of_homogeneous {m : ℕ} {F : TwistorPair → ℂ} {d : ℤ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ d * F p) {r : ℂ} (hr : r ≠ 0)
    (j : Fin m → Fin 2) (p : TwistorPair) :
    dmuIter F j (r • p) = r ^ (d - m) * dmuIter F j p :=
  iteratedFDeriv_smul_of_homogeneous hF hr p _

/-- The homogeneity count for helicity `(n + 1)/2`: the integrand is multiplied by
`s ^ (2 + d - (n + 1))`. -/
theorem penrosePos_integrand_rescale {n : ℕ} {F : TwistorPair → ℂ} {d : ℤ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ d * F p) {s : ℂ → ℂ}
    {l : ℂ → Fin 2 → ℂ} {z : ℂ} (hs : s z ≠ 0) (hsd : DifferentiableAt ℂ s z)
    (hld : DifferentiableAt ℂ l z) (j : Fin (n + 1) → Fin 2) (x : SpinorCoord) :
    angle ((fun z => s z • l z) z) (deriv (fun z => s z • l z) z) *
        dmuIter F j (twistorPt (fun z => s z • l z) x z) =
      s z ^ (2 + (d - ((n : ℤ) + 1))) *
        (angle (l z) (deriv l z) * dmuIter F j (twistorPt l x z)) := by
  rw [deriv_fun_smul hsd hld, twistorPt_smul, dmuIter_smul_of_homogeneous hF hs, angle_smul_add,
    zpow_add₀ hs]
  push_cast
  simp only [zpow_two]
  ring

/-- **Helicity `(n + 1)/2` ↔ homogeneity `2h - 2 = n - 1`** (Adamo (3.39), (3.42)): the transform
does not depend on the section. -/
theorem penrosePos_rescale {n : ℕ} {F : TwistorPair → ℂ}
    (hF : ∀ (r : ℂ) (p : TwistorPair), r ≠ 0 → F (r • p) = r ^ ((n : ℤ) - 1) * F p)
    {s : ℂ → ℂ} {l : ℂ → Fin 2 → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z ∈ sphere c R, s z ≠ 0) (hsd : ∀ z ∈ sphere c R, DifferentiableAt ℂ s z)
    (hld : ∀ z ∈ sphere c R, DifferentiableAt ℂ l z) :
    penrosePos n F (fun z => s z • l z) c R = penrosePos n F l c R := by
  funext j x
  refine circleIntegral.integral_congr hR fun z hz => ?_
  rw [penrosePos_integrand_rescale hF (hs z hz) (hsd z hz) (hld z hz),
    show (2 + (((n : ℤ) - 1) - ((n : ℤ) + 1))) = 0 by ring, zpow_zero, one_mul]

/-! ## The elementary solution (Wolf, Exercise 2.1) -/

/-- The section `λ(z) = (1, z)` of the line (the affine coordinate `λ = Z³/Z²` of ADM §2.3). -/
def affineSection (z : ℂ) : Fin 2 → ℂ := ![1, z]

lemma affineSection_eq : affineSection = fun z => ![1, 0] + z • ![0, 1] := by
  funext z
  ext i
  fin_cases i <;> simp [affineSection]

lemma hasDerivAt_affineSection (z : ℂ) : HasDerivAt affineSection ![0, 1] z := by
  rw [affineSection_eq]
  simpa using ((hasDerivAt_id z).smul_const (![0, 1] : Fin 2 → ℂ)).const_add (![1, 0] : Fin 2 → ℂ)

lemma contDiff_affineSection : ContDiff ℂ 1 affineSection := by
  rw [affineSection_eq]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

lemma angle_affineSection (z : ℂ) : angle (affineSection z) (deriv affineSection z) = -1 := by
  rw [(hasDerivAt_affineSection z).deriv]
  simp [angle, affineSection, Fin.sum_univ_two]

lemma twistorPt_affineSection (x : SpinorCoord) (z : ℂ) :
    twistorPt affineSection x z = (![x 0 0 + x 1 0 * z, x 0 1 + x 1 1 * z], ![1, z]) := by
  simp only [twistorPt, affineSection]
  ext k <;> fin_cases k <;> simp [incid, Fin.sum_univ_two]

lemma neg_inv_mul_eq_partialFraction (a b c d z : ℂ) (h1 : a + b * z ≠ 0) (h2 : c + d * z ≠ 0)
    (h3 : a * d - c * b ≠ 0) (hb : b ≠ 0) :
    -1 * ((a + b * z) * (c + d * z))⁻¹ =
      (a * d - c * b)⁻¹ * ((z - -(a / b))⁻¹ - d * (c + d * z)⁻¹) := by
  have e : (z - -(a / b))⁻¹ = b * (a + b * z)⁻¹ := by
    rw [show z - -(a / b) = (a + b * z) / b by field_simp; ring, inv_div, div_eq_mul_inv]
  rw [e, mul_inv]
  have hP := mul_inv_cancel₀ h1
  have hQ := mul_inv_cancel₀ h2
  have hD := mul_inv_cancel₀ h3
  linear_combination ((a + b * z)⁻¹ * (c + d * z)⁻¹) * hD +
    (b * (a * d - c * b)⁻¹ * (a + b * z)⁻¹) * hQ - (d * (a * d - c * b)⁻¹ * (c + d * z)⁻¹) * hP

/-- **The elementary solution of the wave equation** (Wolf, Exercise 2.1, p. 12): the twistor
function `f = 1/(μ⁰ μ¹)`, homogeneous of degree `-2`, along `λ = (1, z)` on a circle `|z| = R` that
separates the two poles, gives `2πi / det x`. -/
theorem penroseScalar_elementary {R : ℝ} (hR : 0 < R) {x : SpinorCoord}
    (h1 : ‖x 0 0‖ < R * ‖x 1 0‖) (h2 : R * ‖x 1 1‖ < ‖x 0 1‖) :
    penroseScalar (fun p => (p.1 0 * p.1 1)⁻¹) affineSection 0 R x =
      2 * Real.pi * Complex.I / (x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
  set a := x 0 0 with hA
  set b := x 1 0 with hB
  set c' := x 0 1 with hC
  set d := x 1 1 with hD
  have hb : b ≠ 0 := by
    rintro hb0
    rw [hb0, norm_zero, mul_zero] at h1
    exact absurd h1 (not_lt.2 (norm_nonneg _))
  have hc' : 0 < ‖c'‖ := (mul_nonneg hR.le (norm_nonneg d)).trans_lt h2
  have hdet : a * d - c' * b ≠ 0 := by
    intro h0
    have heq : ‖a‖ * ‖d‖ = ‖c'‖ * ‖b‖ := by rw [← norm_mul, ← norm_mul, sub_eq_zero.1 h0]
    have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb
    have : ‖a‖ * ‖d‖ < ‖c'‖ * ‖b‖ := by
      rcases (norm_nonneg d).eq_or_lt with hd0 | hd0
      · rw [← hd0, mul_zero]; exact mul_pos hc' hbpos
      · calc ‖a‖ * ‖d‖ < R * ‖b‖ * ‖d‖ := mul_lt_mul_of_pos_right h1 hd0
          _ = ‖b‖ * (R * ‖d‖) := by ring
          _ < ‖b‖ * ‖c'‖ := mul_lt_mul_of_pos_left h2 hbpos
          _ = ‖c'‖ * ‖b‖ := mul_comm _ _
    exact this.ne heq
  have hz1 : ∀ z ∈ sphere (0 : ℂ) R, a + b * z ≠ 0 := by
    intro z hz h0
    have hzR : ‖z‖ = R := by simpa using hz
    have : ‖a‖ = ‖b‖ * R := by rw [eq_neg_of_add_eq_zero_left h0, norm_neg, norm_mul, hzR]
    linarith [mul_comm R ‖b‖]
  have hz2 : ∀ z ∈ closedBall (0 : ℂ) R, c' + d * z ≠ 0 := by
    intro z hz h0
    have hzR : ‖z‖ ≤ R := by simpa using hz
    have : ‖c'‖ = ‖d‖ * ‖z‖ := by rw [eq_neg_of_add_eq_zero_left h0, norm_neg, norm_mul]
    nlinarith [norm_nonneg d, norm_nonneg z]
  -- partial fractions on the circle
  have hpf : ∀ z ∈ sphere (0 : ℂ) R,
      angle (affineSection z) (deriv affineSection z) *
          (fun p : TwistorPair => (p.1 0 * p.1 1)⁻¹) (twistorPt affineSection x z) =
        (a * d - c' * b)⁻¹ * ((z - -(a / b))⁻¹ - d * (c' + d * z)⁻¹) := by
    intro z hz
    have e1 := hz1 z hz
    have e2 := hz2 z (sphere_subset_closedBall hz)
    rw [angle_affineSection, twistorPt_affineSection]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← hA, ← hB, ← hC, ← hD]
    exact neg_inv_mul_eq_partialFraction a b c' d z e1 e2 hdet hb
  have hint1 : CircleIntegrable (fun z => (z - -(a / b))⁻¹) 0 R := by
    refine ContinuousOn.circleIntegrable' ?_
    refine (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => ?_
    rw [abs_of_pos hR] at hz
    have h := hz1 z hz
    have hba : b * (a / b) = a := by field_simp
    intro h0
    apply h
    simp only [Pi.sub_apply, id] at h0
    have hz' : z = -(a / b) := by linear_combination h0
    rw [hz', mul_neg, hba]
    ring
  have hd2 : DifferentiableOn ℂ (fun z => d * (c' + d * z)⁻¹) (closedBall 0 R) :=
    (differentiableOn_const _).mul ((differentiableOn_const _).add
      ((differentiableOn_const _).mul differentiableOn_id) |>.inv fun z hz => hz2 z hz)
  have hint2 : CircleIntegrable (fun z => d * (c' + d * z)⁻¹) 0 R :=
    (hd2.continuousOn.mono (by rw [abs_of_pos hR]; exact sphere_subset_closedBall)).circleIntegrable'
  have hres1 : ∮ z in C(0, R), (z - -(a / b))⁻¹ = 2 * Real.pi * Complex.I := by
    refine circleIntegral.integral_sub_inv_of_mem_ball ?_
    rw [mem_ball_zero_iff, norm_neg, norm_div]
    rw [div_lt_iff₀ (norm_pos_iff.2 hb)]
    linarith [mul_comm R ‖b‖]
  have hres2 : ∮ z in C(0, R), d * (c' + d * z)⁻¹ = 0 :=
    DiffContOnCl.circleIntegral_eq_zero hR.le
      (DifferentiableOn.diffContOnCl (by rw [closure_ball 0 hR.ne']; exact hd2))
  rw [penroseScalar, circleIntegral.integral_congr hR.le hpf, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub hint1 hint2, hres1, hres2]
  field_simp
  ring

/-- The elementary solution solves the wave equation where the circle separates the poles (an
instance of `penroseScalar_isZrmScalar`). -/
theorem penroseScalar_elementary_isZrmScalar {R : ℝ} (hR : 0 < R) :
    IsZrmScalar {x : SpinorCoord | ‖x 0 0‖ < R * ‖x 1 0‖ ∧ R * ‖x 1 1‖ < ‖x 0 1‖}
      (penroseScalar (fun p => (p.1 0 * p.1 1)⁻¹) affineSection 0 R) := by
  refine penroseScalar_isZrmScalar (W := {p : TwistorPair | p.1 0 * p.1 1 ≠ 0})
    (isOpen_ne_fun (by fun_prop) continuous_const) ?_ contDiff_affineSection 0 R
    ((isOpen_lt (f := fun x : SpinorCoord => ‖x 0 0‖) (g := fun x => R * ‖x 1 0‖) (by fun_prop)
      (by fun_prop)).inter (isOpen_lt (f := fun x : SpinorCoord => R * ‖x 1 1‖)
        (g := fun x => ‖x 0 1‖) (by fun_prop) (by fun_prop))) ?_
  · exact (contDiff_id.contDiffOn.inv fun p hp => hp).comp (by fun_prop : ContDiff ℂ 2
      (fun p : TwistorPair => p.1 0 * p.1 1)).contDiffOn fun p hp => hp
  · intro x hx z hz
    rw [abs_of_pos hR] at hz
    have hzR : ‖z‖ = R := by simpa using hz
    rw [twistorPt_affineSection]
    show _ * _ ≠ 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine mul_ne_zero ?_ ?_
    · intro h0
      have : ‖x 0 0‖ = ‖x 1 0‖ * R := by
        rw [eq_neg_of_add_eq_zero_left h0, norm_neg, norm_mul, hzR]
      linarith [hx.1, mul_comm R ‖x 1 0‖]
    · intro h0
      have : ‖x 0 1‖ = ‖x 1 1‖ * R := by
        rw [eq_neg_of_add_eq_zero_left h0, norm_neg, norm_mul, hzR]
      linarith [hx.2, mul_comm R ‖x 1 1‖]

end Lightlike.Spinor

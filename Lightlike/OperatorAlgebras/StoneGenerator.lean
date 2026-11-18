import Lightlike.OperatorAlgebras.UnitaryGroup
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The generator of a unitary group: derivative along the group and invariance of the domain

Helper lemmas for `T-OP1-P1` (`Tasks/OP/T_OP1_P1.lean`): the generator of a strongly continuous unitary
group `U` is self-adjoint. Here: `U s` maps the domain of the generator into itself, commutes with the
generator, and `t ↦ U t ψ` has derivative `U t (i A ψ)` at every `t` for `ψ` in the domain.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.UnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : UnitaryGroup H)

lemma apply_add (s t : ℝ) (ψ : H) : U (s + t) ψ = U s (U t ψ) := by
  rw [U.map_add']; rfl

lemma apply_zero (ψ : H) : U 0 ψ = ψ := by
  rw [U.map_zero']; rfl

lemma comm (s t : ℝ) (ψ : H) : U s (U t ψ) = U t (U s ψ) := by
  rw [← apply_add, ← apply_add, add_comm]

/-- `U s` as a continuous linear map. -/
noncomputable def clm (s : ℝ) : H →L[ℂ] H :=
  (U s).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma clm_apply (s : ℝ) (ψ : H) : U.clm s ψ = U s ψ := rfl

/-- The derivative of `t ↦ U t ψ` at `0`. -/
noncomputable def dvec (ψ : H) : H := deriv (fun t => U t ψ) 0

/-- If `ψ` is in the domain, so is `U s ψ`, and `t ↦ U t ψ` has derivative `U t (dvec ψ)` at `t`. -/
lemma hasDerivAt_of_mem {ψ : H} (hψ : DifferentiableAt ℝ (fun t => U t ψ) 0) (t : ℝ) :
    HasDerivAt (fun s => U s ψ) (U t (U.dvec ψ)) t := by
  have h0 : HasDerivAt (fun s => U s ψ) (U.dvec ψ) 0 := hψ.hasDerivAt
  have h1 : HasDerivAt (fun h : ℝ => U.clm t (U h ψ)) (U.clm t (U.dvec ψ)) 0 :=
    by
    have hl : HasFDerivAt (U.clm t) ((U.clm t).restrictScalars ℝ) (U 0 ψ) :=
      ((U.clm t).restrictScalars ℝ).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hl h0
  have h2 : HasDerivAt (fun h : ℝ => U (t + h) ψ) (U t (U.dvec ψ)) 0 := by
    simpa [apply_add] using h1
  have h3 : HasDerivAt (fun s : ℝ => U (t + (s - t)) ψ) (U t (U.dvec ψ)) t :=
    HasDerivAt.comp_sub_const t t (by simpa using h2)
  simpa using h3

/-- The adjoint of `U s` is `U (-s)`. -/
lemma inner_apply (s : ℝ) (a b : H) : ⟪U s a, b⟫_ℂ = ⟪a, U (-s) b⟫_ℂ := by
  have h : U (-s) b = (U s).symm b := by
    apply (U s).injective
    rw [LinearIsometryEquiv.apply_symm_apply, ← apply_add]; simp [apply_zero]
  rw [h, LinearIsometryEquiv.inner_map_eq_flip]

/-- `U s` preserves the domain of the generator, and commutes with the derivative at `0`. -/
lemma differentiableAt_apply {ψ : H} (hψ : DifferentiableAt ℝ (fun t => U t ψ) 0) (s : ℝ) :
    DifferentiableAt ℝ (fun t => U t (U s ψ)) 0 := by
  have h : (fun t => U t (U s ψ)) = fun t => U.clm s (U t ψ) := by
    funext t; exact U.comm t s ψ
  rw [h]
  exact ((U.clm s).restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hψ

lemma dvec_apply {ψ : H} (hψ : DifferentiableAt ℝ (fun t => U t ψ) 0) (s : ℝ) :
    U.dvec (U s ψ) = U s (U.dvec ψ) := by
  have h' : HasDerivAt (fun t => U t (U s ψ)) (U s (U.dvec ψ)) 0 := by
    have : (fun t => U t (U s ψ)) = fun t => U s (U t ψ) := by
      funext t; exact U.comm t s ψ
    rw [this]
    have hl : HasFDerivAt (U.clm s) ((U.clm s).restrictScalars ℝ) (U 0 ψ) :=
      ((U.clm s).restrictScalars ℝ).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hl hψ.hasDerivAt
  exact h'.deriv

variable [CompleteSpace H]

/-- The primitive `x ↦ ∫₀ˣ U s ψ ds`. -/
noncomputable def prim (ψ : H) (x : ℝ) : H := ∫ s in (0 : ℝ)..x, U s ψ

lemma hasDerivAt_prim (ψ : H) (x : ℝ) : HasDerivAt (U.prim ψ) (U x ψ) x :=
  ((U.continuous' ψ).integral_hasStrictDerivAt 0 x).hasDerivAt

omit [CompleteSpace H] in
lemma intervalIntegrable_apply (ψ : H) (a b : ℝ) :
    IntervalIntegrable (fun s => U s ψ) MeasureTheory.volume a b :=
  (U.continuous' ψ).intervalIntegrable a b

lemma apply_prim (h ε : ℝ) (ψ : H) : U h (U.prim ψ ε) = U.prim ψ (h + ε) - U.prim ψ h := by
  unfold prim
  have h1 : U h (∫ s in (0 : ℝ)..ε, U s ψ) = ∫ s in (0 : ℝ)..ε, U h (U s ψ) :=
    ((U.clm h).intervalIntegral_comp_comm (U.intervalIntegrable_apply ψ 0 ε)).symm
  rw [h1]
  have h2 : ∫ s in (0 : ℝ)..ε, U h (U s ψ) = ∫ s in (0 : ℝ)..ε, U (h + s) ψ := by
    congr 1; funext s; rw [apply_add]
  rw [h2, intervalIntegral.integral_comp_add_left (fun s => U s ψ) h, add_zero,
    ← intervalIntegral.integral_interval_sub_left (U.intervalIntegrable_apply ψ 0 (h + ε))
      (U.intervalIntegrable_apply ψ 0 h)]

lemma prim_mem (ψ : H) (ε : ℝ) :
    DifferentiableAt ℝ (fun t => U t (U.prim ψ ε)) 0 := by
  have h : (fun t => U t (U.prim ψ ε)) = fun h => U.prim ψ (h + ε) - U.prim ψ h := by
    funext h; rw [apply_prim, add_comm]
  rw [h]
  have h1 : HasDerivAt (fun h => U.prim ψ (h + ε)) (U ε ψ) 0 :=
    HasDerivAt.comp_add_const 0 ε (by simpa using U.hasDerivAt_prim ψ ε)
  exact (h1.sub (by simpa using U.hasDerivAt_prim ψ 0)).differentiableAt

omit [CompleteSpace H] in
lemma prim_zero (ψ : H) : U.prim ψ 0 = 0 := by simp [prim]

/-- The domain of the generator is dense. -/
lemma dense_generatorDomain : Dense (U.generatorDomain : Set H) := by
  intro ψ
  have hmem : ∀ ε : ℝ, ε⁻¹ • U.prim ψ ε ∈ U.generatorDomain := fun ε =>
    U.generatorDomain.smul_mem _ (U.prim_mem ψ ε)
  have hlim : Filter.Tendsto (fun ε : ℝ => ε⁻¹ • U.prim ψ ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds ψ) := by
    have h := (hasDerivAt_iff_tendsto_slope_zero.1 (U.hasDerivAt_prim ψ 0))
    rw [apply_zero] at h
    refine (h.mono_left (nhdsWithin_mono _ ?_)).congr ?_
    · intro x hx; exact ne_of_gt hx
    · intro x; simp [prim_zero]
  exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hmem)

omit [CompleteSpace H] in
/-- `⟪φ, d ψ⟫ + ⟪d φ, ψ⟫ = 0` for `φ, ψ` in the domain (the derivative of `⟪U t φ, U t ψ⟫ = ⟪φ, ψ⟫`). -/
lemma inner_dvec_add {φ ψ : H} (hφ : DifferentiableAt ℝ (fun t => U t φ) 0)
    (hψ : DifferentiableAt ℝ (fun t => U t ψ) 0) :
    ⟪φ, U.dvec ψ⟫_ℂ + ⟪U.dvec φ, ψ⟫_ℂ = 0 := by
  have a : HasDerivAt (fun t => U t φ) (U.dvec φ) 0 := hφ.hasDerivAt
  have b : HasDerivAt (fun t => U t ψ) (U.dvec ψ) 0 := hψ.hasDerivAt
  have h := HasDerivAt.inner ℂ a b
  have hc : (fun t => ⟪U t φ, U t ψ⟫_ℂ) = fun _ => ⟪φ, ψ⟫_ℂ := by
    funext t; exact LinearIsometryEquiv.inner_map_map _ _ _
  rw [hc] at h
  have h0 := (hasDerivAt_const (0 : ℝ) ⟪φ, ψ⟫_ℂ)
  have := h.unique h0
  simpa [apply_zero, dvec] using this

omit [CompleteSpace H] in
lemma generator_apply (ψ : U.generator.domain) : U.generator ψ = (-Complex.I) • U.dvec (ψ : H) := rfl

lemma dvec_eq (ψ : U.generator.domain) : U.dvec (ψ : H) = Complex.I • U.generator ψ := by
  rw [generator_apply, smul_smul]; simp

/-- The generator is symmetric. -/
lemma generator_isFormalAdjoint : U.generator.IsFormalAdjoint U.generator := by
  intro x y
  have h := U.inner_dvec_add x.2 y.2
  rw [generator_apply, generator_apply, inner_smul_left, inner_smul_right]
  have h' : ⟪(x : H), U.dvec (y : H)⟫_ℂ = -⟪U.dvec (x : H), (y : H)⟫_ℂ := eq_neg_of_add_eq_zero_left h
  rw [h']; simp

lemma generator_le_adjoint : U.generator ≤ U.generator.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint U.dense_generatorDomain U.generator_isFormalAdjoint

/-- For `y` in the domain of the adjoint and `ψ` in the domain of the generator:
`d/dt ⟪U t y, ψ⟫ = ⟪i U t (A† y), ψ⟫`. -/
lemma hasDerivAt_inner_adjoint (y : (U.generator.adjoint).domain) (ψ : U.generator.domain) (t : ℝ) :
    HasDerivAt (fun t => ⟪U t (y : H), (ψ : H)⟫_ℂ)
      ⟪Complex.I • U t ((U.generator.adjoint y : H)), (ψ : H)⟫_ℂ t := by
  have hψ : DifferentiableAt ℝ (fun t => U t (ψ : H)) 0 := ψ.2
  have hg := U.hasDerivAt_of_mem hψ (-t)
  have h2 : HasDerivAt (fun s : ℝ => U (-s) (ψ : H)) ((-1 : ℝ) • U (-t) (U.dvec (ψ : H))) t :=
    HasDerivAt.scomp t hg (hasDerivAt_neg t)
  have h3 := HasDerivAt.inner ℂ (hasDerivAt_const t (y : H)) h2
  have hfun : (fun t => ⟪U t (y : H), (ψ : H)⟫_ℂ) = fun s => ⟪(y : H), U (-s) (ψ : H)⟫_ℂ := by
    funext s; exact U.inner_apply s _ _
  rw [hfun]
  refine h3.congr_deriv ?_
  have hx : U (-t) (ψ : H) ∈ U.generator.domain := U.differentiableAt_apply hψ (-t)
  have hd : U.dvec (U (-t) (ψ : H)) = U (-t) (U.dvec (ψ : H)) := U.dvec_apply hψ (-t)
  have hdv := U.dvec_eq ⟨_, hx⟩
  have hadj := LinearPMap.adjoint_isFormalAdjoint U.dense_generatorDomain y ⟨_, hx⟩
  simp only at hdv
  rw [hd] at hdv
  rw [hdv]
  simp only [inner_zero_left, add_zero, neg_smul, one_smul, inner_neg_right, inner_smul_right,
    inner_smul_left]
  have hadj' : ⟪(y : H), (U.generator ⟨U (-t) (ψ : H), hx⟩ : H)⟫_ℂ =
      ⟪(U.generator.adjoint y : H), U (-t) (ψ : H)⟫_ℂ := hadj.symm
  rw [hadj', U.inner_apply t]
  simp

/-- A vector orthogonal to the domain of the generator is zero. -/
lemma eq_zero_of_inner_domain {v : H} (h : ∀ ψ ∈ U.generatorDomain, ⟪v, ψ⟫_ℂ = 0) : v = 0 := by
  have h1 : Continuous fun x : H => ⟪v, x⟫_ℂ := continuous_const.inner continuous_id
  have h2 : ⟪v, v⟫_ℂ = 0 := by
    have := Continuous.ext_on U.dense_generatorDomain h1 continuous_const (f := fun x : H => ⟪v, x⟫_ℂ)
      (g := fun _ => (0 : ℂ)) (fun x hx => h x hx)
    exact congrFun this v
  exact inner_self_eq_zero.1 h2

/-- The integral form of the evolution of a vector `y` in the domain of the adjoint of the generator:
`U t y = y + i ∫₀ᵗ U s (A† y) ds`. -/
lemma apply_eq_of_adjoint (y : U.generator.adjoint.domain) (t : ℝ) :
    U t (y : H) = (y : H) + Complex.I • U.prim (U.generator.adjoint y : H) t := by
  set w : H := (U.generator.adjoint y : H) with hw
  have key : ∀ ψ : U.generator.domain,
      ⟪U t (y : H) - (y : H) - Complex.I • U.prim w t, (ψ : H)⟫_ℂ = 0 := by
    intro ψ
    let Φ : ℝ → ℂ := fun t => ⟪U t (y : H) - (y : H) - Complex.I • U.prim w t, (ψ : H)⟫_ℂ
    have hd : ∀ x, HasDerivAt Φ 0 x := by
      intro x
      have a := U.hasDerivAt_inner_adjoint y ψ x
      have b : HasDerivAt (fun t => Complex.I • U.prim w t) (Complex.I • U x w) x :=
        (U.hasDerivAt_prim w x).const_smul Complex.I
      have c := HasDerivAt.inner ℂ b (hasDerivAt_const x (ψ : H))
      have hΦ : Φ = fun t => ⟪U t (y : H), (ψ : H)⟫_ℂ - ⟪(y : H), (ψ : H)⟫_ℂ
          - ⟪Complex.I • U.prim w t, (ψ : H)⟫_ℂ := by
        funext t; simp only [Φ, inner_sub_left]
      rw [hΦ]
      have := (a.sub (hasDerivAt_const x ⟪(y : H), (ψ : H)⟫_ℂ)).sub c
      refine this.congr_deriv ?_
      rw [← hw]; simp
    have hconst := is_const_of_deriv_eq_zero (f := Φ)
      (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
    have h0 : Φ 0 = 0 := by simp [Φ, apply_zero, prim_zero]
    rw [← h0]; exact hconst
  have hz := U.eq_zero_of_inner_domain (fun ψ hψ => key ⟨ψ, hψ⟩)
  exact sub_eq_zero.1 (by rw [sub_sub] at hz; exact hz) |>.trans rfl

/-- The vector `y` in the domain of `A†` lies in the domain of `A`, and `A y = A† y`. -/
lemma adjoint_le_generator : U.generator.adjoint ≤ U.generator := by
  have hmem : ∀ y : U.generator.adjoint.domain, (y : H) ∈ U.generator.domain := by
    intro y
    set w : H := (U.generator.adjoint y : H)
    have hfun : (fun t => U t (y : H)) = fun t => (y : H) + Complex.I • U.prim w t := by
      funext t; exact U.apply_eq_of_adjoint y t
    show DifferentiableAt ℝ (fun t => U t (y : H)) 0
    rw [hfun]
    exact ((hasDerivAt_const (0 : ℝ) (y : H)).add
      ((U.hasDerivAt_prim w 0).const_smul Complex.I)).differentiableAt
  refine ⟨fun y hy => hmem ⟨y, hy⟩, ?_⟩
  intro x y hxy
  have hy : (x : H) ∈ U.generator.domain := hmem x
  set w : H := (U.generator.adjoint x : H)
  have hfun : (fun t => U t (x : H)) = fun t => (x : H) + Complex.I • U.prim w t := by
    funext t; exact U.apply_eq_of_adjoint x t
  have hder : HasDerivAt (fun t => U t (x : H)) (Complex.I • w) 0 := by
    rw [hfun]
    have := (hasDerivAt_const (0 : ℝ) (x : H)).add ((U.hasDerivAt_prim w 0).const_smul Complex.I)
    refine this.congr_deriv ?_
    rw [apply_zero, zero_add]
  have hdv : U.dvec (x : H) = Complex.I • w := hder.deriv
  have hxy' : y = ⟨(x : H), hy⟩ := Subtype.ext hxy.symm
  rw [hxy', generator_apply, hdv, smul_smul]
  simp

/-- **Stone's theorem, generator is self-adjoint**: the generator of a strongly continuous unitary group is
self-adjoint. -/
theorem generator_isSelfAdjoint : IsSelfAdjoint U.generator :=
  le_antisymm U.adjoint_le_generator U.generator_le_adjoint

end Lightlike.OperatorAlgebras.UnitaryGroup

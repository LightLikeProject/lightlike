import Mathlib

/-!
# The Morse lemma with parameters (SP4)

A smooth function `f (x, λ)` on `E × F` (finite-dimensional real normed spaces), with a critical point at `x = 0` for every `λ`
near `λ₀` and a nondegenerate Hessian `B = ∂ₓ² f (0, λ₀)` there, is, in new coordinates `y = Φ (x, λ)`, a quadratic form:
`f (x, λ) = f (0, λ) + ½ B (Φ (x, λ)) (Φ (x, λ))` near `(0, λ₀)`, with `Φ` smooth, `Φ (0, λ) = 0` and
`∂ₓ Φ (0, λ₀) = id`; and `(x, λ) ↦ (Φ (x, λ), λ)` is a local diffeomorphism.

Proof (the textbook proof, Hörmander, *The Analysis of Linear Partial Differential Operators* III, Lemma C.6.1; the comparison with the
book at that location is pending: it was not read): Hadamard's lemma gives `f (x, λ) = f (0, λ) + ½ B x (Q (x, λ) x)` with
`Q` a smooth family of `B`-self-adjoint endomorphisms, `Q (0, λ₀) = 1`; a smooth square root `ρ` near `1` of `B`-self-adjoint
endomorphisms (inverse function theorem in the algebra of endomorphisms) gives `Φ (x, λ) = ρ (Q (x, λ)) x`.

**Limits.** The function is smooth on the whole of `E × F` (a function defined near `(0, λ₀)` reduces to this by a cut-off); the
critical point is at `x = 0` (a critical point depending on `λ` reduces to this by a smooth translation); the normal form has the
Hessian at `λ₀` itself as quadratic form (a diagonal form follows by Sylvester's law, not proved here); `E` and `F` are
finite-dimensional real normed spaces in `Type` (not `Type u`).

The Hessian is written with the partial derivatives `partialE`, `partialE2` of `f` in the `E` variable.
-/

open Set Filter Topology MeasureTheory intervalIntegral Metric
open scoped ContDiff

namespace Lightlike.Morse

/-- **A parametric integral over `[0, 1]` of a `Cⁿ` function is `Cⁿ`** (finite-dimensional parameter space). -/
theorem contDiff_integral_unit {X G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] (n : ℕ) :
    ∀ {g : ℝ → X → G}, ContDiff ℝ n (fun p : ℝ × X => g p.1 p.2) →
      ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, g t x) := by
  induction n generalizing G with
  | zero =>
    intro g hg
    have hc : Continuous (fun p : ℝ × X => g p.1 p.2) := by simpa using hg.continuous
    have hc' : Continuous (Function.uncurry fun (x : X) (t : ℝ) => g t x) :=
      hc.comp (continuous_snd.prodMk continuous_fst)
    exact contDiff_zero.2 (continuous_parametric_intervalIntegral_of_continuous' hc' 0 1)
  | succ n ih =>
    intro g hg
    set G2 : ℝ × X → G := fun p => g p.1 p.2 with hG2
    have hdiff : Differentiable ℝ G2 := hg.differentiable (by simp)
    set g' : ℝ → X → (X →L[ℝ] G) := fun t x => fderiv ℝ (g t) x with hg'
    have hg'eq : ∀ p : ℝ × X, g' p.1 p.2 = (fderiv ℝ G2 p).comp (ContinuousLinearMap.inr ℝ ℝ X) := by
      intro p
      have h1 : HasFDerivAt (fun x : X => G2 (p.1, x)) ((fderiv ℝ G2 (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ X)) p.2 :=
        (hdiff (p.1, p.2)).hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
      exact h1.fderiv
    have hg'c : ContDiff ℝ n (fun p : ℝ × X => g' p.1 p.2) := by
      have h1 : ContDiff ℝ n (fderiv ℝ G2) := hg.fderiv_right (by push_cast; exact le_rfl)
      have h2 := h1.clm_comp (contDiff_const (c := ContinuousLinearMap.inr ℝ ℝ X))
      have : (fun p : ℝ × X => g' p.1 p.2) = fun p => (fderiv ℝ G2 p).comp (ContinuousLinearMap.inr ℝ ℝ X) :=
        funext hg'eq
      rw [this]
      exact h2
    have hF' : ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, g' t x) := ih (G := X →L[ℝ] G) hg'c
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun x => ∫ t in (0 : ℝ)..1, g' t x, hF', fun x₀ => ?_⟩
    have hcont : Continuous (fun p : ℝ × X => g p.1 p.2) := hg.continuous
    have hcont' : Continuous (fun p : ℝ × X => g' p.1 p.2) := hg'c.continuous
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      (f := fun p : ℝ × X => g' p.1 p.2) hcont'.continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (a := 0) (b := 1)
      (μ := volume) (F := fun x t => g t x) (F' := fun x t => g' t x) (s := ball x₀ 1)
      (bound := fun _ => C) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x => (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    · exact (hcont'.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht x hx => ?_
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at ht
        exact ⟨ht.1.le, ht.2⟩
      exact hC (t, x) ⟨ht', ball_subset_closedBall hx⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t ht x hx => ?_
      exact ((hdiff.comp (differentiable_const t |>.prodMk differentiable_id)) x).hasFDerivAt


section Root

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The endomorphism of a bilinear form**: for a nondegenerate symmetric form `B`, a continuous linear map `M` from bilinear
forms to endomorphisms with `B u (M S v) = S u v`. -/
theorem exists_endo_of_form (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) :
    ∃ M : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E), ∀ S u v, B u (M S v) = S u v := by
  classical
  have hBnd : B.toBilinForm.Nondegenerate := by
    refine ⟨fun v hv => hnd v fun w => by simpa using hv w, fun w hw => hnd w fun v => ?_⟩
    simpa [hB w v] using hw v
  set T := B.toBilinForm.toDual hBnd with hT
  let Tc : (E →L[ℝ] ℝ) →L[ℝ] E :=
    LinearMap.toContinuousLinearMap (T.symm.toLinearMap ∘ₗ (ContinuousLinearMap.coeLM ℝ))
  have hTc : ∀ φ : E →L[ℝ] ℝ, Tc φ = T.symm (φ : E →ₗ[ℝ] ℝ) := fun φ => rfl
  let M : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E Tc).comp
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨M, fun S u v => ?_⟩
  have h1 : M S v = T.symm ((S.flip v : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) := rfl
  have h2 := LinearMap.BilinForm.apply_toDual_symm_apply (B := B.toBilinForm) (hB := hBnd)
    (f := ((S.flip v : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ)) (v := u)
  rw [← hT] at h2
  rw [hB, h1]
  simpa using h2


set_option maxHeartbeats 4000000 in
/-- **A smooth square root near `1` in the algebra of endomorphisms**, unique near `1`. -/
theorem exists_smooth_sqrt_near_one :
    ∃ ρ : (E →L[ℝ] E) → (E →L[ℝ] E), ContDiffAt ℝ ∞ ρ 1 ∧ ρ 1 = 1 ∧
      ∃ 𝒮 ∈ 𝓝 (1 : E →L[ℝ] E), (∀ᶠ M in 𝓝 (1 : E →L[ℝ] E), ρ M ∈ 𝒮 ∧ ρ M * ρ M = M) ∧
        ∀ R ∈ 𝒮, ∀ R' ∈ 𝒮, R * R = R' * R' → R = R' := by
  classical
  set q : (E →L[ℝ] E) → (E →L[ℝ] E) := fun R => R * R with hq
  have hqc : ContDiff ℝ ∞ q := contDiff_id.mul contDiff_id
  obtain ⟨f', hf'⟩ : ∃ f' : (E →L[ℝ] E) ≃L[ℝ] (E →L[ℝ] E), (f' : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (E →L[ℝ] E) :=
    ⟨(LinearEquiv.smulOfUnit (Units.mk0 (2 : ℝ) two_ne_zero)).toContinuousLinearEquiv, by
      ext H : 1; rfl⟩
  have hd : HasFDerivAt q (f' : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) 1 := by
    have hb := (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).isBoundedBilinearMap.hasFDerivAt
      ((1, 1) : (E →L[ℝ] E) × (E →L[ℝ] E))
    have hdiag : HasFDerivAt (fun R : E →L[ℝ] E => (R, R))
        ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).prod (ContinuousLinearMap.id ℝ (E →L[ℝ] E))) 1 :=
      (hasFDerivAt_id (1 : E →L[ℝ] E)).prodMk (hasFDerivAt_id (1 : E →L[ℝ] E))
    have key : HasFDerivAt (fun R : E →L[ℝ] E => (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)) R R) _ (1 : E →L[ℝ] E) :=
      HasFDerivAt.comp (g := fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)) p.1 p.2)
        (f := fun R : E →L[ℝ] E => (R, R)) (1 : E →L[ℝ] E) hb hdiag
    refine key.congr_fderiv ?_
    rw [hf']
    ext H : 1
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    rw [IsBoundedBilinearMap.deriv_apply]
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.mul_apply', one_mul, mul_one]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, two_smul]
  have hc : ContDiffAt ℝ ∞ q 1 := hqc.contDiffAt
  set e := hc.toOpenPartialHomeomorph q hd (by norm_num) with he
  have h1src : (1 : E →L[ℝ] E) ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hq1 : q 1 = 1 := mul_one 1
  have hqe : ∀ R, e R = R * R := fun R => rfl
  have h1tgt : (1 : E →L[ℝ] E) ∈ e.target := by
    have := hc.image_mem_toOpenPartialHomeomorph_target hd (by norm_num)
    rwa [hq1] at this
  have hsy1 : e.symm 1 = 1 := by
    have : e 1 = 1 := by rw [hqe]; exact mul_one 1
    rw [← this]; exact e.left_inv h1src
  have hsymm : ContDiffAt ℝ ∞ e.symm 1 := by
    refine e.contDiffAt_symm (f₀' := f') h1tgt ?_ ?_
    · rw [hsy1]; exact hd
    · rw [hsy1]; exact hc
  refine ⟨e.symm, hsymm, hsy1, e.source, e.open_source.mem_nhds h1src, ?_, ?_⟩
  · filter_upwards [e.open_target.mem_nhds h1tgt] with M hM
    refine ⟨e.map_target hM, ?_⟩
    have := e.right_inv hM
    rwa [hqe] at this
  · intro R hR R' hR' h
    refine e.injOn hR hR' ?_
    rw [hqe, hqe]; exact h


/-- **Smooth root of a `B`-self-adjoint endomorphism near `1`**: `ρ 1 = 1`, `ρ` smooth at `1`, and for `Q` near `1` with
`B (Q u) v = B u (Q v)`, `B (ρ Q u) (ρ Q v) = B u (Q v)`. -/
theorem exists_smooth_selfadjoint_root (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) :
    ∃ ρ : (E →L[ℝ] E) → (E →L[ℝ] E), ContDiffAt ℝ ∞ ρ 1 ∧ ρ 1 = 1 ∧
      ∀ᶠ Q in 𝓝 (1 : E →L[ℝ] E), (∀ u v, B (Q u) v = B u (Q v)) → ∀ u v, B (ρ Q u) (ρ Q v) = B u (Q v) := by
  classical
  obtain ⟨M, hM⟩ := exists_endo_of_form B hB hnd
  have hnd' : ∀ x y : E, (∀ w, B x w = B y w) → x = y := fun x y h =>
    sub_eq_zero.1 (hnd (x - y) fun w => by simp [h w])
  obtain ⟨ρ, hρ, hρ1, 𝒮, h𝒮, hev, huniq⟩ := exists_smooth_sqrt_near_one (E := E)
  let P : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) B
  let ad : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := M.comp P
  have had : ∀ (R : E →L[ℝ] E) u w, B u (ad R w) = B (R u) w := fun R u w => hM (P R) u w
  have hmul : ∀ R R' : E →L[ℝ] E, ad (R * R') = ad R' * ad R := by
    intro R R'
    ext w : 1
    refine hnd' _ _ fun u => ?_
    rw [hB (ad (R * R') w) u, had, hB ((ad R' * ad R) w) u, ContinuousLinearMap.mul_apply (ad R') (ad R) w, had,
      ContinuousLinearMap.mul_apply R R' u]
    exact (had R (R' u) w).symm
  have hone : ad 1 = 1 := by
    ext w : 1
    refine hnd' _ _ fun u => ?_
    rw [hB (ad 1 w) u, had]
    simp [hB]
  have hself : ∀ Q : E →L[ℝ] E, (∀ u v, B (Q u) v = B u (Q v)) → ad Q = Q := by
    intro Q hQ
    ext w : 1
    refine hnd' _ _ fun u => ?_
    rw [hB (ad Q w) u, had, hB (Q w) u, hQ]
  have hadc : Continuous ad := ad.continuous
  have hadρ : ∀ᶠ Q in 𝓝 (1 : E →L[ℝ] E), ad (ρ Q) ∈ 𝒮 := by
    have hρc : ContinuousAt ρ 1 := hρ.continuousAt
    have : Tendsto (fun Q => ad (ρ Q)) (𝓝 (1 : E →L[ℝ] E)) (𝓝 (ad (ρ 1))) := (hadc.tendsto _).comp hρc.tendsto
    rw [hρ1, hone] at this
    exact this.eventually h𝒮
  refine ⟨ρ, hρ, hρ1, ?_⟩
  filter_upwards [hev, hadρ] with Q ⟨hQ𝒮, hQ2⟩ hadQ hsa u v
  set R := ρ Q with hR
  have hRM : ad R * ad R = Q := by
    rw [← hmul R R, hQ2, hself Q hsa]
  have hadR : ad R = R := huniq _ hadQ _ hQ𝒮 (by rw [hRM, hQ2])
  have e1 : B (R u) (R v) = B u (ad R (R v)) := (had R u (R v)).symm
  rw [e1, hadR, ← ContinuousLinearMap.mul_apply, hQ2]

end Root

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]


noncomputable def partialE (f : E × F → ℝ) (p : E × F) : E →L[ℝ] ℝ :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E F)

noncomputable def partialE2 (f : E × F → ℝ) (p : E × F) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ (partialE f) p).comp (ContinuousLinearMap.inl ℝ E F)

theorem contDiff_partialE {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialE f) := by
  unfold partialE
  exact (hf.fderiv_right (by simp)).clm_comp contDiff_const

theorem partialE_eq {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) (y : E) (l : F) :
    partialE f (y, l) = fderiv ℝ (fun z : E => f (z, l)) y := by
  have h1 : HasFDerivAt (fun z : E => (z, l)) (ContinuousLinearMap.inl ℝ E F) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const l y)
  have h2 := (hf.differentiable (by simp) (y, l)).hasFDerivAt.comp y h1
  exact h2.fderiv.symm

theorem partialE2_eq {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) (y : E) (l : F) :
    partialE2 f (y, l) = fderiv ℝ (fderiv ℝ (fun z : E => f (z, l))) y := by
  have h1 : HasFDerivAt (fun z : E => (z, l)) (ContinuousLinearMap.inl ℝ E F) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const l y)
  have h2 := ((contDiff_partialE hf).differentiable (by simp) (y, l)).hasFDerivAt.comp y h1
  have h3 : (fun z : E => partialE f (z, l)) = fderiv ℝ (fun z : E => f (z, l)) := by
    funext z; exact partialE_eq hf z l
  have h4 : HasFDerivAt (fderiv ℝ (fun z : E => f (z, l))) (partialE2 f (y, l)) y := by
    have : (partialE f ∘ fun z : E => (z, l)) = fderiv ℝ (fun z : E => f (z, l)) := by
      funext z; exact partialE_eq hf z l
    rw [← this]; exact h2
  exact h4.fderiv.symm

theorem partialE2_symm {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) (p : E × F) (u v : E) :
    partialE2 f p u v = partialE2 f p v u := by
  obtain ⟨y, l⟩ := p
  rw [partialE2_eq hf]
  have hg : ContDiff ℝ ∞ (fun z : E => f (z, l)) := hf.comp (contDiff_id.prodMk contDiff_const)
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp)) u v


theorem contDiff_partialE2 {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialE2 f) := by
  unfold partialE2
  exact ((contDiff_partialE hf).fderiv_right (by simp)).clm_comp contDiff_const

theorem hasDerivAt_along {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) (l : F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (s • x, l)) (partialE f (t • x, l) x) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s • x, l)) (x, (0 : F)) t := by
    have : HasDerivAt (fun s : ℝ => s • x) x t := by simpa using (hasDerivAt_id t).smul_const x
    exact this.prodMk (hasDerivAt_const t l)
  have h2 := (hf.differentiable (by simp) (t • x, l)).hasFDerivAt.comp_hasDerivAt t h1
  have e : partialE f (t • x, l) x = fderiv ℝ f (t • x, l) (x, 0) := by simp [partialE]
  rw [e]
  exact h2

theorem hasDerivAt_along2 {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) (l : F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => partialE f (s • x, l) x) (partialE2 f (t • x, l) x x) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s • x, l)) (x, (0 : F)) t := by
    have : HasDerivAt (fun s : ℝ => s • x) x t := by simpa using (hasDerivAt_id t).smul_const x
    exact this.prodMk (hasDerivAt_const t l)
  have hd := ((contDiff_partialE hf).differentiable (by simp) (t • x, l)).hasFDerivAt.comp_hasDerivAt t h1
  have := (ContinuousLinearMap.apply ℝ ℝ x).hasFDerivAt.comp_hasDerivAt t hd
  have e : partialE2 f (t • x, l) x x = (fderiv ℝ (partialE f) (t • x, l) (x, 0)) x := by simp [partialE2]
  rw [e]
  exact this


/-- **Hadamard's lemma with remainder in integral form**, at a critical point: if `∂ₓ f (0, l) = 0` then
`f (x, l) = f (0, l) + ∫₀¹ (1 - t) ∂ₓ² f (t x, l) (x, x) dt`. -/
theorem hadamard_integral {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) (l : F)
    (hcrit : partialE f (0, l) = 0) :
    f (x, l) = f (0, l) + ∫ t in (0 : ℝ)..1, (1 - t) * partialE2 f (t • x, l) x x := by
  have hc1 : Continuous (fun s : ℝ => partialE f (s • x, l) x) :=
    ((contDiff_partialE hf).continuous.comp (by fun_prop)).clm_apply continuous_const
  have hc2 : Continuous (fun s : ℝ => partialE2 f (s • x, l) x x) :=
    (((contDiff_partialE2 hf).continuous.comp (by fun_prop : Continuous fun s : ℝ => (s • x, l))).clm_apply
      continuous_const).clm_apply continuous_const
  have hftc : ∫ t in (0 : ℝ)..1, partialE f (t • x, l) x = f (x, l) - f (0, l) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (f := fun s : ℝ => f (s • x, l)) (f' := fun s => partialE f (s • x, l) x)
      (fun t _ => hasDerivAt_along hf x l t) (hc1.intervalIntegrable 0 1)
    simpa using this
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun t : ℝ => 1 - t) (u' := fun _ => (-1 : ℝ)) (v := fun s : ℝ => partialE f (s • x, l) x)
    (v' := fun s => partialE2 f (s • x, l) x x)
    (fun t _ => by simpa using (hasDerivAt_id t).const_sub 1) (fun t _ => hasDerivAt_along2 hf x l t)
    intervalIntegrable_const (hc2.intervalIntegrable 0 1)
  have h0 : partialE f ((0 : ℝ) • x, l) x = 0 := by simp [hcrit]
  simp only [h0, mul_zero, sub_zero, sub_self, zero_mul, zero_sub, neg_mul, one_mul] at hibp
  rw [hibp]
  simp only [neg_mul, one_mul, intervalIntegral.integral_neg, neg_neg]
  rw [hftc]
  ring


/-- **A parametric integral over `[0, 1]` of a smooth function is smooth.** -/
theorem contDiff_integral_unit_infty {X G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {g : ℝ → X → G}
    (hg : ContDiff ℝ ∞ (fun p : ℝ × X => g p.1 p.2)) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, g t x) :=
  contDiff_infty.2 fun n => contDiff_integral_unit n (hg.of_le (by exact_mod_cast le_top))


/-- **The Morse lemma with parameters.** See the module docstring. -/
theorem morse_lemma_with_parameters {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) {l₀ : F}
    (hcrit : ∀ᶠ l in 𝓝 l₀, partialE f (0, l) = 0)
    (hnd : ∀ v, (∀ w, partialE2 f (0, l₀) v w = 0) → v = 0) :
    ∃ Φ : E × F → E, ContDiffAt ℝ ∞ Φ (0, l₀) ∧ (∀ᶠ l in 𝓝 l₀, Φ (0, l) = 0) ∧
      fderiv ℝ (fun x : E => Φ (x, l₀)) 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ᶠ p in 𝓝 ((0 : E), l₀), f p = f (0, p.2) + (1 / 2 : ℝ) * partialE2 f (0, l₀) (Φ p) (Φ p) := by
  classical
  obtain ⟨B, hBdef⟩ : ∃ B : E →L[ℝ] E →L[ℝ] ℝ, B = partialE2 f (0, l₀) := ⟨_, rfl⟩
  rw [← hBdef] at hnd ⊢
  have hB : ∀ u v, B u v = B v u := fun u v => by rw [hBdef]; exact partialE2_symm hf _ u v
  obtain ⟨Mm, hM⟩ := exists_endo_of_form B hB hnd
  have hnd' : ∀ x y : E, (∀ w, B x w = B y w) → x = y := fun x y h =>
    sub_eq_zero.1 (hnd (x - y) fun w => by simp [h w])
  have hMB : Mm B = 1 := by
    ext v : 1
    refine hnd' _ _ fun w => ?_
    rw [hB, hM]
    simp [hB w v]
  obtain ⟨ρ, hρ, hρ1, hroot⟩ := exists_smooth_selfadjoint_root B hB hnd
  -- the endomorphism-valued Hessian and its Hadamard average
  set Hhat : E × F → (E →L[ℝ] E) := fun p => Mm (partialE2 f p) with hHhat
  have hHs : ContDiff ℝ ∞ Hhat := (by fun_prop : ContDiff ℝ ∞ Mm).comp (contDiff_partialE2 hf)
  set g : ℝ → E × F → (E →L[ℝ] E) := fun t p => (1 - t) • Hhat (t • p.1, p.2) with hg
  have hgs : ContDiff ℝ ∞ (fun q : ℝ × (E × F) => g q.1 q.2) := by
    refine (contDiff_const.sub contDiff_fst).smul ?_
    exact hHs.comp (by fun_prop)
  set Ahat : E × F → (E →L[ℝ] E) := fun p => ∫ t in (0 : ℝ)..1, g t p with hAhat
  have hAs : ContDiff ℝ ∞ Ahat := contDiff_integral_unit_infty hgs
  set Q : E × F → (E →L[ℝ] E) := fun p => (2 : ℝ) • Ahat p with hQ
  have hQs : ContDiff ℝ ∞ Q := hAs.const_smul (2 : ℝ)
  -- `Q (0, l₀) = 1`
  have hA0 : ∀ l : F, Ahat (0, l) = (1 / 2 : ℝ) • Hhat (0, l) := by
    intro l
    simp only [hAhat, hg, smul_zero]
    rw [intervalIntegral.integral_smul_const]
    congr 1
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    norm_num
  have hQ0 : Q (0, l₀) = 1 := by
    simp only [hQ, hA0, hHhat]
    rw [← hBdef, hMB]
    simp
  -- self-adjointness
  have hHsa : ∀ q u v, B (Hhat q u) v = B u (Hhat q v) := by
    intro q u v
    simp only [hHhat]
    rw [hB, hM, hM]
    exact partialE2_symm hf q v u
  have hgint : ∀ p : E × F, IntervalIntegrable (fun t : ℝ => g t p) volume 0 1 := fun p =>
    (hgs.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  have hAsa : ∀ p u v, B (Ahat p u) v = B u (Ahat p v) := by
    intro p u v
    have e1 := ((B.flip v).comp (ContinuousLinearMap.apply ℝ E u)).intervalIntegral_comp_comm (hgint p)
    have e2 := ((B u).comp (ContinuousLinearMap.apply ℝ E v)).intervalIntegral_comp_comm (hgint p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.flip_apply] at e1 e2
    have hAp : Ahat p = ∫ t in (0 : ℝ)..1, g t p := rfl
    rw [← hAp] at e1 e2
    rw [← e1, ← e2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hg, ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hHsa]
  have hQsa : ∀ p u v, B (Q p u) v = B u (Q p v) := by
    intro p u v
    simp only [hQ, ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.smul_apply]
    rw [hAsa]
  have hadam : ∀ p : E × F, partialE f (0, p.2) = 0 → f p = f (0, p.2) + B p.1 (Ahat p p.1) := by
    intro p hp
    have h1 := hadamard_integral hf p.1 p.2 hp
    have e1 := ((B p.1).comp (ContinuousLinearMap.apply ℝ E p.1)).intervalIntegral_comp_comm (hgint p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at e1
    have hAp : Ahat p = ∫ t in (0 : ℝ)..1, g t p := rfl
    rw [← hAp] at e1
    rw [h1, ← e1]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hg, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hHhat]
    simp only []
    rw [hM]
  have hρQ : ContDiffAt ℝ ∞ (fun p => ρ (Q p)) (0, l₀) := by
    have : ContDiffAt ℝ ∞ ρ (Q (0, l₀)) := by rw [hQ0]; exact hρ
    exact this.comp (0, l₀) hQs.contDiffAt
  refine ⟨fun p => ρ (Q p) p.1, hρQ.clm_apply contDiffAt_fst, Eventually.of_forall fun l => by simp, ?_, ?_⟩
  · set c : E → (E →L[ℝ] E) := fun x => ρ (Q (x, l₀)) with hc
    have hcc : ContDiffAt ℝ ∞ c 0 := by
      have hpair : ContDiffAt ℝ ∞ (fun x : E => (x, l₀)) 0 := contDiffAt_id.prodMk contDiffAt_const
      exact ContDiffAt.comp (g := fun p : E × F => ρ (Q p)) (f := fun x : E => (x, l₀)) (0 : E) hρQ hpair
    have hcd : HasFDerivAt c (fderiv ℝ c 0) 0 :=
      (hcc.differentiableAt (by simp)).hasFDerivAt
    have := hcd.clm_apply (hasFDerivAt_id (0 : E))
    have hc0 : c 0 = 1 := by simp only [hc, hQ0, hρ1]
    refine this.fderiv.trans ?_
    ext v : 1
    simp [hc0]
  · have hc1 : ∀ᶠ p in 𝓝 ((0 : E), l₀), partialE f (0, p.2) = 0 :=
      (continuous_snd.tendsto ((0 : E), l₀)).eventually hcrit
    have hQt : Tendsto Q (𝓝 ((0 : E), l₀)) (𝓝 (1 : E →L[ℝ] E)) := by
      rw [← hQ0]; exact hQs.continuous.tendsto _
    have hc2 := hQt.eventually hroot
    filter_upwards [hc1, hc2] with p hp1 hp2
    have h1 := hadam p hp1
    have h2 := hp2 (hQsa p) p.1 p.1
    rw [h1]
    have hAQ : Ahat p = (1 / 2 : ℝ) • Q p := by
      simp only [hQ, smul_smul]; norm_num
    rw [hAQ, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, ← h2]


/-- **Morse coordinates**: the change of variables `(x, λ) ↦ (Φ (x, λ), λ)` is a local diffeomorphism at `(0, λ₀)`. -/
theorem morse_coordinates {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) {l₀ : F}
    (hcrit : ∀ᶠ l in 𝓝 l₀, partialE f (0, l) = 0)
    (hnd : ∀ v, (∀ w, partialE2 f (0, l₀) v w = 0) → v = 0) :
    ∃ (Φ : E × F → E) (e : OpenPartialHomeomorph (E × F) (E × F)),
      ContDiffAt ℝ ∞ Φ (0, l₀) ∧ (∀ᶠ l in 𝓝 l₀, Φ (0, l) = 0) ∧
      (0, l₀) ∈ e.source ∧ (∀ p, e p = (Φ p, p.2)) ∧
      ContDiffAt ℝ ∞ e.symm (e (0, l₀)) ∧
      ∀ᶠ p in 𝓝 ((0 : E), l₀), f p = f (0, p.2) + (1 / 2 : ℝ) * partialE2 f (0, l₀) (Φ p) (Φ p) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦd, hfΦ⟩ := morse_lemma_with_parameters hf hcrit hnd
  set Ψ : E × F → E × F := fun p => (Φ p, p.2) with hΨ
  have hΨc : ContDiffAt ℝ ∞ Ψ (0, l₀) := hΦ.prodMk contDiffAt_snd
  set Φ' : E × F →L[ℝ] E := fderiv ℝ Φ (0, l₀) with hΦ'
  have hΦdiff : HasFDerivAt Φ Φ' (0, l₀) := (hΦ.differentiableAt (by simp)).hasFDerivAt
  have hΦ'inl : ∀ u : E, Φ' (u, 0) = u := by
    have h1 : HasFDerivAt (fun z : E => (z, l₀)) (ContinuousLinearMap.inl ℝ E F) (0 : E) :=
      (hasFDerivAt_id (0 : E)).prodMk (hasFDerivAt_const l₀ (0 : E))
    have h2 := hΦdiff.comp (0 : E) h1
    have h3 : fderiv ℝ (fun x : E => Φ (x, l₀)) 0 = Φ'.comp (ContinuousLinearMap.inl ℝ E F) := h2.fderiv
    rw [hΦd] at h3
    intro u
    have := congrArg (fun L => L u) h3
    simpa using this.symm
  have hΦ'split : ∀ u : E, ∀ v : F, Φ' (u, v) = u + Φ' (0, v) := by
    intro u v
    have : ((u, v) : E × F) = (u, 0) + (0, v) := by simp
    rw [this, map_add, hΦ'inl]
  set Ψ' : E × F →L[ℝ] E × F := Φ'.prod (ContinuousLinearMap.snd ℝ E F) with hΨ'
  have hΨd : HasFDerivAt Ψ Ψ' (0, l₀) := hΦdiff.prodMk (hasFDerivAt_snd)
  set Ψ'' : E × F →L[ℝ] E × F :=
    ((ContinuousLinearMap.fst ℝ E F) - Φ'.comp ((ContinuousLinearMap.inr ℝ E F).comp (ContinuousLinearMap.snd ℝ E F))).prod
      (ContinuousLinearMap.snd ℝ E F) with hΨ''
  obtain ⟨f', hf'⟩ : ∃ f' : (E × F) ≃L[ℝ] (E × F), (f' : E × F →L[ℝ] E × F) = Ψ' :=
    ⟨ContinuousLinearEquiv.equivOfInverse Ψ' Ψ''
      (fun p => by
        obtain ⟨u, v⟩ := p
        simp only [hΨ', hΨ'', ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
          ContinuousLinearMap.inr_apply]
        rw [hΦ'split u v]
        simp)
      (fun p => by
        obtain ⟨u, v⟩ := p
        simp only [hΨ', hΨ'', ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
          ContinuousLinearMap.inr_apply]
        rw [hΦ'split (u - Φ' (0, v)) v]
        simp), rfl⟩
  have hΨd' : HasFDerivAt Ψ (f' : E × F →L[ℝ] E × F) (0, l₀) := by rw [hf']; exact hΨd
  set e := hΨc.toOpenPartialHomeomorph Ψ hΨd' (by norm_num) with he
  have hsrc : ((0 : E), l₀) ∈ e.source := hΨc.mem_toOpenPartialHomeomorph_source hΨd' (by norm_num)
  have htgt : e (0, l₀) ∈ e.target := e.map_source hsrc
  have hsy : e.symm (e (0, l₀)) = (0, l₀) := e.left_inv hsrc
  refine ⟨Φ, e, hΦ, hΦ0, hsrc, fun p => rfl, ?_, hfΦ⟩
  refine e.contDiffAt_symm (f₀' := f') htgt ?_ ?_
  · rw [hsy]; exact hΨd'
  · rw [hsy]; exact hΨc

end Lightlike.Morse

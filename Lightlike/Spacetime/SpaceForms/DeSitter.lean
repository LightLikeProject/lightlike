import Lightlike.Spacetime.PullbackMetric
import Lightlike.Spacetime.ModelTransport
import Lightlike.Spacetime.Lorentzian

/-!
# De Sitter space as a manifold: `ℝ × Sᵐ` with the metric induced from the quadric

De Sitter space of dimension `m + 1` and radius `L` is the whole manifold `deSitterSpace m = ℝ × Sᵐ` (Mathlib's product
of the line and the unit sphere of `ℝ^{m+1}`, the model transported to `Fin (m + 1) → ℝ`, time first, as for `J × S³`),
with the metric `deSitterSpaceMetric m L` induced by the immersion `ι(τ, ω) = (L sinh τ, L cosh τ ω)` into the
Minkowski space `ℝ × ℝ^{m+1}` with the form `η((a, x), (b, y)) = -a b + ⟪x, y⟫`. The image of `ι` is the quadric
`η(x, x) = L²` (`dSForm_dSIncl_self`). In the coordinates `(τ, ω)` the metric is `L² (-dτ² + cosh² τ dΩ²)`, the global
form of de Sitter space.

* `contMDiff_dSIncl`, `dι_dSIncl`: the immersion is smooth, with derivative
  `(s, u) ↦ (L cosh τ s, L sinh τ s ω + L cosh τ dω(u))`;
* `dι_dSIncl_injective`, `dSForm_dSIncl_dι`, `exists_dι_dSIncl_eq`: `dι` is injective with image exactly the
  `η`-orthogonal complement of `ι(τ, ω)`, so the induced form is nondegenerate (`pullback_nondeg_of_quadric`);
* `deSitterSpaceMetric`: the metric, a `NondegMetric` on the whole manifold;
* `isLorentzianForm_deSitterSpaceMetric`: at every point it has signature `(-, +, …, +)`, through an explicit
  orthonormal frame; `deSitterSpaceLorentzian` packages it as a `LorentzianMetric`.

**Statements are about the abstract manifold** `ℝ × Sᵐ`; the quadric enters only through `ι` and the metric `ι* η`.

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), section 8.1 (de Sitter space as the
hyperboloid `-u² + x₁² + … = α²` in Minkowski space, the global coordinates `ds² = -dt² + α² cosh²(t/α) dΩ²`).
-/

open Manifold Metric Bundle Set
open scoped ContDiff RealInnerProductSpace Manifold

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

/-! ## Signature from an orthonormal frame -/

section Frame

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] {n : ℕ}

/-- **A form with an `η`-orthonormal frame of the right length is Lorentzian**: if `B(e i, e j) = η_ij` for `n` vectors
of an `n`-dimensional space, they form a basis and `B` has signature `(-, +, …, +)`. -/
theorem isLorentzianForm_of_frame [FiniteDimensional ℝ W] [NeZero n] (B : W →L[ℝ] W →L[ℝ] ℝ) (e : Fin n → W)
    (he : ∀ i j, B (e i) (e j) = eta n i j) (hdim : Module.finrank ℝ W = n) : IsLorentzianForm n B := by
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (fun v => B v (e j)) hc
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, he, smul_eq_mul, map_zero, zero_apply] at h
    simpa [eta_apply, etaDiag_ne_zero] using h
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim]), fun i j => ?_⟩
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact he i j

end Frame

/-! ## The manifold, the ambient space and the immersion -/

variable (m : ℕ)

/-- The unit sphere `Sᵐ` of `ℝ^{m+1}`, with Mathlib's manifold structure (model `𝓡 m`). -/
abbrev SphereM : Type := sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1

instance fact_finrank_sphereM : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩

/-- **De Sitter space as a manifold**: `ℝ × Sᵐ`. -/
abbrev deSitterSpace : Type := ℝ × SphereM m

/-- the product model of `ℝ × Sᵐ` -/
abbrev IdSP : ModelWithCorners ℝ (ℝ × EuclideanSpace ℝ (Fin m)) (ModelProd ℝ (EuclideanSpace ℝ (Fin m))) :=
  𝓘(ℝ, ℝ).prod (𝓡 m)

/-- the identification of the model `ℝ × ℝᵐ` with `Fin (m + 1) → ℝ` (time first) -/
def dSModelEquiv : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin m) ℝ)).trans
    (Fin.consEquivL ℝ (fun _ : Fin (m + 1) => ℝ))

/-- the model with corners of `ℝ × Sᵐ` on `Fin (m + 1) → ℝ` -/
abbrev IdS : ModelWithCorners ℝ (Fin (m + 1) → ℝ) (ModelProd ℝ (EuclideanSpace ℝ (Fin m))) :=
  (IdSP m).transContinuousLinearEquiv (dSModelEquiv m)

example : IsManifold (IdS m) ∞ (deSitterSpace m) := inferInstance

/-- The ambient Minkowski space `ℝ × ℝ^{m+1}`. -/
abbrev DSAmb : Type := ℝ × EuclideanSpace ℝ (Fin (m + 1))

/-- The Minkowski form `η((a, x), (b, y)) = -a b + ⟪x, y⟫` of `ℝ × ℝ^{m+1}`. -/
def dSForm : DSAmb m →L[ℝ] DSAmb m →L[ℝ] ℝ :=
  (-(ContinuousLinearMap.mul ℝ ℝ)).bilinearComp (ContinuousLinearMap.fst ℝ ℝ _) (ContinuousLinearMap.fst ℝ ℝ _)
  + (innerSL ℝ : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] _ →L[ℝ] ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ ℝ _) (ContinuousLinearMap.snd ℝ ℝ _)

variable {m}

theorem dSForm_apply (x y : DSAmb m) : dSForm m x y = -(x.1 * y.1) + ⟪x.2, y.2⟫ := by
  simp [dSForm]

theorem dSForm_symm (x y : DSAmb m) : dSForm m x y = dSForm m y x := by
  rw [dSForm_apply, dSForm_apply, real_inner_comm]; ring

/-- The Minkowski form is nondegenerate. -/
theorem dSForm_nondeg (u : DSAmb m) (h : ∀ z, dSForm m u z = 0) : u = 0 := by
  have h1 := h (u.1, 0)
  have h2 := h (0, u.2)
  rw [dSForm_apply] at h1 h2
  simp only [inner_zero_right, add_zero, real_inner_self_eq_norm_sq] at h1 h2
  have hu1 : u.1 = 0 := by nlinarith [sq_nonneg u.1]
  have hu2 : u.2 = 0 := by simpa using h2
  exact Prod.ext hu1 hu2

variable (L : ℝ)

/-- The map `Φ(t, v) = (L sinh t, L cosh t v)` of `ℝ × ℝ^{m+1}`. -/
def dSPhi (q : ℝ × EuclideanSpace ℝ (Fin (m + 1))) : DSAmb m :=
  (L * Real.sinh q.1, (L * Real.cosh q.1) • q.2)

/-- The derivative of `Φ` at `(t, v)`. -/
def dSPhiD (t : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1))) : (ℝ × EuclideanSpace ℝ (Fin (m + 1))) →L[ℝ] DSAmb m :=
  ((L * Real.cosh t) • ContinuousLinearMap.fst ℝ ℝ _).prod
    ((L * Real.sinh t) • (ContinuousLinearMap.fst ℝ ℝ _).smulRight v + (L * Real.cosh t) • ContinuousLinearMap.snd ℝ ℝ _)

theorem hasFDerivAt_dSPhi (t : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    HasFDerivAt (dSPhi L) (dSPhiD L t v) (t, v) := by
  have h1 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => q.1) (ContinuousLinearMap.fst ℝ ℝ _) (t, v) :=
    hasFDerivAt_fst
  have hS : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => L * Real.sinh q.1)
      ((L * Real.cosh t) • ContinuousLinearMap.fst ℝ ℝ _) (t, v) := by
    have := ((Real.hasDerivAt_sinh t).hasFDerivAt.comp (t, v) h1).const_mul L
    refine this.congr_fderiv ?_
    ext <;> simp [mul_comm, mul_left_comm]
  have hC : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => L * Real.cosh q.1)
      ((L * Real.sinh t) • ContinuousLinearMap.fst ℝ ℝ _) (t, v) := by
    have := ((Real.hasDerivAt_cosh t).hasFDerivAt.comp (t, v) h1).const_mul L
    refine this.congr_fderiv ?_
    ext <;> simp [mul_comm, mul_left_comm]
  have hX : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => (L * Real.cosh q.1) • q.2)
      ((L * Real.sinh t) • (ContinuousLinearMap.fst ℝ ℝ _).smulRight v
        + (L * Real.cosh t) • ContinuousLinearMap.snd ℝ ℝ _) (t, v) := by
    have := hC.smul (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := EuclideanSpace ℝ (Fin (m + 1))) (p := (t, v)))
    refine this.congr_fderiv ?_
    ext <;> simp [add_comm, mul_comm]
  exact hS.prodMk hX

theorem contDiff_dSPhi : ContDiff ℝ ∞ (dSPhi (m := m) L) :=
  (contDiff_const.mul (Real.contDiff_sinh.comp contDiff_fst)).prodMk
    ((contDiff_const.mul (Real.contDiff_cosh.comp contDiff_fst)).smul contDiff_snd)

/-- **The immersion of de Sitter space** `ι(τ, ω) = (L sinh τ, L cosh τ ω)` onto the quadric `η(x, x) = L²`. -/
def dSIncl (p : deSitterSpace m) : DSAmb m := dSPhi L (p.1, (p.2 : EuclideanSpace ℝ (Fin (m + 1))))

/-- The derivative of the inclusion of the sphere, as a plain continuous linear map. -/
def dcoeM (x : SphereM m) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  mfderiv (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (Subtype.val : SphereM m → _) x

theorem hasMFDerivAt_coe_sphereM (x : SphereM m) :
    HasMFDerivAt (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (Subtype.val : SphereM m → _) x (dcoeM x) :=
  ((contMDiff_coe_sphere (m := ∞) (n := m) x).mdifferentiableAt (by simp)).hasMFDerivAt

/-- The inclusion maps tangent vectors of the sphere to vectors orthogonal to the point. -/
theorem inner_dcoeM (x : SphereM m) (u : EuclideanSpace ℝ (Fin m)) : ⟪(x : EuclideanSpace ℝ (Fin (m + 1))), dcoeM x u⟫ = 0 := by
  have h2 := range_mvfderiv_subtypeVal (E := EuclideanSpace ℝ (Fin (m + 1))) (n := m) x
  have h : dcoeM x u ∈ (mvfderiv (𝓡 m) ((↑) : SphereM m → EuclideanSpace ℝ (Fin (m + 1))) x).range := ⟨u, rfl⟩
  rw [h2] at h
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 h

theorem dcoeM_injective (x : SphereM m) : Function.Injective (dcoeM x) :=
  injective_mvfderiv_subtypeVal_sphere (E := EuclideanSpace ℝ (Fin (m + 1))) (n := m) x

/-- Every vector orthogonal to `x` is the image of a tangent vector of the sphere at `x`. -/
theorem exists_dcoeM_eq (x : SphereM m) (y : EuclideanSpace ℝ (Fin (m + 1)))
    (hy : ⟪(x : EuclideanSpace ℝ (Fin (m + 1))), y⟫ = 0) : ∃ u, dcoeM x u = y := by
  have h2 := range_mvfderiv_subtypeVal (E := EuclideanSpace ℝ (Fin (m + 1))) (n := m) x
  have : y ∈ (mvfderiv (𝓡 m) ((↑) : SphereM m → EuclideanSpace ℝ (Fin (m + 1))) x).range := by
    rw [h2]; exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 hy
  obtain ⟨u, hu⟩ := this
  exact ⟨u, hu⟩

theorem inner_self_sphereM (x : SphereM m) : ⟪(x : EuclideanSpace ℝ (Fin (m + 1))), (x : EuclideanSpace ℝ (Fin (m + 1)))⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]; norm_num

/-- The derivative of the immersion with respect to the product model. -/
theorem hasMFDerivAt_dSIncl_prod (p : deSitterSpace m) :
    HasMFDerivAt (IdSP m) 𝓘(ℝ, DSAmb m) (dSIncl L) p
      ((dSPhiD L p.1 (p.2 : EuclideanSpace ℝ (Fin (m + 1)))).comp
        ((ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))).prod
          ((dcoeM p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))))) := by
  have h1 : HasMFDerivAt (IdSP m) 𝓘(ℝ, ℝ) (fun q : deSitterSpace m => q.1) p
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))) := hasMFDerivAt_fst p
  have h2 : HasMFDerivAt (IdSP m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (fun q : deSitterSpace m => (q.2 : EuclideanSpace ℝ (Fin (m + 1)))) p
      ((dcoeM p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))) :=
    (hasMFDerivAt_coe_sphereM p.2).comp p (hasMFDerivAt_snd p)
  have h3 := h1.prodMk h2
  have h4 : HasMFDerivAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (m + 1))) 𝓘(ℝ, DSAmb m) (dSPhi L) (p.1, (p.2 : EuclideanSpace ℝ (Fin (m + 1))))
      (dSPhiD L p.1 (p.2 : EuclideanSpace ℝ (Fin (m + 1)))) :=
    (hasFDerivAt_dSPhi L p.1 _).hasMFDerivAt
  exact h4.comp p h3

theorem contMDiff_dSIncl : ContMDiff (IdS m) 𝓘(ℝ, DSAmb m) ∞ (dSIncl (m := m) L) := by
  have hP : ContMDiff (IdSP m) 𝓘(ℝ, DSAmb m) ∞ (dSIncl (m := m) L) := by
    have hq : ContMDiff (IdSP m) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (m + 1))) ∞
        (fun q : deSitterSpace m => (q.1, (q.2 : EuclideanSpace ℝ (Fin (m + 1))))) :=
      contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd)
    exact (contDiff_dSPhi L).contMDiff.comp hq
  exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left (e := dSModelEquiv m)).2 hP

/-- **The derivative of the immersion**: for `w` with components `(s, u) = e⁻¹ w` in `ℝ × ℝᵐ`,
`dι(w) = (L cosh τ s, L sinh τ s ω + L cosh τ dω(u))`. -/
theorem dι_dSIncl (p : deSitterSpace m) (w : TangentSpace (IdS m) p) :
    dι (I := IdS m) (dSIncl L) p w =
      (L * Real.cosh p.1 * ((dSModelEquiv m).symm w).1,
        (L * Real.sinh p.1 * ((dSModelEquiv m).symm w).1) • (p.2 : EuclideanSpace ℝ (Fin (m + 1)))
          + (L * Real.cosh p.1) • dcoeM p.2 ((dSModelEquiv m).symm w).2) := by
  have h := hasMFDerivAt_transContinuousLinearEquiv (dSModelEquiv m) (hasMFDerivAt_dSIncl_prod L p)
  unfold dι
  rw [h.mfderiv]
  change (dSPhiD L p.1 (p.2 : EuclideanSpace ℝ (Fin (m + 1))))
    (((ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))).prod
      ((dcoeM p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m))))) ((dSModelEquiv m).symm w)) = _
  simp [dSPhiD, smul_smul]

/-- **The image is the quadric** `η(x, x) = L²`. -/
theorem dSForm_dSIncl_self (p : deSitterSpace m) : dSForm m (dSIncl L p) (dSIncl L p) = L ^ 2 := by
  rw [dSForm_apply]
  simp only [dSIncl, dSPhi, inner_smul_left, inner_smul_right, inner_self_sphereM, RCLike.conj_to_real]
  have := Real.cosh_sq_sub_sinh_sq p.1
  nlinarith [this]

/-- The image of `dι` is `η`-orthogonal to the point. -/
theorem dSForm_dSIncl_dι (p : deSitterSpace m) (w : TangentSpace (IdS m) p) :
    dSForm m (dSIncl L p) (dι (I := IdS m) (dSIncl L) p w) = 0 := by
  rw [dι_dSIncl, dSForm_apply]
  simp only [dSIncl, dSPhi, inner_add_right, inner_smul_left, inner_smul_right, inner_self_sphereM, inner_dcoeM,
    RCLike.conj_to_real]
  ring

variable {L}

/-- `dι` is injective for `L ≠ 0`. -/
theorem dι_dSIncl_injective (hL : L ≠ 0) (p : deSitterSpace m) :
    Function.Injective (dι (I := IdS m) (dSIncl L) p) := by
  intro a b hab
  rw [← sub_eq_zero]
  set w := a - b with hwdef
  have hw' : dι (I := IdS m) (dSIncl L) p w = 0 := by rw [hwdef, map_sub, hab, sub_self]
  erw [dι_dSIncl] at hw'
  have hc : L * Real.cosh p.1 ≠ 0 := mul_ne_zero hL (Real.cosh_pos p.1).ne'
  have hs : ((dSModelEquiv m).symm w).1 = 0 := by
    have := congrArg Prod.fst hw'
    simp only [Prod.fst_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  have hu : ((dSModelEquiv m).symm w).2 = 0 := by
    have := congrArg Prod.snd hw'
    simp only [hs, mul_zero, zero_smul, zero_add, Prod.snd_zero, smul_eq_zero, hc, false_or] at this
    exact dcoeM_injective p.2 (this.trans (map_zero _).symm)
  have : (dSModelEquiv m).symm w = 0 := Prod.ext hs hu
  simpa using congrArg (dSModelEquiv m) this

/-- Every vector `η`-orthogonal to the point is in the image of `dι`. -/
theorem exists_dι_dSIncl_eq (hL : L ≠ 0) (p : deSitterSpace m) (z : DSAmb m)
    (hz : dSForm m (dSIncl L p) z = 0) : ∃ w, dι (I := IdS m) (dSIncl L) p w = z := by
  have hc : L * Real.cosh p.1 ≠ 0 := mul_ne_zero hL (Real.cosh_pos p.1).ne'
  set s := z.1 / (L * Real.cosh p.1) with hsdef
  set y := (L * Real.cosh p.1)⁻¹ • (z.2 - (L * Real.sinh p.1 * s) • (p.2 : EuclideanSpace ℝ (Fin (m + 1)))) with hydef
  have hy : ⟪(p.2 : EuclideanSpace ℝ (Fin (m + 1))), y⟫ = 0 := by
    rw [dSForm_apply] at hz
    simp only [dSIncl, dSPhi, inner_smul_left, RCLike.conj_to_real] at hz
    have h1 : Real.cosh p.1 * ⟪(p.2 : EuclideanSpace ℝ (Fin (m + 1))), z.2⟫ - Real.sinh p.1 * z.1 = 0 := by
      apply mul_left_cancel₀ hL
      linear_combination hz
    rw [hydef, inner_smul_right, inner_sub_right, inner_smul_right, inner_self_sphereM]
    have hcosh := (Real.cosh_pos p.1).ne'
    rw [hsdef]
    field_simp
    linear_combination h1
  obtain ⟨u, hu⟩ := exists_dcoeM_eq p.2 y hy
  refine ⟨dSModelEquiv m (s, u), ?_⟩
  rw [dι_dSIncl L p (dSModelEquiv m (s, u))]
  simp only [ContinuousLinearEquiv.symm_apply_apply, hu, hydef, smul_smul]
  refine Prod.ext ?_ ?_
  · show L * Real.cosh p.1 * s = z.1
    rw [hsdef]; field_simp
  · show (L * Real.sinh p.1 * s) • _ + ((L * Real.cosh p.1) * (L * Real.cosh p.1)⁻¹) • _ = z.2
    rw [mul_inv_cancel₀ hc, one_smul]
    abel

/-- **The metric of de Sitter space** on `ℝ × Sᵐ`: the pullback `ι* η`, nondegenerate at every point. -/
def deSitterSpaceMetric (m : ℕ) (L : ℝ) (hL : L ≠ 0) : NondegMetric (IdS m) (deSitterSpace m) :=
  NondegMetric.pullback (dSForm m) dSForm_symm (dSIncl L) (contMDiff_dSIncl L) fun p v hv =>
    pullback_nondeg_of_quadric (L := dSForm m) dSForm_symm dSForm_nondeg (x := dSIncl L p)
      (by rw [dSForm_dSIncl_self]; exact pow_ne_zero 2 hL) (dι_dSIncl_injective hL p)
      (dSForm_dSIncl_dι L p) (exists_dι_dSIncl_eq hL p) v hv

theorem deSitterSpaceMetric_apply (hL : L ≠ 0) (p : deSitterSpace m) (v w : TangentSpace (IdS m) p) :
    (deSitterSpaceMetric m L hL).g p v w =
      dSForm m (dι (I := IdS m) (dSIncl L) p v) (dι (I := IdS m) (dSIncl L) p w) :=
  NondegMetric.pullback_apply _ _ _ _ _ p v w

/-! ## Signature -/

/-- The orthonormal frame of de Sitter space at `(τ, ω)`: `(1/L) ∂_τ`, and `(L cosh τ)⁻¹` times the preimages of an
orthonormal basis of `ω^⊥`. -/
def dSFrame (L : ℝ) (p : deSitterSpace m) : Fin (m + 1) → TangentSpace (IdS m) p :=
  Fin.cons (dSModelEquiv m (L⁻¹, 0)) fun i =>
    dSModelEquiv m (0, (L * Real.cosh p.1)⁻¹ •
      Classical.choose (exists_dcoeM_eq p.2
        ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (ne_zero_of_mem_unit_sphere p.2) i :
          EuclideanSpace ℝ (Fin (m + 1))))
        (Submodule.mem_orthogonal_singleton_iff_inner_right.1
          (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (ne_zero_of_mem_unit_sphere p.2) i).2)))

theorem dι_dSFrame_zero (hL : L ≠ 0) (p : deSitterSpace m) :
    dι (I := IdS m) (dSIncl L) p (dSFrame L p 0) =
      (Real.cosh p.1, Real.sinh p.1 • (p.2 : EuclideanSpace ℝ (Fin (m + 1)))) := by
  change dι (I := IdS m) (dSIncl L) p (dSModelEquiv m (L⁻¹, 0)) = _
  rw [dι_dSIncl L p (dSModelEquiv m (L⁻¹, 0))]
  simp only [ContinuousLinearEquiv.symm_apply_apply, map_zero, smul_zero, add_zero]
  refine Prod.ext ?_ ?_
  · show L * Real.cosh p.1 * L⁻¹ = _
    field_simp
  · show (L * Real.sinh p.1 * L⁻¹) • _ = _
    congr 1; field_simp

theorem dι_dSFrame_succ (hL : L ≠ 0) (p : deSitterSpace m) (i : Fin m) :
    dι (I := IdS m) (dSIncl L) p (dSFrame L p i.succ) =
      (0, (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (ne_zero_of_mem_unit_sphere p.2) i :
        EuclideanSpace ℝ (Fin (m + 1)))) := by
  have hc : L * Real.cosh p.1 ≠ 0 := mul_ne_zero hL (Real.cosh_pos p.1).ne'
  change dι (I := IdS m) (dSIncl L) p (dSModelEquiv m (0, (L * Real.cosh p.1)⁻¹ •
      Classical.choose (exists_dcoeM_eq p.2
        ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (ne_zero_of_mem_unit_sphere p.2) i :
          EuclideanSpace ℝ (Fin (m + 1))))
        (Submodule.mem_orthogonal_singleton_iff_inner_right.1
          (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (ne_zero_of_mem_unit_sphere p.2) i).2)))) = _
  erw [dι_dSIncl]
  simp only [ContinuousLinearEquiv.symm_apply_apply, mul_zero, zero_smul, zero_add, map_smul, smul_smul,
    mul_inv_cancel₀ hc, one_smul]
  rw [Classical.choose_spec (exists_dcoeM_eq p.2 _ _)]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (ne_zero_of_mem_unit_sphere p.2) i).2

/-- **De Sitter space is Lorentzian at every point**: the induced form has signature `(-, +, …, +)` on every tangent
space. -/
theorem isLorentzianForm_deSitterSpaceMetric (hL : L ≠ 0) (p : deSitterSpace m) :
    IsLorentzianForm (m + 1) ((deSitterSpaceMetric m L hL).g p) := by
  refine isLorentzianForm_of_frame _ (dSFrame L p) (fun i j => ?_)
    (show Module.finrank ℝ (Fin (m + 1) → ℝ) = m + 1 by simp)
  set b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (ne_zero_of_mem_unit_sphere p.2)
  have hb : ∀ k, ⟪(p.2 : EuclideanSpace ℝ (Fin (m + 1))), (b k : EuclideanSpace ℝ (Fin (m + 1)))⟫ = 0 := fun k =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (b k).2
  rw [deSitterSpaceMetric_apply, eta_apply]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [dι_dSFrame_zero hL, dSForm_apply]
    simp only [inner_smul_left, inner_smul_right, inner_self_sphereM, RCLike.conj_to_real, ite_true, etaDiag,
      Fin.val_zero]
    have := Real.cosh_sq_sub_sinh_sq p.1
    nlinarith [this]
  · rw [dι_dSFrame_zero hL, dι_dSFrame_succ hL, dSForm_apply]
    simp [inner_smul_left, (Fin.succ_ne_zero j').symm]
    exact Or.inr (hb j')
  · rw [dι_dSFrame_zero hL, dι_dSFrame_succ hL, dSForm_apply]
    simp [inner_smul_right, Fin.succ_ne_zero i']
    exact Or.inr (by rw [real_inner_comm]; exact hb i')
  · rw [dι_dSFrame_succ hL, dι_dSFrame_succ hL, dSForm_apply]
    have ho := b.orthonormal
    rw [orthonormal_iff_ite] at ho
    simp only [mul_zero, neg_zero, zero_add, Fin.succ_inj]
    rw [show ⟪(b i' : EuclideanSpace ℝ (Fin (m + 1))), (b j' : EuclideanSpace ℝ (Fin (m + 1)))⟫ = ⟪b i', b j'⟫ from rfl,
      ho i' j']
    by_cases h : i' = j'
    · subst h; simp [etaDiag]
    · simp [h]

/-- **De Sitter space as a Lorentzian manifold**: `ℝ × Sᵐ` with the induced metric, Lorentzian at every point. -/
def deSitterSpaceLorentzian (m : ℕ) (L : ℝ) (hL : L ≠ 0) : LorentzianMetric (IdS m) (deSitterSpace m) (m + 1) where
  toNondegMetric := deSitterSpaceMetric m L hL
  lorentzian p := isLorentzianForm_deSitterSpaceMetric hL p

end Lightlike

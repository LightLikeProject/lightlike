import Lightlike.Spacetime.SpaceForms.DeSitter
import Lightlike.Spacetime.Causal.TimeCylinder

/-!
# Anti-de Sitter space as a manifold: `S¹ × ℝᵐ` with the metric induced from the quadric

Anti-de Sitter space of dimension `m + 1` and radius `L` is here the whole manifold
`antiDeSitterSpace m = S¹ × ℝᵐ` (Mathlib's unit circle `Circle` of `ℂ`, model `𝓡 1`, times `ℝᵐ`, the
model transported to `Fin (m + 1) → ℝ`, the circle first), with the metric `antiDeSitterSpaceMetric m L`
induced by the immersion `ι(θ, y) = (√(L² + |y|²) θ, y)` into `ℝ^{2,m} = ℂ × ℝᵐ` with the form
`B((a, x), (b, y)) = -⟪a, b⟫ + ⟪x, y⟫` of signature `(2, m)`.  The image of `ι` is the whole quadric
`B(x, x) = -L²` (`adsSpaceForm_adsIncl_self`), and `ι` is a diffeomorphism onto it.

**Which space.** The statement is about the quadric itself, `S¹ × ℝᵐ`, whose circle is timelike: it has
closed timelike curves.  Its universal cover `ℝ × ℝᵐ` (often also called anti-de Sitter space) is not
constructed here; local statements such as constant curvature hold for both.

* `contMDiff_adsIncl`, `dι_adsIncl`: the immersion is smooth, with derivative
  `(u, v) ↦ (r⁻¹ ⟪y, v⟫ θ + r dθ(u), v)`, `r = √(L² + |y|²)`;
* `dι_adsIncl_injective`, `adsSpaceForm_adsIncl_dι`, `exists_dι_adsIncl_eq`: `dι` is injective with image
  exactly the `B`-orthogonal complement of `ι(θ, y)`, so the induced form is nondegenerate
  (`pullback_nondeg_of_quadric`);
* `antiDeSitterSpaceMetric`: the metric, a `NondegMetric` on the whole manifold;
* `isLorentzianForm_antiDeSitterSpaceMetric`: at every point it has signature `(-, +, …, +)`, through an
  explicit orthonormal frame (`adsFrame`: the unit tangent vector of the circle, and the images of the
  standard basis under `adsS`, which makes the spatial block `|v|² - ⟪y, v⟫²/r²` the Euclidean one);
  `antiDeSitterSpaceLorentzian` packages it as a `LorentzianMetric`.

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), section 8.1 (anti-de
Sitter space as the hyperboloid `-u² - v² + x₁² + … = -α²` in a flat space of signature `(2, n)`).
-/

open Manifold Metric Bundle Set
open scoped ContDiff RealInnerProductSpace Manifold

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

attribute [local instance] finrank_real_complex_fact'

/-! ## The manifold, the ambient space and the immersion -/

variable (m : ℕ)

/-- **Anti-de Sitter space as a manifold**: `S¹ × ℝᵐ`, with `S¹` the unit circle of `ℂ`. -/
abbrev antiDeSitterSpace : Type := Circle × EuclideanSpace ℝ (Fin m)

/-- the product model of `S¹ × ℝᵐ` -/
abbrev IAdSP : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin m))
    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin m))) :=
  (𝓡 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m))

/-- the identification of the model `ℝ¹ × ℝᵐ` with `Fin (m + 1) → ℝ` (the circle first) -/
def adsModelEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
  (((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).prodCongr
    (EuclideanSpace.equiv (Fin m) ℝ)).trans (Fin.consEquivL ℝ (fun _ : Fin (m + 1) => ℝ))

/-- the model with corners of `S¹ × ℝᵐ` on `Fin (m + 1) → ℝ` -/
abbrev IAdS : ModelWithCorners ℝ (Fin (m + 1) → ℝ)
    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin m))) :=
  (IAdSP m).transContinuousLinearEquiv (adsModelEquiv m)

example : IsManifold (IAdS m) ∞ (antiDeSitterSpace m) := inferInstance

/-- The ambient space `ℝ^{2,m} = ℂ × ℝᵐ`. -/
abbrev AdSAmb : Type := ℂ × EuclideanSpace ℝ (Fin m)

/-- The form `B((a, x), (b, y)) = -⟪a, b⟫ + ⟪x, y⟫` of `ℂ × ℝᵐ`, of signature `(2, m)`. -/
def adsSpaceForm : AdSAmb m →L[ℝ] AdSAmb m →L[ℝ] ℝ :=
  (-LinnerC).bilinearComp (ContinuousLinearMap.fst ℝ ℂ _) (ContinuousLinearMap.fst ℝ ℂ _)
  + (innerSL ℝ : EuclideanSpace ℝ (Fin m) →L[ℝ] _ →L[ℝ] ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ ℂ _) (ContinuousLinearMap.snd ℝ ℂ _)

variable {m}

theorem adsSpaceForm_apply (x y : AdSAmb m) :
    adsSpaceForm m x y = -⟪x.1, y.1⟫ + ⟪x.2, y.2⟫ := by
  simp [adsSpaceForm, LinnerC_apply]

theorem adsSpaceForm_symm (x y : AdSAmb m) : adsSpaceForm m x y = adsSpaceForm m y x := by
  rw [adsSpaceForm_apply, adsSpaceForm_apply, real_inner_comm x.1, real_inner_comm x.2]

/-- The form is nondegenerate. -/
theorem adsSpaceForm_nondeg (u : AdSAmb m) (h : ∀ z, adsSpaceForm m u z = 0) : u = 0 := by
  have h1 := h (u.1, 0)
  have h2 := h (0, u.2)
  rw [adsSpaceForm_apply] at h1 h2
  simp only [inner_zero_right, add_zero, real_inner_self_eq_norm_sq, neg_eq_zero] at h1 h2
  exact Prod.ext (by simpa using h1) (by simpa using h2)

variable (L : ℝ)

/-- The radius `r(y) = √(L² + |y|²)` of the circle over `y`. -/
def adsRad (y : EuclideanSpace ℝ (Fin m)) : ℝ := Real.sqrt (L ^ 2 + ‖y‖ ^ 2)

variable {L}

theorem adsRad_pos (hL : L ≠ 0) (y : EuclideanSpace ℝ (Fin m)) : 0 < adsRad L y :=
  Real.sqrt_pos.2 (by nlinarith [pow_pos (abs_pos.2 hL) 2, sq_abs L, sq_nonneg ‖y‖])

theorem adsRad_sq (y : EuclideanSpace ℝ (Fin m)) : adsRad L y ^ 2 = L ^ 2 + ‖y‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

variable (L)

/-- The map `Φ(z, y) = (r(y) z, y)` of `ℂ × ℝᵐ`. -/
def adsPhi (q : ℂ × EuclideanSpace ℝ (Fin m)) : AdSAmb m := (adsRad L q.2 • q.1, q.2)

/-- The derivative of `Φ` at `(z, y)`. -/
def adsPhiD (z : ℂ) (y : EuclideanSpace ℝ (Fin m)) : (ℂ × EuclideanSpace ℝ (Fin m)) →L[ℝ] AdSAmb m :=
  (((adsRad L y)⁻¹ • (innerSL ℝ y).comp (ContinuousLinearMap.snd ℝ ℂ _)).smulRight z
    + adsRad L y • ContinuousLinearMap.fst ℝ ℂ _).prod (ContinuousLinearMap.snd ℝ ℂ _)

variable {L}

theorem hasFDerivAt_adsRad (hL : L ≠ 0) (z : ℂ) (y : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (fun q : ℂ × EuclideanSpace ℝ (Fin m) => adsRad L q.2)
      ((adsRad L y)⁻¹ • (innerSL ℝ y).comp (ContinuousLinearMap.snd ℝ ℂ _)) (z, y) := by
  have h0 := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℂ) (F := EuclideanSpace ℝ (Fin m)) (p := (z, y))).norm_sq
  have h1 := h0.const_add (L ^ 2)
  have hpos : 0 < L ^ 2 + ‖y‖ ^ 2 := by nlinarith [pow_pos (abs_pos.2 hL) 2, sq_abs L, sq_nonneg ‖y‖]
  have h2 := h1.sqrt hpos.ne'
  refine h2.congr_fderiv ?_
  have hr := (adsRad_pos hL y).ne'
  refine ContinuousLinearMap.ext fun q => ?_
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [adsRad] at hr ⊢
  field_simp

theorem hasFDerivAt_adsPhi (hL : L ≠ 0) (z : ℂ) (y : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (adsPhi L) (adsPhiD L z y) (z, y) := by
  have hX := (hasFDerivAt_adsRad hL z y).smul
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℂ) (F := EuclideanSpace ℝ (Fin m)) (p := (z, y)))
  refine (hX.prodMk hasFDerivAt_snd).congr_fderiv ?_
  ext q <;> simp [adsPhiD, add_comm]

theorem contDiff_adsPhi (hL : L ≠ 0) : ContDiff ℝ ∞ (adsPhi (m := m) L) := by
  have hR : ContDiff ℝ ∞ (fun q : ℂ × EuclideanSpace ℝ (Fin m) => adsRad L q.2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_snd)).sqrt fun q =>
      (Real.sqrt_pos.1 (adsRad_pos hL q.2)).ne'
  exact (hR.smul contDiff_fst).prodMk contDiff_snd

variable (L)

/-- **The immersion of anti-de Sitter space** `ι(θ, y) = (√(L² + |y|²) θ, y)` onto the quadric
`B(x, x) = -L²`. -/
def adsIncl (p : antiDeSitterSpace m) : AdSAmb m := adsPhi L ((p.1 : ℂ), p.2)

/-- The circle point is a unit vector of `ℂ`. -/
theorem inner_self_circle (z : Circle) : ⟪(z : ℂ), (z : ℂ)⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, Circle.norm_coe]; norm_num

/-- The range of the derivative of the inclusion of the circle is the orthogonal complement of the
point. -/
theorem range_dcoeC (z : Circle) : LinearMap.range (dcoeC z : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℂ) = (ℝ ∙ (z : ℂ))ᗮ :=
  range_mvfderiv_subtypeVal (E := ℂ) (n := 1) z

/-- The inclusion maps tangent vectors of the circle to vectors orthogonal to the point. -/
theorem inner_dcoeC (z : Circle) (u : EuclideanSpace ℝ (Fin 1)) : ⟪(z : ℂ), dcoeC z u⟫ = 0 := by
  have h : dcoeC z u ∈ LinearMap.range (dcoeC z : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℂ) := ⟨u, rfl⟩
  rw [range_dcoeC] at h
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 h

/-- Every vector orthogonal to `z` is the image of a tangent vector of the circle at `z`. -/
theorem exists_dcoeC_eq (z : Circle) (c : ℂ) (hc : ⟪(z : ℂ), c⟫ = 0) : ∃ u, dcoeC z u = c := by
  have : c ∈ LinearMap.range (dcoeC z : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℂ) := by
    rw [range_dcoeC]; exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 hc
  obtain ⟨u, hu⟩ := this
  exact ⟨u, hu⟩

variable {L}

/-- The derivative of the immersion with respect to the product model. -/
theorem hasMFDerivAt_adsIncl_prod (hL : L ≠ 0) (p : antiDeSitterSpace m) :
    HasMFDerivAt (IAdSP m) 𝓘(ℝ, AdSAmb m) (adsIncl L) p
      ((adsPhiD L (p.1 : ℂ) p.2).comp
        (((dcoeC p.1).comp (ContinuousLinearMap.fst ℝ _ (EuclideanSpace ℝ (Fin m)))).prod
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin m))))) := by
  have h1 : HasMFDerivAt (IAdSP m) 𝓘(ℝ, ℂ) (fun q : antiDeSitterSpace m => (q.1 : ℂ)) p
      ((dcoeC p.1).comp (ContinuousLinearMap.fst ℝ _ (EuclideanSpace ℝ (Fin m)))) :=
    (hasMFDerivAt_circleCoe p.1).comp p
      (hasMFDerivAt_fst (I := 𝓡 1) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p)
  have h2 : HasMFDerivAt (IAdSP m) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun q : antiDeSitterSpace m => q.2) p
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin m))) :=
    hasMFDerivAt_snd (I := 𝓡 1) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p
  have h3 := h1.prodMk h2
  have h4 : HasMFDerivAt 𝓘(ℝ, ℂ × EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, AdSAmb m) (adsPhi L)
      ((p.1 : ℂ), p.2) (adsPhiD L (p.1 : ℂ) p.2) :=
    (hasFDerivAt_adsPhi hL _ _).hasMFDerivAt
  exact h4.comp p h3

theorem contMDiff_adsIncl (hL : L ≠ 0) : ContMDiff (IAdS m) 𝓘(ℝ, AdSAmb m) ∞ (adsIncl (m := m) L) := by
  have hP : ContMDiff (IAdSP m) 𝓘(ℝ, AdSAmb m) ∞ (adsIncl (m := m) L) := by
    have hq : ContMDiff (IAdSP m) 𝓘(ℝ, ℂ × EuclideanSpace ℝ (Fin m)) ∞
        (fun q : antiDeSitterSpace m => ((q.1 : ℂ), q.2)) :=
      (contMDiff_circleCoe.comp contMDiff_fst).prodMk_space contMDiff_snd
    exact (contDiff_adsPhi hL).contMDiff.comp hq
  exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left (e := adsModelEquiv m)).2 hP

/-- **The derivative of the immersion**: for `w` with components `(u, v) = e⁻¹ w` in `ℝ¹ × ℝᵐ`,
`dι(w) = (r⁻¹ ⟪y, v⟫ θ + r dθ(u), v)`. -/
theorem dι_adsIncl (hL : L ≠ 0) (p : antiDeSitterSpace m) (w : TangentSpace (IAdS m) p) :
    dι (I := IAdS m) (adsIncl L) p w =
      (((adsRad L p.2)⁻¹ * ⟪p.2, ((adsModelEquiv m).symm w).2⟫) • (p.1 : ℂ)
          + adsRad L p.2 • dcoeC p.1 ((adsModelEquiv m).symm w).1,
        ((adsModelEquiv m).symm w).2) := by
  have h := hasMFDerivAt_transContinuousLinearEquiv (adsModelEquiv m) (hasMFDerivAt_adsIncl_prod hL p)
  unfold dι
  rw [h.mfderiv]
  change (adsPhiD L (p.1 : ℂ) p.2)
    ((((dcoeC p.1).comp (ContinuousLinearMap.fst ℝ _ (EuclideanSpace ℝ (Fin m)))).prod
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin m))))
        ((adsModelEquiv m).symm w)) = _
  simp [adsPhiD]

/-- **The image is the quadric** `B(x, x) = -L²`. -/
theorem adsSpaceForm_adsIncl_self (p : antiDeSitterSpace m) :
    adsSpaceForm m (adsIncl L p) (adsIncl L p) = -L ^ 2 := by
  rw [adsSpaceForm_apply]
  simp only [adsIncl, adsPhi, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq, Circle.norm_coe]
  have h := adsRad_sq (L := L) p.2
  nlinarith [h]

/-- The image of `dι` is `B`-orthogonal to the point. -/
theorem adsSpaceForm_adsIncl_dι (hL : L ≠ 0) (p : antiDeSitterSpace m) (w : TangentSpace (IAdS m) p) :
    adsSpaceForm m (adsIncl L p) (dι (I := IAdS m) (adsIncl L) p w) = 0 := by
  rw [dι_adsIncl hL, adsSpaceForm_apply]
  have hr := (adsRad_pos hL p.2).ne'
  simp only [adsIncl, adsPhi, inner_add_right, inner_smul_left, inner_smul_right, inner_self_circle,
    inner_dcoeC, RCLike.conj_to_real]
  field_simp
  ring

/-- `dι` is injective for `L ≠ 0`. -/
theorem dι_adsIncl_injective (hL : L ≠ 0) (p : antiDeSitterSpace m) :
    Function.Injective (dι (I := IAdS m) (adsIncl L) p) := by
  intro a b hab
  rw [← sub_eq_zero]
  set w := a - b with hwdef
  have hw' : dι (I := IAdS m) (adsIncl L) p w = 0 := by rw [hwdef, map_sub, hab, sub_self]
  erw [dι_adsIncl hL] at hw'
  have hr := (adsRad_pos hL p.2).ne'
  have hv : ((adsModelEquiv m).symm w).2 = 0 := by
    have := congrArg Prod.snd hw'
    simpa using this
  have hu : ((adsModelEquiv m).symm w).1 = 0 := by
    have := congrArg Prod.fst hw'
    simp only [hv, inner_zero_right, mul_zero, zero_smul, zero_add, Prod.fst_zero, smul_eq_zero, hr,
      false_or] at this
    exact injective_dcoeC p.1 (this.trans (map_zero _).symm)
  have : (adsModelEquiv m).symm w = 0 := Prod.ext hu hv
  simpa using congrArg (adsModelEquiv m) this

/-- Every vector `B`-orthogonal to the point is in the image of `dι`. -/
theorem exists_dι_adsIncl_eq (hL : L ≠ 0) (p : antiDeSitterSpace m) (z : AdSAmb m)
    (hz : adsSpaceForm m (adsIncl L p) z = 0) : ∃ w, dι (I := IAdS m) (adsIncl L) p w = z := by
  have hr := (adsRad_pos hL p.2).ne'
  set c := (adsRad L p.2)⁻¹ • (z.1 - ((adsRad L p.2)⁻¹ * ⟪p.2, z.2⟫) • (p.1 : ℂ)) with hcdef
  have hc : ⟪(p.1 : ℂ), c⟫ = 0 := by
    rw [adsSpaceForm_apply] at hz
    simp only [adsIncl, adsPhi, inner_smul_left, RCLike.conj_to_real] at hz
    rw [hcdef, inner_smul_right, inner_sub_right, inner_smul_right, inner_self_circle]
    field_simp
    linear_combination -hz
  obtain ⟨u, hu⟩ := exists_dcoeC_eq p.1 c hc
  refine ⟨adsModelEquiv m (u, z.2), ?_⟩
  rw [dι_adsIncl hL p (adsModelEquiv m (u, z.2))]
  simp only [ContinuousLinearEquiv.symm_apply_apply, hu, hcdef, smul_smul]
  refine Prod.ext ?_ rfl
  show _ + (adsRad L p.2 * (adsRad L p.2)⁻¹) • _ = z.1
  rw [mul_inv_cancel₀ hr, one_smul]
  abel

/-- **The metric of anti-de Sitter space** on `S¹ × ℝᵐ`: the pullback `ι* B`, nondegenerate at every
point. -/
def antiDeSitterSpaceMetric (m : ℕ) (L : ℝ) (hL : L ≠ 0) :
    NondegMetric (IAdS m) (antiDeSitterSpace m) :=
  NondegMetric.pullback (adsSpaceForm m) adsSpaceForm_symm (adsIncl L) (contMDiff_adsIncl hL)
    fun p v hv =>
      pullback_nondeg_of_quadric (L := adsSpaceForm m) adsSpaceForm_symm adsSpaceForm_nondeg
        (x := adsIncl L p) (by rw [adsSpaceForm_adsIncl_self]; exact neg_ne_zero.2 (pow_ne_zero 2 hL))
        (dι_adsIncl_injective hL p) (adsSpaceForm_adsIncl_dι hL p) (exists_dι_adsIncl_eq hL p) v hv

theorem antiDeSitterSpaceMetric_apply (hL : L ≠ 0) (p : antiDeSitterSpace m)
    (v w : TangentSpace (IAdS m) p) :
    (antiDeSitterSpaceMetric m L hL).g p v w =
      adsSpaceForm m (dι (I := IAdS m) (adsIncl L) p v) (dι (I := IAdS m) (adsIncl L) p w) :=
  NondegMetric.pullback_apply _ _ _ _ _ p v w

/-! ## Signature -/

variable (L)

/-- The linear map `S v = v + ⟪y, v⟫ / (|L| (r + |L|)) y` of `ℝᵐ`, which turns the induced spatial form
`|v|² - ⟪y, v⟫²/r²` into the Euclidean one (`adsS_spec`). -/
def adsS (y : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  v + (⟪y, v⟫ / (|L| * (adsRad L y + |L|))) • y

variable {L}

/-- **The spatial block in the frame `adsS`** is Euclidean:
`-r⁻² ⟪y, S v⟫ ⟪y, S w⟫ + ⟪S v, S w⟫ = ⟪v, w⟫`. -/
theorem adsS_spec (hL : L ≠ 0) (y v w : EuclideanSpace ℝ (Fin m)) :
    -((adsRad L y)⁻¹ * ⟪y, adsS L y v⟫) * ((adsRad L y)⁻¹ * ⟪y, adsS L y w⟫) +
      ⟪adsS L y v, adsS L y w⟫ = ⟪v, w⟫ := by
  have ha : 0 < |L| := abs_pos.2 hL
  have hr := adsRad_pos hL y
  have hr2 := adsRad_sq (L := L) y
  have ha2 : |L| ^ 2 = L ^ 2 := sq_abs L
  have hyy : ⟪y, y⟫ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  have hS : ∀ u, adsS L y u = u + ((|L| * (adsRad L y + |L|))⁻¹ * ⟪y, u⟫) • y := fun u => by
    rw [adsS]; congr 1; ring
  simp only [hS, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, hyy, real_inner_comm v y, real_inner_comm w y]
  have hs : ‖y‖ ^ 2 = adsRad L y ^ 2 - |L| ^ 2 := by rw [hr2, ha2]; ring
  rw [hs]
  have hra : adsRad L y + |L| ≠ 0 := by positivity
  field_simp
  ring

/-- The unit vector of `ℝ¹`. -/
def u₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

theorem dcoeC_u₀_ne_zero (z : Circle) : dcoeC z u₀ ≠ 0 := by
  intro h
  have h0 : u₀ = 0 := injective_dcoeC z (h.trans (map_zero _).symm)
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h0
  simp [u₀] at this

/-- The orthonormal frame of anti-de Sitter space at `(θ, y)`: the unit tangent vector of the circle,
and the images `S eᵢ` of the standard basis of `ℝᵐ`. -/
def adsFrame (L : ℝ) (p : antiDeSitterSpace m) : Fin (m + 1) → TangentSpace (IAdS m) p :=
  Fin.cons (adsModelEquiv m ((adsRad L p.2 * ‖dcoeC p.1 u₀‖)⁻¹ • u₀, 0))
    fun i => adsModelEquiv m (0, adsS L p.2 (EuclideanSpace.single i 1))

theorem dι_adsFrame_zero (hL : L ≠ 0) (p : antiDeSitterSpace m) :
    dι (I := IAdS m) (adsIncl L) p (adsFrame L p 0) = (‖dcoeC p.1 u₀‖⁻¹ • dcoeC p.1 u₀, 0) := by
  have hr := (adsRad_pos hL p.2).ne'
  rw [show adsFrame L p 0 = adsModelEquiv m ((adsRad L p.2 * ‖dcoeC p.1 u₀‖)⁻¹ • u₀, 0) from rfl,
    dι_adsIncl hL p (adsModelEquiv m ((adsRad L p.2 * ‖dcoeC p.1 u₀‖)⁻¹ • u₀, 0))]
  simp only [ContinuousLinearEquiv.symm_apply_apply, inner_zero_right, mul_zero, zero_smul, zero_add,
    map_smul, smul_smul]
  congr 2
  field_simp

theorem dι_adsFrame_succ (hL : L ≠ 0) (p : antiDeSitterSpace m) (i : Fin m) :
    dι (I := IAdS m) (adsIncl L) p (adsFrame L p i.succ) =
      (((adsRad L p.2)⁻¹ * ⟪p.2, adsS L p.2 (EuclideanSpace.single i 1)⟫) • (p.1 : ℂ),
        adsS L p.2 (EuclideanSpace.single i 1)) := by
  rw [show adsFrame L p i.succ = adsModelEquiv m (0, adsS L p.2 (EuclideanSpace.single i 1)) from rfl,
    dι_adsIncl hL p (adsModelEquiv m (0, adsS L p.2 (EuclideanSpace.single i 1)))]
  simp

/-- **Anti-de Sitter space is Lorentzian at every point**: the induced form has signature
`(-, +, …, +)` on every tangent space. -/
theorem isLorentzianForm_antiDeSitterSpaceMetric (hL : L ≠ 0) (p : antiDeSitterSpace m) :
    IsLorentzianForm (m + 1) ((antiDeSitterSpaceMetric m L hL).g p) := by
  refine isLorentzianForm_of_frame _ (adsFrame L p) (fun i j => ?_)
    (show Module.finrank ℝ (Fin (m + 1) → ℝ) = m + 1 by simp)
  have hd := dcoeC_u₀_ne_zero p.1
  have hn : ‖dcoeC p.1 u₀‖ ≠ 0 := norm_ne_zero_iff.2 hd
  have hz : ∀ c : ℝ, ⟪dcoeC p.1 u₀, c • (p.1 : ℂ)⟫ = 0 := fun c => by
    rw [inner_smul_right, real_inner_comm, inner_dcoeC, mul_zero]
  have hz' : ∀ c : ℝ, ⟪c • (p.1 : ℂ), dcoeC p.1 u₀⟫ = 0 := fun c => by
    rw [real_inner_comm, hz]
  rw [antiDeSitterSpaceMetric_apply, eta_apply]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [dι_adsFrame_zero hL, adsSpaceForm_apply]
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
      inner_zero_right, add_zero, ite_true, etaDiag, Fin.val_zero]
    field_simp
  · rw [dι_adsFrame_zero hL, dι_adsFrame_succ hL, adsSpaceForm_apply]
    simp only [inner_smul_left, hz, RCLike.conj_to_real, mul_zero, neg_zero, inner_zero_left, add_zero,
      (Fin.succ_ne_zero j').symm, ite_false]
  · rw [dι_adsFrame_zero hL, dι_adsFrame_succ hL, adsSpaceForm_apply]
    simp only [inner_smul_right, hz', mul_zero, neg_zero, inner_zero_right, add_zero,
      Fin.succ_ne_zero i', ite_false]
  · rw [dι_adsFrame_succ hL, dι_adsFrame_succ hL, adsSpaceForm_apply]
    simp only [inner_smul_left, inner_smul_right, inner_self_circle, RCLike.conj_to_real, mul_one,
      Fin.succ_inj]
    have h := adsS_spec hL p.2 (EuclideanSpace.single i' 1) (EuclideanSpace.single j' 1)
    refine (show _ = ⟪(EuclideanSpace.single i' 1 : EuclideanSpace ℝ (Fin m)),
      EuclideanSpace.single j' 1⟫ by linarith [h]).trans ?_
    by_cases hij : i' = j'
    · subst hij; simp [etaDiag]
    · simp [hij, EuclideanSpace.inner_single_left]

/-- **Anti-de Sitter space as a Lorentzian manifold**: `S¹ × ℝᵐ` with the induced metric, Lorentzian
at every point. -/
def antiDeSitterSpaceLorentzian (m : ℕ) (L : ℝ) (hL : L ≠ 0) :
    LorentzianMetric (IAdS m) (antiDeSitterSpace m) (m + 1) where
  toNondegMetric := antiDeSitterSpaceMetric m L hL
  lorentzian p := isLorentzianForm_antiDeSitterSpaceMetric hL p

/-- Non-vacuity: four-dimensional anti-de Sitter space `S¹ × ℝ³` of radius `1` is a Lorentzian
manifold. -/
example : LorentzianMetric (IAdS 3) (antiDeSitterSpace 3) 4 := antiDeSitterSpaceLorentzian 3 1 one_ne_zero

/-- Trust check: the base point `(1, 0)` of `S¹ × ℝᵐ` goes to `(|L|, 0)`, on the quadric `B(x, x) = -L²`. -/
example : adsIncl L ((1 : Circle), (0 : EuclideanSpace ℝ (Fin m))) = (((|L| : ℝ) : ℂ), 0) := by
  simp [adsIncl, adsPhi, adsRad, Real.sqrt_sq_eq_abs]

end Lightlike

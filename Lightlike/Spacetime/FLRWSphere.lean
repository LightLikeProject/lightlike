import Mathlib
import Lightlike.Spacetime.SphereMetric
import Lightlike.Spacetime.Lorentzian

/-!
# The FLRW metric on `J × S³` as a smooth nondegenerate metric (CO30, attempt 1)

For an open `J ⊆ ℝ` and `a` smooth and positive on `J`, `flrwSphereMetric` is the metric `-dt² + a(t)² h` on the product manifold `↥J × S³`
(`h` the round metric of the unit sphere, `SphereMetric.lean`), as a `NondegMetric` for the product model `𝓘(ℝ, ℝ).prod (𝓡 3)`.
It is the pullback of the form `-dT² + |dv|² - dc²` on `ℝ × ℝ⁴ × ℝ` by the embedding `(t, x) ↦ (t, a(t) x, a(t))` (so smoothness is
`contMDiff_pullbackForm`); the derivative of the embedding (`hasMFDerivAt_flrwEmb`) and `⟨x, dx u⟩ = 0` give
`g((s, u), (s', u')) = -s s' + a(t)² h(u, u')` (`flrwForm_apply`), from which nondegeneracy follows.

**Limits.** The metric and its Lorentzian signature (`flrwLorentzMetric`): the connection, the Einstein equations and the Friedmann equations on this manifold are not here.
-/

open Manifold Metric Bundle TopologicalSpace
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

/-- The Euclidean space `ℝ⁴` in which the unit sphere `S³` lies. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin (3 + 1))
/-- the model of `↥J × S³` -/
abbrev IJS : ModelWithCorners ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) :=
  𝓘(ℝ, ℝ).prod (𝓡 3)

example (J : Opens ℝ) : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) (↥J × S3) := inferInstance
example (J : Opens ℝ) : IsManifold IJS ∞ (↥J × S3) := inferInstance

/-- The space `ℝ × ℝ⁴ × ℝ`, with the form `Lmink` (`-dt² + |dx|² - ds²`), into which `J × S³` is mapped by `flrwEmb`. -/
abbrev W : Type := ℝ × E4 × ℝ

/-- the inner product as a bilinear continuous map -/
def Linner : E4 →L[ℝ] E4 →L[ℝ] ℝ := innerSL ℝ

/-- the form `-dT² + |dv|² - dc²` on `ℝ × E4 × ℝ` -/
def Lmink : W →L[ℝ] W →L[ℝ] ℝ :=
  (-(ContinuousLinearMap.mul ℝ ℝ)).bilinearComp (ContinuousLinearMap.fst ℝ ℝ (E4 × ℝ)) (ContinuousLinearMap.fst ℝ ℝ (E4 × ℝ))
  + Linner.bilinearComp ((ContinuousLinearMap.fst ℝ E4 ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E4 × ℝ)))
      ((ContinuousLinearMap.fst ℝ E4 ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E4 × ℝ)))
  - (ContinuousLinearMap.mul ℝ ℝ).bilinearComp ((ContinuousLinearMap.snd ℝ E4 ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E4 × ℝ)))
      ((ContinuousLinearMap.snd ℝ E4 ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E4 × ℝ)))

theorem Lmink_apply (x y : W) : Lmink x y = -(x.1 * y.1) + inner ℝ x.2.1 y.2.1 - x.2.2 * y.2.2 := by
  simp [Lmink, Linner]
  rfl

theorem Lmink_symm (x y : W) : Lmink x y = Lmink y x := by
  rw [Lmink_apply, Lmink_apply, real_inner_comm]; ring
/-- The inclusion of an open subset of `ℝ` has the identity as derivative. -/
theorem hasMFDerivAt_opens_val (J : Opens ℝ) (t : J) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : J → ℝ) t
      (ContinuousLinearMap.id ℝ ℝ : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (t : ℝ)) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp, Function.comp_id]
  have hev : (Subtype.val ∘ (extChartAt 𝓘(ℝ, ℝ) t).symm) =ᶠ[nhdsWithin ((extChartAt 𝓘(ℝ, ℝ) t) t) (Set.range 𝓘(ℝ, ℝ))]
      id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin t] with y hy
    have h2 := OpenPartialHomeomorph.subtypeRestr_symm_apply (OpenPartialHomeomorph.refl ℝ) ⟨t⟩ (U := J) (y := y)
    simp [extChartAt, Opens.chartAt_eq] at hy ⊢
    exact h2 hy
  have : HasFDerivWithinAt (id : ℝ → ℝ) (ContinuousLinearMap.id ℝ ℝ) (Set.range 𝓘(ℝ, ℝ)) ((extChartAt 𝓘(ℝ, ℝ) t) t) :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  exact this.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin (by simp))

/-- The embedding `(t, x) ↦ (t, a(t) x, a(t))` of `J × S³` into `ℝ × ℝ⁴ × ℝ`. -/
def flrwEmb {J : Opens ℝ} (a : ℝ → ℝ) (p : ↥J × S3) : W := ((p.1 : ℝ), a p.1 • (p.2 : E4), a p.1)


/-- The time coordinate `p ↦ t` of `J × S³` is smooth. -/
theorem contMDiff_flrwT (J : Opens ℝ) : ContMDiff IJS 𝓘(ℝ, ℝ) ∞ (fun p : ↥J × S3 => (p.1 : ℝ)) :=
  (contMDiff_subtype_val (I := 𝓘(ℝ, ℝ)) (U := J) (n := ∞)).comp contMDiff_fst

/-- The embedding is smooth when `a` is smooth on `J`. -/
theorem contMDiff_flrwEmb {J : Opens ℝ} {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) :
    ContMDiff IJS 𝓘(ℝ, W) ∞ (flrwEmb (J := J) a) := by
  have hT := contMDiff_flrwT J
  have hA : ContMDiff IJS 𝓘(ℝ, ℝ) ∞ (fun p : ↥J × S3 => a (p.1 : ℝ)) := by
    intro p
    exact ((ha.contDiffAt (J.isOpen.mem_nhds p.1.2)).contMDiffAt).comp p (hT p)
  have hX : ContMDiff IJS 𝓘(ℝ, E4) ∞ (fun p : ↥J × S3 => (p.2 : E4)) :=
    contMDiff_sphereIncl.comp contMDiff_snd
  exact hT.prodMk_space (hA.smul hX |>.prodMk_space hA)


/-- The derivative of the sphere inclusion as a plain continuous linear map. -/
def dcoe (x : S3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] E4 := mfderiv (𝓡 3) 𝓘(ℝ, E4) sphereIncl x

/-- The map `Φ(t, v) = (t, a(t) v, a(t))` on `ℝ × ℝ⁴`. -/
def flrwPhi (a : ℝ → ℝ) (q : ℝ × E4) : W := (q.1, a q.1 • q.2, a q.1)

/-- The derivative of `Φ`. -/
def flrwPhiD (a' a t : ℝ) (v : E4) : (ℝ × E4) →L[ℝ] W :=
  (ContinuousLinearMap.fst ℝ ℝ E4).prod
    ((a' • (ContinuousLinearMap.fst ℝ ℝ E4).smulRight v + a • ContinuousLinearMap.snd ℝ ℝ E4).prod
      (a' • ContinuousLinearMap.fst ℝ ℝ E4))

theorem hasFDerivAt_flrwPhi {a : ℝ → ℝ} {t : ℝ} (ha : DifferentiableAt ℝ a t) (v : E4) :
    HasFDerivAt (flrwPhi a) (flrwPhiD (deriv a t) (a t) t v) (t, v) := by
  have h1 : HasFDerivAt (fun q : ℝ × E4 => q.1) (ContinuousLinearMap.fst ℝ ℝ E4) (t, v) := hasFDerivAt_fst
  have hA : HasFDerivAt (fun q : ℝ × E4 => a q.1) (deriv a t • ContinuousLinearMap.fst ℝ ℝ E4) (t, v) := by
    have := ha.hasDerivAt.hasFDerivAt.comp (t, v) h1
    refine this.congr_fderiv ?_
    ext <;> simp
  have hS : HasFDerivAt (fun q : ℝ × E4 => a q.1 • q.2)
      (deriv a t • (ContinuousLinearMap.fst ℝ ℝ E4).smulRight v + a t • ContinuousLinearMap.snd ℝ ℝ E4) (t, v) := by
    have := hA.smul (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := E4) (p := (t, v)))
    refine this.congr_fderiv ?_
    ext <;> simp [add_comm]
  exact h1.prodMk (hS.prodMk hA)


/-- The derivative of the sphere inclusion at `x`. -/
theorem hasMFDerivAt_sphereIncl (x : S3) :
    HasMFDerivAt (𝓡 3) 𝓘(ℝ, E4) sphereIncl x (dcoe x) :=
  (contMDiff_sphereIncl.mdifferentiableAt (by simp)).hasMFDerivAt

/-- **The derivative of the embedding** `(t, x) ↦ (t, a(t) x, a(t))`. -/
theorem hasMFDerivAt_flrwEmb {J : Opens ℝ} {a : ℝ → ℝ} (p : ↥J × S3) (ha : DifferentiableAt ℝ a (p.1 : ℝ)) :
    HasMFDerivAt IJS 𝓘(ℝ, W) (flrwEmb (J := J) a) p
      ((flrwPhiD (deriv a (p.1 : ℝ)) (a p.1) p.1 (p.2 : E4)).comp
        ((ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3))).prod
          ((dcoe p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))))) := by
  have h1 : HasMFDerivAt IJS 𝓘(ℝ, ℝ) (fun q : ↥J × S3 => (q.1 : ℝ)) p
      ((ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) :=
    (hasMFDerivAt_opens_val J p.1).comp p (hasMFDerivAt_fst p)
  have h2 : HasMFDerivAt IJS 𝓘(ℝ, E4) (fun q : ↥J × S3 => (q.2 : E4)) p
      ((dcoe p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) :=
    (hasMFDerivAt_sphereIncl p.2).comp p (hasMFDerivAt_snd p)
  have h3 := h1.prodMk h2
  have h4 : HasMFDerivAt 𝓘(ℝ, ℝ × E4) 𝓘(ℝ, W) (flrwPhi a) ((p.1 : ℝ), (p.2 : E4))
      (flrwPhiD (deriv a (p.1 : ℝ)) (a p.1) p.1 (p.2 : E4)) :=
    (hasFDerivAt_flrwPhi ha (p.2 : E4)).hasMFDerivAt
  exact h4.comp p h3


/-- The inclusion maps tangent vectors of the sphere to vectors orthogonal to the point. -/
theorem inner_dcoe (x : S3) (u : EuclideanSpace ℝ (Fin 3)) : inner ℝ (x : E4) (dcoe x u) = 0 := by
  have h2 := range_mfderiv_coe_sphere (E := E4) (n := 3) x
  have h : dcoe x u ∈ (mfderiv (𝓡 3) 𝓘(ℝ, E4) ((↑) : S3 → E4) x : TangentSpace (𝓡 3) x →L[ℝ] E4).range :=
    ⟨u, rfl⟩
  rw [h2] at h
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h)


/-- The FLRW form `-dt² + a(t)² h` on `J × S³`, as the pullback of `Lmink` by the embedding. -/
def flrwForm {J : Opens ℝ} (a : ℝ → ℝ) (p : ↥J × S3) :
    TangentSpace IJS p →L[ℝ] TangentSpace IJS p →L[ℝ] ℝ :=
  pullbackForm (I := IJS) Lmink (flrwEmb (J := J) a) p

/-- **The value of the FLRW form**: `g((s, u), (s', u')) = -s s' + a(t)² h(u, u')`. -/
theorem flrwForm_apply {J : Opens ℝ} {a : ℝ → ℝ} (p : ↥J × S3) (ha : DifferentiableAt ℝ a (p.1 : ℝ))
    (v w : TangentSpace IJS p) :
    flrwForm a p v w = -(v.1 * w.1) + a p.1 ^ 2 * inner ℝ (dcoe p.2 v.2) (dcoe p.2 w.2) := by
  unfold flrwForm
  rw [pullbackForm_apply, dι, (hasMFDerivAt_flrwEmb p ha).mfderiv, Lmink_apply]
  have hx : inner ℝ (p.2 : E4) (p.2 : E4) = 1 := by
    rw [real_inner_self_eq_norm_sq]; simp
  have e : ∀ u : ℝ × EuclideanSpace ℝ (Fin 3),
      ((flrwPhiD (deriv a (p.1 : ℝ)) (a p.1) p.1 (p.2 : E4)).comp
        ((ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3))).prod
          ((dcoe p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))))) u =
      (u.1, deriv a (p.1 : ℝ) • u.1 • (p.2 : E4) + a p.1 • dcoe p.2 u.2, deriv a (p.1 : ℝ) * u.1) := fun u => by
    simp [flrwPhiD, mul_comm]
  erw [e v, e w]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hx, real_inner_comm (p.2 : E4)]
  rw [inner_dcoe, inner_dcoe]
  simp
  ring


/-- **The FLRW metric on `J × S³`**, `-dt² + a(t)² h` with `h` the round metric of the unit sphere, for `a` smooth and positive on `J`. -/
def flrwSphereMetric (J : Opens ℝ) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t) :
    NondegMetric IJS (↥J × S3) where
  g := flrwForm a
  symm p v w := pullbackForm_symm Lmink_symm _ p v w
  nondegenerate p v h := by
    have hd : DifferentiableAt ℝ a (p.1 : ℝ) :=
      ((ha.contDiffAt (J.isOpen.mem_nhds p.1.2)).differentiableAt (by simp))
    have hapos : 0 < a p.1 := hpos _ p.1.2
    have h1 := (flrwForm_apply p hd v (show TangentSpace IJS p from ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))))).symm.trans
      (h (show TangentSpace IJS p from ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))))
    have hv1 : v.1 = 0 := by
      simp at h1
      linarith
    have h2 := (flrwForm_apply p hd v (show TangentSpace IJS p from ((0 : ℝ), v.2))).symm.trans
      (h (show TangentSpace IJS p from ((0 : ℝ), v.2)))
    have h4 : dcoe p.2 v.2 = 0 := by
      simp at h2
      rcases h2 with h2 | h2
      · exact absurd h2 hapos.ne'
      · exact h2
    have h5 : v.2 = 0 := (injective_mvfderiv_subtypeVal_sphere (E := E4) p.2) (h4.trans (map_zero _).symm)
    exact Prod.ext hv1 h5
  contMDiff := contMDiff_pullbackForm Lmink (contMDiff_flrwEmb ha)

/-- The tangent vectors of the sphere form a 3-dimensional space isometric (via `dcoe`) to `(ℝ ∙ x)ᗮ`: there is a basis of
`E3` orthonormal for the pullback of the inner product. -/
theorem exists_round_orthonormal (x : S3) :
    ∃ b : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      ∀ i j, inner ℝ (dcoe x (b i)) (dcoe x (b j)) = if i = j then (1 : ℝ) else 0 := by
  have hinj : Function.Injective (dcoe x) := injective_mvfderiv_subtypeVal_sphere (E := E4) x
  let T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] E4 := (dcoe x : EuclideanSpace ℝ (Fin 3) →L[ℝ] E4)
  have hfr : Module.finrank ℝ (LinearMap.range T) = 3 := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  let b0 : OrthonormalBasis (Fin 3) ℝ (LinearMap.range T) :=
    (stdOrthonormalBasis ℝ (LinearMap.range T)).reindex (finCongr hfr)
  let e : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] LinearMap.range T := LinearEquiv.ofInjective T hinj
  refine ⟨b0.toBasis.map e.symm, fun i j => ?_⟩
  have hT : ∀ i, dcoe x ((b0.toBasis.map e.symm) i) = ((b0 i : LinearMap.range T) : E4) := by
    intro i
    simp only [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
    have := e.apply_symm_apply (b0 i)
    exact congrArg Subtype.val this
  rw [hT, hT]
  have := b0.inner_eq_ite i j
  simpa using this

/-- **A form `-s s' + c² h(u, u')` on `ℝ × E3` with `h` the round metric at `x` is Lorentzian** (a Lorentz frame is `∂_t` and the round
orthonormal frame divided by `c`). -/
theorem isLorentzianForm_flrw (x : S3) {c : ℝ} (hc : 0 < c)
    (B : (ℝ × EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = -(v.1 * w.1) + c ^ 2 * inner ℝ (dcoe x v.2) (dcoe x w.2)) : IsLorentzianForm 4 B := by
  obtain ⟨b, hb⟩ := exists_round_orthonormal x
  let fe : Fin 1 ⊕ Fin 3 ≃ Fin 4 := finSumFinEquiv
  let B2 : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
    b.map (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin 3)) c⁻¹ (inv_ne_zero hc.ne'))
  let B1 : Module.Basis (Fin 1) ℝ ℝ := Module.Basis.singleton (Fin 1) ℝ
  let Bs : Module.Basis (Fin 4) ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) := (B1.prod B2).reindex fe
  refine ⟨Bs, fun i j => ?_⟩
  obtain ⟨k, rfl⟩ := fe.surjective i
  obtain ⟨l, rfl⟩ := fe.surjective j
  have hB' : ∀ m, Bs (fe m) = (B1.prod B2) m := fun m => by
    show ((B1.prod B2).reindex fe) (fe m) = _
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  have e1 : ∀ k : Fin 1, Bs (fe (Sum.inl k)) = ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) := fun k => by
    rw [hB']; simp [B1]
  have e2 : ∀ k : Fin 3, Bs (fe (Sum.inr k)) = ((0 : ℝ), c⁻¹ • b k) := fun k => by
    rw [hB']; simp [B2]
  have hx : ∀ k l : Fin 3, inner ℝ (dcoe x (c⁻¹ • b k)) (dcoe x (c⁻¹ • b l)) =
      (c⁻¹) ^ 2 * (if k = l then (1 : ℝ) else 0) := fun k l => by
    rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_right, hb]; ring
  have hcne : c ≠ 0 := hc.ne'
  have hd0 : etaDiag (fe (Sum.inl (0 : Fin 1))) = -1 := by
    have h0 : ((fe (Sum.inl (0 : Fin 1)) : Fin 4) : ℕ) = 0 := rfl
    unfold etaDiag; rw [if_pos h0]
  have hd1 : ∀ k : Fin 3, etaDiag (fe (Sum.inr k)) = 1 := fun k => by
    have h1 : ((fe (Sum.inr k) : Fin 4) : ℕ) = 1 + k := rfl
    unfold etaDiag; rw [if_neg (by rw [h1]; omega)]
  have hne : ∀ (k : Fin 1) (l : Fin 3), fe (Sum.inl k) ≠ fe (Sum.inr l) := fun k l h => by
    simpa using fe.injective h
  rcases k with k | k <;> rcases l with l | l
  · rw [e1, e1, hB]
    have hk : k = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    subst hk hl
    rw [eta_apply, if_pos rfl, hd0]
    simp
  · rw [e1, e2, hB, eta_apply, if_neg (hne _ _)]
    simp
  · rw [e2, e1, hB, eta_apply, if_neg (hne _ _).symm]
    simp
  · rw [e2, e2, hB, hx, eta_apply]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, hd1]
      simp
      field_simp
    · rw [if_neg hkl, if_neg (fun h => hkl (Sum.inr.inj (fe.injective h)))]
      simp


/-- **The FLRW metric on `J × S³` is Lorentzian** (signature `−+++`), for `a` smooth and positive on `J`. -/
def flrwLorentzMetric (J : Opens ℝ) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t) :
    LorentzianMetric IJS (↥J × S3) 4 where
  toNondegMetric := flrwSphereMetric J ha hpos
  lorentzian p := by
    have hd : DifferentiableAt ℝ a (p.1 : ℝ) :=
      ((ha.contDiffAt (J.isOpen.mem_nhds p.1.2)).differentiableAt (by simp))
    exact isLorentzianForm_flrw p.2 (hpos _ p.1.2) (flrwForm a p) (fun v w => flrwForm_apply p hd v w)

end Lightlike

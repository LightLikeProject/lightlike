import Mathlib
import Lightlike.Dirac.SpinPrincipalEquiv
import Lightlike.Bundles.SpinLocalSection
import Lightlike.Bundles.Manifold.VectorBundle.GramSchmidt

/-!
# Every lift of the orthonormal frame bundle through `Spin(n) → SO(n)` has a smooth spin atlas

Let `L` be a lift of the orthonormal frame bundle of a manifold with a positive definite metric
through the vector action `Spin(n) → SO(n)` (`SpinLift`, Lawson–Michelsohn II Def. 1.3, with no
smoothness assumed).  This file proves that `L` carries a smooth spin atlas
(`SpinStructure.SmoothSpinAtlas`): local sections whose frames are smooth and whose transition
elements are smooth.

* Smooth local sections (`SpinLift.exists_smooth_section`): a continuous local section `s₀` (the
  points with coordinate `1` in a trivialization) is corrected by `spinOfFrame W`, the explicit
  local inverse of the vector action (`Lightlike.Bundles.SpinLocalSection`) applied to the
  coordinates `W` in the frame of `s₀` of a smooth orthonormal frame with the same value at the
  base point (Gram–Schmidt, `NondegMetric.exists_smooth_orthonormal_frame`).
* Transitions (`SpinLift.contMDiffAt_division`): for two continuous local sections with smooth
  frames, the transition element `d` has the smooth rotation matrix `Rot` of the two frames as
  vector action.  Near a point `y₀`, `d(y₀)⁻¹ d(y)` and the explicit local inverse
  `spinOfFrame` of the vector action applied to `d(y₀)⁻¹ Rot(y)` agree up to the kernel `{±1}`,
  and by continuity they agree; so `d = d(y₀) · spinOfFrame (…)` is smooth.
* `SpinLift.smoothSpinAtlas` and `SpinLift.exists_spinStructure_equiv`: every lift has a smooth
  spin atlas, hence is equivalent to the principal bundle `SpinStructure.principal` of a spin
  structure in atlas form.  With `SpinStructure.principal` this is the equivalence of the
  principal-bundle definition (Lawson–Michelsohn II Def. 1.3, for any lift) with the atlas form,
  with no side condition.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, Definition 1.3.
-/

open Bundle Manifold CliffordAlgebra Filter Set MulOpposite
open scoped Manifold ContDiff Topology InnerProductSpace RealInnerProductSpace

namespace Lightlike.Dirac

variable {n : ℕ}
  {M : Type} [TopologicalSpace M] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Fin n → ℝ) H} [ChartedSpace H M] [IsManifold I ∞ M]
  {g : NondegMetric I M} {hpos : ∀ x (v : TangentSpace I x), v ≠ 0 → 0 < g.g x v v}

/-- The Riemannian bundle of a positive definite smooth metric is a smooth Riemannian bundle. -/
lemma _root_.Lightlike.NondegMetric.isContMDiffRiemannianBundleOfPos :
    letI := g.riemannianBundleOfPos hpos
    IsContMDiffRiemannianBundle I ∞ (Fin n → ℝ) (fun x : M => TangentSpace I x) :=
  letI := g.riemannianBundleOfPos hpos
  ⟨⟨g.g, g.contMDiff, fun _ _ _ => rfl⟩⟩

/-- A spin element preserves inner products of vectors. -/
lemma inner_vecConj (s : spinGroup (Qneg n)) (v w : E n) :
    ⟪vecConj s v, vecConj s w⟫ = ⟪v, w⟫ := by
  rw [← vecIso_apply, ← vecIso_apply, LinearIsometryEquiv.inner_map_map]

/-- The transformed standard frame `a ↦ vecConj s (e a)` is orthonormal. -/
lemma isOrthonormalFrame_vecConj (s : spinGroup (Qneg n)) :
    IsOrthonormalFrame fun a => vecConj s (e a) := fun a b => by
  rw [inner_vecConj]; exact isOrthonormalFrame_e a b

/-- A spin element is determined up to sign by its vector action on the standard frame. -/
lemma eq_or_eq_neg_of_vecConj_e {s t : spinGroup (Qneg n)}
    (h : ∀ a, vecConj s (e a) = vecConj t (e a)) :
    (s : CliffordAlgebra (Qneg n)) * star (t : CliffordAlgebra (Qneg n)) = 1 ∨
      (s : CliffordAlgebra (Qneg n)) * star (t : CliffordAlgebra (Qneg n)) = -1 := by
  have hst : ∀ v, vecConj (s * t⁻¹) v = v := by
    intro v
    have hlin : vecConj s = vecConj t := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro a
      simpa [e] using h a
    rw [vecConj_mul, hlin, ← vecConj_mul, mul_inv_cancel, vecConj_one]
  have := (vecConj_eq_id_iff (s * t⁻¹)).1 hst
  exact this

/-- The scalars `1` and `-1` of `Cl(ℝⁿ, -‖·‖²)` differ. -/
lemma one_ne_neg_one_cl : (1 : CliffordAlgebra (Qneg n)) ≠ -1 := by
  intro h
  have h2 : (algebraMap ℝ (CliffordAlgebra (Qneg n))) 1 = algebraMap ℝ _ (-1) := by
    rw [map_neg, map_one]; exact h
  have := algebraMap_injective_Qneg h2
  norm_num at this

/-! ## Transitions -/

section Transition

variable (L : SpinLift g hpos)

/-- The vector action of the transition element of two points of a fibre is the matrix of the
second frame in the first: `vecConj (division p q) (e a) = (g (F_p e_b, F_q e_a))_b`. -/
lemma SpinLift.vecConj_division (y : M) (p q : letI := g.riemannianBundleOfPos hpos; L.P y)
    (a : Fin n) :
    letI := g.riemannianBundleOfPos hpos
    vecConj (PrincipalBundle.division (spinGroup (Qneg n)) p q) (e a) =
      WithLp.toLp 2 (fun b => g.g y (L.frameAt y p (e b)) (L.frameAt y q (e a))) := by
  let _ := g.riemannianBundleOfPos hpos
  have hq : q = op (PrincipalBundle.division (spinGroup (Qneg n)) p q) • p :=
    (PrincipalBundle.smul_division p q).symm
  ext b
  change _ = g.g y (L.frameAt y p (e b)) (L.frameAt y q (e a))
  conv_rhs => rw [hq]
  rw [SpinStructure.SmoothSpinAtlas.frameAt_smul, SpinStructure.SmoothSpinAtlas.g_frameAt]
  simp [e, EuclideanSpace.inner_single_left]

/-- **The transition elements of two continuous local sections with smooth frames are smooth.**
Every linear coordinate of `y ↦ division (s₁ y) (s₂ y)` is smooth at `y₀`. -/
theorem SpinLift.contMDiffAt_division
    (s₁ s₂ : letI := g.riemannianBundleOfPos hpos; (x : M) → L.P x) (y₀ : M)
    (h₁ : letI := g.riemannianBundleOfPos hpos
      ContinuousAt (fun x => TotalSpace.mk' (spinGroup (Qneg n)) x (s₁ x)) y₀)
    (h₂ : letI := g.riemannianBundleOfPos hpos
      ContinuousAt (fun x => TotalSpace.mk' (spinGroup (Qneg n)) x (s₂ x)) y₀)
    (hf₁ : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun y => (⟨y, L.frameAt y (s₁ y) (e a)⟩ : TangentBundle I M)) y₀)
    (hf₂ : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun y => (⟨y, L.frameAt y (s₂ y) (e a)⟩ : TangentBundle I M)) y₀)
    (φ : Module.Dual ℝ (CliffordAlgebra (Qneg n))) :
    letI := g.riemannianBundleOfPos hpos
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => φ (PrincipalBundle.division (spinGroup (Qneg n)) (s₁ y) (s₂ y) :
        CliffordAlgebra (Qneg n))) y₀ := by
  let _ := g.riemannianBundleOfPos hpos
  have _ := (Lightlike.NondegMetric.isContMDiffRiemannianBundleOfPos (g := g) (hpos := hpos))
  let _ := clNormedRing n
  let _ := clNormedAlgebra n
  set d : M → spinGroup (Qneg n) := fun y =>
    PrincipalBundle.division (spinGroup (Qneg n)) (s₁ y) (s₂ y) with hd_def
  have hd : ContinuousAt d y₀ := h₁.division h₂
  -- the rotation matrix of the two frames, smooth
  set Rot : M → Fin n → E n := fun y a =>
    WithLp.toLp 2 (fun b => g.g y (L.frameAt y (s₁ y) (e b)) (L.frameAt y (s₂ y) (e a)))
  have hRot : ∀ y a, vecConj (d y) (e a) = Rot y a := fun y a =>
    L.vecConj_division y (s₁ y) (s₂ y) a
  have hRots : ContMDiffAt I 𝓘(ℝ, Fin n → E n) ∞ Rot y₀ := by
    refine contMDiffAt_pi_module_iff.2 fun a => ?_
    have hc : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞
        (fun y => fun b => g.g y (L.frameAt y (s₁ y) (e b)) (L.frameAt y (s₂ y) (e a))) y₀ :=
      contMDiffAt_pi_module_iff.2 fun b => ContMDiffAt.inner_bundle (hf₁ b) (hf₂ a)
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff.contDiffAt
      |>.comp_contMDiffAt hc
  -- conjugate back by the value at `y₀`
  set c := d y₀
  set A : (Fin n → E n) →L[ℝ] (Fin n → E n) :=
    ContinuousLinearMap.pi fun a => ((vecIso c⁻¹ : E n ≃ₗᵢ[ℝ] E n) : E n →L[ℝ] E n).comp
      (ContinuousLinearMap.proj a)
  set W : M → Fin n → E n := fun y => A (Rot y)
  have hWs : ContMDiffAt I 𝓘(ℝ, Fin n → E n) ∞ W y₀ := A.contDiff.contDiffAt.comp_contMDiffAt hRots
  set t : M → spinGroup (Qneg n) := fun y => c⁻¹ * d y
  have hWt : ∀ y, W y = fun a => vecConj (t y) (e a) := fun y => by
    funext a
    change vecConj c⁻¹ (Rot y a) = _
    rw [← hRot, ← vecConj_mul]
  have hW0 : W y₀ = e := by
    rw [hWt]; funext a; simp only [t, c, inv_mul_cancel, vecConj_one]
  have hgood0 : FrameGood (W y₀) := hW0 ▸ frameGood_e
  have hgood : ∀ᶠ y in 𝓝 y₀, FrameGood (W y) :=
    hWs.continuousAt.preimage_mem_nhds (isOpen_frameGood.mem_nhds hgood0)
  -- the explicit lift and the transition element agree near `y₀`
  have hσc : ContinuousAt (fun y => spinOfFrame (W y)) y₀ :=
    (contDiffAt_spinPartial n (W y₀) ((frameGood_iff _).1 hgood0)).continuousAt.comp
      hWs.continuousAt
  have hcoe : Continuous fun s : spinGroup (Qneg n) => (s : CliffordAlgebra (Qneg n)) :=
    continuous_spinGroup_iff.1 continuous_id
  have htc : ContinuousAt (fun y => ((t y)⁻¹ : spinGroup (Qneg n))) y₀ :=
    (continuousAt_const.mul hd).inv
  have hprod : ContinuousAt (fun y => spinOfFrame (W y) * (((t y)⁻¹ : spinGroup (Qneg n)) :
      CliffordAlgebra (Qneg n))) y₀ := hσc.mul (hcoe.continuousAt.comp htc)
  have hval : spinOfFrame (W y₀) * (((t y₀)⁻¹ : spinGroup (Qneg n)) : CliffordAlgebra (Qneg n)) = 1 := by
    rw [hW0, spinOfFrame_standard, one_mul]
    simp [t, c]
  have hne : ∀ᶠ y in 𝓝 y₀, spinOfFrame (W y) * (((t y)⁻¹ : spinGroup (Qneg n)) :
      CliffordAlgebra (Qneg n)) ≠ -1 :=
    hprod.preimage_mem_nhds (isOpen_ne.mem_nhds (hval ▸ one_ne_neg_one_cl))
  have heq : ∀ᶠ y in 𝓝 y₀, (d y : CliffordAlgebra (Qneg n)) = c * spinOfFrame (W y) := by
    filter_upwards [hgood, hne] with y hy hy2
    have hON : IsOrthonormalFrame (W y) := by rw [hWt]; exact isOrthonormalFrame_vecConj _
    set σ : spinGroup (Qneg n) := ⟨spinOfFrame (W y), spinOfFrame_mem hON hy⟩
    have hlift : ∀ a, vecConj σ (e a) = vecConj (t y) (e a) := fun a => by
      rw [vecConj_spinOfFrame hON hy, hWt]
    have h := eq_or_eq_neg_of_vecConj_e hlift
    have hinv : (((t y)⁻¹ : spinGroup (Qneg n)) : CliffordAlgebra (Qneg n)) =
        star (t y : CliffordAlgebra (Qneg n)) := by
      rw [← spinGroup.star_eq_inv]; rfl
    have h1 : (σ : CliffordAlgebra (Qneg n)) * star (t y : CliffordAlgebra (Qneg n)) = 1 :=
      h.resolve_right (by rw [← hinv]; exact hy2)
    have h2 : σ * (t y)⁻¹ = 1 := Subtype.ext (by rw [Submonoid.coe_mul, hinv]; exact h1)
    have h3 : σ = t y := by rw [← mul_inv_eq_one]; exact h2
    have h4 : d y = c * σ := by rw [h3]; simp [t]
    rw [h4]; rfl
  -- conclude
  have hsm : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (φ ∘ₗ LinearMap.mulLeft ℝ (c : CliffordAlgebra (Qneg n))) (spinOfFrame (W y))) y₀ :=
    (contDiffAt_spinOfFrame _ hgood0).comp_contMDiffAt hWs
  refine hsm.congr_of_eventuallyEq ?_
  filter_upwards [heq] with y hy
  change φ (d y : CliffordAlgebra (Qneg n)) = _
  rw [hy]; rfl

end Transition

/-! ## Frames of a lift -/

section Frames

variable (L : SpinLift g hpos)

/-- The frame of a point of a lift is onto: every tangent vector is the frame applied to its
coordinates `(g (F e_b, w))_b`. -/
lemma SpinLift.frameAt_coords (y : M) (p : letI := g.riemannianBundleOfPos hpos; L.P y)
    (w : TangentSpace I y) :
    L.frameAt y p (WithLp.toLp 2 fun b => g.g y (L.frameAt y p (e b)) w) = w := by
  let _ := g.riemannianBundleOfPos hpos
  have hsurj : ∃ v, L.frameAt y p v = w := by
    have hproj := L.proj_toFrame ⟨y, p⟩
    unfold SpinLift.frameAt
    generalize L.toFrame ⟨y, p⟩ = F at hproj ⊢
    obtain ⟨x, f⟩ := F
    simp only at hproj
    subst hproj
    exact ⟨f.symm w, f.apply_symm_apply w⟩
  obtain ⟨v, rfl⟩ := hsurj
  congr 1
  ext b
  change g.g y (L.frameAt y p (e b)) (L.frameAt y p v) = v b
  rw [SpinStructure.SmoothSpinAtlas.g_frameAt]
  simp [e, EuclideanSpace.inner_single_left]

/-- The frames of a continuous local section are continuous sections of the tangent bundle. -/
lemma SpinLift.continuousAt_frameAt {s : letI := g.riemannianBundleOfPos hpos; (x : M) → L.P x}
    {y₀ : M} (hs : letI := g.riemannianBundleOfPos hpos
      ContinuousAt (fun x => TotalSpace.mk' (spinGroup (Qneg n)) x (s x)) y₀) (v : E n) :
    ContinuousAt (fun y => (⟨y, L.frameAt y (s y) v⟩ : TangentBundle I M)) y₀ := by
  let _ := g.riemannianBundleOfPos hpos
  have h := ((OrthonormalFrameBundle.continuous_totalSpaceMk_frame v).comp
    L.continuous_toFrame).continuousAt.comp hs
  refine h.congr (Eventually.of_forall fun y => ?_)
  exact L.mk_frame ⟨y, s y⟩ v

/-- A lift has continuous local sections around every point: the points with coordinate `1` in
the trivialization at `x₀`. -/
lemma SpinLift.exists_continuousOn_section (x₀ : M) :
    letI := g.riemannianBundleOfPos hpos
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ s : (x : M) → L.P x,
      ContinuousOn (fun x => TotalSpace.mk' (spinGroup (Qneg n)) x (s x)) U := by
  let _ := g.riemannianBundleOfPos hpos
  set T := trivializationAt (spinGroup (Qneg n)) L.P x₀
  have hne : ∀ y, Nonempty (L.P y) := fun y => by
    set T' := trivializationAt (spinGroup (Qneg n)) L.P y
    have hy : y ∈ T'.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
    have h := T'.proj_symm_apply' (b := y) (x := (1 : spinGroup (Qneg n))) hy
    exact ⟨h ▸ (T'.toOpenPartialHomeomorph.symm (y, 1)).snd⟩
  let pt : (y : M) → L.P y := fun y => Classical.choice (hne y)
  let s : (y : M) → L.P y := fun y => op ((T ⟨y, pt y⟩).2⁻¹) • pt y
  refine ⟨T.baseSet, T.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x₀, s, ?_⟩
  have hc : ContinuousOn (fun y : M => T.toOpenPartialHomeomorph.symm (y, 1)) T.baseSet :=
    T.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn fun y hy => by
        rw [T.target_eq]; exact ⟨hy, Set.mem_univ _⟩
  refine hc.congr fun y hy => ?_
  have hT : T ⟨y, s y⟩ = (y, 1) := by
    rw [Bundle.Trivialization.apply_smul T hy, mul_inv_cancel]
  beta_reduce
  rw [← hT]
  exact (T.toOpenPartialHomeomorph.left_inv (T.mem_source.2 hy)).symm

end Frames

/-! ## Smooth orthonormal frames with a given value -/

/-- Around every point there is a smooth `g`-orthonormal frame of the tangent bundle with a
prescribed orthonormal value at the point: a smooth orthonormal frame (Gram–Schmidt) rotated by a
constant matrix. -/
lemma _root_.Lightlike.NondegMetric.exists_smooth_orthonormal_frame
    (hg : ∀ x (v : TangentSpace I x), v ≠ 0 → 0 < g.g x v v) (x₀ : M) (f₀ : Fin n → TangentSpace I x₀)
    (hf₀ : ∀ a b, g.g x₀ (f₀ a) (f₀ b) = if a = b then 1 else 0) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ F : Fin n → (y : M) → TangentSpace I y,
      (∀ a y, y ∈ U → ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun z => (⟨z, F a z⟩ : TangentBundle I M)) y) ∧
      (∀ y ∈ U, ∀ a b, g.g y (F a y) (F b y) = if a = b then 1 else 0) ∧
      ∀ a, F a x₀ = f₀ a := by
  let _ := g.riemannianBundleOfPos hg
  have _ := (Lightlike.NondegMetric.isContMDiffRiemannianBundleOfPos (g := g) (hpos := hg))
  obtain ⟨U, hU, hx₀, u, hu, huo⟩ := Lightlike.exists_isLocalFrameOn_orthonormal (I := I)
    (n := ∞) (F := Fin n → ℝ) (V := fun x : M => TangentSpace I x) x₀
  have hk : Module.finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  let k : Fin n ≃ Fin (Module.finrank ℝ (Fin n → ℝ)) := finCongr hk.symm
  let v : Fin n → (y : M) → TangentSpace I y := fun b => u (k b)
  have hvo : ∀ y ∈ U, Orthonormal ℝ (v · y) := fun y hy => (huo y hy).comp k k.injective
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x₀) := by
    simp only [Fintype.card_fin]; exact hk.symm
  let B : OrthonormalBasis (Fin n) ℝ (TangentSpace I x₀) :=
    OrthonormalBasis.mk (hvo x₀ hx₀) (by
      rw [(hvo x₀ hx₀).linearIndependent.span_eq_top_of_card_eq_finrank' hcard])
  have hB : ∀ b, B b = v b x₀ := fun b => by simp [B]
  let A : Fin n → Fin n → ℝ := fun b a => ⟪v b x₀, f₀ a⟫
  refine ⟨U, hU, hx₀, fun a y => ∑ b, A b a • v b y, ?_, ?_, ?_⟩
  · intro a y hy
    refine ContMDiffAt.sum_section fun b _ => ?_
    exact (hu.contMDiffAt hU hy (k b)).const_smul_section
  · intro y hy a c
    change ⟪∑ b, A b a • v b y, ∑ d, A d c • v d y⟫ = _
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    have hvy := hvo y hy
    simp_rw [orthonormal_iff_ite.1 hvy]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h := B.sum_inner_mul_inner (f₀ a) (f₀ c)
    simp only [hB] at h
    rw [← hf₀ a c]
    change _ = ⟪f₀ a, f₀ c⟫
    rw [← h]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [A, real_inner_comm (f₀ a)]
    ring
  · intro a
    change ∑ b, ⟪v b x₀, f₀ a⟫ • v b x₀ = f₀ a
    have h := B.sum_repr' (f₀ a)
    simp only [hB] at h
    exact h

/-- The Riemannian bundle of a positive definite smooth metric is a continuous Riemannian bundle. -/
lemma _root_.Lightlike.NondegMetric.isContinuousRiemannianBundleOfPos :
    letI := g.riemannianBundleOfPos hpos
    IsContinuousRiemannianBundle (Fin n → ℝ) (fun x : M => TangentSpace I x) :=
  letI := g.riemannianBundleOfPos hpos
  ⟨⟨g.g, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩

/-! ## Smooth local sections and the smooth spin atlas -/

section Atlas

variable (L : SpinLift g hpos)

/-- **Every lift has smooth local sections**: around every point a continuous local section whose
frame is smooth.  A continuous section `s₀` of the bundle is turned by the spin element
`spinOfFrame W` lifting the coordinates `W` of a smooth orthonormal frame `F` (with
`F(x₀) = frame of s₀(x₀)`) in the frame of `s₀`. -/
lemma SpinLift.exists_smooth_section (x₀ : M) :
    letI := g.riemannianBundleOfPos hpos
    ∃ V : Set M, IsOpen V ∧ x₀ ∈ V ∧ ∃ s : (x : M) → L.P x,
      ContinuousOn (fun x => TotalSpace.mk' (spinGroup (Qneg n)) x (s x)) V ∧
      ∀ a y, y ∈ V → ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun z => (⟨z, L.frameAt z (s z) (e a)⟩ : TangentBundle I M)) y := by
  let _ := g.riemannianBundleOfPos hpos
  have _ := (Lightlike.NondegMetric.isContinuousRiemannianBundleOfPos (g := g) (hpos := hpos))
  classical
  obtain ⟨U₀, hU₀, hx₀U₀, s₀, hs₀⟩ := L.exists_continuousOn_section x₀
  set F₀ : Fin n → (y : M) → TangentSpace I y := fun b y => L.frameAt y (s₀ y) (e b)
  have hf₀ : ∀ a b, g.g x₀ (F₀ a x₀) (F₀ b x₀) = if a = b then 1 else 0 := fun a b => by
    simp only [F₀]
    rw [SpinStructure.SmoothSpinAtlas.g_frameAt]
    exact isOrthonormalFrame_e a b
  obtain ⟨U₁, hU₁, hx₀U₁, F, hFs, hFo, hF₀⟩ :=
    g.exists_smooth_orthonormal_frame hpos x₀ (fun a => F₀ a x₀) hf₀
  set V₀ := U₀ ∩ U₁
  have hV₀ : IsOpen V₀ := hU₀.inter hU₁
  set W : M → Fin n → E n := fun y a => WithLp.toLp 2 (fun b => g.g y (F₀ b y) (F a y))
  have hWc : ContinuousOn W V₀ := by
    intro y hy
    refine ContinuousAt.continuousWithinAt (continuousAt_pi.2 fun a => ?_)
    have hc : ContinuousAt (fun z => fun b => g.g z (F₀ b z) (F a z)) y :=
      continuousAt_pi.2 fun b => ContinuousAt.inner_bundle
        (L.continuousAt_frameAt (hs₀.continuousAt (hU₀.mem_nhds hy.1)) (e b))
        (hFs a y hy.2).continuousAt
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous.continuousAt.comp hc
  have hWF : ∀ y a, L.frameAt y (s₀ y) (W y a) = F a y := fun y a =>
    L.frameAt_coords y (s₀ y) (F a y)
  have hWo : ∀ y ∈ V₀, IsOrthonormalFrame (W y) := fun y hy a c => by
    rw [← SpinStructure.SmoothSpinAtlas.g_frameAt (L := L) y (s₀ y), hWF, hWF]
    exact hFo y hy.2 a c
  have hW₀ : W x₀ = e := by
    funext a
    ext b
    change g.g x₀ (F₀ b x₀) (F a x₀) = (e a) b
    rw [hF₀, hf₀]
    simp [e, eq_comm]
  set V := V₀ ∩ W ⁻¹' {W | FrameGood W}
  have hV : IsOpen V := hWc.isOpen_inter_preimage hV₀ isOpen_frameGood
  have hx₀V : x₀ ∈ V := ⟨⟨hx₀U₀, hx₀U₁⟩, by
    change FrameGood (W x₀); rw [hW₀]; exact frameGood_e⟩
  set σs : M → spinGroup (Qneg n) := fun y =>
    if h : IsOrthonormalFrame (W y) ∧ FrameGood (W y) then
      ⟨spinOfFrame (W y), spinOfFrame_mem h.1 h.2⟩ else 1
  have hσs : ∀ y ∈ V, (σs y : CliffordAlgebra (Qneg n)) = spinOfFrame (W y) := fun y hy => by
    simp only [σs, dite_eq_left (show IsOrthonormalFrame (W y) ∧ FrameGood (W y) from
      ⟨hWo y hy.1, hy.2⟩)]
  have hσv : ∀ y ∈ V, ∀ a, vecConj (σs y) (e a) = W y a := fun y hy a => by
    have h : IsOrthonormalFrame (W y) ∧ FrameGood (W y) := ⟨hWo y hy.1, hy.2⟩
    simp only [σs, dite_eq_left h]
    exact vecConj_spinOfFrame h.1 h.2 a
  refine ⟨V, hV, hx₀V, fun y => op (σs y) • s₀ y, ?_, ?_⟩
  · have hσc : ContinuousOn σs V := by
      let _ := clNormedRing n
      let _ := clNormedAlgebra n
      rw [continuousOn_spinGroup_iff]
      refine ContinuousOn.congr (f := fun y => spinOfFrame (W y)) ?_ hσs
      intro y hy
      exact ((contDiffAt_spinPartial n (W y) ((frameGood_iff _).1 hy.2)).continuousAt.comp
        (hWc.continuousAt (hV₀.mem_nhds hy.1))).continuousWithinAt
    exact (hs₀.mono fun y hy => hy.1.1).totalSpaceMk_smul hσc
  · intro a y hy
    refine (hFs a y hy.1.2).congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hy] with z hz
    rw [SpinStructure.SmoothSpinAtlas.frameAt_smul, hσv z hz a, hWF]

/-- **Every lift of the orthonormal frame bundle through `Spin(n) → SO(n)` has a smooth spin
atlas**: the smooth local sections of `SpinLift.exists_smooth_section`, one around each point;
their transition elements are smooth by `SpinLift.contMDiffAt_division`. -/
noncomputable def SpinLift.smoothSpinAtlas : SpinStructure.SmoothSpinAtlas hpos L := by
  let _ := g.riemannianBundleOfPos hpos
  choose V hVo hxV s hsc hsf using L.exists_smooth_section
  exact
    { ι := M
      dom := V
      dom_open := hVo
      dom_cover := fun x => ⟨x, hxV x⟩
      sec := s
      sec_cont := hsc
      frame_smooth := fun i a x hx => hsf i a x hx
      trans_smooth := fun i j φ x hi hj =>
        L.contMDiffAt_division (s i) (s j) x ((hsc i).continuousAt ((hVo i).mem_nhds hi))
          ((hsc j).continuousAt ((hVo j).mem_nhds hj)) (fun a => hsf i a x hi)
          (fun a => hsf j a x hj) φ }

/-- **Lawson–Michelsohn II Def. 1.3 and the atlas form are equivalent, with no side condition**:
every lift `L` of the orthonormal frame bundle through `Spin(n) → SO(n)` (any `SpinLift`, with no
smoothness assumed) is equivalent, as a lift, to the principal bundle of a spin structure in atlas
form; conversely every atlas spin structure gives a lift (`SpinStructure.principal`). -/
theorem SpinLift.exists_spinStructure_equiv [I.Boundaryless] :
    ∃ (ι : Type) (S : SpinStructure g ι),
      Nonempty (letI := g.riemannianBundleOfPos hpos; S.principal.Equiv L) :=
  ⟨_, SpinStructure.ofSmoothAtlas L.smoothSpinAtlas,
    ⟨SpinStructure.ofSmoothAtlasEquiv L.smoothSpinAtlas⟩⟩

end Atlas

/-- Non-vacuity: the theorem applies to any lift, for instance the principal bundle of the
standard spin structure of `ℝⁿ` (a lift that is not given with a smooth atlas). -/
example (n : ℕ) : ∃ (ι : Type) (S : SpinStructure (euclideanMetric n) ι),
    Nonempty (letI := (euclideanSpinStructure n).riemannianBundle;
      S.principal.Equiv (euclideanSpinStructure n).principal) :=
  SpinLift.exists_spinStructure_equiv (euclideanSpinStructure n).principal

end Lightlike.Dirac

import Mathlib
import Lightlike.Bundles.SpinGroup
import Lightlike.Bundles.FiberBundle.GroupCocycle
import Lightlike.Bundles.VectorBundle.OrthonormalFrame.Lift.Basic
import Lightlike.Bundles.VectorBundle.Riemannian.Basic
import Lightlike.Dirac.SpinorBundle

/-!
# The principal `Spin(n)`-bundle of a spin structure (Lawson–Michelsohn, II Def. 1.3)

A spin structure in atlas form `S` (`SpinStructure`: local orthonormal frames `F_i` whose
changes `F_j a = ∑_b R_ab F_i b` carry lifts `lift i j ∈ Spin(n)`) determines a spin structure in
the sense of Lawson–Michelsohn, *Spin Geometry*, II Definition 1.3: a principal `Spin(n)`-bundle
`P → M` together with an equivariant map to the orthonormal frame bundle of `TM`, covering the
identity of `M` (`Lightlike.OrthonormalFrameLift` along the vector action
`Spin(n) →* GL(ℝⁿ)`, `s ↦ (v ↦ s v s⋆)`, `vectorAction`).  This file constructs it:

* `SpinStructure.riemannianMetric`: the metric `g` is positive definite (it has an orthonormal frame
  at every point), so it is a Riemannian metric on the tangent bundle in Mathlib's sense;
* `SpinStructure.frameIso`: the frame `F_i` at `x` as a linear isometry `ℝⁿ ≃ₗᵢ T_x M`;
* `SpinStructure.spinCore`: the principal `Spin(n)`-bundle glued from the cocycle `lift j i`
  (Tau Ceti's `fiberBundleCoreOfGroupCocycle`, a principal bundle for right multiplication);
* `SpinStructure.toFrame`: a point with fibre coordinate `p` in the chart chosen at `x` goes to the
  frame `F_{i(x)}(x) ∘ (s ↦ s v s⋆)(p)`; it is independent of the chart, continuous and equivariant
  along the vector action;
* `SpinStructure.principal`: the resulting `OrthonormalFrameLift`, the spin structure of
  Lawson–Michelsohn II Def. 1.3.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, Definition 1.3.
-/

open Bundle Manifold CliffordAlgebra Filter Set MulOpposite
open scoped Manifold ContDiff Topology InnerProductSpace

namespace Lightlike.Dirac

variable {n : ℕ}
  {M : Type} [TopologicalSpace M] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Fin n → ℝ) H} [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {g : NondegMetric I M} {ι : Type} (S : SpinStructure g ι)

/-! ## The Riemannian metric -/

/-- The chart chosen at a point: a frame domain containing it. -/
noncomputable def SpinStructure.idx (x : M) : ι := (S.dom_cover x).choose

lemma SpinStructure.mem_idx (x : M) : x ∈ S.dom (S.idx x) := (S.dom_cover x).choose_spec

/-- The metric in an orthonormal frame: `g(v, v) = ∑ₐ g(v, Fₐ)²`. -/
lemma SpinStructure.g_self_eq_sum {i : ι} {x : M} (hx : x ∈ S.dom i) (v : TangentSpace I x) :
    g.g x v v = ∑ a, g.g x v (S.frame i a x) ^ 2 := by
  conv_lhs => rw [S.frame_expand hx v]
  conv_lhs => rw [S.frame_expand hx v]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, S.frame_orthonormal i _ _ x hx,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

include S in
/-- The metric of a spin structure is positive definite. -/
lemma SpinStructure.g_pos {x : M} (v : TangentSpace I x) (hv : v ≠ 0) : 0 < g.g x v v := by
  have hx := S.mem_idx x
  rw [S.g_self_eq_sum hx]
  by_contra hlt
  have hle := not_lt.mp hlt
  have h0 : ∀ a, g.g x v (S.frame (S.idx x) a x) = 0 := by
    intro a
    have hsum : ∑ a, g.g x v (S.frame (S.idx x) a x) ^ 2 = 0 :=
      le_antisymm hle (Finset.sum_nonneg fun a _ => sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg _)).1 hsum a (Finset.mem_univ a)
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  apply hv
  rw [S.frame_expand hx v]
  simp [h0]

/-- A positive definite symmetric form on `ℝⁿ` is bounded below by a multiple of the square of
the norm: `c ‖v‖² ≤ B v v` for some `c > 0` (compactness of the unit sphere). -/
lemma exists_pos_mul_norm_sq_le {B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) : ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ B v v := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, one_pos, fun v => ?_⟩
    have : v = 0 := Subsingleton.elim _ _
    simp [this]
  have hcont : Continuous fun v : Fin n → ℝ => B v v := B.continuous.clm_apply continuous_id
  have hsph : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
    obtain ⟨a⟩ := hn
    exact ⟨Pi.single a 1, by simp [Metric.mem_sphere, dist_zero_right, Pi.norm_single]⟩
  obtain ⟨u, hu, hmin⟩ := hsph.exists_isMinOn hne hcont.continuousOn
  have hu0 : u ≠ 0 := by
    intro h; rw [h, Metric.mem_sphere, dist_self] at hu; norm_num at hu
  refine ⟨B u u, hpos u hu0, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set w := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [w, Metric.mem_sphere, dist_zero_right, norm_smul, inv_mul_cancel₀ hnv.ne']
  have h1 : B u u ≤ B w w := hmin hw
  have hBw : B w w = ‖v‖⁻¹ ^ 2 * B v v := by
    simp only [w, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  rw [hBw] at h1
  calc B u u * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ ^ 2 * B v v * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = B v v := by field_simp

/-- **The Riemannian metric of a positive definite metric**, in Mathlib's sense. -/
noncomputable def _root_.Lightlike.NondegMetric.riemannianMetricOfPos (g : NondegMetric I M)
    (hpos : ∀ x (v : TangentSpace I x), v ≠ 0 → 0 < g.g x v v) :
    RiemannianMetric (fun x : M => TangentSpace I x) where
  inner x := g.g x
  symm x v w := g.symm x v w
  pos x v hv := hpos x v hv
  continuousAt x := by
    change ContinuousAt (fun v : Fin n → ℝ => g.g x v v) 0
    exact ((g.g x).continuous.clm_apply continuous_id).continuousAt
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : Fin n → ℝ | g.g x v v < 1}
    obtain ⟨c, hc, hle⟩ := exists_pos_mul_norm_sq_le (B := g.g x) (hpos x)
    rw [NormedSpace.isVonNBounded_iff]
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨Real.sqrt (1 / c), fun v hv => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hle v) hv
    rw [Real.le_sqrt (norm_nonneg _) (by positivity), le_div_iff₀ hc]
    nlinarith

/-- **The Riemannian metric of a spin structure**: `g`, positive definite because it has an
orthonormal frame at every point. -/
noncomputable def SpinStructure.riemannianMetric :
    RiemannianMetric (fun x : M => TangentSpace I x) :=
  g.riemannianMetricOfPos fun _ v hv => SpinStructure.g_pos S v hv

/-- The Riemannian bundle of a positive definite metric. Not a global instance; statements install
it with `letI`. -/
@[instance_reducible]
noncomputable def _root_.Lightlike.NondegMetric.riemannianBundleOfPos (g : NondegMetric I M)
    (hpos : ∀ x (v : TangentSpace I x), v ≠ 0 → 0 < g.g x v v) :
    RiemannianBundle (fun x : M => TangentSpace I x) :=
  ⟨g.riemannianMetricOfPos hpos⟩

/-- The tangent bundle of a manifold with a spin structure as a Riemannian bundle: the one of the
positive definite metric `g`, so that it is the same instance for every proof of positivity. Not a
global instance; statements install it with `letI`. -/
@[instance_reducible]
noncomputable def SpinStructure.riemannianBundle : RiemannianBundle (fun x : M => TangentSpace I x) :=
  g.riemannianBundleOfPos fun _ v hv => SpinStructure.g_pos S v hv

/-! ## Frames as isometries -/

section Frames

/-- The vector action preserves the quadratic form: `s v s⋆` has the norm of `v`. -/
lemma norm_vecConj (s : spinGroup (Qneg n)) (v : E n) : ‖vecConj s v‖ = ‖v‖ := by
  have hss : (s : CliffordAlgebra (Qneg n)) * star (s : CliffordAlgebra (Qneg n)) = 1 :=
    spinGroup.mul_star_self_of_mem s.2
  have h1 : ι (Qneg n) (vecConj s v) * ι (Qneg n) (vecConj s v) =
      algebraMap ℝ _ (Qneg n v) := by
    rw [ι_vecConj]
    calc (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v * star (s : CliffordAlgebra (Qneg n)) *
          ((s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v * star (s : CliffordAlgebra (Qneg n)))
        = (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v *
            (star (s : CliffordAlgebra (Qneg n)) * (s : CliffordAlgebra (Qneg n))) *
            ι (Qneg n) v * star (s : CliffordAlgebra (Qneg n)) := by simp only [mul_assoc]
      _ = (s : CliffordAlgebra (Qneg n)) * (ι (Qneg n) v * ι (Qneg n) v) *
            star (s : CliffordAlgebra (Qneg n)) := by
          rw [spinGroup.star_mul_self_of_mem s.2, mul_one]; simp only [mul_assoc]
      _ = algebraMap ℝ _ (Qneg n v) := by
          rw [ι_sq_scalar, ← Algebra.commutes, mul_assoc, hss, mul_one]
  rw [ι_sq_scalar] at h1
  have hnt : Nontrivial (CliffordAlgebra (Qneg n)) := by
    have : Nontrivial (ExteriorAlgebra ℝ (E n)) := inferInstance
    exact (CliffordAlgebra.equivExterior (Qneg n)).toEquiv.nontrivial
  have h2 := (algebraMap ℝ (CliffordAlgebra (Qneg n))).injective h1
  simp only [Qneg_apply, neg_inj] at h2
  have := congrArg Real.sqrt h2
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- The vector action of `s`, as a linear isometry of `ℝⁿ`. -/
noncomputable def vecIso (s : spinGroup (Qneg n)) : E n ≃ₗᵢ[ℝ] E n :=
  { toLinearEquiv :=
      { toLinearMap := vecConj s
        invFun := vecConj s⁻¹
        left_inv := fun v => by
          show vecConj s⁻¹ (vecConj s v) = v
          rw [← vecConj_mul, inv_mul_cancel, vecConj_one]
        right_inv := fun v => by
          show vecConj s (vecConj s⁻¹ v) = v
          rw [← vecConj_mul, mul_inv_cancel, vecConj_one] }
    norm_map' := norm_vecConj s }

@[simp] lemma vecIso_apply (s : spinGroup (Qneg n)) (v : E n) : vecIso s v = vecConj s v := rfl

lemma vecIso_mul (s t : spinGroup (Qneg n)) (v : E n) : vecIso (s * t) v = vecIso s (vecIso t v) :=
  vecConj_mul s t v

/-- `vecIso` is `vectorAction` read on `E n = EuclideanSpace ℝ (Fin n)`. -/
lemma vecIso_toLp (s : spinGroup (Qneg n)) (v : Fin n → ℝ) :
    vecIso s (WithLp.toLp 2 v) = WithLp.toLp 2 (vectorAction n s v) := by
  simp [vectorAction]

/-- The frame `i` at `x`: `v ↦ ∑ₐ vₐ Fₐ(x)`. -/
noncomputable def SpinStructure.frameMap (i : ι) (x : M) : E n →ₗ[ℝ] TangentSpace I x where
  toFun v := ∑ a, v a • S.frame i a x
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

lemma SpinStructure.g_frameMap {i : ι} {x : M} (hx : x ∈ S.dom i) (v w : E n) :
    g.g x (S.frameMap i x v) (S.frameMap i x w) = ∑ a, v a * w a := by
  simp only [SpinStructure.frameMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, S.frame_orthonormal i _ _ x hx, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- **The frame `i` at `x` as a linear isometry** `ℝⁿ ≃ₗᵢ T_x M`, for the Riemannian metric of the
spin structure. -/
noncomputable def SpinStructure.frameIso {i : ι} {x : M} (hx : x ∈ S.dom i) :
    letI := S.riemannianBundle
    E n ≃ₗᵢ[ℝ] TangentSpace I x :=
  letI := S.riemannianBundle
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := S.frameMap i x
      norm_map' := fun v => by
        have h1 : ‖S.frameMap i x v‖ ^ 2 = ‖v‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
          change g.g x (S.frameMap i x v) (S.frameMap i x v) = _
          rw [S.g_frameMap hx, EuclideanSpace.inner_eq_star_dotProduct]
          simp [dotProduct, mul_comm]
        have := congrArg Real.sqrt h1
        simpa [Real.sqrt_sq (norm_nonneg _)] using this }
    (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ (Fin n → ℝ)
      simp)

lemma SpinStructure.frameIso_apply {i : ι} {x : M} (hx : x ∈ S.dom i) (v : E n) :
    (letI := S.riemannianBundle; S.frameIso hx v) = S.frameMap i x v := rfl

/-- The frames of two charts differ by the vector action of the lift:
`F_j(x) = F_i(x) ∘ vecIso (lift i j x)`. -/
lemma SpinStructure.frameMap_change {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : E n) :
    S.frameMap j x v = S.frameMap i x (vecConj ⟨S.lift i j x, S.lift_mem hi hj⟩ v) := by
  -- coordinates of the vector action of the lift: `vecConj (lift i j) eₐ = ∑_b R_ab e_b`
  have hvec : ∀ w : E n, vecConj ⟨S.lift i j x, S.lift_mem hi hj⟩ w =
      ∑ a, w a • ∑ b, S.rmat i j x a b • e b := by
    intro w
    rw [vecConj_eq_iff]
    have hw : w = ∑ a, w a • e a := by
      simpa [e] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w).symm
    conv_lhs => rw [hw]
    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    have := S.lift_conj hi hj a
    simpa [cgen, map_sum, map_smul] using this
  have hframe : ∀ a, S.frame j a x = ∑ b, S.rmat i j x a b • S.frame i b x := fun a => by
    rw [S.frame_change i j x hi hj a, S.rot_eq_rmat hi hj]
  have he : ∀ b, S.frameMap i x (e b) = S.frame i b x := fun b => by
    simp [SpinStructure.frameMap, e, Finset.sum_ite_eq']
  rw [hvec, map_sum]
  simp only [map_smul, map_sum, he]
  simp only [SpinStructure.frameMap, LinearMap.coe_mk, AddHom.coe_mk, hframe]

end Frames

/-! ## The principal `Spin(n)`-bundle -/

section Principal

/-- **The principal `Spin(n)`-bundle of the spin structure**, glued from the cocycle `lift j i`:
over the frame domain `i` a point is `(x, p)` with `p ∈ Spin(n)`, and the coordinate `p` in chart
`j` is `lift i j x · p` in chart `i`. -/
noncomputable abbrev SpinStructure.spinCore : FiberBundleCore ι M (spinGroup (Qneg n)) :=
  fiberBundleCoreOfGroupCocycle S.dom S.spinCocycle
    (fun i j k x hx => S.spinCocycle_cocycle i j k x hx.1.1 hx.1.2 hx.2) (spinGroup (Qneg n))
    S.dom_open S.idx S.mem_idx S.continuousOn_spinCocycle

/-- The fibres of the principal bundle. -/
abbrev SpinStructure.PSpin (x : M) : Type := S.spinCore.Fiber x

/-- A point of a fibre of the principal bundle, as an element of `Spin(n)` (its coordinate in the
chart chosen at the base point). -/
def SpinStructure.PSpin.val {S : SpinStructure g ι} {x : M} (p : S.PSpin x) : spinGroup (Qneg n) := p

/-- The point of the principal bundle with fibre coordinate `p` in chart `i` has fibre coordinate
`lift i (idx x) x · p` … in the chart chosen at `x`: the coordinate in chart `i` of a point. -/
lemma SpinStructure.spinCore_localTriv_snd {i : ι} {x : M} (hx : x ∈ S.dom i) (p : S.PSpin x) :
    ((S.spinCore.localTriv i ⟨x, p⟩).2 : CliffordAlgebra (Qneg n)) =
      S.lift i (S.idx x) x * (p.val : CliffordAlgebra (Qneg n)) := by
  rw [FiberBundleCore.localTriv_apply]
  change ((S.spinCocycle (S.idx x) i x * p.val : spinGroup (Qneg n)) : CliffordAlgebra (Qneg n)) = _
  rw [Submonoid.coe_mul, S.coe_spinCocycle (S.mem_idx x) hx]


/-- **The frame map.** The point with coordinate `p` in the chart chosen at `x` goes to the
orthonormal frame `v ↦ F_{idx x}(x) (p v p⋆)`. -/
noncomputable def SpinStructure.toFrame :
    letI := S.riemannianBundle
    TotalSpace (spinGroup (Qneg n)) S.PSpin →
      OrthonormalFrameBundle ℝ (Fin n → ℝ) (fun x : M => TangentSpace I x) (EuclideanSpace ℝ (Fin n)) :=
  letI := S.riemannianBundle
  fun q => ⟨q.proj, (vecIso q.snd.val).trans (S.frameIso (S.mem_idx q.proj))⟩

lemma SpinStructure.toFrame_apply (q : TotalSpace (spinGroup (Qneg n)) S.PSpin) (v : E n) :
    (letI := S.riemannianBundle; (S.toFrame q).frame v) =
      S.frameMap (S.idx q.proj) q.proj (vecConj q.snd.val v) := rfl

/-- The frame map read in any chart containing the base point: with the fibre coordinate `h` of
the point in chart `i`, it is `F_i(x) ∘ (v ↦ h v h⋆)`. -/
lemma SpinStructure.toFrame_apply_chart {i : ι} (q : TotalSpace (spinGroup (Qneg n)) S.PSpin)
    (hq : q.proj ∈ S.dom i) (v : E n) :
    (letI := S.riemannianBundle; (S.toFrame q).frame v) =
      S.frameMap i q.proj (vecConj (S.spinCore.localTriv i q).2 v) := by
  have hel : (⟨S.lift i (S.idx q.proj) q.proj, S.lift_mem hq (S.mem_idx q.proj)⟩ * q.snd.val :
      spinGroup (Qneg n)) = (S.spinCore.localTriv i q).2 := by
    apply Subtype.ext
    rw [Submonoid.coe_mul]
    obtain ⟨x, p⟩ := q
    exact (S.spinCore_localTriv_snd hq p).symm
  rw [S.toFrame_apply, S.frameMap_change hq (S.mem_idx q.proj), ← vecConj_mul, hel]

/-- The frame map is equivariant along the vector action. -/
lemma SpinStructure.toFrame_smul (x : M) (p : S.PSpin x) (s : spinGroup (Qneg n)) (v : Fin n → ℝ) :
    letI := S.riemannianBundle
    TotalSpace.mk' (Fin n → ℝ) (S.toFrame ⟨x, op s • p⟩).proj
        ((S.toFrame ⟨x, op s • p⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' (Fin n → ℝ) (S.toFrame ⟨x, p⟩).proj
        ((S.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (vectorAction n s v))) := by
  letI := S.riemannianBundle
  change TotalSpace.mk' (Fin n → ℝ) x _ = TotalSpace.mk' (Fin n → ℝ) x _
  congr 1
  rw [S.toFrame_apply, S.toFrame_apply]
  change S.frameMap (S.idx x) x (vecConj (p.val * s) (WithLp.toLp 2 v)) = _
  rw [vecConj_mul, ← vecIso_apply s, vecIso_toLp]

end Principal

/-! ## Continuity of the frame map and the spin structure in the sense of Lawson–Michelsohn -/

section Continuity

/-- The coordinates of the vector action depend continuously on the group element. -/
lemma continuous_vecConj_apply (v : E n) (b : Fin n) :
    Continuous fun s : spinGroup (Qneg n) => (vecConj s v) b := by
  let _ := clNormedRing n
  let _ := clNormedAlgebra n
  -- a linear functional on the Clifford algebra reading the `b`-th coordinate of vectors
  obtain ⟨T, hT⟩ := (ι (Qneg n)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ι_injective_Qneg)
  set φ : CliffordAlgebra (Qneg n) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj b : E n →L[ℝ] ℝ).toLinearMap ∘ₗ T
  have hφι : ∀ w : E n, φ (ι (Qneg n) w) = w b := fun w => by
    have := LinearMap.congr_fun hT w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at this
    simp [φ, this]
  have hφc : Continuous φ := (LinearMap.toContinuousLinearMap φ).continuous
  have hcoe : Continuous fun s : spinGroup (Qneg n) => (s : CliffordAlgebra (Qneg n)) :=
    continuous_spinGroup_iff.1 continuous_id
  have hstar : Continuous fun x : CliffordAlgebra (Qneg n) => star x := by
    have : (fun x : CliffordAlgebra (Qneg n) => star x) =
        (LinearMap.toContinuousLinearMap ((reverse : CliffordAlgebra (Qneg n) →ₗ[ℝ] _).comp
          (involute : CliffordAlgebra (Qneg n) →ₐ[ℝ] _).toLinearMap) : _ → _) := by
      funext x; simp [star_def]
    rw [this]; exact ContinuousLinearMap.continuous _
  have h : (fun s : spinGroup (Qneg n) => (vecConj s v) b) = fun s : spinGroup (Qneg n) =>
      φ ((s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v * star (s : CliffordAlgebra (Qneg n))) := by
    funext s; rw [← ι_vecConj, hφι]
  rw [h]
  exact hφc.comp ((hcoe.mul continuous_const).mul (hstar.comp hcoe))

/-- A combination of the frame `i` with continuous coefficients is continuous into the tangent
bundle. -/
lemma SpinStructure.continuousAt_frame_comb {Z : Type*} [TopologicalSpace Z] {f : Z → M} {z₀ : Z}
    {i : ι} (hz₀ : f z₀ ∈ S.dom i) (hf : ContinuousAt f z₀) {c : Fin n → Z → ℝ}
    (hc : ∀ b, ContinuousAt (c b) z₀) :
    ContinuousAt (fun z => (⟨f z, ∑ b, c b z • S.frame i b (f z)⟩ : TangentBundle I M)) z₀ := by
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hf, ?_⟩
  set e := trivializationAt (Fin n → ℝ) (TangentSpace I) (f z₀)
  have hbase : ∀ᶠ z in 𝓝 z₀, f z ∈ e.baseSet :=
    hf.preimage_mem_nhds (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  have hsec : ∀ b, ContinuousAt (fun z => (e ⟨f z, S.frame i b (f z)⟩).2) z₀ := by
    intro b
    have hs : ContinuousAt (fun y => (⟨y, S.frame i b y⟩ : TangentBundle I M)) (f z₀) :=
      (S.frame_smooth i b (f z₀) hz₀).continuousAt
    have := ((FiberBundle.continuousAt_totalSpace (Fin n → ℝ)
      (fun y : M => (⟨y, S.frame i b y⟩ : TangentBundle I M))).1 hs).2
    exact this.comp hf
  have hlin : (fun z => (e ⟨f z, ∑ b, c b z • S.frame i b (f z)⟩).2) =ᶠ[𝓝 z₀]
      fun z => ∑ b, c b z • (e ⟨f z, S.frame i b (f z)⟩).2 := by
    filter_upwards [hbase] with z hz
    have h := map_sum (IsLinearMap.mk' _ (e.linear ℝ hz))
      (fun b => c b z • S.frame i b (f z)) Finset.univ
    simp only [IsLinearMap.mk'_apply, map_smul] at h
    exact h
  refine ContinuousAt.congr ?_ hlin.symm
  exact tendsto_finset_sum _ fun b _ => (hc b).smul (hsec b)

/-- **The frame map is continuous.** -/
lemma SpinStructure.continuous_toFrame :
    letI := S.riemannianBundle
    Continuous S.toFrame := by
  letI := S.riemannianBundle
  rw [OrthonormalFrameBundle.continuous_iff]
  intro v
  rw [continuous_iff_continuousAt]
  intro q₀
  set i := S.idx q₀.proj
  have hq₀ : q₀.proj ∈ S.dom i := S.mem_idx q₀.proj
  have hproj : Continuous fun q : TotalSpace (spinGroup (Qneg n)) S.PSpin => q.proj :=
    FiberBundle.continuous_proj _ _
  have hnear : ∀ᶠ q in 𝓝 q₀, q.proj ∈ S.dom i :=
    hproj.continuousAt.preimage_mem_nhds ((S.dom_open i).mem_nhds hq₀)
  have hloc : ContinuousAt (fun q : TotalSpace (spinGroup (Qneg n)) S.PSpin =>
      (S.spinCore.localTriv i q).2) q₀ :=
    (continuous_snd.continuousAt).comp ((S.spinCore.localTriv i).continuousAt
      ((S.spinCore.localTriv i).mem_source.2 hq₀))
  have hcomb := S.continuousAt_frame_comb (f := fun q : TotalSpace (spinGroup (Qneg n)) S.PSpin =>
      q.proj) (z₀ := q₀) hq₀ hproj.continuousAt
    (c := fun b q => (vecConj (S.spinCore.localTriv i q).2 v) b)
    (fun b => (continuous_vecConj_apply v b).continuousAt.comp hloc)
  refine hcomb.congr ?_
  filter_upwards [hnear] with q hq
  change (⟨q.proj, _⟩ : TangentBundle I M) = ⟨q.proj, (S.toFrame q).frame v⟩
  rw [S.toFrame_apply_chart q hq]
  rfl

/-- **The spin structure in the sense of Lawson–Michelsohn, II Def. 1.3**: the principal
`Spin(n)`-bundle of the atlas, with its continuous frame map to the orthonormal frame bundle of
`TM`, covering the identity and equivariant along the vector action `Spin(n) → SO(n)`. -/
noncomputable def SpinStructure.principal :
    letI := S.riemannianBundle
    OrthonormalFrameLift (Fin n → ℝ) (fun x : M => TangentSpace I x) n (spinGroup (Qneg n))
      (vectorAction n) :=
  letI := S.riemannianBundle
  { P := S.PSpin
    toFrame := S.toFrame
    continuous_toFrame := S.continuous_toFrame
    proj_toFrame := fun _ => rfl
    toFrame_smul := S.toFrame_smul }

end Continuity

/-- **Non-vacuity**: the standard global frame of `ℝⁿ` (`euclideanSpinStructure`) gives a spin
structure in the sense of Lawson–Michelsohn II Def. 1.3. -/
noncomputable example (n : ℕ) :
    letI := (euclideanSpinStructure n).riemannianBundle
    OrthonormalFrameLift (Fin n → ℝ) (fun x : Fin n → ℝ => TangentSpace 𝓘(ℝ, Fin n → ℝ) x) n
      (spinGroup (Qneg n)) (vectorAction n) :=
  (euclideanSpinStructure n).principal

end Lightlike.Dirac

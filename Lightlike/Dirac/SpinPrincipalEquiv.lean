import Mathlib
import Lightlike.Dirac.SpinPrincipal

/-!
# Spin structures: the atlas form and the principal-bundle form are equivalent

Lawson–Michelsohn, *Spin Geometry*, II Definition 1.3 defines a spin structure on an oriented
Riemannian manifold as a principal `Spin(n)`-bundle `P` with a `Spin(n)`-equivariant map to the
orthonormal frame bundle (`Lightlike.OrthonormalFrameLift` along the vector action
`Spin(n) → SO(n)`).  In the smooth category such a bundle comes with local sections whose frames
are smooth and whose transition elements are smooth (`SpinStructure.SmoothSpinAtlas`).  This file
proves that these data are equivalent to the atlas form `SpinStructure`:

* `SpinStructure.ofSmoothAtlas`: a lift with a smooth atlas of sections gives a spin structure in
  atlas form (frames read off the sections, lifts their transition elements);
* `SpinStructure.ofSmoothAtlasEquiv`: the principal bundle of that spin structure is equivalent, as
  a lift of the orthonormal frame bundle, to the given one;
* `SpinStructure.smoothAtlas`: conversely the principal bundle `S.principal` of a spin structure has
  the smooth atlas of the unit sections of its charts, and reading it back gives the frames and the
  lifts of `S` (`SpinStructure.ofSmoothAtlas_frame`, `SpinStructure.ofSmoothAtlas_lift`).

## Difference from the source

Lawson–Michelsohn state Definition 1.3 for principal bundles without a smooth structure, and
`Lightlike.OrthonormalFrameLift` is not smooth by definition either: its bundle is a topological
fibre bundle and its map to frames is only required to be continuous.  The
equivalence here is with lifts that carry a smooth atlas of local sections (the smooth-category
form of the definition, the one in which the Dirac operator is defined).  That every lift of the
orthonormal frame bundle of a smooth manifold admits such an atlas (by lifting smooth local frames
through the covering `Spin(n) → SO(n)` on simply connected chart domains) is not proved here.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, Definition 1.3.
-/

open Bundle Manifold CliffordAlgebra Filter Set MulOpposite
open scoped Manifold ContDiff Topology InnerProductSpace

namespace Lightlike.Dirac

variable {n : ℕ}
  {M : Type} [TopologicalSpace M] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Fin n → ℝ) H} [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {g : NondegMetric I M} (hpos : ∀ x (v : TangentSpace I x), v ≠ 0 → 0 < g.g x v v)


/-- A lift of the orthonormal frame bundle along the vector action of `Spin(n)`: a spin structure
in the sense of Lawson–Michelsohn II Def. 1.3, for the metric `g`. -/
abbrev SpinLift (g : NondegMetric I M) (hpos : ∀ x (v : TangentSpace I x), v ≠ 0 → 0 < g.g x v v) :=
  letI := g.riemannianBundleOfPos hpos
  OrthonormalFrameLift (Fin n → ℝ) (fun x : M => TangentSpace I x) n (spinGroup (Qneg n))
    (vectorAction n)

/-- The frame of a point of a lift applied to `v`, as a tangent vector at the base point. -/
noncomputable def SpinLift.frameAt {hpos : ∀ x (v : TangentSpace I x), v ≠ 0 → 0 < g.g x v v}
    (L : SpinLift g hpos) (y : M) :
    letI := g.riemannianBundleOfPos hpos
    L.P y → E n → TangentSpace I y :=
  letI := g.riemannianBundleOfPos hpos
  fun p v => ((L.toFrame ⟨y, p⟩).frame v : TangentSpace I (L.toFrame ⟨y, p⟩).proj)

/-- **A smooth atlas of a spin lift**: local sections over an open cover whose frames are smooth
vector fields and whose transition elements are smooth (every linear coordinate). -/
structure SpinStructure.SmoothSpinAtlas (L : SpinLift g hpos) where
  /-- The index set of the cover. -/
  ι : Type
  /-- The domains of the sections. -/
  dom : ι → Set M
  dom_open : ∀ i, IsOpen (dom i)
  dom_cover : ∀ x, ∃ i, x ∈ dom i
  /-- The local sections. -/
  sec : letI := g.riemannianBundleOfPos hpos; ι → (x : M) → L.P x
  sec_cont : letI := g.riemannianBundleOfPos hpos
    ∀ i, ContinuousOn (fun x => (⟨x, sec i x⟩ : TotalSpace (spinGroup (Qneg n)) L.P)) (dom i)
  frame_smooth : ∀ i a x, x ∈ dom i →
    ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun y => (⟨y, L.frameAt y (sec i y) (EuclideanSpace.single a 1)⟩ : TangentBundle I M)) x
  trans_smooth : letI := g.riemannianBundleOfPos hpos
    ∀ i j (φ : Module.Dual ℝ (CliffordAlgebra (Qneg n))) x, x ∈ dom i → x ∈ dom j →
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => φ (PrincipalBundle.division (spinGroup (Qneg n)) (sec i y) (sec j y) :
        CliffordAlgebra (Qneg n))) x

/-- The vector action on a basis vector, expanded in the basis. -/
lemma vecConj_single_expand (s : spinGroup (Qneg n)) (a : Fin n) :
    vecConj s (EuclideanSpace.single a 1) =
      ∑ b, (vecConj s (EuclideanSpace.single a 1)) b • EuclideanSpace.single b (1 : ℝ) := by
  simpa using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (vecConj s (EuclideanSpace.single a 1))).symm


namespace SpinStructure.SmoothSpinAtlas

variable {hpos} {L : SpinLift g hpos} (A : SpinStructure.SmoothSpinAtlas hpos L)

/-- The transition element of the sections `i`, `j` at `y`: `sec j y = sec i y · trans i j y`. -/
noncomputable def trans (i j : A.ι) (y : M) : spinGroup (Qneg n) :=
  letI := g.riemannianBundleOfPos hpos
  PrincipalBundle.division (spinGroup (Qneg n)) (A.sec i y) (A.sec j y)

omit [I.Boundaryless] in
lemma sec_eq_smul_trans (i j : A.ι) (y : M) :
    letI := g.riemannianBundleOfPos hpos
    A.sec j y = op (A.trans i j y) • A.sec i y :=
  letI := g.riemannianBundleOfPos hpos
  (PrincipalBundle.smul_division (A.sec i y) (A.sec j y)).symm

omit [I.Boundaryless] in
lemma trans_mul (i j k : A.ι) (y : M) : A.trans i j y * A.trans j k y = A.trans i k y :=
  letI := g.riemannianBundleOfPos hpos
  PrincipalBundle.division_mul_division (A.sec i y) (A.sec j y) (A.sec k y)

omit [I.Boundaryless] in
/-- The frame of a point of a fibre is linear in the vector. -/
lemma frameAt_sum (y : M) (p : letI := g.riemannianBundleOfPos hpos; L.P y) (c : Fin n → ℝ)
    (w : Fin n → E n) :
    L.frameAt y p (∑ a, c a • w a) = ∑ a, c a • L.frameAt y p (w a) := by
  let _ := g.riemannianBundleOfPos hpos
  simp only [SpinLift.frameAt, map_sum, map_smul]
  rfl

omit [I.Boundaryless] in
/-- Equivariance: the frame of `p · s` is the frame of `p` after the vector action of `s`. -/
lemma frameAt_smul (y : M) (p : letI := g.riemannianBundleOfPos hpos; L.P y)
    (s : spinGroup (Qneg n)) (v : E n) :
    letI := g.riemannianBundleOfPos hpos
    L.frameAt y (op s • p) v = L.frameAt y p (vecConj s v) := by
  let _ := g.riemannianBundleOfPos hpos
  have h := L.toFrame_smul y p s (WithLp.ofLp v)
  have h2 := congrArg (fun q : TangentBundle I M => (q.snd : Fin n → ℝ)) h
  simp only [WithLp.toLp_ofLp] at h2
  change ((L.toFrame ⟨y, op s • p⟩).frame v : Fin n → ℝ) = _
  rw [h2, ← vecIso_toLp, WithLp.toLp_ofLp]
  rfl

omit [I.Boundaryless] in
/-- The frames of a lift are orthonormal for the metric at the base point. -/
lemma g_frameAt (y : M) (p : letI := g.riemannianBundleOfPos hpos; L.P y) (v w : E n) :
    g.g y (L.frameAt y p v) (L.frameAt y p w) = inner ℝ v w := by
  let _ := g.riemannianBundleOfPos hpos
  have hproj := L.proj_toFrame ⟨y, p⟩
  unfold SpinLift.frameAt
  generalize L.toFrame ⟨y, p⟩ = F at hproj ⊢
  obtain ⟨x, f⟩ := F
  simp only at hproj
  subst hproj
  have := f.inner_map_map v w
  exact this

/-- The frame change between the sections `i` and `j`: the matrix of the vector action of the
transition element. -/
noncomputable def rot (i j : A.ι) (y : M) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => (vecConj (A.trans i j y) (EuclideanSpace.single a 1)) b

end SpinStructure.SmoothSpinAtlas

/-- **The spin structure (atlas form) of a smooth spin atlas** of a lift: the frames are the frames
of the sections, the lifts their transition elements. -/
noncomputable def SpinStructure.ofSmoothAtlas {hpos} {L : SpinLift g hpos}
    (A : SpinStructure.SmoothSpinAtlas hpos L) : SpinStructure g A.ι where
  dom := A.dom
  Rot := A.rot
  lift i j y := (A.trans i j y : CliffordAlgebra (Qneg n))
  isLift i j x _ _ := by
    refine ⟨(A.trans i j x).2, fun a => ?_⟩
    have h : (∑ b, A.rot i j x a b • e b) = vecConj (A.trans i j x) (e a) :=
      (vecConj_single_expand (A.trans i j x) a).symm
    rw [h]
    exact (ι_vecConj _ _).symm
  rot_cocycle i j k x _ _ _ := by
    ext a b
    simp only [SpinStructure.SmoothSpinAtlas.rot, Matrix.of_apply, Matrix.mul_apply]
    rw [← A.trans_mul i j k x, vecConj_mul]
    conv_lhs => rw [vecConj_single_expand (A.trans j k x) a, map_sum]
    simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  lift_cocycle i j k x _ _ _ := by
    rw [← A.trans_mul i j k x]; rfl
  frame i a y := L.frameAt y (A.sec i y) (e a)
  dom_open := A.dom_open
  dom_cover := A.dom_cover
  frame_smooth := A.frame_smooth
  lift_smooth := A.trans_smooth
  frame_orthonormal i a b y _ := by
    rw [SpinStructure.SmoothSpinAtlas.g_frameAt]
    simp [e, EuclideanSpace.inner_single_left]
  frame_change i j y _ _ a := by
    rw [A.sec_eq_smul_trans i j y, SpinStructure.SmoothSpinAtlas.frameAt_smul]
    have h : vecConj (A.trans i j y) (e a) = ∑ b, A.rot i j y a b • e b :=
      vecConj_single_expand (A.trans i j y) a
    rw [h]
    exact SpinStructure.SmoothSpinAtlas.frameAt_sum _ _ _ _

/-! ## From the atlas form to the principal bundle and back -/

section Forward

variable {ι : Type} (S : SpinStructure g ι)

/-- The chart trivializations of the principal bundle belong to its atlas. -/
instance SpinStructure.memTrivializationAtlas_spinCore (i : ι) :
    MemTrivializationAtlas (S.spinCore.localTriv i) :=
  ⟨⟨i, rfl⟩⟩

/-- The unit section of the chart `i` of the principal bundle of `S`, written in the chart chosen
at each point: its coordinate there is `lift (idx x) i x`. -/
noncomputable def SpinStructure.unitSec (i : ι) (x : M) : S.PSpin x :=
  S.spinCocycle i (S.idx x) x

/-- The coordinate in chart `i` of the unit section of chart `i` is `1`. -/
lemma SpinStructure.localTriv_unitSec {i : ι} {x : M} (hx : x ∈ S.dom i) :
    (S.spinCore.localTriv i ⟨x, S.unitSec i x⟩).2 = 1 := by
  apply Subtype.ext
  rw [S.spinCore_localTriv_snd hx]
  change S.lift i (S.idx x) x * (S.spinCocycle i (S.idx x) x : CliffordAlgebra (Qneg n)) = 1
  rw [S.coe_spinCocycle hx (S.mem_idx x), ← S.lift_cocycle i (S.idx x) i x hx (S.mem_idx x) hx,
    S.lift_self hx]

/-- The frames of the unit sections are the frames of `S`. -/
lemma SpinStructure.frameAt_unitSec {i : ι} {x : M} (hx : x ∈ S.dom i) (v : E n) :
    (letI := S.riemannianBundle; (S.toFrame ⟨x, S.unitSec i x⟩).frame v) = S.frameMap i x v := by
  rw [S.toFrame_apply_chart ⟨x, S.unitSec i x⟩ hx, S.localTriv_unitSec hx, vecConj_one]

/-- The transition elements of the unit sections are the lifts of `S`. -/
lemma SpinStructure.division_unitSec {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j) :
    (PrincipalBundle.division (spinGroup (Qneg n)) (S.unitSec i x) (S.unitSec j x) :
      CliffordAlgebra (Qneg n)) = S.lift i j x := by
  rw [PrincipalBundle.division_eq_of_mem_baseSet (e := S.spinCore.localTriv i) (by exact hi)]
  rw [S.localTriv_unitSec hi]
  simp only [inv_one, one_mul]
  have h := S.spinCore_localTriv_snd hi (S.unitSec j x)
  rw [h]
  change S.lift i (S.idx x) x * (S.spinCocycle j (S.idx x) x : CliffordAlgebra (Qneg n)) = _
  rw [S.coe_spinCocycle hj (S.mem_idx x), ← S.lift_cocycle i (S.idx x) j x hi (S.mem_idx x) hj]

end Forward

section Forward2

variable {ι : Type} (S : SpinStructure g ι)

omit [I.Boundaryless] in
lemma SpinStructure.frameMap_e (i : ι) (x : M) (a : Fin n) : S.frameMap i x (e a) = S.frame i a x := by
  simp [SpinStructure.frameMap, e, Finset.sum_ite_eq']

/-- **The principal bundle of a spin structure has a smooth spin atlas**: the unit sections of its
charts. -/
noncomputable def SpinStructure.smoothAtlas :
    SpinStructure.SmoothSpinAtlas (fun _ v hv => SpinStructure.g_pos S v hv) S.principal where
  ι := ι
  dom := S.dom
  dom_open := S.dom_open
  dom_cover := S.dom_cover
  sec := S.unitSec
  sec_cont i := by
    have hcont : ContinuousOn (fun x : M => (S.spinCore.localTriv i).toOpenPartialHomeomorph.symm
        (x, (1 : spinGroup (Qneg n)))) (S.dom i) := by
      refine (S.spinCore.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_id.prodMk continuous_const).continuousOn fun x hx => ?_
      rw [(S.spinCore.localTriv i).target_eq]
      exact ⟨hx, Set.mem_univ _⟩
    refine hcont.congr fun x hx => ?_
    beta_reduce
    rw [FiberBundleCore.localTriv_symm_apply]
    simp only [fiberBundleCoreOfGroupCocycle_coordChange, fiberBundleCoreOfGroupCocycle_indexAt,
      smul_eq_mul, mul_one]
    rfl
  frame_smooth i a x hx := by
    refine (S.frame_smooth i a x hx).congr_of_eventuallyEq ?_
    filter_upwards [(S.dom_open i).mem_nhds hx] with y hy
    change (⟨y, (letI := S.riemannianBundle; (S.toFrame ⟨y, S.unitSec i y⟩).frame (e a))⟩ :
      TangentBundle I M) = ⟨y, S.frame i a y⟩
    rw [S.frameAt_unitSec hy, S.frameMap_e]
  trans_smooth i j φ x hi hj := by
    refine (S.lift_smooth i j φ x hi hj).congr_of_eventuallyEq ?_
    filter_upwards [((S.dom_open i).inter (S.dom_open j)).mem_nhds ⟨hi, hj⟩] with y hy
    change φ (PrincipalBundle.division (spinGroup (Qneg n)) (S.unitSec i y) (S.unitSec j y) :
      CliffordAlgebra (Qneg n)) = φ (S.lift i j y)
    rw [S.division_unitSec hy.1 hy.2]

/-- Reading back the smooth atlas of `S.principal` gives the frames of `S`. -/
theorem SpinStructure.ofSmoothAtlas_frame {i : ι} {x : M} (hx : x ∈ S.dom i) (a : Fin n) :
    (SpinStructure.ofSmoothAtlas S.smoothAtlas).frame i a x = S.frame i a x := by
  change (letI := S.riemannianBundle; (S.toFrame ⟨x, S.unitSec i x⟩).frame (e a)) = _
  rw [S.frameAt_unitSec hx, S.frameMap_e]

/-- Reading back the smooth atlas of `S.principal` gives the lifts of `S`. -/
theorem SpinStructure.ofSmoothAtlas_lift {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j) :
    (SpinStructure.ofSmoothAtlas S.smoothAtlas).lift i j x = S.lift i j x :=
  S.division_unitSec hi hj

end Forward2

/-! ## From the principal bundle to the atlas form and back -/

section Converse

variable {hpos} {L : SpinLift g hpos} (A : SpinStructure.SmoothSpinAtlas hpos L)

omit [I.Boundaryless] in
/-- The frame of a point of a lift, as a point of the tangent bundle, is its `frameAt`. -/
lemma SpinLift.mk_frame (q : letI := g.riemannianBundleOfPos hpos; TotalSpace (spinGroup (Qneg n)) L.P)
    (w : E n) :
    letI := g.riemannianBundleOfPos hpos
    (TotalSpace.mk' (Fin n → ℝ) (L.toFrame q).proj ((L.toFrame q).frame w) : TangentBundle I M) =
      ⟨q.proj, L.frameAt q.proj q.snd w⟩ := by
  let _ := g.riemannianBundleOfPos hpos
  obtain ⟨y, p⟩ := q
  have hproj := L.proj_toFrame ⟨y, p⟩
  unfold SpinLift.frameAt
  generalize L.toFrame ⟨y, p⟩ = F at hproj ⊢
  obtain ⟨x, f⟩ := F
  simp only at hproj
  subst hproj
  rfl

omit [I.Boundaryless] in
/-- The frame of a section of the atlas is the frame map of the atlas spin structure. -/
lemma SpinStructure.SmoothSpinAtlas.frameAt_sec (i : A.ι) (y : M) (w : E n) :
    L.frameAt y (A.sec i y) w = (SpinStructure.ofSmoothAtlas A).frameMap i y w := by
  have hw : w = ∑ a, w a • e a := by
    simpa [e] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w).symm
  conv_lhs => rw [hw]
  rw [SpinStructure.SmoothSpinAtlas.frameAt_sum]
  rfl

/-- The fibre bijection of the equivalence: the point with coordinate `p` in the chart chosen at
`x` goes to `sec (idx x) x · p`. -/
noncomputable def SpinStructure.SmoothSpinAtlas.fibreEquiv (x : M) :
    (SpinStructure.ofSmoothAtlas A).PSpin x ≃ (letI := g.riemannianBundleOfPos hpos; L.P x) :=
  letI := g.riemannianBundleOfPos hpos
  { toFun := fun p => op p.val • A.sec ((SpinStructure.ofSmoothAtlas A).idx x) x
    invFun := fun q => (PrincipalBundle.division (spinGroup (Qneg n))
      (A.sec ((SpinStructure.ofSmoothAtlas A).idx x) x) q : spinGroup (Qneg n))
    left_inv := fun p => by
      change PrincipalBundle.division (spinGroup (Qneg n)) _ (op p.val • _) = p
      rw [PrincipalBundle.division_smul_right, PrincipalBundle.division_self, one_mul]
      rfl
    right_inv := fun q => PrincipalBundle.smul_division _ _ }

/-- The fibre bijection read in the chart `i` of the atlas spin structure. -/
lemma SpinStructure.SmoothSpinAtlas.fibreEquiv_chart {i : A.ι} {y : M} (hy : y ∈ A.dom i)
    (p : (SpinStructure.ofSmoothAtlas A).PSpin y) :
    letI := g.riemannianBundleOfPos hpos
    A.fibreEquiv y p = op ((SpinStructure.ofSmoothAtlas A).spinCore.localTriv i ⟨y, p⟩).2 • A.sec i y := by
  let _ := g.riemannianBundleOfPos hpos
  have hcoord : (((SpinStructure.ofSmoothAtlas A).spinCore.localTriv i ⟨y, p⟩).2 :
      spinGroup (Qneg n)) = A.trans i ((SpinStructure.ofSmoothAtlas A).idx y) y * p.val := by
    apply Subtype.ext
    rw [(SpinStructure.ofSmoothAtlas A).spinCore_localTriv_snd hy]
    rfl
  change op p.val • A.sec ((SpinStructure.ofSmoothAtlas A).idx y) y = _
  rw [hcoord, A.sec_eq_smul_trans i ((SpinStructure.ofSmoothAtlas A).idx y) y, smul_smul, ← op_mul]

/-- The fibre bijections are continuous on total spaces. -/
lemma SpinStructure.SmoothSpinAtlas.continuous_fibreEquiv :
    letI := g.riemannianBundleOfPos hpos
    Continuous fun q : TotalSpace (spinGroup (Qneg n)) (SpinStructure.ofSmoothAtlas A).PSpin =>
      (⟨q.proj, A.fibreEquiv q.proj q.snd⟩ : TotalSpace (spinGroup (Qneg n)) L.P) := by
  let _ := g.riemannianBundleOfPos hpos
  rw [continuous_iff_continuousAt]
  intro q₀
  have hq₀ : q₀.proj ∈ A.dom ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) :=
    (SpinStructure.ofSmoothAtlas A).mem_idx q₀.proj
  have hproj : Continuous fun q : TotalSpace (spinGroup (Qneg n))
      (SpinStructure.ofSmoothAtlas A).PSpin => q.proj :=
    FiberBundle.continuous_proj _ _
  have hnear : ∀ᶠ q in 𝓝 q₀, q.proj ∈ A.dom ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) :=
    hproj.continuousAt.preimage_mem_nhds ((A.dom_open _).mem_nhds hq₀)
  have hsec : ContinuousAt (fun q : TotalSpace (spinGroup (Qneg n))
      (SpinStructure.ofSmoothAtlas A).PSpin =>
        TotalSpace.mk' (spinGroup (Qneg n)) q.proj
          (A.sec ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) q.proj)) q₀ :=
    ((A.sec_cont _).continuousAt ((A.dom_open _).mem_nhds hq₀)).comp hproj.continuousAt
  have hloc : ContinuousAt (fun q : TotalSpace (spinGroup (Qneg n))
      (SpinStructure.ofSmoothAtlas A).PSpin =>
        ((SpinStructure.ofSmoothAtlas A).spinCore.localTriv
          ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) q).2) q₀ :=
    (continuous_snd.continuousAt).comp (((SpinStructure.ofSmoothAtlas A).spinCore.localTriv _).continuousAt
      (((SpinStructure.ofSmoothAtlas A).spinCore.localTriv _).mem_source.2 hq₀))
  refine (hsec.totalSpaceMk_smul hloc).congr ?_
  filter_upwards [hnear] with q hq
  exact congrArg (TotalSpace.mk' (spinGroup (Qneg n)) q.proj) (A.fibreEquiv_chart hq q.snd).symm

/-- The inverse fibre bijections are continuous on total spaces. -/
lemma SpinStructure.SmoothSpinAtlas.continuous_fibreEquiv_symm :
    letI := g.riemannianBundleOfPos hpos
    Continuous fun q : TotalSpace (spinGroup (Qneg n)) L.P =>
      (⟨q.proj, (A.fibreEquiv q.proj).symm q.snd⟩ :
        TotalSpace (spinGroup (Qneg n)) (SpinStructure.ofSmoothAtlas A).PSpin) := by
  let _ := g.riemannianBundleOfPos hpos
  rw [continuous_iff_continuousAt]
  intro q₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  have hq₀ : q₀.proj ∈ A.dom ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) :=
    (SpinStructure.ofSmoothAtlas A).mem_idx q₀.proj
  have hproj : Continuous fun q : TotalSpace (spinGroup (Qneg n)) L.P => q.proj :=
    FiberBundle.continuous_proj _ _
  have hnear : ∀ᶠ q in 𝓝 q₀, q.proj ∈ A.dom ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) :=
    hproj.continuousAt.preimage_mem_nhds ((A.dom_open _).mem_nhds hq₀)
  have hsec : ContinuousAt (fun q : TotalSpace (spinGroup (Qneg n)) L.P =>
      TotalSpace.mk' (spinGroup (Qneg n)) q.proj
        (A.sec ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) q.proj)) q₀ :=
    ((A.sec_cont _).continuousAt ((A.dom_open _).mem_nhds hq₀)).comp hproj.continuousAt
  have hdiv := hsec.division (q := fun q => q.snd) continuousAt_id
  refine hdiv.congr ?_
  filter_upwards [hnear] with q hq
  have hcoord : (((SpinStructure.ofSmoothAtlas A).spinCore.localTriv
      ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) ⟨q.proj, (A.fibreEquiv q.proj).symm q.snd⟩).2 :
        spinGroup (Qneg n)) =
      A.trans ((SpinStructure.ofSmoothAtlas A).idx q₀.proj) ((SpinStructure.ofSmoothAtlas A).idx q.proj)
        q.proj * PrincipalBundle.division _ (A.sec ((SpinStructure.ofSmoothAtlas A).idx q.proj) q.proj)
          q.snd := by
    apply Subtype.ext
    rw [(SpinStructure.ofSmoothAtlas A).spinCore_localTriv_snd hq]
    rfl
  exact (hcoord.trans (PrincipalBundle.division_mul_division _ _ _)).symm

/-- The fibre bijections are equivariant. -/
lemma SpinStructure.SmoothSpinAtlas.fibreEquiv_smul (x : M)
    (p : (SpinStructure.ofSmoothAtlas A).PSpin x) (h : spinGroup (Qneg n)) :
    letI := g.riemannianBundleOfPos hpos
    A.fibreEquiv x (op h • p) = (op h • (A.fibreEquiv x p : L.P x) : L.P x) := by
  let _ := g.riemannianBundleOfPos hpos
  change op ((p.val : spinGroup (Qneg n)) * h) • A.sec ((SpinStructure.ofSmoothAtlas A).idx x) x =
    op h • (op p.val • A.sec ((SpinStructure.ofSmoothAtlas A).idx x) x)
  rw [op_mul, mul_smul]

/-- The fibre bijections commute with the maps to frames. -/
lemma SpinStructure.SmoothSpinAtlas.toFrame_fibreEquiv (x : M)
    (p : (SpinStructure.ofSmoothAtlas A).PSpin x) :
    letI := g.riemannianBundleOfPos hpos
    L.toFrame ⟨x, A.fibreEquiv x p⟩ = (SpinStructure.ofSmoothAtlas A).toFrame ⟨x, p⟩ := by
  let _ := g.riemannianBundleOfPos hpos
  refine OrthonormalFrameBundle.ext_totalSpaceMk fun v => ?_
  rw [L.mk_frame ⟨x, A.fibreEquiv x p⟩ (WithLp.toLp 2 v)]
  have h1 : L.frameAt x (A.fibreEquiv x p) (WithLp.toLp 2 v) =
      (SpinStructure.ofSmoothAtlas A).frameMap ((SpinStructure.ofSmoothAtlas A).idx x) x
        (vecConj p.val (WithLp.toLp 2 v)) := by
    change L.frameAt x (op p.val • A.sec ((SpinStructure.ofSmoothAtlas A).idx x) x)
      (WithLp.toLp 2 v) = _
    rw [SpinStructure.SmoothSpinAtlas.frameAt_smul, A.frameAt_sec]
  exact congrArg (TotalSpace.mk' (Fin n → ℝ) x) (h1.trans
    ((SpinStructure.ofSmoothAtlas A).toFrame_apply ⟨x, p⟩ (WithLp.toLp 2 v)).symm)

/-- **A lift with a smooth spin atlas is the principal bundle of the atlas spin structure**: the
fibre bijections form an equivalence of lifts of the orthonormal frame bundle. -/
noncomputable def SpinStructure.ofSmoothAtlasEquiv :
    letI := g.riemannianBundleOfPos hpos
    (SpinStructure.ofSmoothAtlas A).principal.Equiv L :=
  letI := g.riemannianBundleOfPos hpos
  { toEquiv := A.fibreEquiv
    continuous_toFun := A.continuous_fibreEquiv
    continuous_invFun := A.continuous_fibreEquiv_symm
    map_smul := A.fibreEquiv_smul
    toFrame_map := A.toFrame_fibreEquiv }

end Converse

/-- **Non-vacuity**: the round trip on the standard global frame of `ℝⁿ`. The principal bundle of
`euclideanSpinStructure n` has the smooth atlas of its unit sections, and the principal bundle of the
spin structure read back from that atlas is equivalent to it as a lift of the frame bundle. -/
noncomputable example (n : ℕ) :
    letI := (euclideanSpinStructure n).riemannianBundle
    (SpinStructure.ofSmoothAtlas (euclideanSpinStructure n).smoothAtlas).principal.Equiv
      (euclideanSpinStructure n).principal :=
  SpinStructure.ofSmoothAtlasEquiv _

/-- Trust check: reading back the smooth atlas of the standard frame of `ℝⁿ` gives the standard
basis vectors as frame. -/
example (n : ℕ) (a : Fin n) (x : Fin n → ℝ) :
    (SpinStructure.ofSmoothAtlas (euclideanSpinStructure n).smoothAtlas).frame () a x =
      (Pi.single a 1 : Fin n → ℝ) :=
  (euclideanSpinStructure n).ofSmoothAtlas_frame trivial a

end Lightlike.Dirac

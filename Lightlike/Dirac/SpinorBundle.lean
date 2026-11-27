import Mathlib
import Lightlike.Bundles.SpinGroup
import Lightlike.Dirac.SpinLichnerowicz
import Lightlike.Gauge.Connection.PrincipalAssociated

/-!
# The spinor bundle of a spin structure and its sections

A spin structure `S` (atlas form) has the transition functions `x ↦ lift j i x ∈ Spin(n)` on the
overlaps of its frame domains: they form a `Spin(n)`-valued cocycle (`SpinStructure.spinCocycle`,
`SpinStructure.toPrincipalCocycle`), the transition data of the principal `Spin(n)`-bundle of the
spin structure.  For a Clifford module `ρ` on `V`, the **spinor bundle** `P ×_ρ V` is the vector
bundle with fibre `V` and transition maps `ρ(lift j i x)` (the associated bundle of
`Lightlike.Gauge.PrincipalCocycle.assocCore`, Svetlichny's Theorem 7: the bundle with the cocycle
of `P` and the action `ρ`): `SpinorBundle S ρ`, a Mathlib vector bundle, smooth because the lifts
are (`SpinStructure.spinorCore_isContMDiff`).

Its smooth sections (`SpinorSection S ρ`, Mathlib's `ContMDiffSection`) correspond to the smooth
spinor fields of the atlas form that vanish off their frame domains (`SpinorField.IsNormalized`):
the representation of a section in the frame `i` is its fibre coordinate in the trivialization `i`
(`SpinorSection.toField`), and a field is glued back through the trivialization chosen at each
point (`SpinorSection.ofField`); the two maps are inverse (`SpinorSection.equivField`).

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, §3 (spinor bundles
  `P_Spin ×_ρ V`); here the bundle is built from the transition functions of `P_Spin`.
* G. Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1, Theorem 7, p. 22.
-/

open Bundle Manifold CliffordAlgebra Filter Set
open scoped Manifold ContDiff Topology

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type} [TopologicalSpace M] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Fin n → ℝ) H} [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {g : NondegMetric I M} {ι : Type} (S : SpinStructure g ι)

/-! ## The `Spin(n)`-cocycle -/

/-- The lifts of a spin structure lie in `Spin(n)`. -/
lemma SpinStructure.lift_mem {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j) :
    S.lift i j x ∈ spinGroup (Qneg n) :=
  (S.isLift i j x hi hj).1

open Classical in
/-- The transition function from the frame `i` to the frame `j`, as an element of `Spin(n)`:
`lift j i x` on the overlap, `1` elsewhere. -/
noncomputable def SpinStructure.spinCocycle (i j : ι) (x : M) : spinGroup (Qneg n) :=
  if h : x ∈ S.dom i ∧ x ∈ S.dom j then ⟨S.lift j i x, S.lift_mem h.2 h.1⟩ else 1

lemma SpinStructure.coe_spinCocycle {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j) :
    (S.spinCocycle i j x : CliffordAlgebra (Qneg n)) = S.lift j i x := by
  simp [SpinStructure.spinCocycle, hi, hj]

lemma SpinStructure.spinCocycle_cocycle (i j k : ι) (x : M) (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (hk : x ∈ S.dom k) : S.spinCocycle j k x * S.spinCocycle i j x = S.spinCocycle i k x := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, S.coe_spinCocycle hj hk, S.coe_spinCocycle hi hj,
    S.coe_spinCocycle hi hk]
  exact (S.lift_cocycle k j i x hk hj hi).symm

lemma SpinStructure.spinCocycle_self (i : ι) (x : M) : S.spinCocycle i i x = 1 := by
  by_cases hx : x ∈ S.dom i
  · have h := S.spinCocycle_cocycle i i i x hx hx hx
    exact mul_eq_left.mp h
  · simp [SpinStructure.spinCocycle, hx]

lemma SpinStructure.continuousOn_spinCocycle (i j : ι) :
    ContinuousOn (S.spinCocycle i j) (S.dom i ∩ S.dom j) := by
  rw [continuousOn_spinGroup_iff]
  let _ := clNormedRing n
  let _ := clNormedAlgebra n
  have h : ContinuousOn (S.lift j i) (S.dom i ∩ S.dom j) := fun x hx =>
    ((S.contMDiffAt_lift hx.2 hx.1).continuousAt).continuousWithinAt
  refine h.congr fun x hx => ?_
  exact S.coe_spinCocycle hx.1 hx.2

/-- The transition data of the principal `Spin(n)`-bundle of a spin structure. -/
noncomputable def SpinStructure.toPrincipalCocycle : Gauge.PrincipalCocycle M (spinGroup (Qneg n)) where
  ι := ι
  U i := ⟨S.dom i, S.dom_open i⟩
  g := S.spinCocycle
  cont i j := S.continuousOn_spinCocycle i j
  self i x := S.spinCocycle_self i x
  cocycle i j k x hi hj hk := S.spinCocycle_cocycle i j k x hi hj hk

/-! ## The spinor bundle -/

variable (ρ : CliffordRep n V)

/-- **The spinor bundle** of the spin structure `S` and the Clifford module `ρ`, as a vector bundle
core: fibre `V`, transition maps `ρ(lift j i x)` from the frame `i` to the frame `j`. -/
noncomputable def SpinStructure.spinorCore : VectorBundleCore ℝ M V ι :=
  S.toPrincipalCocycle.assocCore S.dom_cover (spinRep ρ) (continuous_spinRep ρ)

lemma SpinStructure.spinorCore_coordChange {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : V) : (S.spinorCore ρ).coordChange i j x v = ρ (S.lift j i x) v := by
  change spinRep ρ (S.spinCocycle i j x) v = _
  rw [spinRep_apply, S.coe_spinCocycle hi hj]

@[simp] lemma SpinStructure.spinorCore_baseSet (i : ι) : (S.spinorCore ρ).baseSet i = S.dom i := rfl

/-- The spinor bundle is smooth: its transition maps `ρ(lift j i)` are smooth on the overlaps. -/
instance SpinStructure.spinorCore_isContMDiff : (S.spinorCore ρ).IsContMDiff I ∞ where
  contMDiffOn_coordChange i j := by
    let _ := clNormedRing n
    let _ := clNormedAlgebra n
    intro x hx
    have hρ : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) ∞ (fun y => ρ (S.lift j i y)) x :=
      (LinearMap.toContinuousLinearMap ρ.toLinearMap).contMDiff.contMDiffAt.comp x
        (S.contMDiffAt_lift hx.2 hx.1)
    refine (hρ.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [((S.dom_open i).inter (S.dom_open j)).mem_nhds hx] with y hy
    ext v
    exact S.spinorCore_coordChange ρ hy.1 hy.2 v

/-- The trivializations of the spinor core belong to the atlas of the spinor bundle. -/
instance SpinStructure.memTrivializationAtlas_spinorCore (i : ι) :
    MemTrivializationAtlas ((S.spinorCore ρ).localTriv i) :=
  ⟨⟨i, rfl⟩⟩

/-- **The spinor bundle** `P ×_ρ V` of the spin structure `S` for the Clifford module `ρ`: a smooth
real vector bundle over `M` with fibre `V`. -/
abbrev SpinorBundle : M → Type _ := (S.spinorCore ρ).Fiber

/-- **Smooth spinors**: the smooth sections of the spinor bundle. -/
abbrev SpinorSection := ContMDiffSection I V ∞ (SpinorBundle S ρ)

/-! ## Sections and spinor fields -/

/-- A spinor field of the atlas form vanishes off its frame domains: it carries no junk values. -/
def SpinorField.IsNormalized {S : SpinStructure g ι} {ρ : CliffordRep n V} (ψ : SpinorField S ρ) :
    Prop :=
  ∀ i x, x ∉ S.dom i → ψ.rep i x = 0

variable {S ρ}

/-- Spinor fields with the same representations are equal. -/
lemma SpinorField.ext_rep {ψ φ : SpinorField S ρ} (h : ψ.rep = φ.rep) : ψ = φ := by
  cases ψ; cases φ
  simp only at h
  subst h
  rfl

open Classical in
/-- The representation in the frame `i` of a section of the spinor bundle: its fibre coordinate in
the trivialization `i` on the frame domain, `0` elsewhere. -/
noncomputable def SpinorSection.rep (σ : SpinorSection S ρ) (i : ι) (x : M) : V :=
  if x ∈ S.dom i then (S.spinorCore ρ).coordChange ((S.spinorCore ρ).indexAt x) i x (σ x) else 0

lemma SpinorSection.rep_of_mem (σ : SpinorSection S ρ) {i : ι} {x : M} (hx : x ∈ S.dom i) :
    σ.rep i x = (S.spinorCore ρ).coordChange ((S.spinorCore ρ).indexAt x) i x (σ x) := by
  simp [SpinorSection.rep, hx]

lemma SpinorSection.rep_eq_localTriv (σ : SpinorSection S ρ) {i : ι} {x : M} (hx : x ∈ S.dom i) :
    σ.rep i x = ((S.spinorCore ρ).localTriv i ⟨x, σ x⟩).2 := by
  rw [σ.rep_of_mem hx, VectorBundleCore.localTriv_apply]

/-- The spinor field of a section: its representations in the frames. -/
noncomputable def SpinorSection.toField (σ : SpinorSection S ρ) : SpinorField S ρ where
  rep := σ.rep
  transform i j x hi hj := by
    rw [σ.rep_of_mem hi, σ.rep_of_mem hj]
    have hidx := (S.spinorCore ρ).mem_baseSet_at x
    erw [← (S.spinorCore ρ).coordChange_comp _ j i x ⟨⟨hidx, hj⟩, hi⟩,
      S.spinorCore_coordChange ρ hj hi]

lemma SpinorSection.toField_isNormalized (σ : SpinorSection S ρ) : σ.toField.IsNormalized :=
  fun i x hx => by simp [SpinorSection.toField, SpinorSection.rep, hx]

/-- The representations of a smooth section are smooth on their frame domains. -/
lemma SpinorSection.toField_isSmooth (σ : SpinorSection S ρ) : σ.toField.IsSmooth := by
  intro i x hx
  have hσ := σ.contMDiff x
  have htriv := ((S.spinorCore ρ).localTriv i).contMDiffAt_section_iff (IB := I) (n := ∞)
    (s := fun y => σ y) (x₀ := x) (by exact hx)
  have h := htriv.1 hσ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(S.dom_open i).mem_nhds hx] with y hy
  exact σ.rep_eq_localTriv hy

/-- The section glued from a smooth spinor field: at each point its representation in the frame
chosen there. -/
noncomputable def SpinorSection.ofField (ψ : SpinorField S ρ) (hψ : ψ.IsSmooth) : SpinorSection S ρ where
  toFun x := ψ.rep ((S.spinorCore ρ).indexAt x) x
  contMDiff_toFun := by
    intro x₀
    set i₀ := (S.spinorCore ρ).indexAt x₀
    have hx₀ : x₀ ∈ S.dom i₀ := (S.spinorCore ρ).mem_baseSet_at x₀
    refine (contMDiffAt_section (IB := I) (F := V) (E := (S.spinorCore ρ).Fiber) (s := fun x =>
      (ψ.rep ((S.spinorCore ρ).indexAt x) x : (S.spinorCore ρ).Fiber x)) x₀).2 ?_
    refine (hψ i₀ x₀ hx₀).congr_of_eventuallyEq ?_
    filter_upwards [(S.dom_open i₀).mem_nhds hx₀] with y hy
    change ((S.spinorCore ρ).localTriv i₀ ⟨y, ψ.rep ((S.spinorCore ρ).indexAt y) y⟩).2 = ψ.rep i₀ y
    rw [VectorBundleCore.localTriv_apply, S.spinorCore_coordChange ρ ((S.spinorCore ρ).mem_baseSet_at y) hy,
      ← ψ.transform i₀ _ y hy ((S.spinorCore ρ).mem_baseSet_at y)]

lemma SpinorSection.ofField_apply (ψ : SpinorField S ρ) (hψ : ψ.IsSmooth) (x : M) :
    SpinorSection.ofField ψ hψ x = ψ.rep ((S.spinorCore ρ).indexAt x) x := rfl

/-- The field of the glued section is the given field on the frame domains. -/
lemma SpinorSection.toField_ofField_rep (ψ : SpinorField S ρ) (hψ : ψ.IsSmooth) {i : ι} {x : M}
    (hx : x ∈ S.dom i) : (SpinorSection.ofField ψ hψ).toField.rep i x = ψ.rep i x := by
  change (SpinorSection.ofField ψ hψ).rep i x = _
  rw [SpinorSection.rep_of_mem _ hx, SpinorSection.ofField_apply,
    S.spinorCore_coordChange ρ ((S.spinorCore ρ).mem_baseSet_at x) hx,
    ← ψ.transform i _ x hx ((S.spinorCore ρ).mem_baseSet_at x)]

/-- Gluing the field of a section gives back the section. -/
lemma SpinorSection.ofField_toField (σ : SpinorSection S ρ) :
    SpinorSection.ofField σ.toField σ.toField_isSmooth = σ := by
  ext x
  change σ.rep ((S.spinorCore ρ).indexAt x) x = σ x
  rw [σ.rep_of_mem ((S.spinorCore ρ).mem_baseSet_at x)]
  erw [(S.spinorCore ρ).coordChange_self _ x ((S.spinorCore ρ).mem_baseSet_at x)]

/-- **Smooth spinors are smooth normalized spinor fields**: the sections of the spinor bundle
correspond bijectively to the smooth spinor fields of the atlas form vanishing off their frame
domains. -/
noncomputable def SpinorSection.equivField :
    SpinorSection S ρ ≃ {ψ : SpinorField S ρ // ψ.IsSmooth ∧ ψ.IsNormalized} where
  toFun σ := ⟨σ.toField, σ.toField_isSmooth, σ.toField_isNormalized⟩
  invFun ψ := SpinorSection.ofField ψ.1 ψ.2.1
  left_inv σ := SpinorSection.ofField_toField σ
  right_inv ψ := by
    apply Subtype.ext
    have hrep : (SpinorSection.ofField ψ.1 ψ.2.1).toField.rep = ψ.1.rep := by
      funext i x
      by_cases hx : x ∈ S.dom i
      · exact SpinorSection.toField_ofField_rep ψ.1 ψ.2.1 hx
      · rw [(SpinorSection.ofField ψ.1 ψ.2.1).toField_isNormalized i x hx, ψ.2.2 i x hx]
    exact SpinorField.ext_rep hrep

/-! ## Smoothness of the operators -/

section Smooth

variable (S ρ)

/-- **The directional derivative of a smooth function along a smooth field is smooth.** -/
lemma contMDiffAt_mvfderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : M → F} {X : Π y : M, TangentSpace I y} {x : M}
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, F) ∞ φ y)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) x) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => mvfderiv I φ y (X y)) x := by
  set ψ := extChartAt I x with hψ
  have hsrc : x ∈ ψ.source := mem_extChartAt_source x
  have hbase : x ∈ (tTrivW (E := Fin n → ℝ) (M := M) (I := I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hXh : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (hatW x X) x := by
    have := (contMDiffAt_section (IB := I) (s := X) x).1 hX
    exact this
  have hhat : ∀ z ∈ ψ.source, hatW x X z =
      mfderiv I 𝓘(ℝ, Fin n → ℝ) ψ z (X z) := by
    intro z hz
    have hz' : z ∈ (chartAt H x).source := by rwa [hψ, extChartAt_source] at hz
    have := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hz'
    have hzb : z ∈ (tTrivW (E := Fin n → ℝ) (M := M) (I := I) x).baseSet := by
      simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hz'
    have h2 : hatW x X z = (tTrivW (E := Fin n → ℝ) (M := M) (I := I) x).continuousLinearMapAt ℝ z (X z) := by
      rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply,
        ite_eq_left hzb]
      rfl
    rw [h2]
    exact congrArg (fun L => L (X z)) this
  have hφt : ContDiffAt ℝ ∞ (φ ∘ ψ.symm) (ψ x) := by
    have h2 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ ψ.symm (ψ x) := by
      have := contMDiffWithinAt_extChartAt_symm_target (I := I) (n := ∞) x
        (ψ.map_source hsrc)
      have ht : ψ.target ∈ 𝓝 (ψ x) := extChartAt_target_mem_nhds x
      exact this.contMDiffAt ht
    have h3 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞ (φ ∘ ψ.symm) (ψ x) := by
      refine ContMDiffAt.comp (ψ x) ?_ h2
      rw [ψ.left_inv hsrc]; exact hφ.self_of_nhds
    exact contMDiffAt_iff_contDiffAt.1 h3
  have hdφ : ContDiffAt ℝ ∞ (fderiv ℝ (φ ∘ ψ.symm)) (ψ x) :=
    hφt.fderiv_right (m := ∞) (by simp)
  have hψx : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ ψ x := contMDiffAt_extChartAt
  have hD : ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => fderiv ℝ (φ ∘ ψ.symm) (ψ y) (hatW x X y)) x :=
    (hdφ.comp_contMDiffAt hψx).clm_apply hXh
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := I) x).mem_nhds hsrc, hφ]
    with y hy hφy
  rw [mvfderiv_eq_chart_at φ hy (hφy.mdifferentiableAt (by simp)), hhat y hy]

/-- The spinorial connection form is smooth on the frame domain. -/
lemma SpinStructure.contMDiffAt_spinForm {i : ι} {x : M} (hx : x ∈ S.dom i) (a : Fin n) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) ∞ (fun y => spinForm ρ (S.connForm i y a)) x := by
  have hexp : (fun y => spinForm ρ (S.connForm i y a)) =
      fun y => ∑ k, ∑ l, S.connForm i y a k l • ((1 / 4 : ℝ) • (gam ρ k * gam ρ l)) := by
    funext y
    simp only [spinForm, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  rw [hexp]
  refine contMDiffAt_finset_sum fun k _ => contMDiffAt_finset_sum fun l _ => ?_
  exact (S.contMDiffAt_connForm hx a k l).smul contMDiffAt_const

/-- The covariant derivative of a function smooth near a point of the frame domain is smooth there. -/
lemma SpinStructure.contMDiffAt_nabla {i : ι} {x : M} (hx : x ∈ S.dom i) {φ : M → V}
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, V) ∞ φ y) (a : Fin n) :
    ContMDiffAt I 𝓘(ℝ, V) ∞ (fun y => S.nabla ρ i a φ y) x := by
  have h1 := contMDiffAt_mvfderiv_apply hφ (S.frame_smooth i a x hx)
  have h2 : ContMDiffAt I 𝓘(ℝ, V) ∞ (fun y => spinForm ρ (S.connForm i y a) (φ y)) x :=
    (S.contMDiffAt_spinForm ρ hx a).clm_apply hφ.self_of_nhds
  exact h1.add h2

lemma SpinStructure.eventually_contMDiffAt_nabla {i : ι} {x : M} (hx : x ∈ S.dom i) {φ : M → V}
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, V) ∞ φ y) (a : Fin n) :
    ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, V) ∞ (fun y => S.nabla ρ i a φ y) y := by
  filter_upwards [(S.dom_open i).mem_nhds hx, eventually_eventually_nhds.2 hφ] with y hy hφy
  exact S.contMDiffAt_nabla ρ hy hφy a

variable {S ρ}

/-- The Dirac operator keeps smooth spinor fields smooth. -/
lemma SpinorField.IsSmooth.dirac {ψ : SpinorField S ρ} (hψ : ψ.IsSmooth) :
    (ψ.dirac hψ.funDiffAt).IsSmooth := by
  intro i x hx
  change ContMDiffAt I 𝓘(ℝ, V) ∞ (fun y => ∑ a, gam ρ a (S.nabla ρ i a (ψ.rep i) y)) x
  exact contMDiffAt_finset_sum fun a _ =>
    contMDiffAt_const.clm_apply (S.contMDiffAt_nabla ρ hx (hψ.eventually hx) a)

/-- The rough Laplacian keeps smooth spinor fields smooth. -/
lemma SpinorField.IsSmooth.roughLaplacian {ψ : SpinorField S ρ} (hψ : ψ.IsSmooth) :
    (ψ.roughLaplacian hψ.funDiffAt hψ.funDiffAt_nabla).IsSmooth := by
  intro i x hx
  change ContMDiffAt I 𝓘(ℝ, V) ∞ (fun y => -∑ a, (S.nabla ρ i a (fun z => S.nabla ρ i a (ψ.rep i) z) y -
    ∑ k, S.connForm i y a a k • S.nabla ρ i k (ψ.rep i) y)) x
  refine (contMDiffAt_finset_sum fun a _ => ?_).neg
  refine (S.contMDiffAt_nabla ρ hx (S.eventually_contMDiffAt_nabla ρ hx (hψ.eventually hx) a) a).sub ?_
  exact contMDiffAt_finset_sum fun k _ =>
    (S.contMDiffAt_connForm hx a a k).smul (S.contMDiffAt_nabla ρ hx (hψ.eventually hx) k)

end Smooth

/-! ## The Dirac operator and the rough Laplacian on smooth spinors -/

/-- **The Dirac operator on smooth spinors**: the section whose representation in every frame is
the Dirac operator of the representation (`SpinorSection.toField_dirac`). -/
noncomputable def SpinorSection.dirac (σ : SpinorSection S ρ) : SpinorSection S ρ :=
  SpinorSection.ofField (σ.toField.dirac σ.toField_isSmooth.funDiffAt) σ.toField_isSmooth.dirac

/-- **The rough Laplacian `∇*∇` on smooth spinors.** -/
noncomputable def SpinorSection.roughLaplacian (σ : SpinorSection S ρ) : SpinorSection S ρ :=
  SpinorSection.ofField (σ.toField.roughLaplacian σ.toField_isSmooth.funDiffAt
    σ.toField_isSmooth.funDiffAt_nabla) σ.toField_isSmooth.roughLaplacian

/-- In every frame, the representation of `D σ` is the Dirac operator of the representation of
`σ`. -/
lemma SpinorSection.toField_dirac (σ : SpinorSection S ρ) {i : ι} {x : M} (hx : x ∈ S.dom i) :
    σ.dirac.toField.rep i x = (σ.toField.dirac σ.toField_isSmooth.funDiffAt).rep i x :=
  SpinorSection.toField_ofField_rep _ _ hx

/-- In every frame, the representation of `∇*∇ σ` is the rough Laplacian of the representation
of `σ`. -/
lemma SpinorSection.toField_roughLaplacian (σ : SpinorSection S ρ) {i : ι} {x : M}
    (hx : x ∈ S.dom i) :
    σ.roughLaplacian.toField.rep i x =
      (σ.toField.roughLaplacian σ.toField_isSmooth.funDiffAt
        σ.toField_isSmooth.funDiffAt_nabla).rep i x :=
  SpinorSection.toField_ofField_rep _ _ hx

/-! ## Two frames: a smooth spinor is a pair of representations -/

section TwoFrames

variable {S₂ : SpinStructure g Bool}

/-- The lift from a frame to itself is `1` on its domain. -/
lemma SpinStructure.lift_self {T : SpinStructure g ι} {i : ι} {x : M} (hx : x ∈ T.dom i) :
    T.lift i i x = 1 := by
  have h := T.lift_cocycle i i i x hx hx hx
  have hu : T.lift i i x * star (T.lift i i x) = 1 :=
    spinGroup.mul_star_self_of_mem (T.lift_mem hx hx)
  calc T.lift i i x = T.lift i i x * (T.lift i i x * star (T.lift i i x)) := by rw [hu, mul_one]
    _ = T.lift i i x * T.lift i i x * star (T.lift i i x) := by rw [mul_assoc]
    _ = 1 := by rw [← h, hu]

/-- The smooth pairs of a two-frame spin structure: a representation in each frame, smooth on its
domain and `0` off it, related on the overlap by `f_true = ρ(lift true false) f_false`. -/
abbrev SpinStructure.SmoothPair (S₂ : SpinStructure g Bool) (ρ : CliffordRep n V) : Type _ :=
  {f : (M → V) × (M → V) //
    (∀ x, x ∈ S₂.dom true → ContMDiffAt I 𝓘(ℝ, V) ∞ f.1 x) ∧
    (∀ x, x ∈ S₂.dom false → ContMDiffAt I 𝓘(ℝ, V) ∞ f.2 x) ∧
    (∀ x, x ∉ S₂.dom true → f.1 x = 0) ∧ (∀ x, x ∉ S₂.dom false → f.2 x = 0) ∧
    ∀ x, x ∈ S₂.dom true → x ∈ S₂.dom false → f.1 x = ρ (S₂.lift true false x) (f.2 x)}

/-- The spinor field of a smooth pair. -/
noncomputable def SpinStructure.SmoothPair.toField (f : S₂.SmoothPair ρ) : SpinorField S₂ ρ where
  rep b := if b then f.1.1 else f.1.2
  transform i j x hi hj := by
    have hrel := f.2.2.2.2.2 
    cases i <;> cases j
    · simp [S₂.lift_self hi]
    · -- `f_false = ρ(lift false true) f_true`
      simp only [Bool.false_eq_true, ite_false, ite_true]
      rw [hrel x hj hi, ← ContinuousLinearMap.mul_apply, ← map_mul,
        ← S₂.lift_cocycle false true false x hi hj hi, S₂.lift_self hi, map_one]
      rfl
    · simp only [ite_true, Bool.false_eq_true, ite_false]
      exact hrel x hi hj
    · simp [S₂.lift_self hi]

/-- **A smooth spinor of a two-frame spin structure is a smooth pair** of representations
`(f_true, f_false)`, related by `f_true = ρ(lift true false) f_false` on the overlap. -/
noncomputable def SpinorSection.equivPair : SpinorSection S₂ ρ ≃ S₂.SmoothPair ρ where
  toFun σ := ⟨(σ.toField.rep true, σ.toField.rep false),
    fun x hx => σ.toField_isSmooth true x hx, fun x hx => σ.toField_isSmooth false x hx,
    fun x hx => σ.toField_isNormalized true x hx, fun x hx => σ.toField_isNormalized false x hx,
    fun x ht hf => σ.toField.transform true false x ht hf⟩
  invFun f := SpinorSection.ofField f.toField (by
    intro b x hx
    cases b
    · exact f.2.2.1 x hx
    · exact f.2.1 x hx)
  left_inv σ := by
    ext x
    have h : (SpinorSection.ofField σ.toField σ.toField_isSmooth) x = σ x :=
      congrArg (fun τ : SpinorSection S₂ ρ => τ x) (SpinorSection.ofField_toField σ)
    rw [← h]
    change (SpinStructure.SmoothPair.toField _).rep ((S₂.spinorCore ρ).indexAt x) x =
      σ.toField.rep ((S₂.spinorCore ρ).indexAt x) x
    cases (S₂.spinorCore ρ).indexAt x <;> rfl
  right_inv f := by
    apply Subtype.ext
    apply Prod.ext
    · funext x
      change (SpinorSection.ofField f.toField _).toField.rep true x = f.1.1 x
      by_cases hx : x ∈ S₂.dom true
      · exact SpinorSection.toField_ofField_rep _ _ hx
      · exact ((SpinorSection.ofField f.toField _).toField_isNormalized true x hx).trans
          (f.2.2.2.1 x hx).symm
    · funext x
      change (SpinorSection.ofField f.toField _).toField.rep false x = f.1.2 x
      by_cases hx : x ∈ S₂.dom false
      · exact SpinorSection.toField_ofField_rep _ _ hx
      · exact ((SpinorSection.ofField f.toField _).toField_isNormalized false x hx).trans
          (f.2.2.2.2.1 x hx).symm

end TwoFrames

end Lightlike.Dirac

import Lightlike.Gauge.Connection.PrincipalConnection

/-!
# Smoothness of the connection form on a glued principal bundle

The connection form `connForm` of `PrincipalConnection.lean` is a family of linear maps on the tangent spaces of `P`.
Written in the charts of `P` (Mathlib's tangent coordinate changes `tangentCoordChange`, the coordinates of the
tangent bundle in which a section of `T*P ⊗ g` is smooth, `contMDiffAt_hom_bundle`), it is `C^m` whenever the local
potentials are `C^m` one-forms in the charts of `M`, for a `C^n` group and `C^n` transition maps with `m + 1 ≤ n`
(`connForm_contMDiffAt`, and `contMDiff_connForm` for Mathlib's hom bundle; smooth data give a smooth form). The proof
writes the form near a point through one trivialization (`connForm_eq_of_mem`), splits the tangent coordinates of
`M × G` into those of `M` and of `G` (`tangentCoordChange_prod`), and uses that the derivatives of the group operations
are `C^m` in coordinates (`contMDiffAt_rightTrivial_coord`, `contMDiffAt_adjointE_inv`, from Mathlib's
`ContMDiffAt.mfderiv`).
-/

open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

universe u

namespace Lightlike.Gauge

section ProdCoord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- The tangent coordinate changes of a product manifold are the products of those of the factors. -/
lemma tangentCoordChange_prod {x y z : M × N}
    (hz : z ∈ (extChartAt (I.prod J) x).source ∩ (extChartAt (I.prod J) y).source) :
    tangentCoordChange (I.prod J) x y z =
      (tangentCoordChange I x.1 y.1 z.1).prodMap (tangentCoordChange J x.2 y.2 z.2) := by
  simp only [extChartAt_prod, PartialEquiv.prod_source, mem_inter_iff, mem_prod] at hz
  have h1 : HasFDerivWithinAt (extChartAt I y.1 ∘ (extChartAt I x.1).symm) (tangentCoordChange I x.1 y.1 z.1)
      (Prod.fst '' (range I ×ˢ range J)) (extChartAt I x.1 z.1) :=
    (hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hz.1.1, hz.2.1⟩).mono (fst_image_prod_subset _ _)
  have h2 : HasFDerivWithinAt (extChartAt J y.2 ∘ (extChartAt J x.2).symm) (tangentCoordChange J x.2 y.2 z.2)
      (Prod.snd '' (range I ×ˢ range J)) (extChartAt J x.2 z.2) :=
    (hasFDerivWithinAt_tangentCoordChange (I := J) ⟨hz.1.2, hz.2.2⟩).mono (snd_image_prod_subset _ _)
  have hd := HasFDerivWithinAt.prodMap (extChartAt I x.1 z.1, extChartAt J x.2 z.2) h1 h2
  rw [tangentCoordChange_def, extChartAt_prod, extChartAt_prod, ModelWithCorners.range_prod]
  exact hd.fderivWithin ((I.uniqueDiffWithinAt_image).prod (J.uniqueDiffWithinAt_image))

end ProdCoord

namespace PrincipalCocycle

variable {M G : Type u} [TopologicalSpace M] [TopologicalSpace G] [Group G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
  {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace ℝ E_G] [ChartedSpace E_G G]
  [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [IsManifold 𝓘(ℝ, E_G) 1 G] {n : ℕ∞ω} [LieGroup 𝓘(ℝ, E_G) n G]

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
/-- **The right trivialization `dR_{k⁻¹}` is `C^m` in coordinates**: `k ↦ dR_{k⁻¹} ∘ (coordinate change at k)`. -/
lemma contMDiffAt_rightTrivial_coord {m : ℕ∞ω} (hm : m + 1 ≤ n) (k₀ : G) :
    ContMDiffAt 𝓘(ℝ, E_G) 𝓘(ℝ, E_G →L[ℝ] E_G) m
      (fun k : G => (rightTrivial E_G k).comp (tangentCoordChange 𝓘(ℝ, E_G) k₀ k k)) k₀ := by
  have hf : ContMDiffAt (𝓘(ℝ, E_G).prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) n
      (Function.uncurry fun (k l : G) => l * k⁻¹) (k₀, id k₀) :=
    (contMDiff_snd.mul contMDiff_fst.inv).contMDiffAt
  have h := hf.mfderiv (fun k l => l * k⁻¹) id contMDiffAt_id hm
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [chart_source_mem_nhds E_G k₀] with k hk
  have hy : (fun x : G => x * x⁻¹) k ∈ (chartAt E_G ((fun x : G => x * x⁻¹) k₀)).source := by
    simp only [mul_inv_cancel]; exact mem_chart_source E_G 1
  rw [inTangentCoordinates_eq _ _ _ hk hy]
  have e : (tangentBundleCore 𝓘(ℝ, E_G) G).coordChange (achart E_G (id k * k⁻¹)) (achart E_G (id k₀ * k₀⁻¹))
      (id k * k⁻¹) = ContinuousLinearMap.id ℝ E_G := by
    simp only [id, mul_inv_cancel]
    exact ContinuousLinearMap.ext fun v => tangentCoordChange_self (mem_extChartAt_source 1)
  rw [e]
  rfl

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
/-- **The adjoint action `Ad_{k⁻¹}` is `C^m`** in `k`. -/
lemma contMDiffAt_adjointE_inv {m : ℕ∞ω} (hm : m + 1 ≤ n) (k₀ : G) :
    ContMDiffAt 𝓘(ℝ, E_G) 𝓘(ℝ, E_G →L[ℝ] E_G) m (fun k : G => adjointE 𝓘(ℝ, E_G) k⁻¹) k₀ := by
  have hf : ContMDiffAt (𝓘(ℝ, E_G).prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) n
      (Function.uncurry fun (k l : G) => conjMap k⁻¹ l) (k₀, (fun _ : G => (1 : G)) k₀) :=
    ((contMDiff_fst.inv.mul contMDiff_snd).mul contMDiff_fst.inv.inv).contMDiffAt
  have h := hf.mfderiv (fun k l => conjMap k⁻¹ l) (fun _ => 1) contMDiffAt_const hm
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun k => ?_)
  have hy : (fun x : G => conjMap x⁻¹ 1) k ∈ (chartAt E_G ((fun x : G => conjMap x⁻¹ 1) k₀)).source := by
    simp only [conjMap_one]; exact mem_chart_source E_G 1
  rw [inTangentCoordinates_eq (fun _ : G => (1 : G)) (fun x : G => conjMap x⁻¹ 1)
    (fun x : G => mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => conjMap x⁻¹ l) 1) (mem_chart_source E_G 1) hy]
  have e1 : (tangentBundleCore 𝓘(ℝ, E_G) G).coordChange (achart E_G (conjMap k⁻¹ 1))
      (achart E_G (conjMap k₀⁻¹ 1)) (conjMap k⁻¹ 1) = ContinuousLinearMap.id ℝ E_G := by
    simp only [conjMap_one]
    exact ContinuousLinearMap.ext fun v => tangentCoordChange_self (mem_extChartAt_source 1)
  have e2 : (tangentBundleCore 𝓘(ℝ, E_G) G).coordChange (achart E_G (1 : G)) (achart E_G (1 : G)) (1 : G) =
      ContinuousLinearMap.id ℝ E_G :=
    ContinuousLinearMap.ext fun v => tangentCoordChange_self (mem_extChartAt_source 1)
  rw [e1, e2]
  rfl

variable [IsManifold I 1 M]

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
/-- **The local form (36) is `C^m` in coordinates** when the potential is: `z ↦ ω^U_z ∘ (coordinate change at z)`
is `C^m` at `z₀` if `x ↦ A(x) ∘ (coordinate change at x)` is `C^m` at `z₀.1`. -/
lemma contMDiffAt_localForm_coord {m : ℕ∞ω} (hm : m + 1 ≤ n) {A : M → E →L[ℝ] E_G}
    {z₀ : M × G}
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E_G) m (fun x => (A x).comp (tangentCoordChange I z₀.1 x x)) z₀.1) :
    ContMDiffAt (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E × E_G →L[ℝ] E_G) m
      (fun z => (localForm A z).comp (tangentCoordChange (I.prod 𝓘(ℝ, E_G)) z₀ z z)) z₀ := by
  have h1 := hA.comp z₀ (contMDiffAt_fst (I := I) (J := 𝓘(ℝ, E_G)))
  have h2 := (contMDiffAt_rightTrivial_coord hm z₀.2).comp z₀ (contMDiffAt_snd (I := I) (J := 𝓘(ℝ, E_G)))
  have h3 := (contMDiffAt_adjointE_inv hm z₀.2).comp z₀ (contMDiffAt_snd (I := I) (J := 𝓘(ℝ, E_G)))
  have hsum := (h1.clm_comp (contMDiffAt_const (c := ContinuousLinearMap.fst ℝ E E_G))).add
    (h2.clm_comp (contMDiffAt_const (c := ContinuousLinearMap.snd ℝ E E_G)))
  refine (h3.clm_comp hsum).congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I.prod 𝓘(ℝ, E_G)) z₀] with z hz
  rw [tangentCoordChange_prod ⟨hz, mem_extChartAt_source z⟩]
  exact ContinuousLinearMap.ext fun v => rfl

variable (c : PrincipalCocycle M G) [ContinuousMul G] [IsManifold I (minSmoothness ℝ 3) M]

omit [IsManifold 𝓘(ℝ, E_G) 1 G] [LieGroup 𝓘(ℝ, E_G) n G] [IsManifold I 1 M] in
/-- **The connection form through any trivialization**: on the domain of `h_i`, `ω_p = ω^{U_i}_{h_i p} ∘ dh_i`. -/
theorem connForm_eq_of_mem {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    (i : c.ι) [Nonempty (c.piece i)] {p : c.total} (hp : p ∈ (c.localTriv i).source) :
    c.connForm I A p =
      (localForm (A i) (c.localTriv i p)).comp
        (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p) := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) :=
    fun i j => c.contMDiffOn_transition (hg i j)
  have := isManifold hT
  refine ContinuousLinearMap.ext fun v => ?_
  have hz : c.localTriv i p ∈ (c.localTriv i).target := (c.localTriv i).map_source hp
  have hLk : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p :=
    ((contMDiffOn_localTriv hT i _ hp).contMDiffAt ((c.localTriv i).open_source.mem_nhds hp)).mdifferentiableAt
      minSmoothness_three_ne_zero
  have hLi : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm (c.localTriv i p) :=
    ((contMDiffOn_localTriv_symm hT i _ hz).contMDiffAt
      ((c.localTriv i).open_target.mem_nhds hz)).mdifferentiableAt minSmoothness_three_ne_zero
  have hc := mfderiv_comp_apply _ hLi hLk v
  have hev : ((c.localTriv i).symm ∘ c.localTriv i) =ᶠ[𝓝 p] id :=
    Filter.eventually_of_mem ((c.localTriv i).open_source.mem_nhds hp) fun y hy => (c.localTriv i).left_inv hy
  rw [hev.mfderiv_eq, mfderiv_id] at hc
  have h := connForm_localTriv_symm hA hg i hz (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v)
  have key : ∀ q : c.total, q = p → ∀ w : TangentSpace (I.prod 𝓘(ℝ, E_G)) q, w = v →
      c.connForm I A q w = c.connForm I A p v := by
    rintro q rfl w rfl; rfl
  exact (key _ ((c.localTriv i).left_inv hp) _ hc.symm).symm.trans h

/-- **The connection form is `C^m`** in the charts of `P` (Theorem 10's connection is smooth): if `G` is a `C^n` Lie
group with `n ≥ 3`, the transition maps are `C^n`, and each local potential `A_i` is a `C^m` one-form on `U_i`
(written in the charts of `M`) with `m + 1 ≤ n`, then `p ↦ ω_p ∘ (tangent coordinate change from p₀ to p)` is `C^m`
at every `p₀`. -/
theorem connForm_contMDiffAt [IsManifold (I.prod 𝓘(ℝ, E_G)) 1 c.total] [IsManifold I n M]
    (hn : minSmoothness ℝ 3 ≤ n) {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hgn : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) n (c.g i j) (c.U i ⊓ c.U j))
    {m : ℕ∞ω} (hm : m + 1 ≤ n)
    (hAs : ∀ i, ∀ x₀ ∈ c.U i,
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E_G) m (fun x => (A i x).comp (tangentCoordChange I x₀ x x)) x₀)
    (p₀ : c.total) :
    ContMDiffAt (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E × E_G →L[ℝ] E_G) m
      (fun p => (c.connForm I A p).comp (tangentCoordChange (I.prod 𝓘(ℝ, E_G)) p₀ p p)) p₀ := by
  have hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j) :=
    fun i j => (hgn i j).of_le hn
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) n := fun i j => c.contMDiffOn_transition (hgn i j)
  have := isManifold hT
  set i := c.idx p₀
  have hp₀ : p₀ ∈ (c.localTriv i).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  have hL : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) n (c.localTriv i) p₀ :=
    (contMDiffOn_localTriv hT i _ hp₀).contMDiffAt ((c.localTriv i).open_source.mem_nhds hp₀)
  have hin := hL.mfderiv_const hm
  have hU : (c.localTriv i p₀).1 ∈ c.U i := by
    have := (c.localTriv i).map_source hp₀
    rw [localTriv_target] at this
    obtain ⟨q, hq⟩ := this
    rw [← hq]; exact q.1.2
  have hQ := (contMDiffAt_localForm_coord hm (hAs i _ hU)).comp p₀ (hL.of_le (le_self_add.trans hm))
  refine (hQ.clm_comp hin).congr_of_eventuallyEq ?_
  filter_upwards [(c.localTriv i).open_source.mem_nhds hp₀, chart_source_mem_nhds (ModelProd H E_G) p₀,
    hL.continuousAt.preimage_mem_nhds (chart_source_mem_nhds (ModelProd H E_G) (c.localTriv i p₀))]
    with p hp hpc hpz
  rw [c.connForm_eq_of_mem hA hg i hp, inTangentCoordinates_eq (I := I.prod 𝓘(ℝ, E_G)) (I' := I.prod 𝓘(ℝ, E_G))
    id (c.localTriv i) (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i)) (x₀ := p₀) (x := p) hpc hpz]
  refine ContinuousLinearMap.ext fun v => ?_
  change localForm (A i) (c.localTriv i p)
      (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p
        (tangentCoordChange (I.prod 𝓘(ℝ, E_G)) p₀ p p v)) =
    localForm (A i) (c.localTriv i p)
      (tangentCoordChange (I.prod 𝓘(ℝ, E_G)) (c.localTriv i p₀) (c.localTriv i p) (c.localTriv i p)
        (tangentCoordChange (I.prod 𝓘(ℝ, E_G)) (c.localTriv i p) (c.localTriv i p₀) (c.localTriv i p)
          (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p
            (tangentCoordChange (I.prod 𝓘(ℝ, E_G)) p₀ p p v))))
  have hs : c.localTriv i p ∈ (extChartAt (I.prod 𝓘(ℝ, E_G)) (c.localTriv i p)).source ∩
      (extChartAt (I.prod 𝓘(ℝ, E_G)) (c.localTriv i p₀)).source ∩
      (extChartAt (I.prod 𝓘(ℝ, E_G)) (c.localTriv i p)).source := by
    rw [extChartAt_source, extChartAt_source]
    exact ⟨⟨mem_chart_source _ _, hpz⟩, mem_chart_source _ _⟩
  exact congrArg (fun w : E × E_G => localForm (A i) (c.localTriv i p) w)
    ((tangentCoordChange_comp hs).trans (tangentCoordChange_self (mem_extChartAt_source _))).symm

/-- **The connection form is a `C^m` section of `Hom(TP, g)`** (Mathlib's hom bundle of the tangent bundle of `P`
and the trivial bundle with fibre the Lie algebra), under the hypotheses of `connForm_contMDiffAt`; for smooth data
(`n = m = ∞`) it is smooth. -/
theorem contMDiff_connForm [IsManifold (I.prod 𝓘(ℝ, E_G)) 1 c.total] [IsManifold I n M]
    (hn : minSmoothness ℝ 3 ≤ n) {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hgn : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) n (c.g i j) (c.U i ⊓ c.U j))
    {m : ℕ∞ω} (hm : m + 1 ≤ n)
    (hAs : ∀ i, ∀ x₀ ∈ c.U i,
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E_G) m (fun x => (A i x).comp (tangentCoordChange I x₀ x x)) x₀) :
    ContMDiff (I.prod 𝓘(ℝ, E_G)) ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E × E_G →L[ℝ] E_G)) m
      (fun p => (⟨p, c.connForm I A p⟩ : Bundle.TotalSpace (E × E_G →L[ℝ] E_G)
        (fun p : c.total => TangentSpace (I.prod 𝓘(ℝ, E_G)) p →L[ℝ] Bundle.Trivial c.total E_G p))) := by
  intro p₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, (c.connForm_contMDiffAt hn hA hgn hm hAs p₀).congr_of_eventuallyEq ?_⟩
  filter_upwards [chart_source_mem_nhds (ModelProd H E_G) p₀] with p hp
  have h1 : (trivializationAt E_G (Bundle.Trivial c.total E_G) p₀).continuousLinearMapAt ℝ p =
      ContinuousLinearMap.id ℝ E_G :=
    Bundle.Trivial.continuousLinearMapAt_trivialization ℝ c.total E_G p
  rw [ContinuousLinearMap.inCoordinates, h1, TangentBundle.symmL_trivializationAt_eq_core hp,
    ContinuousLinearMap.id_comp]

end PrincipalCocycle

end Lightlike.Gauge

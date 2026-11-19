import Mathlib.Topology.Gluing
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# A principal bundle glued from local trivializations (GC1, Theorem 10, attempt 2 at the principal bundle)

Svetlichny, Theorem 10 (p. 31) is stated on a principal `G`-bundle `P`. Here `P` is built directly from transition
data, without Mathlib's `FiberBundle`: an open cover `U_i` of `M` and transition maps `g_ij : U_i ∩ U_j → G` with
`g_ii = 1` and the cocycle condition `g_jk g_ij = g_ik` give the gluing of the spaces `U_i × G` along
`(x, h) ↦ (x, g_ij(x) h)` (`PrincipalCocycle.mkCore`, Mathlib's `TopCat.GlueData.MkCore`), and `P` is the glued space
(`PrincipalCocycle.total`) with the open embeddings `U_i × G → P` (`PrincipalCocycle.isOpenEmbedding_incl`).
-/

open Set TopologicalSpace CategoryTheory

open scoped ContDiff Manifold

universe u

namespace Lightlike.Gauge

/-- **Transition data of a principal `G`-bundle** over `M`: an open cover and transition maps with `g_ii = 1` and
the cocycle condition `g_jk g_ij = g_ik` on triple overlaps. -/
structure PrincipalCocycle (M G : Type u) [TopologicalSpace M] [TopologicalSpace G] [Group G] where
  /-- The index set of the cover. -/
  ι : Type u
  /-- The open sets of the cover. -/
  U : ι → Opens M
  /-- The transition maps. -/
  g : ι → ι → M → G
  cont : ∀ i j, ContinuousOn (g i j) (U i ⊓ U j)
  self : ∀ i x, g i i x = 1
  cocycle : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → g j k x * g i j x = g i k x

namespace PrincipalCocycle

variable {M G : Type u} [TopologicalSpace M] [TopologicalSpace G] [Group G] [ContinuousMul G]
  (c : PrincipalCocycle M G)

/-- The local piece `U_i × G`. -/
abbrev piece (i : c.ι) : Type u := (c.U i) × G

/-- The overlap `(U_i ∩ U_j) × G` inside `U_i × G`. -/
def overlap (i j : c.ι) : Opens (c.piece i) :=
  ⟨{p | (p.1 : M) ∈ c.U j}, (c.U j).isOpen.preimage (continuous_subtype_val.comp continuous_fst)⟩

/-- The transition `(x, h) ↦ (x, g_ij(x) h)` from the overlap in `U_i × G` to the overlap in `U_j × G`. -/
def trans (i j : c.ι) : c.overlap i j → c.overlap j i := fun p =>
  ⟨(⟨(p.1.1 : M), p.2⟩, c.g i j p.1.1 * p.1.2), (p.1.1).2⟩

lemma continuous_trans (i j : c.ι) : Continuous (c.trans i j) := by
  have hx : Continuous fun p : c.overlap i j => ((p.1.1 : M)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hmem : ∀ p : c.overlap i j, ((p.1.1 : M)) ∈ c.U i ⊓ c.U j := fun p => ⟨(p.1.1).2, p.2⟩
  have hg : Continuous fun p : c.overlap i j => c.g i j (p.1.1 : M) :=
    (c.cont i j).comp_continuous hx hmem
  refine Continuous.subtype_mk (Continuous.prodMk ?_ (hg.mul (continuous_snd.comp continuous_subtype_val))) _
  exact hx.subtype_mk _

/-- **The gluing data** of the pieces `U_i × G` along the transitions. -/
noncomputable def mkCore : TopCat.GlueData.MkCore.{u} where
  J := c.ι
  U i := TopCat.of (c.piece i)
  V i j := c.overlap i j
  t i j := TopCat.ofHom ⟨c.trans i j, c.continuous_trans i j⟩
  V_id i := by
    ext p
    simp only [overlap, Opens.coe_mk, Set.mem_ofPred_eq, Opens.coe_top, mem_univ, iff_true]
    exact (p.1).2
  t_id i := by
    funext p
    apply Subtype.ext
    show (c.trans i i p).1 = p.1
    refine Prod.ext rfl ?_
    show c.g i i _ * _ = _
    rw [c.self, one_mul]
  t_inter i j k p hp := hp
  cocycle i j k p hp := by
    show (c.trans j k ⟨(c.trans i j p).1, _⟩).1 = (c.trans i k ⟨p.1, hp⟩).1
    refine Prod.ext rfl ?_
    show c.g j k ((p.1.1 : M)) * (c.g i j (p.1.1 : M) * p.1.2) = c.g i k (p.1.1 : M) * p.1.2
    rw [← mul_assoc, c.cocycle i j k _ (p.1.1).2 p.2 hp]

/-- **The total space** `P`, glued from the pieces `U_i × G`. -/
noncomputable def total : Type u := (TopCat.GlueData.mk' c.mkCore).glued

noncomputable instance : TopologicalSpace c.total :=
  inferInstanceAs (TopologicalSpace (TopCat.GlueData.mk' c.mkCore).glued)

/-- The inclusion of a piece `U_i × G` into `P`. -/
noncomputable def incl (i : c.ι) : c.piece i → c.total := (TopCat.GlueData.mk' c.mkCore).ι i

/-- **The pieces are open in `P`**. -/
theorem isOpenEmbedding_incl (i : c.ι) : Topology.IsOpenEmbedding (c.incl i) :=
  (TopCat.GlueData.mk' c.mkCore).ι_isOpenEmbedding i

omit [ContinuousMul G] in
lemma rel_aux {i j : c.ι} {p : c.piece i} {q : c.piece j} (x : c.overlap i j) (hx1 : (x : c.piece i) = p)
    (hx2 : (c.trans i j x : c.piece j) = q) :
    ∃ h : (p.1 : M) ∈ c.U j, q = (⟨p.1.1, h⟩, c.g i j p.1 * p.2) := by
  subst hx1 hx2
  exact ⟨x.2, rfl⟩

/-- **When two points of the pieces agree in `P`**: `(x, h) ∈ U_i × G` and `q ∈ U_j × G` are the same point of `P`
exactly when `x ∈ U_j` and `q = (x, g_ij(x) h)`. -/
theorem incl_eq_iff {i j : c.ι} (p : c.piece i) (q : c.piece j) :
    c.incl i p = c.incl j q ↔ ∃ h : (p.1 : M) ∈ c.U j, q = (⟨p.1.1, h⟩, c.g i j p.1 * p.2) := by
  refine (TopCat.GlueData.ι_eq_iff_rel (TopCat.GlueData.mk' c.mkCore) i j p q).trans ?_
  constructor
  · rintro ⟨x, hx1, hx2⟩
    exact c.rel_aux x hx1 hx2
  · rintro ⟨h, rfl⟩
    exact ⟨(⟨p, h⟩ : c.overlap i j), rfl, rfl⟩

/-- A piece containing a point of `P`. -/
noncomputable def idx (p : c.total) : c.ι :=
  (TopCat.GlueData.ι_jointly_surjective (TopCat.GlueData.mk' c.mkCore) p).choose

/-- A point of the piece `c.idx p` over `p`. -/
noncomputable def pt (p : c.total) : c.piece (c.idx p) :=
  (TopCat.GlueData.ι_jointly_surjective (TopCat.GlueData.mk' c.mkCore) p).choose_spec.choose

lemma incl_pt (p : c.total) : c.incl (c.idx p) (c.pt p) = p :=
  (TopCat.GlueData.ι_jointly_surjective (TopCat.GlueData.mk' c.mkCore) p).choose_spec.choose_spec

instance (p : c.total) : Nonempty (c.piece (c.idx p)) := ⟨c.pt p⟩

/-- The inclusion `U_i × G → M × G`. -/
def pieceVal (i : c.ι) : c.piece i → M × G := Prod.map Subtype.val id

omit [ContinuousMul G] in
lemma isOpenEmbedding_pieceVal (i : c.ι) : Topology.IsOpenEmbedding (c.pieceVal i) :=
  (c.U i).2.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id

/-- **The local trivialization** `h_i : π⁻¹(U_i) → U_i × G ⊆ M × G` of `P`, as an open partial homeomorphism of `P`
into `M × G`. -/
noncomputable def localTriv (i : c.ι) [Nonempty (c.piece i)] : OpenPartialHomeomorph c.total (M × G) :=
  ((c.isOpenEmbedding_incl i).toOpenPartialHomeomorph (c.incl i)).symm.trans
    ((c.isOpenEmbedding_pieceVal i).toOpenPartialHomeomorph (c.pieceVal i))

section localTriv

variable {i : c.ι} [Nonempty (c.piece i)]

lemma localTriv_source : (c.localTriv i).source = range (c.incl i) := by
  simp [localTriv]

lemma localTriv_target : (c.localTriv i).target = range (c.pieceVal i) := by
  ext z
  simp only [localTriv, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    mem_inter_iff, mem_preimage, mem_univ, and_true]

lemma localTriv_apply (x : c.piece i) : c.localTriv i (c.incl i x) = c.pieceVal i x := by
  simp only [localTriv, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]

lemma localTriv_symm_apply (x : c.piece i) : (c.localTriv i).symm (c.pieceVal i x) = c.incl i x := by
  simp only [localTriv, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]

end localTriv

/-- The right action on a piece: `(x, h) · k = (x, h k)`. -/
def pieceAct {i : c.ι} (q : c.piece i) (k : G) : c.piece i := (q.1, q.2 * k)

/-- **The right action of `G` on `P`**: `h_i⁻¹(x, h) · k = h_i⁻¹(x, h k)`. It does not depend on the trivialization,
since the transition maps multiply on the left (`act_incl`). -/
noncomputable def act (p : c.total) (k : G) : c.total := c.incl (c.idx p) (c.pieceAct (c.pt p) k)

/-- The right action in any piece: `(x, h) · k = (x, h k)`. -/
theorem act_incl {i : c.ι} (q : c.piece i) (k : G) : c.act (c.incl i q) k = c.incl i (c.pieceAct q k) := by
  unfold act
  obtain ⟨h, hq⟩ := (c.incl_eq_iff q (c.pt (c.incl i q))).1 (c.incl_pt (c.incl i q)).symm
  rw [hq]
  symm
  refine (c.incl_eq_iff (c.pieceAct q k) _).2 ⟨h, ?_⟩
  simp only [pieceAct, mul_assoc]

lemma act_one (p : c.total) : c.act p 1 = p := by
  conv_lhs => rw [← c.incl_pt p]
  rw [act_incl, show c.pieceAct (c.pt p) 1 = c.pt p from Prod.ext rfl (mul_one _)]
  exact c.incl_pt p

lemma act_mem_source {i : c.ι} [Nonempty (c.piece i)] {p : c.total} (hp : p ∈ (c.localTriv i).source) (k : G) :
    c.act p k ∈ (c.localTriv i).source := by
  rw [localTriv_source] at hp ⊢
  obtain ⟨q, rfl⟩ := hp
  exact ⟨_, (c.act_incl q k).symm⟩

/-- **The right action in a trivialization**: `h_i(p · k) = (x, h k)` for `h_i(p) = (x, h)`. -/
lemma localTriv_act {i : c.ι} [Nonempty (c.piece i)] {p : c.total} (hp : p ∈ (c.localTriv i).source) (k : G) :
    c.localTriv i (c.act p k) = ((c.localTriv i p).1, (c.localTriv i p).2 * k) := by
  rw [localTriv_source] at hp
  obtain ⟨q, rfl⟩ := hp
  rw [act_incl, localTriv_apply, localTriv_apply]
  rfl

/-- **The chart transitions of `P` are the transition maps** `(x, h) ↦ (x, g_ij(x) h)`: on the domain of
`h_j ∘ h_i⁻¹`, the base point lies in `U_i ∩ U_j` and the map is left multiplication by `g_ij(x)` in the fibre. -/
theorem transition_eq {i j : c.ι} [Nonempty (c.piece i)] [Nonempty (c.piece j)] {z : M × G}
    (hz : z ∈ ((c.localTriv i).symm.trans (c.localTriv j)).source) :
    z.1 ∈ c.U i ∧ z.1 ∈ c.U j ∧ ((c.localTriv i).symm.trans (c.localTriv j)) z = (z.1, c.g i j z.1 * z.2) := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [localTriv_target] at hz1
  obtain ⟨x, rfl⟩ := hz1
  rw [mem_preimage, localTriv_symm_apply, localTriv_source] at hz2
  obtain ⟨q, hq⟩ := hz2
  obtain ⟨h, rfl⟩ := (c.incl_eq_iff x q).1 hq.symm
  refine ⟨x.1.2, h, ?_⟩
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, localTriv_symm_apply, ← hq, localTriv_apply]
  rfl

section Manifold

variable {H' : Type*} [TopologicalSpace H'] [ChartedSpace H' (M × G)]

/-- **The charted space structure on `P`**: the chart at `p` is a local trivialization followed by a chart of
`M × G`. -/
noncomputable instance : ChartedSpace H' c.total where
  atlas := range fun p => (c.localTriv (c.idx p)).trans (chartAt H' (c.localTriv (c.idx p) p))
  chartAt p := (c.localTriv (c.idx p)).trans (chartAt H' (c.localTriv (c.idx p) p))
  mem_chart_source p := by
    rw [OpenPartialHomeomorph.trans_source, localTriv_source]
    exact ⟨⟨c.pt p, c.incl_pt p⟩, mem_chart_source H' _⟩
  chart_mem_atlas p := ⟨p, rfl⟩

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {I' : ModelWithCorners ℝ E' H'} {n : ℕ∞ω}
  [IsManifold I' n (M × G)]

variable (I' n) in
omit [IsManifold I' n (M × G)] in
/-- The hypothesis that the transition maps `(x, h) ↦ (x, g_ij(x) h)` are `C^n` on `(U_i ∩ U_j) × G`. -/
def TransitionsSmooth : Prop :=
  ∀ i j, ContMDiffOn I' I' n (fun z : M × G => (z.1, c.g i j z.1 * z.2)) {z | z.1 ∈ c.U i ∧ z.1 ∈ c.U j}

variable {c}

omit [IsManifold I' n (M × G)] in
lemma contMDiffOn_symm_trans_localTriv (hT : c.TransitionsSmooth I' n) (i j : c.ι) [Nonempty (c.piece i)]
    [Nonempty (c.piece j)] :
    ContMDiffOn I' I' n ((c.localTriv i).symm.trans (c.localTriv j))
      ((c.localTriv i).symm.trans (c.localTriv j)).source :=
  ((hT i j).mono fun _ hz => ⟨(c.transition_eq hz).1, (c.transition_eq hz).2.1⟩).congr
    fun _ hz => (c.transition_eq hz).2.2

omit [IsManifold I' n (M × G)] in
lemma contMDiffOn_symm_trans_localTriv_symm (hT : c.TransitionsSmooth I' n) (i j : c.ι) [Nonempty (c.piece i)]
    [Nonempty (c.piece j)] :
    ContMDiffOn I' I' n ((c.localTriv i).symm.trans (c.localTriv j)).symm
      ((c.localTriv i).symm.trans (c.localTriv j)).target := by
  rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]
  exact contMDiffOn_symm_trans_localTriv hT j i

/-- **`P` is a `C^n` manifold** when the transition maps `(x, h) ↦ (x, g_ij(x) h)` are `C^n` on `(U_i ∩ U_j) × G`. -/
theorem isManifold (hT : c.TransitionsSmooth I' n) : IsManifold I' n c.total where
  compatible := by
    rintro _ _ ⟨p₁, rfl⟩ ⟨p₂, rfl⟩
    dsimp only
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc (c.localTriv (c.idx p₁)).symm]
    exact symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn (IsManifold.chart_mem_maximalAtlas _)
      (IsManifold.chart_mem_maximalAtlas _) (contMDiffOn_symm_trans_localTriv hT _ _)
      (contMDiffOn_symm_trans_localTriv_symm hT _ _)

/-- A local trivialization followed by a chart of `M × G` from the maximal atlas is a chart of `P` from the maximal
atlas. -/
theorem localTriv_trans_mem_maximalAtlas (hT : c.TransitionsSmooth I' n) (i : c.ι) [Nonempty (c.piece i)]
    {e : OpenPartialHomeomorph (M × G) H'} (he : e ∈ IsManifold.maximalAtlas I' n (M × G)) :
    (c.localTriv i).trans e ∈ IsManifold.maximalAtlas I' n c.total := by
  show _ ∈ (contDiffGroupoid n I').maximalAtlas c.total
  rw [mem_maximalAtlas_iff]
  rintro _ ⟨p, rfl⟩
  dsimp only
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc (c.localTriv i).symm]
    exact symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn he (IsManifold.chart_mem_maximalAtlas _)
      (contMDiffOn_symm_trans_localTriv hT _ _) (contMDiffOn_symm_trans_localTriv_symm hT _ _)
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc (c.localTriv (c.idx p)).symm]
    exact symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn (IsManifold.chart_mem_maximalAtlas _) he
      (contMDiffOn_symm_trans_localTriv hT _ _) (contMDiffOn_symm_trans_localTriv_symm hT _ _)

/-- **The local trivializations are `C^n`** on their sources. -/
theorem contMDiffOn_localTriv (hT : c.TransitionsSmooth I' n) (i : c.ι) [Nonempty (c.piece i)] :
    ContMDiffOn I' I' n (c.localTriv i) (c.localTriv i).source := by
  have := c.isManifold hT
  intro q hq
  have hc := IsManifold.chart_mem_maximalAtlas (I := I') (n := n) (c.localTriv i q)
  have h1 := contMDiffOn_of_mem_maximalAtlas (c.localTriv_trans_mem_maximalAtlas hT i hc)
  have h2 := contMDiffOn_symm_of_mem_maximalAtlas hc
  have h3 : ContMDiffOn I' I' n (c.localTriv i) ((c.localTriv i).trans (chartAt H' (c.localTriv i q))).source := by
    refine (h2.comp h1 fun y hy => ?_).congr fun y hy => ?_
    · have := ((c.localTriv i).trans (chartAt H' (c.localTriv i q))).map_source hy
      rw [OpenPartialHomeomorph.trans_target] at this
      exact this.1
    · rw [OpenPartialHomeomorph.trans_source] at hy
      exact ((chartAt H' _).left_inv hy.2).symm
  have hq' : q ∈ ((c.localTriv i).trans (chartAt H' (c.localTriv i q))).source := by
    rw [OpenPartialHomeomorph.trans_source]; exact ⟨hq, mem_chart_source H' _⟩
  exact ((h3 q hq').contMDiffAt (((c.localTriv i).trans _).open_source.mem_nhds hq')).contMDiffWithinAt

/-- **The inverse local trivializations are `C^n`** on their targets. -/
theorem contMDiffOn_localTriv_symm (hT : c.TransitionsSmooth I' n) (i : c.ι) [Nonempty (c.piece i)] :
    ContMDiffOn I' I' n (c.localTriv i).symm (c.localTriv i).target := by
  have := c.isManifold hT
  intro z hz
  have hc := IsManifold.chart_mem_maximalAtlas (I := I') (n := n) z
  have h1 := contMDiffOn_symm_of_mem_maximalAtlas (c.localTriv_trans_mem_maximalAtlas hT i hc)
  have h2 := contMDiffOn_of_mem_maximalAtlas hc
  have h3 : ContMDiffOn I' I' n (c.localTriv i).symm
      ((chartAt H' z).source ∩ chartAt H' z ⁻¹' ((c.localTriv i).trans (chartAt H' z)).target) := by
    refine (h1.comp (h2.mono inter_subset_left) fun y hy => hy.2).congr fun y hy => ?_
    show (c.localTriv i).symm y = (c.localTriv i).symm ((chartAt H' z).symm (chartAt H' z y))
    rw [(chartAt H' z).left_inv hy.1]
  have hz' : z ∈ (chartAt H' z).source ∩ chartAt H' z ⁻¹' ((c.localTriv i).trans (chartAt H' z)).target := by
    refine ⟨mem_chart_source H' z, ?_⟩
    rw [mem_preimage, OpenPartialHomeomorph.trans_target]
    refine ⟨(chartAt H' z).map_source (mem_chart_source H' z), ?_⟩
    rw [mem_preimage, (chartAt H' z).left_inv (mem_chart_source H' z)]
    exact hz
  exact ((h3 z hz').contMDiffAt (((chartAt H' z).isOpen_inter_preimage
    ((c.localTriv i).trans (chartAt H' z)).open_target).mem_nhds hz')).contMDiffWithinAt

end Manifold

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace ℝ E_G]
  [ChartedSpace E_G G] {n : ℕ∞ω} [LieGroup 𝓘(ℝ, E_G) n G]

omit [ContinuousMul G] in
/-- The transition maps are `C^n` when the `g_ij` are. -/
lemma contMDiffOn_transition {i j : c.ι}
    (hg : ContMDiffOn I 𝓘(ℝ, E_G) n (c.g i j) (c.U i ⊓ c.U j)) :
    ContMDiffOn (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) n (fun z : M × G => (z.1, c.g i j z.1 * z.2))
      {z | z.1 ∈ c.U i ∧ z.1 ∈ c.U j} :=
  contMDiffOn_fst.prodMk ((hg.comp contMDiffOn_fst fun _ hz => ⟨hz.1, hz.2⟩).mul contMDiffOn_snd)

/-- **The glued principal bundle is a `C^n` manifold**, modelled on `M × G`, when `M` is one and the transition maps
`g_ij` are `C^n`. -/
theorem isManifold_of_contMDiffOn [IsManifold I n M]
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) n (c.g i j) (c.U i ⊓ c.U j)) :
    IsManifold (I.prod 𝓘(ℝ, E_G)) n c.total :=
  isManifold fun i j => c.contMDiffOn_transition (hg i j)

end Smooth

end PrincipalCocycle

end Lightlike.Gauge

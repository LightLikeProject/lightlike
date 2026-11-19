import Lightlike.Gauge.Connection.PrincipalSmooth
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The horizontal distribution of the connection (Svetlichny §4.6, pp. 26-29)

Svetlichny defines a connection on a bundle `π : E → M` as a choice at each `p` of a subspace `H_p ⊂ T_p E`
complementary to the vertical subspace `V_p = ker dπ_p` (p. 27); on a principal bundle the vertical projection is
represented by the connection form `ω_p : T_p P → g` through `V_p ≃ g`, `L ↦ L_p` (eq. (34), p. 29), and the
connection is invariant if `H_{p·g} = dR_g(H_p)` (p. 29).

On the glued principal bundle `P` of `PrincipalGlue.lean` with the connection form `connForm` of
`PrincipalConnection.lean`: the projection `π` (`proj`), the vertical subspaces `V_p = ker dπ_p` (`vertical`), and the
horizontal subspaces `H_p = ker ω_p` (`horizontal`). They are complementary (`isCompl_vertical_horizontal`), the
vertical subspace consists of the fundamental vectors `d(p ·)_1 L` (`mem_vertical_iff`), the vertical projection is
`π^v_p = d(p ·)_1 ∘ ω_p` (`vertProj`, `vertProj_mem_vertical`, `sub_vertProj_mem_horizontal`), the horizontal
distribution is invariant, `H_{p·k} = dR_k(H_p)` (`horizontal_act`), and it is smooth in the source's sense: for a
`C^m` vector field `X` the horizontal part `π^h X = X - π^v X` is a `C^m` vector field (`contMDiffAt_horizontalPart`,
for `C^n` data with `m + 1 ≤ n`, from the smoothness of the fundamental vector fields, `contMDiffAt_fundamental`).
-/

open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

universe u

namespace Lightlike.Gauge

namespace PrincipalCocycle

section Top

variable {M G : Type u} [TopologicalSpace M] [TopologicalSpace G] [Group G] [ContinuousMul G]
  (c : PrincipalCocycle M G)

/-- **The projection** `π : P → M`. -/
noncomputable def proj (p : c.total) : M := ((c.pt p).1 : M)

lemma proj_incl {i : c.ι} (q : c.piece i) : c.proj (c.incl i q) = q.1 := by
  obtain ⟨h, hq⟩ := (c.incl_eq_iff q (c.pt (c.incl i q))).1 (c.incl_pt (c.incl i q)).symm
  unfold proj
  rw [hq]

lemma proj_localTriv {i : c.ι} [Nonempty (c.piece i)] {p : c.total} (hp : p ∈ (c.localTriv i).source) :
    c.proj p = (c.localTriv i p).1 := by
  rw [localTriv_source] at hp
  obtain ⟨q, rfl⟩ := hp
  rw [proj_incl, localTriv_apply]
  rfl

/-- The right action preserves the fibres: `π(p · k) = π(p)`. -/
lemma proj_act (p : c.total) (k : G) : c.proj (c.act p k) = c.proj p := by
  show c.proj (c.incl (c.idx p) (c.pieceAct (c.pt p) k)) = c.proj p
  rw [proj_incl]
  conv_rhs => rw [← c.incl_pt p]
  rw [proj_incl]
  rfl

lemma act_mul (p : c.total) (k k' : G) : c.act (c.act p k) k' = c.act p (k * k') := by
  show c.act (c.incl (c.idx p) (c.pieceAct (c.pt p) k)) k' = c.incl (c.idx p) (c.pieceAct (c.pt p) (k * k'))
  rw [act_incl]
  exact congrArg (c.incl (c.idx p)) (Prod.ext rfl (mul_assoc _ _ _))

lemma act_eq_localTriv_symm {i : c.ι} [Nonempty (c.piece i)] {p : c.total} (hp : p ∈ (c.localTriv i).source) :
    c.act p = (c.localTriv i).symm ∘ fun l : G => ((c.localTriv i p).1, (c.localTriv i p).2 * l) := by
  funext l
  change c.act p l = (c.localTriv i).symm ((c.localTriv i p).1, (c.localTriv i p).2 * l)
  rw [← c.localTriv_act hp l, (c.localTriv i).left_inv (c.act_mem_source hp l)]

end Top

variable {M G : Type u} [TopologicalSpace M] [TopologicalSpace G] [Group G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
  {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace ℝ E_G] [ChartedSpace E_G G]
  [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G]

omit [TopologicalSpace M] in
lemma adjointE_inv_eq_zero {h : G} {u : E_G} (hu : adjointE 𝓘(ℝ, E_G) h⁻¹ u = 0) : u = 0 := by
  have h1 := adjointE_mul_apply h h⁻¹ u
  rw [hu, map_zero, mul_inv_cancel] at h1
  simp only [adjointE, adjoint_one] at h1
  exact h1.symm

omit [TopologicalSpace M] in
lemma rightTrivial_eq_zero {h : G} {w : E_G} (hw : rightTrivial E_G h w = 0) : w = 0 := by
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E_G)) h (mdifferentiableAt_mul_right' h (h * h⁻¹))
    (mdifferentiableAt_mul_right' h⁻¹ h)
  have hf : (fun l : G => l * h) ∘ (fun l : G => l * h⁻¹) = id := by
    funext l; simp
  rw [hf, mfderiv_id] at hc
  have h0 : mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * h⁻¹) h w = 0 := hw
  have h2 := ContinuousLinearMap.ext_iff.1 hc w
  have h3 : ((mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun x : G => x * h) (h * h⁻¹)).comp
      (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun x : G => x * h⁻¹) h)) w = 0 := by
    show mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun x : G => x * h) (h * h⁻¹)
      (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun x : G => x * h⁻¹) h w) = 0
    rw [h0, map_zero]
  exact h2.trans h3

variable (c : PrincipalCocycle M G) [ContinuousMul G] [IsManifold I (minSmoothness ℝ 3) M]

section Diff

variable {c}
variable (hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3))
include hT

lemma mdifferentiableAt_localTriv {i : c.ι} [Nonempty (c.piece i)] {p : c.total}
    (hp : p ∈ (c.localTriv i).source) :
    MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p := by
  have := isManifold hT
  exact ((contMDiffOn_localTriv hT i _ hp).contMDiffAt ((c.localTriv i).open_source.mem_nhds hp)).mdifferentiableAt
    minSmoothness_three_ne_zero

lemma mdifferentiableAt_localTriv_symm {i : c.ι} [Nonempty (c.piece i)] {z : M × G}
    (hz : z ∈ (c.localTriv i).target) :
    MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm z := by
  have := isManifold hT
  exact ((contMDiffOn_localTriv_symm hT i _ hz).contMDiffAt
    ((c.localTriv i).open_target.mem_nhds hz)).mdifferentiableAt minSmoothness_three_ne_zero

lemma mfderiv_localTriv_symm_apply {i : c.ι} [Nonempty (c.piece i)] {p : c.total}
    (hp : p ∈ (c.localTriv i).source) (v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :
    mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm (c.localTriv i p)
      (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v) = v := by
  have hz : c.localTriv i p ∈ (c.localTriv i).target := (c.localTriv i).map_source hp
  have hc := mfderiv_comp_apply _ (mdifferentiableAt_localTriv_symm hT hz) (mdifferentiableAt_localTriv hT hp) v
  have hev : ((c.localTriv i).symm ∘ c.localTriv i) =ᶠ[𝓝 p] id :=
    Filter.eventually_of_mem ((c.localTriv i).open_source.mem_nhds hp) fun y hy => (c.localTriv i).left_inv hy
  rw [hev.mfderiv_eq, mfderiv_id] at hc
  exact hc.symm

lemma mdifferentiableAt_proj (p : c.total) :
    MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) I c.proj p := by
  have hp : p ∈ (c.localTriv (c.idx p)).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  have hev : c.proj =ᶠ[𝓝 p] Prod.fst ∘ c.localTriv (c.idx p) :=
    Filter.eventually_of_mem ((c.localTriv (c.idx p)).open_source.mem_nhds hp) fun y hy => c.proj_localTriv hy
  exact (mdifferentiableAt_fst.comp p (mdifferentiableAt_localTriv hT hp)).congr_of_eventuallyEq hev

/-- `dπ` in a trivialization: the base component of `dh_i`. -/
lemma mfderiv_proj_apply {i : c.ι} [Nonempty (c.piece i)] {p : c.total} (hp : p ∈ (c.localTriv i).source)
    (v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :
    mfderiv (I.prod 𝓘(ℝ, E_G)) I c.proj p v =
      (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v).1 := by
  have hev : c.proj =ᶠ[𝓝 p] Prod.fst ∘ c.localTriv i :=
    Filter.eventually_of_mem ((c.localTriv i).open_source.mem_nhds hp) fun y hy => c.proj_localTriv hy
  have hc := mfderiv_comp_apply (g := Prod.fst) (f := c.localTriv i) p
    (mdifferentiableAt_fst (I := I) (I' := 𝓘(ℝ, E_G))) (mdifferentiableAt_localTriv hT hp) v
  rw [mfderiv_fst] at hc
  rw [hev.mfderiv_eq]
  exact hc

lemma mdifferentiableAt_act_left (p : c.total) (l : G) :
    MDifferentiableAt 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) l := by
  have hp : p ∈ (c.localTriv (c.idx p)).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  rw [c.act_eq_localTriv_symm hp]
  have hz : ((c.localTriv (c.idx p) p).1, (c.localTriv (c.idx p) p).2 * l) ∈ (c.localTriv (c.idx p)).target := by
    rw [← c.localTriv_act hp l]; exact (c.localTriv (c.idx p)).map_source (c.act_mem_source hp l)
  exact (mdifferentiableAt_localTriv_symm hT hz).comp l
    (mdifferentiableAt_const.prodMk (mdifferentiableAt_mul_left' (I := 𝓘(ℝ, E_G)) _ l))

lemma mdifferentiableAt_act_right (k : G) (q : c.total) :
    MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k) q := by
  set i := c.idx q
  have hq : q ∈ (c.localTriv i).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  set R : M × G → M × G := fun z => (z.1, z.2 * k)
  have hz : R (c.localTriv i q) ∈ (c.localTriv i).target := by
    rw [show R (c.localTriv i q) = c.localTriv i (c.act q k) from (c.localTriv_act hq k).symm]
    exact (c.localTriv i).map_source (c.act_mem_source hq k)
  have hR : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) R (c.localTriv i q) :=
    mdifferentiableAt_fst.prodMk ((mdifferentiableAt_mul_right' k _).comp _ mdifferentiableAt_snd)
  have hev : (fun q => c.act q k) =ᶠ[𝓝 q] (c.localTriv i).symm ∘ (R ∘ c.localTriv i) :=
    Filter.eventually_of_mem ((c.localTriv i).open_source.mem_nhds hq) fun y hy => by
      show c.act y k = (c.localTriv i).symm ((c.localTriv i y).1, (c.localTriv i y).2 * k)
      rw [← c.localTriv_act hy k, (c.localTriv i).left_inv (c.act_mem_source hy k)]
  exact ((mdifferentiableAt_localTriv_symm hT hz).comp q (hR.comp q (mdifferentiableAt_localTriv hT hq))).congr_of_eventuallyEq
    hev

end Diff

variable (I) in
/-- **The vertical subspace** `V_p = ker dπ_p` (Svetlichny §4.6, p. 26). -/
noncomputable def vertical (p : c.total) : Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :=
  LinearMap.ker (mfderiv (I.prod 𝓘(ℝ, E_G)) I c.proj p).toLinearMap

variable (I) in
/-- **The horizontal subspace** `H_p = ker ω_p` of the connection form. -/
noncomputable def horizontal (A : c.ι → M → E →L[ℝ] E_G) (p : c.total) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :=
  LinearMap.ker (c.connForm I A p).toLinearMap

variable {c}

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [IsManifold I (minSmoothness ℝ 3) M] in
lemma mem_vertical {p : c.total} {v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p} :
    v ∈ c.vertical I p ↔ mfderiv (I.prod 𝓘(ℝ, E_G)) I c.proj p v = 0 := LinearMap.mem_ker

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [IsManifold I (minSmoothness ℝ 3) M] in
lemma mem_horizontal {A : c.ι → M → E →L[ℝ] E_G} {p : c.total} {v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p} :
    v ∈ c.horizontal I A p ↔ c.connForm I A p v = 0 := LinearMap.mem_ker

/-- The fundamental vectors are vertical: `dπ_p(d(p ·)_1 L) = 0`. -/
lemma mfderiv_proj_fundamental (hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3)) (p : c.total)
    (L : E_G) :
    mfderiv (I.prod 𝓘(ℝ, E_G)) I c.proj p (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L) = 0 := by
  have hc := mfderiv_comp_apply (g := c.proj) (f := c.act p) 1 (mdifferentiableAt_proj hT (c.act p 1))
    (mdifferentiableAt_act_left hT p 1) L
  have hconst : c.proj ∘ c.act p = fun _ => c.proj p := by
    funext l; exact c.proj_act p l
  rw [hconst, mfderiv_const] at hc
  have key : ∀ q : c.total, q = c.act p 1 →
      mfderiv (I.prod 𝓘(ℝ, E_G)) I c.proj q (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L) =
        mfderiv (I.prod 𝓘(ℝ, E_G)) I c.proj (c.act p 1) (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L) := by
    rintro q rfl; rfl
  exact (key p (c.act_one p).symm).trans hc.symm

/-- `ω_p(d(p ·)_1 L) = L` at the point `p` itself (eq. (34), with `p · 1 = p`). -/
lemma connForm_fundamental {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j)) (p : c.total) (L : E_G) :
    c.connForm I A p (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L) = L := by
  have h := c.connForm_vertical hA hg p L
  have key : ∀ q : c.total, q = c.act p 1 →
      c.connForm I A q (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L) =
        c.connForm I A (c.act p 1) (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L) := by
    rintro q rfl; rfl
  exact (key p (c.act_one p).symm).trans h

/-- **The vertical and horizontal subspaces are complementary**, `T_p P = V_p ⊕ H_p`: the kernel of the connection
form is a connection in Svetlichny's sense (p. 27), with the vertical projection `v ↦ d(p ·)_1 (ω_p v)` (p. 29). -/
theorem isCompl_vertical_horizontal {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j)) (p : c.total) :
    IsCompl (c.vertical I p) (c.horizontal I A p) := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) :=
    fun i j => c.contMDiffOn_transition (hg i j)
  set i := c.idx p
  have hp : p ∈ (c.localTriv i).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  refine isCompl_iff.2 ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    have h1 : (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v).1 = 0 :=
      (mfderiv_proj_apply hT hp v).symm.trans (mem_vertical.1 hv1)
    have h2 : localForm (A i) (c.localTriv i p)
        (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v) = 0 := mem_horizontal.1 hv2
    erw [localForm_apply] at h2
    rw [h1, map_zero, zero_add] at h2
    have h3 := rightTrivial_eq_zero (adjointE_inv_eq_zero h2)
    have hu : mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v = 0 := Prod.ext h1 h3
    have h4 := mfderiv_localTriv_symm_apply hT hp v
    rw [hu, map_zero] at h4
    exact h4.symm
  · refine eq_top_iff.2 fun v _ => ?_
    let u : TangentSpace (I.prod 𝓘(ℝ, E_G)) p :=
      mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 (c.connForm I A p v)
    refine Submodule.mem_sup.2 ⟨u, ?_, v - u, ?_, add_sub_cancel _ _⟩
    · exact mem_vertical.2 (mfderiv_proj_fundamental hT p _)
    · refine mem_horizontal.2 ?_
      rw [map_sub]
      have : c.connForm I A p u = c.connForm I A p v := connForm_fundamental hA hg p _
      rw [this, sub_self]

/-- **The vertical subspace consists of the fundamental vectors** `d(p ·)_1 L`, `L ∈ g` (Svetlichny, p. 29). -/
theorem mem_vertical_iff {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j)) (p : c.total)
    (v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :
    v ∈ c.vertical I p ↔ ∃ L : E_G, mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L = v := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) :=
    fun i j => c.contMDiffOn_transition (hg i j)
  constructor
  · intro hv
    refine ⟨c.connForm I A p v, ?_⟩
    have hd := (isCompl_vertical_horizontal hA hg p).inf_eq_bot
    let w : TangentSpace (I.prod 𝓘(ℝ, E_G)) p :=
      mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 (c.connForm I A p v)
    have hw : v - w ∈ c.vertical I p ⊓ c.horizontal I A p := by
      refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hv (mem_vertical.2 (mfderiv_proj_fundamental hT p _)),
        mem_horizontal.2 ?_⟩
      rw [map_sub]
      have : c.connForm I A p w = c.connForm I A p v := connForm_fundamental hA hg p _
      rw [this, sub_self]
    rw [hd, Submodule.mem_bot, sub_eq_zero] at hw
    exact hw.symm
  · rintro ⟨L, rfl⟩
    exact mem_vertical.2 (mfderiv_proj_fundamental hT p L)

/-- **The horizontal distribution is invariant**, `H_{p·k} = dR_k(H_p)` (Svetlichny, p. 29). -/
theorem horizontal_act {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j)) (p : c.total) (k : G) :
    c.horizontal I A (c.act p k) =
      (c.horizontal I A p).map (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k) p).toLinearMap := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) :=
    fun i j => c.contMDiffOn_transition (hg i j)
  have hpk : c.act (c.act p k) k⁻¹ = p := by rw [act_mul, mul_inv_cancel, act_one]
  ext w
  constructor
  · intro hw
    set v := mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k⁻¹) (c.act p k) w
    have h0 := c.connForm_act hA hg (c.act p k) k⁻¹ w
    rw [mem_horizontal.1 hw, map_zero] at h0
    have key : ∀ q : c.total, q = p → ∀ x : TangentSpace (I.prod 𝓘(ℝ, E_G)) q, c.connForm I A q x = 0 →
        ∀ y : TangentSpace (I.prod 𝓘(ℝ, E_G)) p, y = x → c.connForm I A p y = 0 := by
      rintro q rfl x hx y rfl; exact hx
    refine Submodule.mem_map.2 ⟨v, mem_horizontal.2 (key _ hpk _ h0 v rfl), ?_⟩
    have hc := mfderiv_comp_apply (g := fun q => c.act q k) (f := fun q => c.act q k⁻¹) (c.act p k)
      (mdifferentiableAt_act_right hT k _) (mdifferentiableAt_act_right hT k⁻¹ _) w
    have hid : (fun q => c.act q k) ∘ (fun q => c.act q k⁻¹) = id := by
      funext q; simp only [Function.comp_apply, act_mul, inv_mul_cancel, act_one, id]
    rw [hid, mfderiv_id] at hc
    have key2 : ∀ q : c.total, q = c.act (c.act p k) k⁻¹ →
        mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k) q v =
          mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k) (c.act (c.act p k) k⁻¹) v := by
      rintro q rfl; rfl
    exact (key2 p hpk.symm).trans hc.symm
  · rintro ⟨v, hv, rfl⟩
    refine mem_horizontal.2 ?_
    change c.connForm I A (c.act p k) (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k) p v) = 0
    rw [c.connForm_act hA hg p k v, mem_horizontal.1 hv, map_zero]

variable (I c) in
/-- **The vertical projection** `π^v_p = d(p ·)_1 ∘ ω_p`, through `V_p ≃ g` (Svetlichny, p. 29). -/
noncomputable def vertProj (A : c.ι → M → E →L[ℝ] E_G) (p : c.total) :
    TangentSpace (I.prod 𝓘(ℝ, E_G)) p →L[ℝ] TangentSpace (I.prod 𝓘(ℝ, E_G)) p :=
  (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1).comp (c.connForm I A p)

/-- The vertical projection lands in `V_p`. -/
lemma vertProj_mem_vertical (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    (A : c.ι → M → E →L[ℝ] E_G) (p : c.total) (v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :
    c.vertProj I A p v ∈ c.vertical I p :=
  mem_vertical.2 (mfderiv_proj_fundamental (fun i j => c.contMDiffOn_transition (hg i j)) p _)

/-- `v - π^v v` is horizontal: `π^h = 1 - π^v` projects onto `H_p`. -/
lemma sub_vertProj_mem_horizontal {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j)) (p : c.total)
    (v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :
    v - c.vertProj I A p v ∈ c.horizontal I A p := by
  refine mem_horizontal.2 ?_
  rw [map_sub]
  have : c.connForm I A p (c.vertProj I A p v) = c.connForm I A p v := connForm_fundamental hA hg p _
  rw [this, sub_self]

section Smooth

variable [IsManifold 𝓘(ℝ, E_G) 1 G] {n : ℕ∞ω} [LieGroup 𝓘(ℝ, E_G) n G] [IsManifold I 1 M]
  [IsManifold (I.prod 𝓘(ℝ, E_G)) 1 c.total]

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [IsManifold I (minSmoothness ℝ 3) M] [IsManifold 𝓘(ℝ, E_G) 1 G]
  [IsManifold I 1 M] [IsManifold (I.prod 𝓘(ℝ, E_G)) 1 c.total] in
/-- The right action `(p, k) ↦ p · k` is `C^n` near `(p₀, 1)`. -/
lemma contMDiffAt_act_uncurry [IsManifold I n M] (hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) n) (p₀ : c.total) :
    ContMDiffAt ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) n
      (Function.uncurry fun (q : c.total) (k : G) => c.act q k) (p₀, 1) := by
  have := isManifold hT
  set i := c.idx p₀
  have hp : p₀ ∈ (c.localTriv i).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  set Y : c.total × G → M × G := fun x => ((c.localTriv i x.1).1, (c.localTriv i x.1).2 * x.2) with hY
  have hz : Y (p₀, 1) ∈ (c.localTriv i).target := by
    rw [show Y (p₀, 1) = c.localTriv i (c.act p₀ 1) from (c.localTriv_act hp 1).symm]
    exact (c.localTriv i).map_source (c.act_mem_source hp 1)
  have hL : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) n (c.localTriv i) p₀ :=
    (contMDiffOn_localTriv hT i _ hp).contMDiffAt ((c.localTriv i).open_source.mem_nhds hp)
  have hLs : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) n (c.localTriv i).symm (Y (p₀, 1)) :=
    (contMDiffOn_localTriv_symm hT i _ hz).contMDiffAt ((c.localTriv i).open_target.mem_nhds hz)
  have hL1 : ContMDiffAt ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) n
      (fun x : c.total × G => c.localTriv i x.1) (p₀, 1) :=
    hL.comp (p₀, 1) contMDiffAt_fst
  have hYs : ContMDiffAt ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) n Y (p₀, 1) :=
    (contMDiffAt_fst.comp (p₀, 1) hL1).prodMk ((contMDiffAt_snd.comp (p₀, 1) hL1).mul contMDiffAt_snd)
  refine (hLs.comp (p₀, 1) hYs).congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_fst.preimage_mem_nhds ((c.localTriv i).open_source.mem_nhds hp)] with x hx
  show c.act x.1 x.2 = (c.localTriv i).symm ((c.localTriv i x.1).1, (c.localTriv i x.1).2 * x.2)
  rw [← c.localTriv_act hx x.2, (c.localTriv i).left_inv (c.act_mem_source hx x.2)]

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [IsManifold I (minSmoothness ℝ 3) M] [IsManifold I 1 M] in
/-- **The fundamental vector fields are `C^m`**: for a `C^m` map `L : P → g`, `p ↦ d(p ·)_1 (L p)` is a `C^m` vector
field on `P`, when the transition maps and `G` are `C^n` with `m + 1 ≤ n`. -/
lemma contMDiffAt_fundamental [IsManifold I n M] (hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) n) {m : ℕ∞ω}
    (hm : m + 1 ≤ n) {L : c.total → E_G} {p₀ : c.total}
    (hL : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) m L p₀) :
    ContMDiffAt (I.prod 𝓘(ℝ, E_G)) ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E × E_G)) m
      (fun p => (⟨p, mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 (L p)⟩ :
        TangentBundle (I.prod 𝓘(ℝ, E_G)) c.total)) p₀ := by
  have h1 := (contMDiffAt_act_uncurry hT p₀).mfderiv (fun q k => c.act q k) (fun _ => (1 : G))
    contMDiffAt_const hm
  have hv : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) (𝓘(ℝ, E_G).prod 𝓘(ℝ, E_G)) m
      (fun p => (⟨(1 : G), L p⟩ : TangentBundle 𝓘(ℝ, E_G) G)) p₀ := by
    refine Bundle.contMDiffAt_totalSpace.2 ⟨contMDiffAt_const,
      hL.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)⟩
    exact tangentCoordChange_self (mem_extChartAt_source (1 : G))
  have hb : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) m (fun q => c.act q 1) p₀ := by
    simp only [act_one]; exact contMDiffAt_id
  have h := ContMDiffAt.clm_apply_of_inCoordinates (F₁ := E_G) (E₁ := (TangentSpace 𝓘(ℝ, E_G) : G → Type _))
    (F₂ := E × E_G) (E₂ := (TangentSpace (I.prod 𝓘(ℝ, E_G)) : c.total → Type _)) (b₁ := fun _ => (1 : G))
    (b₂ := fun q => c.act q 1) (ϕ := fun q => mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act q) 1) (v := L) (m₀ := p₀)
    h1 hv hb
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  have k2 : ∀ q : c.total, q = c.act p 1 →
      (⟨q, mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 (L p)⟩ : TangentBundle (I.prod 𝓘(ℝ, E_G)) c.total) =
        ⟨c.act p 1, mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 (L p)⟩ := by
    rintro q rfl; rfl
  exact k2 p (c.act_one p).symm

/-- **The horizontal distribution is smooth** (Svetlichny, p. 27): for a `C^m` vector field `X` on `P`, the vertical
part `π^v X` and the horizontal part `π^h X = X - π^v X` are `C^m` vector fields, under the hypotheses of
`contMDiff_connForm`. -/
theorem contMDiffAt_horizontalPart [IsManifold I n M] (hn : minSmoothness ℝ 3 ≤ n) {A : c.ι → M → E →L[ℝ] E_G}
    (hA : c.IsCompatible I A) (hgn : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) n (c.g i j) (c.U i ⊓ c.U j))
    {m : ℕ∞ω} (hm : m + 1 ≤ n)
    (hAs : ∀ i, ∀ x₀ ∈ c.U i,
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E_G) m (fun x => (A i x).comp (tangentCoordChange I x₀ x x)) x₀)
    {X : (p : c.total) → TangentSpace (I.prod 𝓘(ℝ, E_G)) p} {p₀ : c.total}
    (hX : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E × E_G)) m
      (fun p => (⟨p, X p⟩ : TangentBundle (I.prod 𝓘(ℝ, E_G)) c.total)) p₀) :
    ContMDiffAt (I.prod 𝓘(ℝ, E_G)) ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E × E_G)) m
        (fun p => (⟨p, c.vertProj I A p (X p)⟩ : TangentBundle (I.prod 𝓘(ℝ, E_G)) c.total)) p₀ ∧
      ContMDiffAt (I.prod 𝓘(ℝ, E_G)) ((I.prod 𝓘(ℝ, E_G)).prod 𝓘(ℝ, E × E_G)) m
        (fun p => (⟨p, X p - c.vertProj I A p (X p)⟩ : TangentBundle (I.prod 𝓘(ℝ, E_G)) c.total)) p₀ := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) n := fun i j => c.contMDiffOn_transition (hgn i j)
  have hω := c.contMDiff_connForm hn hA hgn hm hAs p₀
  have h1 := ContMDiffAt.clm_bundle_apply hω hX
  have h2 : ContMDiffAt (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) m (fun p => c.connForm I A p (X p)) p₀ :=
    (Bundle.contMDiffAt_totalSpace.1 h1).2
  have hv := contMDiffAt_fundamental hT hm h2
  exact ⟨hv, hX.sub_section hv⟩

end Smooth

end PrincipalCocycle

end Lightlike.Gauge

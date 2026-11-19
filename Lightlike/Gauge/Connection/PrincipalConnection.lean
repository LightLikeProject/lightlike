import Lightlike.Gauge.Connection.PrincipalGlue
import Lightlike.Gauge.LieConnection.LieGroup

/-!
# The connection form on a glued principal bundle (Svetlichny, Theorem 10)

`P` is the principal `G`-bundle glued from the pieces `U_i × G` along `(x, h) ↦ (x, g_ij(x) h)`
(`PrincipalGlue.lean`). In a trivialization, Svetlichny eq. (36) writes an invariant connection form as
`ω_(x,h)(ξ, L) = h⁻¹ (A_U(ξ) + L) h`, with `T_h G` identified with the Lie algebra by `dR_{h⁻¹}`; here this is
`localForm`, `ω_(x,h)(ξ, w) = Ad_{h⁻¹}(A(x) ξ + dR_{h⁻¹} w)`. The local potentials transform by eq. (38),
`A_j = Ad_{g_ij} A_i - dg_ij g_ij⁻¹` (`IsCompatible`). Under (38) the local forms agree through the derivative of the
transition maps (eq. (37), `localForm_transition`), so they glue to a form `connForm` on the tangent spaces of `P`
whose representative in every trivialization is the given `A_i` (`connForm_localTriv_symm`), and it is the only such
form (`connForm_unique`): Theorem 10 (p. 31).
-/

open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

universe u

namespace Lightlike.Gauge

namespace PrincipalCocycle

variable {M G : Type u} [TopologicalSpace M] [TopologicalSpace G] [Group G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
  {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace ℝ E_G] [ChartedSpace E_G G]
  [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G]

variable (E_G) in
/-- `dR_{k⁻¹}` at `k`: the derivative at `k` of the right translation by `k⁻¹`, which carries `T_k G` to the Lie
algebra `T_1 G`. -/
noncomputable def rightTrivial (k : G) : E_G →L[ℝ] E_G :=
  mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * k⁻¹) k

/-- **The local connection form** on `M × G` of a potential `A` (Svetlichny eq. (36)):
`ω_(x,h)(ξ, w) = Ad_{h⁻¹}(A(x) ξ + dR_{h⁻¹} w)`. -/
noncomputable def localForm (A : M → E →L[ℝ] E_G) (z : M × G) : E × E_G →L[ℝ] E_G :=
  (adjointE 𝓘(ℝ, E_G) z.2⁻¹).comp ((A z.1).comp (ContinuousLinearMap.fst ℝ E E_G) +
    (rightTrivial E_G z.2).comp (ContinuousLinearMap.snd ℝ E E_G))

/-- `dg g⁻¹`: the right Maurer–Cartan form of `g : M → G` at `x`, as a Lie-algebra valued one-form. -/
noncomputable def rightMC (g : M → G) (x : M) : E →L[ℝ] E_G :=
  (rightTrivial E_G (g x)).comp (mfderiv I 𝓘(ℝ, E_G) g x)

omit [TopologicalSpace M] [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
lemma localForm_apply (A : M → E →L[ℝ] E_G) (z : M × G) (v : E × E_G) :
    localForm A z v = adjointE 𝓘(ℝ, E_G) z.2⁻¹ (A z.1 v.1 + rightTrivial E_G z.2 v.2) := rfl

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
lemma rightMC_apply (g : M → G) (x : M) (ξ : E) :
    rightMC I g x ξ = rightTrivial E_G (g x) (mfderiv I 𝓘(ℝ, E_G) g x ξ) := rfl

variable {I}

lemma mdifferentiableAt_mul_right' (a b : G) : MDifferentiableAt 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (· * a) b :=
  (contMDiff_mul_right (I := 𝓘(ℝ, E_G)) (n := minSmoothness ℝ 3)).contMDiffAt.mdifferentiableAt
    minSmoothness_three_ne_zero

/-- `dR_{(gh)⁻¹} ∘ dR_h = dR_{g⁻¹}` at `g`. -/
lemma rightTrivial_mul_right (g h : G) (u : E_G) :
    rightTrivial E_G (g * h) (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * h) g u) = rightTrivial E_G g u := by
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E_G)) g (mdifferentiableAt_mul_right' (g * h)⁻¹ (g * h))
    (mdifferentiableAt_mul_right' h g)
  have hf : (fun l : G => l * (g * h)⁻¹) ∘ (fun l : G => l * h) = fun l : G => l * g⁻¹ := by
    funext l; simp only [Function.comp_apply]; group
  rw [hf] at hc
  simp only [rightTrivial, hc]
  rfl

/-- `dR_{(gh)⁻¹} ∘ dL_g = Ad_g ∘ dR_{h⁻¹}` at `h`. -/
lemma rightTrivial_mul_left (g h : G) (w : E_G) :
    rightTrivial E_G (g * h) (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => g * l) h w) =
      adjointE 𝓘(ℝ, E_G) g (rightTrivial E_G h w) := by
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E_G)) h (mdifferentiableAt_mul_right' (g * h)⁻¹ (g * h))
    (mdifferentiableAt_mul_left' (I := 𝓘(ℝ, E_G)) g h)
  have hc' := mfderiv_comp (I' := 𝓘(ℝ, E_G)) h
    (mdifferentiableAt_conjMap (I := 𝓘(ℝ, E_G)) g (h * h⁻¹)) (mdifferentiableAt_mul_right' h⁻¹ h)
  have hf : (fun l : G => l * (g * h)⁻¹) ∘ (fun l : G => g * l) = conjMap g ∘ fun l : G => l * h⁻¹ := by
    funext l; simp only [Function.comp_apply, conjMap]; group
  rw [hf, hc'] at hc
  have key : ∀ y : G, y = h * h⁻¹ →
      mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * (g * h)⁻¹) (g * h)
          (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => g * l) h w) =
        mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (conjMap g) y (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * h⁻¹) h w) := by
    rintro y rfl
    exact (ContinuousLinearMap.ext_iff.1 hc w).symm
  exact key 1 (mul_inv_cancel h).symm

lemma adjointE_mul_apply (a b : G) (u : E_G) :
    adjointE 𝓘(ℝ, E_G) a (adjointE 𝓘(ℝ, E_G) b u) = adjointE 𝓘(ℝ, E_G) (a * b) u := by
  simp only [adjointE, adjoint_mul]
  rfl

variable (c : PrincipalCocycle M G) [ContinuousMul G]

variable (I) in
/-- **The transformation law (38) of the local potentials**: on `U_i ∩ U_j`,
`A_j = Ad_{g_ij} A_i - dg_ij g_ij⁻¹`. -/
def IsCompatible (A : c.ι → M → E →L[ℝ] E_G) : Prop :=
  ∀ i j x, x ∈ c.U i → x ∈ c.U j →
    A j x = (adjointE 𝓘(ℝ, E_G) (c.g i j x)).comp (A i x) - rightMC I (c.g i j) x

omit [ContinuousMul G] in
/-- The derivative of the transition map `(x, h) ↦ (x, g_ij(x) h)`: `(ξ, w) ↦ (ξ, dR_h dg_ij ξ + dL_{g_ij} w)`. -/
lemma mfderiv_transition_apply {i j : c.ι} (hg : ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    {z : M × G} (hz : z.1 ∈ c.U i ⊓ c.U j) (v : E × E_G) :
    mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun z : M × G => (z.1, c.g i j z.1 * z.2)) z v =
      (v.1, mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * z.2) (c.g i j z.1)
          (mfderiv I 𝓘(ℝ, E_G) (c.g i j) z.1 v.1) +
        mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => c.g i j z.1 * l) z.2 v.2) := by
  have hgx : MDifferentiableAt I 𝓘(ℝ, E_G) (c.g i j) z.1 :=
    ((hg.contMDiffAt ((c.U i ⊓ c.U j).isOpen.mem_nhds hz))).mdifferentiableAt minSmoothness_three_ne_zero
  have h1 : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) (fun z : M × G => c.g i j z.1) z :=
    hgx.comp z mdifferentiableAt_fst
  have hpair : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (𝓘(ℝ, E_G).prod 𝓘(ℝ, E_G))
      (fun z : M × G => (c.g i j z.1, z.2)) z := h1.prodMk mdifferentiableAt_snd
  have hmul : MDifferentiableAt (𝓘(ℝ, E_G).prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) (fun p : G × G => p.1 * p.2)
      (c.g i j z.1, z.2) :=
    (contMDiff_mul (I := 𝓘(ℝ, E_G)) (n := minSmoothness ℝ 3)).contMDiffAt.mdifferentiableAt
      minSmoothness_three_ne_zero
  have h2 : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) (fun z : M × G => c.g i j z.1 * z.2) z :=
    hmul.comp z hpair
  have hc2 : mfderiv (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) (fun z : M × G => c.g i j z.1) z v =
      mfderiv I 𝓘(ℝ, E_G) (c.g i j) z.1 v.1 := by
    have := mfderiv_comp_apply (g := c.g i j) (f := Prod.fst) (x := z) hgx
      (mdifferentiableAt_fst (I := I) (I' := 𝓘(ℝ, E_G))) v
    rw [mfderiv_fst] at this
    exact this
  rw [mfderiv_prodMk mdifferentiableAt_fst h2]
  refine Prod.ext ?_ ?_
  · change mfderiv (I.prod 𝓘(ℝ, E_G)) I Prod.fst z v = v.1
    rw [mfderiv_fst]; rfl
  have hc := mfderiv_comp_apply (g := fun p : G × G => p.1 * p.2) (f := fun z : M × G => (c.g i j z.1, z.2))
    (x := z) hmul hpair v
  change mfderiv _ _ ((fun p : G × G => p.1 * p.2) ∘ fun z : M × G => (c.g i j z.1, z.2)) z v = _
  rw [hc, mfderiv_prod_eq_add_apply hmul, mfderiv_prodMk h1 mdifferentiableAt_snd]
  change mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * z.2) (c.g i j z.1)
      (mfderiv (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) (fun z : M × G => c.g i j z.1) z v) +
    mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => c.g i j z.1 * l) z.2
      (mfderiv (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) Prod.snd z v) = _
  rw [hc2, mfderiv_snd]
  rfl

variable {c}

omit [ContinuousMul G] in
/-- **The local forms agree through the transition maps** (Svetlichny eq. (37), from (38)):
`ω^{U_j}_{ψ(z)} ∘ dψ_z = ω^{U_i}_z` for `ψ(x, h) = (x, g_ij(x) h)` on `(U_i ∩ U_j) × G`. -/
theorem localForm_transition {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A) {i j : c.ι}
    (hg : ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    {z : M × G} (hzi : z.1 ∈ c.U i) (hzj : z.1 ∈ c.U j) (v : E × E_G) :
    localForm (A j) (z.1, c.g i j z.1 * z.2)
        (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun z : M × G => (z.1, c.g i j z.1 * z.2)) z v) =
      localForm (A i) z v := by
  rw [c.mfderiv_transition_apply hg ⟨hzi, hzj⟩]
  erw [localForm_apply, localForm_apply]
  dsimp only
  rw [hA i j z.1 hzi hzj, sub_apply, ContinuousLinearMap.comp_apply, rightMC_apply]
  erw [map_add (rightTrivial E_G (c.g i j z.1 * z.2)), rightTrivial_mul_right, rightTrivial_mul_left]
  have e : adjointE 𝓘(ℝ, E_G) (c.g i j z.1) ((A i z.1) v.1) -
        rightTrivial E_G (c.g i j z.1) ((mfderiv I 𝓘(ℝ, E_G) (c.g i j) z.1) v.1) +
      (rightTrivial E_G (c.g i j z.1) ((mfderiv I 𝓘(ℝ, E_G) (c.g i j) z.1) v.1) +
        adjointE 𝓘(ℝ, E_G) (c.g i j z.1) (rightTrivial E_G z.2 v.2)) =
      adjointE 𝓘(ℝ, E_G) (c.g i j z.1) ((A i z.1) v.1 + rightTrivial E_G z.2 v.2) := by
    rw [map_add]; abel
  rw [e, adjointE_mul_apply]
  congr 2
  group

section Glue

variable [IsManifold I (minSmoothness ℝ 3) M]

variable (I) in
/-- **The connection form on `P`**: at `p`, the local form of the trivialization `h_k` chosen at `p`, pulled back by
`dh_k`. -/
noncomputable def connForm (c : PrincipalCocycle M G) (A : c.ι → M → E →L[ℝ] E_G) (p : c.total) :
    TangentSpace (I.prod 𝓘(ℝ, E_G)) p →L[ℝ] E_G :=
  (localForm (A (c.idx p)) (c.localTriv (c.idx p) p)).comp
    (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv (c.idx p)) p)

/-- **Theorem 10 (p. 31), existence**: if the local potentials `A_i` satisfy (38) and the transition maps are `C³`,
the connection form `connForm` on `P` has the representative `ω^{U_i}` of eq. (36) in every trivialization `h_i`:
`ω_{h_i⁻¹ z} ∘ d(h_i⁻¹)_z = ω^{U_i}_z`. -/
theorem connForm_localTriv_symm {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    (i : c.ι) [Nonempty (c.piece i)] {z : M × G} (hz : z ∈ (c.localTriv i).target) (v : E × E_G) :
    c.connForm I A ((c.localTriv i).symm z)
        (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm z v) =
      localForm (A i) z v := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) := fun i j => c.contMDiffOn_transition (hg i j)
  have := isManifold hT
  set k := c.idx ((c.localTriv i).symm z)
  have hp : (c.localTriv i).symm z ∈ (c.localTriv k).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  have hzf : z ∈ ((c.localTriv i).symm.trans (c.localTriv k)).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]; exact ⟨hz, hp⟩
  have htr := c.transition_eq hzf
  have hLk : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv k) ((c.localTriv i).symm z) :=
    ((contMDiffOn_localTriv hT k _ hp).contMDiffAt ((c.localTriv k).open_source.mem_nhds hp)).mdifferentiableAt
      minSmoothness_three_ne_zero
  have hLi : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm z :=
    ((contMDiffOn_localTriv_symm hT i _ hz).contMDiffAt
      ((c.localTriv i).open_target.mem_nhds hz)).mdifferentiableAt minSmoothness_three_ne_zero
  have hc := mfderiv_comp_apply _ hLk hLi v
  have hev : (c.localTriv k ∘ (c.localTriv i).symm) =ᶠ[𝓝 z] fun z : M × G => (z.1, c.g i k z.1 * z.2) :=
    Filter.eventually_of_mem (((c.localTriv i).symm.trans (c.localTriv k)).open_source.mem_nhds hzf)
      fun y hy => (c.transition_eq hy).2.2
  rw [hev.mfderiv_eq] at hc
  have hpt : c.localTriv k ((c.localTriv i).symm z) = (z.1, c.g i k z.1 * z.2) := htr.2.2
  calc c.connForm I A ((c.localTriv i).symm z)
        (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm z v)
      = localForm (A k) (c.localTriv k ((c.localTriv i).symm z))
          (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun z : M × G => (z.1, c.g i k z.1 * z.2)) z v) :=
        congrArg (fun w : E × E_G => localForm (A k) (c.localTriv k ((c.localTriv i).symm z)) w) hc.symm
    _ = localForm (A k) (z.1, c.g i k z.1 * z.2)
          (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun z : M × G => (z.1, c.g i k z.1 * z.2)) z v) := by
        rw [hpt]
    _ = localForm (A i) z v := localForm_transition hA (hg i k) htr.1 htr.2.1 v

/-- **Theorem 10 (p. 31), uniqueness**: a form on `P` with the representatives `ω^{U_i}` in every trivialization is
`connForm`. -/
theorem connForm_unique {A : c.ι → M → E →L[ℝ] E_G}
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    (σ : (p : c.total) → TangentSpace (I.prod 𝓘(ℝ, E_G)) p →L[ℝ] E_G)
    (hσ : ∀ (i : c.ι) [Nonempty (c.piece i)], ∀ z ∈ (c.localTriv i).target, ∀ v : E × E_G,
      σ ((c.localTriv i).symm z) (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm z v) =
        localForm (A i) z v) :
    σ = c.connForm I A := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) := fun i j => c.contMDiffOn_transition (hg i j)
  have := isManifold hT
  funext p
  ext v
  set k := c.idx p
  have hp : p ∈ (c.localTriv k).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  have hz : c.localTriv k p ∈ (c.localTriv k).target := (c.localTriv k).map_source hp
  have hLk : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv k) p :=
    ((contMDiffOn_localTriv hT k _ hp).contMDiffAt ((c.localTriv k).open_source.mem_nhds hp)).mdifferentiableAt
      minSmoothness_three_ne_zero
  have hLi : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv k).symm (c.localTriv k p) :=
    ((contMDiffOn_localTriv_symm hT k _ hz).contMDiffAt
      ((c.localTriv k).open_target.mem_nhds hz)).mdifferentiableAt minSmoothness_three_ne_zero
  have hc := mfderiv_comp_apply _ hLi hLk v
  have hev : ((c.localTriv k).symm ∘ c.localTriv k) =ᶠ[𝓝 p] id :=
    Filter.eventually_of_mem ((c.localTriv k).open_source.mem_nhds hp) fun y hy => (c.localTriv k).left_inv hy
  rw [hev.mfderiv_eq, mfderiv_id] at hc
  have h := hσ k (c.localTriv k p) hz (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv k) p v)
  have key : ∀ q : c.total, q = p → ∀ w : TangentSpace (I.prod 𝓘(ℝ, E_G)) q, w = v → σ q w = σ p v := by
    rintro q rfl w rfl; rfl
  exact (key _ ((c.localTriv k).left_inv hp) _ hc.symm).symm.trans h

omit [ContinuousMul G] [IsManifold I (minSmoothness ℝ 3) M] in
/-- The derivative of the right action `(x, h) ↦ (x, h k)` on `M × G`. -/
lemma mfderiv_actR_apply (k : G) (z : M × G) (u : E × E_G) :
    mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun z : M × G => (z.1, z.2 * k)) z u =
      (u.1, mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * k) z.2 u.2) := by
  have hk : MDifferentiableAt 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * k) z.2 := mdifferentiableAt_mul_right' _ _
  have h1 : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) 𝓘(ℝ, E_G) (fun z : M × G => z.2 * k) z :=
    hk.comp z mdifferentiableAt_snd
  rw [mfderiv_prodMk mdifferentiableAt_fst h1]
  refine Prod.ext ?_ ?_
  · change mfderiv (I.prod 𝓘(ℝ, E_G)) I Prod.fst z u = u.1
    rw [mfderiv_fst]; rfl
  have hc := mfderiv_comp_apply (g := fun l : G => l * k) (f := Prod.snd) (x := z) hk
    (mdifferentiableAt_snd (I := I) (I' := 𝓘(ℝ, E_G))) u
  rw [mfderiv_snd] at hc
  exact hc

omit [ContinuousMul G] [IsManifold I (minSmoothness ℝ 3) M] in
/-- **The local forms are equivariant** (Svetlichny eq. (35) in a trivialization):
`ω^U_{(x, hk)}(ξ, dR_k w) = Ad_{k⁻¹} ω^U_{(x, h)}(ξ, w)`. -/
lemma localForm_act (A : M → E →L[ℝ] E_G) (k : G) (z : M × G) (u : E × E_G) :
    localForm A (z.1, z.2 * k)
        (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun z : M × G => (z.1, z.2 * k)) z u) =
      adjointE 𝓘(ℝ, E_G) k⁻¹ (localForm A z u) := by
  rw [mfderiv_actR_apply]
  erw [localForm_apply, localForm_apply]
  dsimp only
  erw [rightTrivial_mul_right, adjointE_mul_apply]
  congr 2
  group

/-- **The connection form is invariant** (Svetlichny eq. (35)): `ω_{p·k}(dR_k v) = Ad_{k⁻¹} ω_p(v)`. -/
theorem connForm_act {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    (p : c.total) (k : G) (v : TangentSpace (I.prod 𝓘(ℝ, E_G)) p) :
    c.connForm I A (c.act p k) (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k) p v) =
      adjointE 𝓘(ℝ, E_G) k⁻¹ (c.connForm I A p v) := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) :=
    fun i j => c.contMDiffOn_transition (hg i j)
  have := isManifold hT
  set i := c.idx p
  have hp : p ∈ (c.localTriv i).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  set R : M × G → M × G := fun z => (z.1, z.2 * k) with hRdef
  have hpk := c.act_mem_source hp k
  have hz : R (c.localTriv i p) ∈ (c.localTriv i).target := by
    rw [show R (c.localTriv i p) = c.localTriv i (c.act p k) from (c.localTriv_act hp k).symm]
    exact (c.localTriv i).map_source hpk
  have hLp : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p :=
    ((contMDiffOn_localTriv hT i _ hp).contMDiffAt ((c.localTriv i).open_source.mem_nhds hp)).mdifferentiableAt
      minSmoothness_three_ne_zero
  have hLs : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm
      (R (c.localTriv i p)) :=
    ((contMDiffOn_localTriv_symm hT i _ hz).contMDiffAt
      ((c.localTriv i).open_target.mem_nhds hz)).mdifferentiableAt minSmoothness_three_ne_zero
  have hR : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) R (c.localTriv i p) :=
    mdifferentiableAt_fst.prodMk ((mdifferentiableAt_mul_right' k _).comp _ mdifferentiableAt_snd)
  have hev : (fun q => c.act q k) =ᶠ[𝓝 p] (c.localTriv i).symm ∘ (R ∘ c.localTriv i) :=
    Filter.eventually_of_mem ((c.localTriv i).open_source.mem_nhds hp) fun q hq => by
      show c.act q k = (c.localTriv i).symm ((c.localTriv i q).1, (c.localTriv i q).2 * k)
      rw [← c.localTriv_act hq k, (c.localTriv i).left_inv (c.act_mem_source hq k)]
  have hd : mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (fun q => c.act q k) p v =
      mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm (R (c.localTriv i p))
        (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) R (c.localTriv i p)
          (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v)) := by
    rw [hev.mfderiv_eq]
    have c1 := mfderiv_comp_apply (g := (c.localTriv i).symm) (f := R ∘ c.localTriv i) p hLs (hR.comp p hLp) v
    have c2 := mfderiv_comp_apply (g := R) (f := c.localTriv i) p hR hLp v
    rw [c2] at c1
    exact c1
  have hpt : c.act p k = (c.localTriv i).symm (R (c.localTriv i p)) := by
    show c.act p k = (c.localTriv i).symm ((c.localTriv i p).1, (c.localTriv i p).2 * k)
    rw [← c.localTriv_act hp k, (c.localTriv i).left_inv hpk]
  have key : ∀ q : c.total, q = (c.localTriv i).symm (R (c.localTriv i p)) →
      ∀ w : TangentSpace (I.prod 𝓘(ℝ, E_G)) q,
        w = mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm (R (c.localTriv i p))
          (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) R (c.localTriv i p)
            (mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i) p v)) →
        c.connForm I A q w = adjointE 𝓘(ℝ, E_G) k⁻¹ (c.connForm I A p v) := by
    rintro q rfl w rfl
    exact (connForm_localTriv_symm hA hg i hz _).trans (localForm_act (A i) k (c.localTriv i p) _)
  exact key _ hpt _ hd

/-- **The connection form reproduces the Lie algebra on vertical vectors** (Svetlichny eq. (34)): for the
fundamental vector `d(p ·)_1 L` of `L ∈ g`, `ω_p(d(p ·)_1 L) = L` (at `p · 1 = p`, `act_one`). -/
theorem connForm_vertical {A : c.ι → M → E →L[ℝ] E_G} (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    (p : c.total) (L : E_G) :
    c.connForm I A (c.act p 1) (mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) (c.act p) 1 L) = L := by
  have hT : c.TransitionsSmooth (I.prod 𝓘(ℝ, E_G)) (minSmoothness ℝ 3) :=
    fun i j => c.contMDiffOn_transition (hg i j)
  have := isManifold hT
  set i := c.idx p
  have hp : p ∈ (c.localTriv i).source := by
    rw [localTriv_source]; exact ⟨c.pt _, c.incl_pt _⟩
  set z := c.localTriv i p
  set Y : G → M × G := fun l => (z.1, z.2 * l) with hYdef
  have hY : MDifferentiableAt 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) Y 1 :=
    mdifferentiableAt_const.prodMk (mdifferentiableAt_mul_left' (I := 𝓘(ℝ, E_G)) z.2 1)
  have hz : Y 1 ∈ (c.localTriv i).target := by
    rw [hYdef]; dsimp only
    rw [← c.localTriv_act hp 1]; exact (c.localTriv i).map_source (c.act_mem_source hp 1)
  have hLs : MDifferentiableAt (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm (Y 1) :=
    ((contMDiffOn_localTriv_symm hT i _ hz).contMDiffAt
      ((c.localTriv i).open_target.mem_nhds hz)).mdifferentiableAt minSmoothness_three_ne_zero
  have hact : c.act p = (c.localTriv i).symm ∘ Y := by
    funext l
    change c.act p l = (c.localTriv i).symm (z.1, z.2 * l)
    rw [← c.localTriv_act hp l, (c.localTriv i).left_inv (c.act_mem_source hp l)]
  have hdY : mfderiv 𝓘(ℝ, E_G) (I.prod 𝓘(ℝ, E_G)) Y 1 L =
      (0, mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => z.2 * l) 1 L) := by
    rw [hYdef, mfderiv_prodMk mdifferentiableAt_const (mdifferentiableAt_mul_left' (I := 𝓘(ℝ, E_G)) z.2 1),
      mfderiv_const]
    rfl
  have key : ∀ q : c.total, q = (c.localTriv i).symm (Y 1) →
      ∀ w : TangentSpace (I.prod 𝓘(ℝ, E_G)) q,
        w = mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm (Y 1)
          (0, mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => z.2 * l) 1 L) → c.connForm I A q w = L := by
    rintro q rfl w rfl
    rw [connForm_localTriv_symm hA hg i hz]
    erw [localForm_apply]
    dsimp only [hYdef]
    rw [map_zero, zero_add]
    erw [rightTrivial_mul_left, adjointE_mul_apply]
    have h1 : rightTrivial E_G (1 : G) L = L := by
      have : (fun l : G => l * (1 : G)⁻¹) = id := by funext l; simp
      unfold rightTrivial
      erw [this, mfderiv_id]
      rfl
    rw [h1, show (z.2 * 1)⁻¹ * z.2 = 1 by group]
    simp only [adjointE, adjoint_one]
    rfl
  refine key _ (congrFun hact 1) _ ?_
  rw [hact]
  exact (mfderiv_comp_apply (g := (c.localTriv i).symm) (f := Y) 1 hLs hY L).trans
    (congrArg (fun w : E × E_G => mfderiv (I.prod 𝓘(ℝ, E_G)) (I.prod 𝓘(ℝ, E_G)) (c.localTriv i).symm (Y 1) w) hdY)

end Glue

end PrincipalCocycle

end Lightlike.Gauge

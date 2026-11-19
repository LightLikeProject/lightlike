import Lightlike.Gauge.Connection.PrincipalConnection
import Lightlike.Gauge.Connection.BundleConnection
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The associated vector bundle and its induced connection (Svetlichny pp. 22 and 31, eq. (39))

For a principal `G`-bundle `P` and a left action `ρ` of `G` on `F`, Svetlichny's associated bundle `P ×_ρ F` is the
orbit space of `P × F` under `(p, f) ↦ (p · g⁻¹, g · f)`, and by Theorem 7 (p. 22) it is the bundle with fibre `F`,
group action `ρ` and the cocycle of `P`. For a representation `ρ` on a vector space, an invariant connection `ω` on
`P` induces a linear connection on `P ×_ρ F` whose vertical projection in a trivialization is
`π^v_(x,f)(ξ, y) = y + r(A(x)(ξ)) f` (eq. (39), p. 31), `r` the representation of `g` induced by `ρ`.

Here, for the glued principal bundle with a cover of `M` and a `C³` representation `ρ : G →* (V →L V)` on a normed
space `V`: the associated vector bundle is Mathlib's vector bundle of the core with transition maps `ρ(g_ij)`
(`assocCore`, the form of Theorem 7), `C^n` when `ρ` and the `g_ij` are (`assocCore_isContMDiff`); `r = dρ_1`
(`lieRep`) satisfies `r(Ad_g X) = ρ(g) r(X) ρ(g)⁻¹` (`lieRep_adjointE`) and `r(dR_{k⁻¹} Y) = dρ_k(Y) ρ(k)⁻¹`
(`lieRep_rightTrivial`), so the local potentials `r ∘ A_i` satisfy the vector-bundle form of (38) for the coordinate
changes `ρ(g_ij)`, and Theorem 10 for the vector bundle gives the induced covariant derivative, whose
representative in the trivialization over `U_i` is `d + r(A_i)`, i.e. (39) (`exists_assocCov`), unique on
differentiable sections (`assocCov_unique`).
-/

open Set Filter Bundle
open scoped ContDiff Manifold Topology

universe u

namespace Lightlike.Gauge

namespace PrincipalCocycle

variable {M G : Type u} [TopologicalSpace M] [TopologicalSpace G] [Group G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
  {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace ℝ E_G] [ChartedSpace E_G G]
  [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Core

variable (c : PrincipalCocycle M G) [ContinuousMul G]

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
/-- **The associated vector bundle** `P ×_ρ V` of a representation `ρ` (Svetlichny, Theorem 7, p. 22: the bundle
with fibre `V`, group action `ρ` and the cocycle of `P`), as a vector bundle core with the transition maps
`ρ(g_ij)` on the cover `U_i`. -/
noncomputable def assocCore (hcov : ∀ x, ∃ i, x ∈ c.U i) (ρ : G →* (V →L[ℝ] V)) (hρ : Continuous ρ) :
    VectorBundleCore ℝ M V c.ι where
  baseSet i := c.U i
  isOpen_baseSet i := (c.U i).isOpen
  indexAt x := (hcov x).choose
  mem_baseSet_at x := (hcov x).choose_spec
  coordChange i j x := ρ (c.g i j x)
  coordChange_self i x _ v := by rw [c.self, map_one]; rfl
  continuousOn_coordChange i j := hρ.comp_continuousOn (c.cont i j)
  coordChange_comp i j k x hx v := by
    rw [← mul_apply_eq_comp, ← map_mul, c.cocycle i j k x hx.1.1 hx.1.2 hx.2]

variable {c}

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [ContinuousMul G] in
/-- The associated bundle is `C^n` when `ρ` and the transition maps are. -/
theorem assocCore_isContMDiff {hcov : ∀ x, ∃ i, x ∈ c.U i} {ρ : G →* (V →L[ℝ] V)} {n : ℕ∞ω}
    (hρ : ContMDiff 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) n ρ)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) n (c.g i j) (c.U i ⊓ c.U j)) :
    (c.assocCore hcov ρ hρ.continuous).IsContMDiff I n :=
  ⟨fun i j => hρ.comp_contMDiffOn (hg i j)⟩

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
/-- The trivializations of the core belong to the atlas of the associated bundle. -/
instance memTrivializationAtlas_assoc (hcov : ∀ x, ∃ i, x ∈ c.U i) (ρ : G →* (V →L[ℝ] V)) (hρ : Continuous ρ)
    (i : c.ι) : MemTrivializationAtlas ((c.assocCore hcov ρ hρ).localTriv i) :=
  ⟨⟨i, rfl⟩⟩

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [ContinuousMul G] in
instance isTopologicalAddGroup_assocFiber {ι : Type*} (Z : VectorBundleCore ℝ M V ι) (x : M) :
    IsTopologicalAddGroup (Z.Fiber x) :=
  inferInstanceAs (IsTopologicalAddGroup V)

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [ContinuousMul G] in
instance continuousSMul_assocFiber {ι : Type*} (Z : VectorBundleCore ℝ M V ι) (x : M) :
    ContinuousSMul ℝ (Z.Fiber x) :=
  inferInstanceAs (ContinuousSMul ℝ V)

end Core

/-- **The representation of the Lie algebra** induced by `ρ`: `r = dρ_1`. -/
noncomputable def lieRep (ρ : G →* (V →L[ℝ] V)) : E_G →L[ℝ] (V →L[ℝ] V) :=
  mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ 1

/-- `r(Ad_g X) = ρ(g) r(X) ρ(g)⁻¹`, from `ρ(g k g⁻¹) = ρ(g) ρ(k) ρ(g⁻¹)`. -/
lemma lieRep_adjointE {ρ : G →* (V →L[ℝ] V)} (hρ : ∀ k, MDifferentiableAt 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ k)
    (g : G) (X : E_G) :
    lieRep ρ (adjointE 𝓘(ℝ, E_G) g X) = ρ g * lieRep ρ X * ρ g⁻¹ := by
  set Φ := ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V) (ρ g) (ρ g⁻¹)
  have hf : ⇑ρ ∘ conjMap g = ⇑Φ ∘ ⇑ρ := by
    funext k
    simp only [Function.comp_apply, conjMap, map_mul, Φ, ContinuousLinearMap.mulLeftRight_apply]
  have h1 := mfderiv_comp_apply (g := ⇑ρ) (f := conjMap g) 1 (hρ _) (mdifferentiableAt_conjMap g 1) X
  have h2 := mfderiv_comp_apply (g := ⇑Φ) (f := ⇑ρ) 1 Φ.hasMFDerivAt.mdifferentiableAt (hρ 1) X
  rw [hf] at h1
  rw [Φ.hasMFDerivAt.mfderiv] at h2
  have key : ∀ y : G, y = conjMap g 1 →
      mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ y (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (conjMap g) 1 X) =
        mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ (conjMap g 1) (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (conjMap g) 1 X) := by
    rintro y rfl; rfl
  exact ((key 1 (conjMap_one g).symm).trans h1.symm).trans h2

/-- `r(dR_{k⁻¹} Y) ρ(k) = dρ_k(Y)`, from `ρ(l) = ρ(l k⁻¹) ρ(k)`. -/
lemma lieRep_rightTrivial {ρ : G →* (V →L[ℝ] V)} (hρ : ∀ k, MDifferentiableAt 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ k)
    (k : G) (Y : E_G) :
    lieRep ρ (rightTrivial E_G k Y) * ρ k = mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ k Y := by
  set Ψ := ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V) 1 (ρ k)
  have hf : ⇑ρ = ⇑Ψ ∘ (⇑ρ ∘ fun l : G => l * k⁻¹) := by
    funext l
    simp only [Function.comp_apply, Ψ, ContinuousLinearMap.mulLeftRight_apply, one_mul, ← map_mul,
      inv_mul_cancel_right]
  have hR : MDifferentiableAt 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) (⇑ρ ∘ fun l : G => l * k⁻¹) k :=
    (hρ _).comp k (mdifferentiableAt_mul_right' k⁻¹ k)
  have h1 := mfderiv_comp_apply (g := ⇑Ψ) (f := ⇑ρ ∘ fun l : G => l * k⁻¹) k Ψ.hasMFDerivAt.mdifferentiableAt hR Y
  have h2 := mfderiv_comp_apply (g := ⇑ρ) (f := fun l : G => l * k⁻¹) k (hρ _) (mdifferentiableAt_mul_right' k⁻¹ k) Y
  rw [Ψ.hasMFDerivAt.mfderiv, h2] at h1
  rw [← hf] at h1
  have key : ∀ y : G, y = k * k⁻¹ →
      mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ y (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * k⁻¹) k Y) =
        mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ (k * k⁻¹)
          (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, E_G) (fun l : G => l * k⁻¹) k Y) := by
    rintro y rfl; rfl
  have h3 : mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ k Y = Ψ (lieRep ρ (rightTrivial E_G k Y)) :=
    h1.trans (congrArg (fun T : V →L[ℝ] V => Ψ T) (key 1 (mul_inv_cancel k).symm).symm)
  rw [h3]
  simp only [Ψ, ContinuousLinearMap.mulLeftRight_apply, one_mul]

variable {c : PrincipalCocycle M G} [ContinuousMul G]

omit [ContinuousMul G] [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] in
/-- `1 ≤ minSmoothness ℝ 3`. -/
lemma one_le_minSmoothness_three : (1 : ℕ∞ω) ≤ minSmoothness ℝ 3 :=
  (show (1 : ℕ∞ω) ≤ 3 by norm_num).trans le_minSmoothness

omit [ContinuousMul G] in
/-- **The induced connection on the associated bundle** (Svetlichny eq. (39), p. 31): for potentials satisfying
(38), there is a covariant derivative on `P ×_ρ V` whose representative in the trivialization over `U_i` is
`d + r(A_i)`, the linear connection with vertical projection `(ξ, y) ↦ y + r(A_i(x) ξ) f`. -/
theorem exists_assocCov [IsManifold I 1 M] (hcov : ∀ x, ∃ i, x ∈ c.U i) {ρ : G →* (V →L[ℝ] V)}
    (hρs : ContMDiff 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) (minSmoothness ℝ 3) ρ) {A : c.ι → M → E →L[ℝ] E_G}
    (hA : c.IsCompatible I A)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, E_G) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j)) :
    ∃ cov : CovariantDerivative I V (c.assocCore hcov ρ hρs.continuous).Fiber,
      ∀ i (x : M) (σ : Π x : M, (c.assocCore hcov ρ hρs.continuous).Fiber x), x ∈ c.U i → MDifferentiableAt I (I.prod 𝓘(ℝ, V)) (fun y => TotalSpace.mk' V y (σ y)) x →
        cov σ x = localCov I ((c.assocCore hcov ρ hρs.continuous).localTriv i)
          (fun y => (lieRep ρ).comp (A i y)) σ x := by
  set Z := c.assocCore hcov ρ hρs.continuous
  have : Z.IsContMDiff I 1 :=
    ⟨fun i j => (hρs.of_le one_le_minSmoothness_three).comp_contMDiffOn ((hg i j).of_le one_le_minSmoothness_three)⟩
  have hρd : ∀ k, MDifferentiableAt 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ k := fun k =>
    (hρs k).mdifferentiableAt minSmoothness_three_ne_zero
  refine exists_covariantDerivative_of_local (fun i => Z.localTriv i) (fun x => hcov x)
    (fun i y => (lieRep ρ).comp (A i y)) ?_
  intro i j x hx v w
  have hxi : x ∈ c.U i := hx.1
  have hxj : x ∈ c.U j := hx.2
  have hU : ((c.U i ⊓ c.U j : TopologicalSpace.Opens M) : Set M) ∈ 𝓝 x :=
    (c.U i ⊓ c.U j).isOpen.mem_nhds ⟨hxi, hxj⟩
  have F1 : ∀ y ∈ ((c.U i ⊓ c.U j : TopologicalSpace.Opens M) : Set M),
      ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) y : V →L[ℝ] V) = ρ (c.g i j y) := fun y hy =>
    ContinuousLinearMap.ext fun u => Z.localTriv_coordChange_eq i j ⟨hy.1, hy.2⟩ u
  have hji : c.g j i x = (c.g i j x)⁻¹ :=
    eq_inv_of_mul_eq_one_left ((c.cocycle i j i x hxi hxj hxi).trans (c.self i x))
  have F2 : ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x).symm w = ρ (c.g i j x)⁻¹ w := by
    rw [Trivialization.symm_coordChangeL _ _ ⟨hxj, hxi⟩, Z.localTriv_coordChange_eq j i ⟨hxj, hxi⟩]
    show ρ (c.g j i x) w = _
    rw [hji]
  have hgx : MDifferentiableAt I 𝓘(ℝ, E_G) (c.g i j) x :=
    ((hg i j).contMDiffAt hU).mdifferentiableAt minSmoothness_three_ne_zero
  have F3 : mvfderiv I (fun y => ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) y : V →L[ℝ] V)) x v =
      mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ (c.g i j x) (mfderiv I 𝓘(ℝ, E_G) (c.g i j) x v) := by
    rw [mvfderiv_congr_of_eventuallyEq (Filter.eventually_of_mem hU F1)]
    exact mfderiv_comp_apply (g := ⇑ρ) (f := c.g i j) x (hρd _) hgx v
  have hAx := hA i j x hxi hxj
  have hr := lieRep_rightTrivial hρd (c.g i j x) (mfderiv I 𝓘(ℝ, E_G) (c.g i j) x v)
  have e1 : A j x v = adjointE 𝓘(ℝ, E_G) (c.g i j x) (A i x v) -
      rightTrivial E_G (c.g i j x) (mfderiv I 𝓘(ℝ, E_G) (c.g i j) x v) := by
    rw [hAx]; rfl
  have hL : lieRep ρ (A j x v) w = ρ (c.g i j x) (lieRep ρ (A i x v) (ρ (c.g i j x)⁻¹ w)) -
      (@id (V →L[ℝ] V) (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ (c.g i j x) (mfderiv I 𝓘(ℝ, E_G) (c.g i j) x v)))
        (ρ (c.g i j x)⁻¹ w) := by
    rw [e1, map_sub, lieRep_adjointE hρd, sub_apply]
    congr 1
    rw [← hr]
    show _ = lieRep ρ (rightTrivial E_G (c.g i j x) (mfderiv I 𝓘(ℝ, E_G) (c.g i j) x v))
      (ρ (c.g i j x) (ρ (c.g i j x)⁻¹ w))
    rw [← mul_apply_eq_comp (ρ (c.g i j x)), ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self]
  have hR : (Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x
        (((lieRep ρ).comp (A i x)) v (((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x).symm w)) -
      mvfderiv I (fun y => ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) y : V →L[ℝ] V)) x v
        (((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x).symm w) =
      ρ (c.g i j x) (lieRep ρ (A i x v) (ρ (c.g i j x)⁻¹ w)) -
        (@id (V →L[ℝ] V) (mfderiv 𝓘(ℝ, E_G) 𝓘(ℝ, V →L[ℝ] V) ρ (c.g i j x) (mfderiv I 𝓘(ℝ, E_G) (c.g i j) x v)))
          (ρ (c.g i j x)⁻¹ w) := by
    rw [F2, F3]
    congr 1
    exact Z.localTriv_coordChange_eq i j ⟨hxi, hxj⟩ _
  exact hL.trans hR.symm

omit [LieGroup 𝓘(ℝ, E_G) (minSmoothness ℝ 3) G] [ContinuousMul G] in
/-- **Uniqueness of the induced connection**: two covariant derivatives on `P ×_ρ V` with the representatives
`d + r(A_i)` agree on every section differentiable at the point. -/
theorem assocCov_unique (hcov : ∀ x, ∃ i, x ∈ c.U i) {ρ : G →* (V →L[ℝ] V)} (hρ : Continuous ρ)
    {A : c.ι → M → E →L[ℝ] E_G}
    (cov cov' : CovariantDerivative I V (c.assocCore hcov ρ hρ).Fiber)
    (h : ∀ i (x : M) (σ : Π x : M, (c.assocCore hcov ρ hρ).Fiber x), x ∈ c.U i → MDifferentiableAt I (I.prod 𝓘(ℝ, V)) (fun y => TotalSpace.mk' V y (σ y)) x →
      cov σ x = localCov I ((c.assocCore hcov ρ hρ).localTriv i) (fun y => (lieRep ρ).comp (A i y)) σ x)
    (h' : ∀ i (x : M) (σ : Π x : M, (c.assocCore hcov ρ hρ).Fiber x), x ∈ c.U i → MDifferentiableAt I (I.prod 𝓘(ℝ, V)) (fun y => TotalSpace.mk' V y (σ y)) x →
      cov' σ x = localCov I ((c.assocCore hcov ρ hρ).localTriv i) (fun y => (lieRep ρ).comp (A i y)) σ x)
    (σ : Π x : M, (c.assocCore hcov ρ hρ).Fiber x) (x : M) (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, V)) (fun y => TotalSpace.mk' V y (σ y)) x) : cov σ x = cov' σ x :=
  covariantDerivative_eq_of_local (fun i => (c.assocCore hcov ρ hρ).localTriv i) (fun x => hcov x)
    (fun i y => (lieRep ρ).comp (A i y)) cov cov' h h' σ x hσ

end PrincipalCocycle

end Lightlike.Gauge

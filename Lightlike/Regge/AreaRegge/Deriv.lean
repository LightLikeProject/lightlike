import Mathlib
import Lightlike.Regge.AreaRegge.Basic

/-!
# The squared-area map is a local diffeomorphism at the regular 4-simplex

`areaSqMap : ℝ¹⁰ → ℝ¹⁰` sends squared edge lengths to the squared areas of the ten triangles. Its
Fréchet derivative at `s` is the matrix `jac s`. At the regular simplex that matrix is invertible,
so the areas determine the squared lengths in a neighbourhood of the regular simplex.
-/

open Matrix Filter Topology

namespace Lightlike.AreaRegge

noncomputable section

/-- The squared-area map from the ten squared edge lengths to the ten squared areas. -/
def areaSqMap (s : Fin 10 → ℝ) : Fin 10 → ℝ := fun t => areaSq s t

/-- The Jacobian as a continuous linear map. -/
def jacCLM (s : Fin 10 → ℝ) : (Fin 10 → ℝ) →L[ℝ] (Fin 10 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (jac s))

theorem triAreaSq_abs_le {a b c m : ℝ} (ha : |a| ≤ m) (hb : |b| ≤ m) (hc : |c| ≤ m) :
    |triAreaSq a b c| ≤ m ^ 2 := by
  have hm : 0 ≤ m := (abs_nonneg a).trans ha
  rw [abs_le] at ha hb hc
  unfold triAreaSq
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (a + c), sq_nonneg m, sq_nonneg (a + b + c)]

theorem areaSqMap_norm_le (h : Fin 10 → ℝ) : ‖areaSqMap h‖ ≤ ‖h‖ ^ 2 := by
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
  intro t
  rw [Real.norm_eq_abs]
  exact triAreaSq_abs_le (by simpa using norm_le_pi_norm h _)
    (by simpa using norm_le_pi_norm h _) (by simpa using norm_le_pi_norm h _)

/-- **The derivative of the squared-area map is the Jacobian matrix.** -/
theorem hasFDerivAt_areaSqMap (s : Fin 10 → ℝ) : HasFDerivAt areaSqMap (jacCLM s) s := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun h : Fin 10 → ℝ => areaSqMap (s + h) - areaSqMap s - jacCLM s h) =
      fun h => areaSqMap h := by
    ext h t
    have := areaSq_add s h 1 t
    simp only [one_smul, one_mul, one_pow] at this
    simp only [areaSqMap, jacCLM, Pi.sub_apply, LinearMap.coe_toContinuousLinearMap',
      Matrix.toLin'_apply, this]
    ring
  rw [h1]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) (by norm_num))
  exact Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => by
    simpa using areaSqMap_norm_le h)

theorem contDiff_areaSqMap : ContDiff ℝ 1 areaSqMap := by
  refine contDiff_pi.2 fun t => ?_
  have hc : ∀ i : Fin 10, ContDiff ℝ 1 (fun s : Fin 10 → ℝ => s i) := fun i => contDiff_pi.1 contDiff_id i
  unfold areaSqMap areaSq triAreaSq
  fun_prop

/-- The area-squared map is strictly differentiable, with derivative `jacCLM`. -/
theorem hasStrictFDerivAt_areaSqMap (s : Fin 10 → ℝ) : HasStrictFDerivAt areaSqMap (jacCLM s) s := by
  have h := (contDiff_areaSqMap.contDiffAt (x := s)).hasStrictFDerivAt one_ne_zero
  rwa [(hasFDerivAt_areaSqMap s).fderiv] at h

/-- **The areas determine the squared lengths near the regular 4-simplex.** There is a
neighbourhood `U` of the regular simplex on which the squared-area map is injective and whose image
is a neighbourhood of the squared areas of the regular simplex. -/
theorem areaSqMap_local_inj :
    ∃ U ∈ 𝓝 sReg, Set.InjOn areaSqMap U ∧ areaSqMap '' U ∈ 𝓝 (areaSqMap sReg) := by
  have hu : IsUnit (jac sReg).det := jac_regular_isUnit
  let _ : Invertible (jac sReg) := Matrix.invertibleOfIsUnitDet _ hu
  let e : (Fin 10 → ℝ) ≃L[ℝ] (Fin 10 → ℝ) :=
    (Matrix.toLinearEquiv' (jac sReg) inferInstance).toContinuousLinearEquiv
  have he : (e : (Fin 10 → ℝ) →L[ℝ] (Fin 10 → ℝ)) = jacCLM sReg := by
    ext1 x; rfl
  have hs : HasStrictFDerivAt areaSqMap (e : (Fin 10 → ℝ) →L[ℝ] (Fin 10 → ℝ)) sReg := by
    rw [he]; exact hasStrictFDerivAt_areaSqMap sReg
  let p := hs.toOpenPartialHomeomorph areaSqMap
  have hp : (p : (Fin 10 → ℝ) → (Fin 10 → ℝ)) = areaSqMap := rfl
  refine ⟨p.source, p.open_source.mem_nhds (hs.mem_toOpenPartialHomeomorph_source), ?_, ?_⟩
  · simpa [hp] using p.injOn
  · have : areaSqMap '' p.source = p.target := by rw [← hp]; exact p.image_source_eq_target
    rw [this]
    exact p.open_target.mem_nhds (by simpa [hp] using p.map_source hs.mem_toOpenPartialHomeomorph_source)

/-- **The areas themselves determine the lengths near the regular simplex.** -/
theorem area_local_inj : ∃ U ∈ 𝓝 sReg, Set.InjOn area U := by
  obtain ⟨U, hU, hinj, -⟩ := areaSqMap_local_inj
  have hpos : ∀ᶠ s in 𝓝 sReg, ∀ t, 0 < areaSq s t := by
    rw [eventually_all]
    intro t
    have hc : Continuous fun s : Fin 10 → ℝ => areaSq s t := by
      have := (contDiff_areaSqMap.continuous)
      exact (continuous_apply t).comp this
    refine hc.continuousAt.eventually (lt_mem_nhds ?_)
    fin_cases t <;> simp [areaSq, triAreaSq, sReg] <;> norm_num
  refine ⟨U ∩ {s | ∀ t, 0 < areaSq s t}, inter_mem hU hpos, ?_⟩
  intro a ha b hb hab
  apply hinj ha.1 hb.1
  ext t
  have := congrFun hab t
  simp only [area] at this
  have h1 := Real.sq_sqrt (ha.2 t).le
  have h2 := Real.sq_sqrt (hb.2 t).le
  simp only [areaSqMap]
  rw [← h1, ← h2, this]

end

end Lightlike.AreaRegge

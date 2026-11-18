import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Calculus.TangentCone.Basic

/-!
# The kernel of a surjective derivative lies in the tangent cone of the level set

Part of the third attempt at the nonlinear Dirac algorithm (`DiracNonlinear`, `DiracWire`): the stage surfaces are zero
sets of regular constraint tuples, and "the evolution velocity is tangent to the surface" must be turned into the
linear condition `Φ'(x) v = 0`. One half, the one that needs the implicit function theorem, is here: if `f` has a
strict derivative `f'` at `a` with `f'` onto a finite-dimensional space, then `ker f'` is contained in the tangent
cone at `a` of the level set `f ⁻¹ {f a}`. The curve in the level set is `t ↦ ψ (t v)` for Mathlib's implicit function
`ψ`, whose derivative at `0` is the inclusion of `ker f'`.
-/

open Filter Topology Asymptotics

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **`ker f'` is in the tangent cone of the level set** (implicit function theorem). -/
theorem ker_subset_tangentCone_levelSet {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    (f'.ker : Set E) ⊆ tangentConeAt ℝ (f ⁻¹' {f a}) a := by
  intro v hv
  set ψ := hf.implicitFunction f f' hf' (f a) with hψ
  have hψd : HasStrictFDerivAt ψ f'.ker.subtypeL 0 := hf.to_implicitFunction hf'
  have hψ0 : ψ 0 = a := hf.implicitFunction_apply_image hf'
  let v' : f'.ker := ⟨v, hv⟩
  have hline : HasDerivAt (fun t : ℝ => ψ (t • v')) (v' : E) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v') v' 0 := by
      have := (hasDerivAt_id' (0 : ℝ)).smul_const v'
      simpa using this
    have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hψd.hasFDerivAt) h1 (by simp)
    exact (by simpa using h2 : HasDerivAt (ψ ∘ fun t : ℝ => t • v') (v' : E) 0)
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hline
  let tn : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have htn0 : Tendsto tn atTop (𝓝 0) := by
    simpa [tn, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htn : Tendsto tn atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨htn0, Eventually.of_forall fun n => by simp [tn]; positivity⟩
  have hcont : Tendsto (fun n => ψ (tn n • v')) atTop (𝓝 a) := by
    have := hline.continuousAt.tendsto.comp htn0
    simpa [Function.comp_def, hψ0] using this
  refine mem_tangentConeAt_of_seq atTop (fun n : ℕ => ((n : ℝ) + 1)) (fun n => ψ (tn n • v') - a) ?_ ?_ ?_
  · simpa using hcont.sub_const a
  · have hev := hf.map_implicitFunction_eq hf'
    have hp : Tendsto (fun n => ((f a, tn n • v') : F × f'.ker)) atTop (𝓝 (f a, 0)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      simpa using htn0.smul_const v'
    filter_upwards [hp.eventually hev] with n hn
    simpa using hn
  · have := hslope.comp htn
    refine this.congr fun n => ?_
    simp [Function.comp_def, tn, hψ0]

omit [CompleteSpace E] [FiniteDimensional ℝ F] in
/-- **The tangent cone of a level set lies in the kernel of the derivative**: if `f` is differentiable at `a` with
derivative `f'`, every tangent vector of the level set `f ⁻¹ {f a}` at `a` is killed by `f'`. -/
theorem tangentCone_levelSet_subset_ker {f : E → F} {f' : E →L[ℝ] F} {a : E} (hf : HasFDerivAt f f' a) :
    tangentConeAt ℝ (f ⁻¹' {f a}) a ⊆ (f'.ker : Set E) := by
  intro v hv
  obtain ⟨α, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  have hr : (fun n => f (a + d n) - f a - f' (d n)) =o[l] d := by
    have hta : Tendsto (fun n => a + d n) l (𝓝 a) := by simpa using (tendsto_const_nhds (x := a)).add hd0
    have := (hf.isLittleO).comp_tendsto hta
    simpa [Function.comp_def] using this
  have hr' : (fun n => c n • (f (a + d n) - f a - f' (d n))) =o[l] (fun n => c n • d n) := by
    have h1 := (isBigO_refl (fun n => ‖c n‖) l).mul_isLittleO hr.norm_norm
    refine IsLittleO.of_norm_norm ?_
    simpa only [norm_smul] using h1
  have hbig : (fun n => c n • d n) =O[l] (fun _ => (1 : ℝ)) := hcd.isBigO_one ℝ
  have h0 : Tendsto (fun n => c n • (f (a + d n) - f a - f' (d n))) l (𝓝 0) :=
    (isLittleO_one_iff ℝ).mp (hr'.trans_isBigO hbig)
  have h1 : Tendsto (fun n => f' (c n • d n)) l (𝓝 (f' v)) := (f'.continuous.tendsto v).comp hcd
  have h2 : Tendsto (fun n => f' (c n • d n)) l (𝓝 0) := by
    have := h0.neg
    rw [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [hds] with n hn
    have hn' : f (a + d n) = f a := hn
    simp [hn', map_smul, smul_sub]
  exact tendsto_nhds_unique h1 h2

section Tuple

variable {n : ℕ}

/-- The map `v ↦ (Φ'_i v)_i` of independent functionals is onto `ℝⁿ`. -/
theorem range_pi_eq_top {Φ' : Fin n → E →L[ℝ] ℝ} (hind : LinearIndependent ℝ Φ') :
    (ContinuousLinearMap.pi Φ').range = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hlin : ∑ i, φ (Pi.single i 1) • Φ' i = 0 := by
    ext v
    have hv : φ (ContinuousLinearMap.pi Φ' v) = 0 := by
      have : φ (ContinuousLinearMap.pi Φ' v) ∈ Submodule.map φ (ContinuousLinearMap.pi Φ').range :=
        ⟨_, ⟨v, rfl⟩, rfl⟩
      rw [hφ] at this
      simpa using this
    have hpi : ContinuousLinearMap.pi Φ' v = ∑ i, Φ' i v • (Pi.single i 1 : Fin n → ℝ) := by
      ext j; simp [Pi.single_apply]
    rw [hpi, map_sum] at hv
    simpa [mul_comm] using hv
  have hg := Fintype.linearIndependent_iff.mp hind _ hlin
  apply hφ0
  refine LinearMap.pi_ext fun i y => ?_
  rw [show (Pi.single i y : Fin n → ℝ) = y • Pi.single i 1 by ext j; simp [Pi.single_apply]]
  simp [hg i]

/-- **The tangent cone of the zero set of a regular tuple is the common kernel of the derivatives**: for constraint
functions with strict derivatives `Φ'_i` at `x`, linearly independent, and `x` in the zero set. -/
theorem mem_tangentCone_zeroSet_iff {Φ : Fin n → E → ℝ} {Φ' : Fin n → E →L[ℝ] ℝ} {x : E}
    (hΦ : ∀ i, HasStrictFDerivAt (Φ i) (Φ' i) x) (hind : LinearIndependent ℝ Φ')
    (hx : ∀ i, Φ i x = 0) (v : E) :
    v ∈ tangentConeAt ℝ {y | ∀ i, Φ i y = 0} x ↔ ∀ i, Φ' i v = 0 := by
  let F : E → (Fin n → ℝ) := fun y i => Φ i y
  have hF : HasStrictFDerivAt F (ContinuousLinearMap.pi Φ') x :=
    hasStrictFDerivAt_pi'' fun i => by simpa using hΦ i
  have hFx : F x = 0 := funext hx
  have hset : {y | ∀ i, Φ i y = 0} = F ⁻¹' {F x} := by
    ext y; simp [F, hFx, funext_iff]
  rw [hset]
  constructor
  · intro hv i
    have := tangentCone_levelSet_subset_ker hF.hasFDerivAt hv
    exact congrFun (by simpa using this) i
  · intro hv
    exact ker_subset_tangentCone_levelSet hF (range_pi_eq_top hind) (by
      simp [LinearMap.mem_ker, funext_iff, hv])

end Tuple

end Lightlike.Gauge

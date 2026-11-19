import Lightlike.Spacetime.Hypersurface
import Lightlike.Canonical.MatrixSmooth

/-!
# The unit normal of a level set with a non-null gradient (GE13)

For a function `φ` smooth near `x₀` whose gradient at `x₀` (the vector `ξ` with `g(ξ, ·) = dφ`) is not null, the level sets
of `φ` near `x₀` have a unit normal field `n` with `g(n, n) = ε = ±1` (`exists_isUnitNormal`): the hypothesis
`IsUnitNormal` of `Hypersurface.lean` is a consequence, not an assumption.

* `contMDiffAt_mfderiv_field`: the derivative `dφ(V)` of a smooth function along a smooth field is smooth;
* `frame`: the local frame `y ↦ e_y⁻¹(bᵢ)` of the trivialization at `x₀`, smooth near `x₀` (`smoothNear_frame`);
* `gradField`: `∇φ = Σᵢⱼ (G⁻¹)ᵢⱼ dφ(e_j) eᵢ` with `G` the Gram matrix of the frame; `g(∇φ, v) = dφ(v)` near `x₀`
  (`gradField_spec`) and `∇φ` is smooth near `x₀` (`smoothNear_gradField`);
* `exists_isUnitNormal`: `n = |g(∇φ, ∇φ)|^{-1/2} ∇φ`, `ε` the sign of `g(∇φ, ∇φ)` at `x₀`.
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]

namespace Hypersurface

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompleteSpace E] in
/-- **`dφ(V)` is smooth** for `φ` smooth at `y` and `V` a field smooth at `y`. -/
theorem contMDiffAt_mfderiv_field {φ : M → ℝ} {V : Π y : M, TangentSpace 𝓘(ℝ, E) y} {y : M}
    (hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ y)
    (hV : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)) y) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ z (V z)) y := by
  set e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) y with he
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z => (e ⟨z, V z⟩).2) y :=
    (contMDiffAt_section (IB := 𝓘(ℝ, E)) (E := TangentSpace 𝓘(ℝ, E)) (F := E) (s := V) y).1 hV
  have hφ2 : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry fun (_ : M) (z : M) => φ z) (y, y) :=
    hφ.comp (y, y) contMDiffAt_snd
  have h := ContMDiffAt.mfderiv_apply (fun (_ : M) (z : M) => φ z) id id (fun z => (e ⟨z, V z⟩).2) hφ2
    contMDiffAt_id contMDiffAt_id hc (by simp)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' y)] with z hz
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id]
  erw [TangentBundle.continuousLinearMapAt_model_space]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ z (V z) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ z (e.symmL ℝ z (e ⟨z, V z⟩).2)
  congr 1
  rw [Trivialization.symmL_apply e hz, e.symm_apply_apply_mk hz]

/-- The local frame of the trivialization at `x₀`: `y ↦ e_y⁻¹(bᵢ)`. -/
def frame (x₀ : M) (i : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace 𝓘(ℝ, E) y :=
  FiberBundle.extend E ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symm x₀ (Module.finBasis ℝ E i))

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompleteSpace E] in
theorem frame_apply (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M) :
    frame x₀ i y = (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symm y (Module.finBasis ℝ E i) := by
  unfold frame FiberBundle.extend
  rw [(trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).apply_mk_symm
    (FiberBundle.mem_baseSet_trivializationAt' x₀)]

theorem smoothNear_frame (x₀ : M) (i : Fin (Module.finrank ℝ E)) : SmoothNear (frame x₀ i) x₀ :=
  eventually_extend x₀ _

/-- The differential `dφ_y` as a real linear form. -/
def dφL (φ : M → ℝ) (y : M) : TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ y

/-- The derivative `dφ_y(v)` as a real number. -/
def dφ (φ : M → ℝ) (y : M) (v : TangentSpace 𝓘(ℝ, E) y) : ℝ := dφL φ y v

/-- The Gram matrix of the frame at `y`. -/
def gram (g : NondegMetric 𝓘(ℝ, E) M) (x₀ y : M) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.g y (frame x₀ i y) (frame x₀ j y)

/-- **The gradient** of `φ` in the frame of `x₀`: `Σᵢⱼ (G⁻¹)ᵢⱼ dφ(e_j) eᵢ`. -/
def gradField (g : NondegMetric 𝓘(ℝ, E) M) (φ : M → ℝ) (x₀ : M) : Π y : M, TangentSpace 𝓘(ℝ, E) y :=
  fun y => ∑ i, (∑ j, (gram g x₀ y)⁻¹ i j * dφ φ y (frame x₀ j y)) • frame x₀ i y

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompleteSpace E] in
/-- The frame at a point of the base set is a basis. -/
theorem frame_basis (x₀ : M) {y : M} (hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet) :
    ∃ B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) y), ∀ i, B i = frame x₀ i y := by
  set e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀
  refine ⟨(Module.finBasis ℝ E).map (e.continuousLinearEquivAt ℝ y hy).symm.toLinearEquiv, fun i => ?_⟩
  rw [Module.Basis.map_apply, frame_apply]
  rfl

omit [T2Space M] [CompleteSpace E] in
/-- The Gram matrix of the frame is invertible on the base set. -/
theorem gram_det_ne_zero (g : NondegMetric 𝓘(ℝ, E) M) (x₀ : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet) : (gram g x₀ y).det ≠ 0 := by
  obtain ⟨B, hB⟩ := frame_basis x₀ hy
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero B).mp (g.bilinForm_nondegenerate y)
  have hm : LinearMap.BilinForm.toMatrix B (g.g y).toBilinForm = gram g x₀ y := by
    ext i j; simp [LinearMap.BilinForm.toMatrix_apply, gram, hB]
  rwa [hm] at h

omit [T2Space M] [CompleteSpace E] in
/-- **`g(∇φ, v) = dφ(v)`** on the base set of the trivialization at `x₀`. -/
theorem gradField_spec (g : NondegMetric 𝓘(ℝ, E) M) (φ : M → ℝ) (x₀ : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet) (v : TangentSpace 𝓘(ℝ, E) y) :
    g.g y (gradField g φ x₀ y) v = dφ φ y v := by
  obtain ⟨B, hB⟩ := frame_basis x₀ hy
  set G := gram g x₀ y with hG
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 (gram_det_ne_zero g x₀ hy)
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hsym : ∀ i k, G i k = G k i := fun i k => g.symm y _ _
  suffices h : ((g.g y (gradField g φ x₀ y) : TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) : TangentSpace 𝓘(ℝ, E) y →ₗ[ℝ] ℝ) =
      ((dφL φ y : TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) : TangentSpace 𝓘(ℝ, E) y →ₗ[ℝ] ℝ) by
    exact congrArg (fun f => f v) h
  refine B.ext fun k => ?_
  simp only [ContinuousLinearMap.coe_coe, hB, gradField, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  have e1 : ∀ i, g.g y (frame x₀ i y) (frame x₀ k y) = G k i := fun i => by rw [hsym]; rfl
  simp only [e1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e2 : ∀ j, ∑ i, (G⁻¹ i j * dφ φ y (frame x₀ j y)) * G k i =
      (G * G⁻¹) k j * dφ φ y (frame x₀ j y) := fun j => by
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← hG]
  simp only [e2, hGG, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-- **The gradient is smooth near `x₀`** for `φ` smooth near `x₀`. -/
theorem smoothNear_gradField (g : NondegMetric 𝓘(ℝ, E) M) {φ : M → ℝ} {x₀ : M}
    (hφ : ∀ᶠ y in 𝓝 x₀, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ y) : SmoothNear (gradField g φ x₀) x₀ := by
  have hfr : ∀ᶠ y in 𝓝 x₀, ∀ i, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, frame x₀ i q⟩ : TangentBundle 𝓘(ℝ, E) M)) y :=
    eventually_all.2 fun i => smoothNear_frame x₀ i
  filter_upwards [hφ, hfr, (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x₀)] with y hy hfy hyb
  -- the entries of the Gram matrix and of its inverse are smooth at `y`
  set Gf : M → (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
    fun z i j => g.g z (frame x₀ i z) (frame x₀ j z) with hGf
  have hGfs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ∞ Gf y :=
    contMDiffAt_pi_module_iff.2 fun i => contMDiffAt_pi_module_iff.2 fun j => contMDiffAt_gpair g (hfy i) (hfy j)
  have hinv : ∀ a b, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (gram g x₀ z)⁻¹ a b) y := by
    intro a b
    have h1 : ContDiffAt ℝ ∞ (fun Z : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => (Matrix.of Z)⁻¹ a b)
        (Gf y) := by
      refine Lightlike.Canonical.contDiffAt_inv_entry (fun Z => Matrix.of Z) (fun i j => ?_) ?_ a b
      · show ContDiffAt ℝ ∞ (fun Z : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => Z i j) _
        fun_prop
      · exact gram_det_ne_zero g x₀ hyb
    exact h1.comp_contMDiffAt hGfs
  -- the gradient is a sum of smooth multiples of smooth fields
  have hsum := ContMDiffAt.sum_section (s := Finset.univ)
    (t := fun i z => (∑ j, (gram g x₀ z)⁻¹ i j * dφ φ z (frame x₀ j z)) • frame x₀ i z)
    (x₀ := y) fun i _ => by
      refine ContMDiffAt.smul_section ?_ (hfy i)
      refine ContMDiffAt.sum fun j _ => (hinv i j).mul ?_
      exact contMDiffAt_mfderiv_field hy (hfy j)
  exact hsum

/-- **A non-null gradient gives a unit normal** (GE13): if `φ` is smooth near `x₀` and its gradient at `x₀` (a vector `ξ` with
`g(ξ, ·) = dφ`) is not null, the level sets of `φ` near `x₀` have a unit normal field `n = |g(∇φ, ∇φ)|^{-1/2} ∇φ` with
`g(n, n) = ε = ±1`. -/
theorem exists_isUnitNormal (g : NondegMetric 𝓘(ℝ, E) M) {φ : M → ℝ} {x₀ : M}
    (hφ : ∀ᶠ y in 𝓝 x₀, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ y)
    (hnn : ∀ ξ : TangentSpace 𝓘(ℝ, E) x₀, (∀ v, g.g x₀ ξ v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x₀ v) → g.g x₀ ξ ξ ≠ 0) :
    ∃ (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) (ε : ℝ), IsUnitNormal g φ n ε x₀ := by
  set N := gradField g φ x₀ with hNdef
  have hN : SmoothNear N x₀ := smoothNear_gradField g hφ
  have hbase : ∀ᶠ y in 𝓝 x₀, y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet :=
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀)
  set q : M → ℝ := fun y => g.g y (N y) (N y) with hqdef
  have hq0 : q x₀ ≠ 0 := hnn (N x₀) fun v => gradField_spec g φ x₀ hbase.self_of_nhds v
  set ε : ℝ := if 0 < q x₀ then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by by_cases h : 0 < q x₀ <;> simp [hεdef, h]
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεq : 0 < ε * q x₀ := by
    by_cases h : 0 < q x₀
    · simp [hεdef, h]
    · have : q x₀ < 0 := lt_of_le_of_ne (not_lt.1 h) hq0
      simp [hεdef, h]; linarith
  have hqs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ q x₀ := contMDiffAt_gpair g hN.self_of_nhds hN.self_of_nhds
  have hpos : ∀ᶠ y in 𝓝 x₀, 0 < ε * q y :=
    ((continuousAt_const.mul hqs.continuousAt).eventually (lt_mem_nhds hεq))
  set c : M → ℝ := fun y => (Real.sqrt (ε * q y))⁻¹ with hcdef
  refine ⟨fun y => c y • N y, ε, hε, hφ, ?_, ?_, ?_⟩
  · filter_upwards [hN, hpos] with y hNy hy
    have hqy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => ε * q z) y :=
      contMDiffAt_const.mul (contMDiffAt_gpair g hNy hNy)
    have hsq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => Real.sqrt (ε * q z)) y :=
      ContDiffAt.comp_contMDiffAt (g := fun r : ℝ => Real.sqrt r) (f := fun z => ε * q z) (x := y)
        (Real.contDiffAt_sqrt hy.ne') hqy
    have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ c y := hsq.inv₀ (Real.sqrt_pos.2 hy).ne'
    exact hc.smul_section hNy
  · filter_upwards [hpos] with y hy
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hs : Real.sqrt (ε * q y) ^ 2 = ε * q y := Real.sq_sqrt hy.le
    have hs0 : Real.sqrt (ε * q y) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
    have hqy : g.g y (N y) (N y) = q y := rfl
    rw [hqy]
    simp only [hcdef]
    field_simp
    rw [hs]
    linear_combination (-q y) * hε2
  · filter_upwards [hpos, hbase] with y hy hyb v
    have hspec := gradField_spec g φ x₀ hyb v
    have hc0 : c y ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hy).ne'
    simp only [map_smul, smul_apply, smul_eq_mul]
    change dφ φ y v = 0 ↔ c y * g.g y (N y) v = 0
    rw [hspec, mul_eq_zero, or_iff_right hc0]

end Hypersurface
end Lightlike

import Mathlib

/-!
# Integral operators with continuous kernels on `L²` of a compact space

For a compact space `X` with a finite Borel measure `μ` and a continuous kernel `K : C(X × X, ℂ)`,
the integral operator `(T_K ψ)(x) = ∫ K(x, y) ψ(y) dμ(y)` on `L²(X, μ)` (`kernelOp`). It is built
as in `Lightlike.HarmonicAnalysis.convOp` and `Lightlike.HarmonicAnalysis.kerOp`, which are the
case of a compact group with its Haar measure (and `K(x, y) = conj φ(y⁻¹ x)` for `convOp`):
`T_K ψ = toLp (x ↦ ⟪k_x, ψ⟫)` with `k_x ∈ L²` the class of `y ↦ conj K(x, y)`, and `x ↦ k_x`
continuous into `C(X, ℂ)`. The integral formula holds almost everywhere (`kernelOp_ae_eq`), and the
operator is compact (`isCompactOperator_kernelOp`), by Arzelà–Ascoli: the images of the unit ball
are bounded and equicontinuous in `C(X, ℂ)`.

## Main results

* `kernelOp`, `kernelOp_ae_eq`, `isCompactOperator_kernelOp`
* `isSymmetric_kernelOp`: a Hermitian kernel `K(y, x) = conj K(x, y)` gives a self-adjoint operator
  (Fubini on `X × X`, for second-countable `X`)

## References

* P. Garrett, *Compact operators* (notes 09b, 2020), §1 [1.2] and §2: integral operators with
  kernels in `L²(X × Y)` are Hilbert–Schmidt, hence compact; here the kernel is continuous on a
  compact space and compactness is proved directly.  §2.1: the adjoint has kernel `conj K(y, x)`.
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- The map `x ↦ (y ↦ conj K(x, y))` into the continuous functions. -/
def kernelCurry (K : C(X × X, ℂ)) : C(X, C(X, ℂ)) :=
  ContinuousMap.curry ⟨fun p : X × X => starRingEnd ℂ (K p), by fun_prop⟩

lemma kernelCurry_apply (K : C(X × X, ℂ)) (x y : X) :
    kernelCurry K x y = starRingEnd ℂ (K (x, y)) := rfl

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The kernel vector `k_x ∈ L²`, the class of `y ↦ conj K(x, y)`. -/
def kernelVecOf (K : C(X × X, ℂ)) (x : X) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ (kernelCurry K x)

lemma continuous_kernelVecOf (K : C(X × X, ℂ)) : Continuous (kernelVecOf μ K) :=
  (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp (kernelCurry K).continuous

/-- The integral operator into the continuous functions, `ψ ↦ (x ↦ ⟪k_x, ψ⟫)`. -/
def kernelToC (K : C(X × X, ℂ)) : Lp ℂ 2 μ →L[ℂ] C(X, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟨fun x => inner ℂ (kernelVecOf μ K x) ψ,
        (continuous_kernelVecOf μ K).inner continuous_const⟩
      map_add' := fun ψ χ => by ext x; simp [inner_add_right]
      map_smul' := fun c ψ => by ext x; simp [inner_smul_right] }
    (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelCurry K‖)
    (fun ψ => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
      calc ‖inner ℂ (kernelVecOf μ K x) ψ‖ ≤ ‖kernelVecOf μ K x‖ * ‖ψ‖ := norm_inner_le_norm _ _
        _ ≤ (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelCurry K‖) * ‖ψ‖ := by
            gcongr
            calc ‖kernelVecOf μ K x‖ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ *
                ‖kernelCurry K x‖ := (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).le_opNorm _
              _ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelCurry K‖ := by
                  gcongr; exact (kernelCurry K).norm_coe_le_norm x)

/-- The integral operator `T_K` on `L²(X, μ)`. -/
def kernelOp (K : C(X × X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).comp (kernelToC μ K)

lemma kernelToC_apply (K : C(X × X, ℂ)) (ψ : Lp ℂ 2 μ) (x : X) :
    kernelToC μ K ψ x = inner ℂ (kernelVecOf μ K x) ψ := rfl

/-- `⟪k_x, ψ⟫ = ∫ K(x, y) ψ(y) dμ(y)`. -/
lemma inner_kernelVecOf (K : C(X × X, ℂ)) (ψ : Lp ℂ 2 μ) (x : X) :
    inner ℂ (kernelVecOf μ K x) ψ = ∫ y, K (x, y) * ψ y ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (kernelCurry K x)]
    with y hy
  simp only [kernelVecOf, RCLike.inner_apply, hy, kernelCurry_apply, Complex.conj_conj]
  ring

/-- **The integral formula**: `(T_K ψ)(x) = ∫ K(x, y) ψ(y) dμ(y)` for almost every `x`. -/
theorem kernelOp_ae_eq (K : C(X × X, ℂ)) (ψ : Lp ℂ 2 μ) :
    (kernelOp μ K ψ : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * ψ y ∂μ := by
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (kernelToC μ K ψ)]
    with x hx
  rw [kernelOp, ContinuousLinearMap.comp_apply, hx, kernelToC_apply, inner_kernelVecOf]

/-- The images of the unit ball under `kernelToC K` form an equicontinuous family. -/
lemma equicontinuous_kernelToC (K : C(X × X, ℂ)) :
    Equicontinuous (fun ψ : Metric.ball (0 : Lp ℂ 2 μ) 1 =>
      ((kernelToC μ K ψ : C(X, ℂ)) : X → ℂ)) := by
  have hk := continuous_kernelVecOf μ K
  intro x₀ U hU
  have hbase : ∀ᶠ v in nhds (kernelVecOf μ K x₀), ∀ ψ : Metric.ball (0 : Lp ℂ 2 μ) 1,
      (inner ℂ (kernelVecOf μ K x₀) (ψ : Lp ℂ 2 μ), inner ℂ v (ψ : Lp ℂ 2 μ)) ∈ U := by
    have hlip : UniformEquicontinuous
        (fun ψ : Metric.ball (0 : Lp ℂ 2 μ) 1 => fun v : Lp ℂ 2 μ => inner ℂ v (ψ : Lp ℂ 2 μ)) := by
      refine Metric.uniformEquicontinuous_of_continuity_modulus id Filter.tendsto_id _ fun v w ψ => ?_
      simp only [id]
      rw [dist_eq_norm, ← inner_sub_left]
      calc ‖inner ℂ (v - w) (ψ : Lp ℂ 2 μ)‖ ≤ ‖v - w‖ * ‖(ψ : Lp ℂ 2 μ)‖ := norm_inner_le_norm _ _
        _ ≤ ‖v - w‖ * 1 := by
            gcongr
            exact (mem_ball_zero_iff.1 ψ.2).le
        _ = dist v w := by rw [mul_one, dist_eq_norm]
    exact hlip.equicontinuous (kernelVecOf μ K x₀) U hU
  exact (hk.continuousAt.eventually hbase).mono fun y hy ψ => hy ψ

/-- The integral operator into the continuous functions is compact (Arzelà–Ascoli). -/
theorem isCompactOperator_kernelToC (K : C(X × X, ℂ)) : IsCompactOperator (kernelToC μ K) := by
  refine (isCompactOperator_iff_isCompact_closure_image_ball (kernelToC μ K).toLinearMap one_pos).2 ?_
  set e := ContinuousMap.isometryEquivBoundedOfCompact X ℂ
  set S : Set C(X, ℂ) := kernelToC μ K '' Metric.ball 0 1 with hS
  set A : Set (BoundedContinuousFunction X ℂ) := e '' S with hA
  have hAc : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) ‖kernelToC μ K‖)
      (isCompact_closedBall _ _) A ?_ ?_
    · rintro f x ⟨g, ⟨ψ, hψ, rfl⟩, rfl⟩
      have h1 : ‖kernelToC μ K ψ x‖ ≤ ‖kernelToC μ K‖ :=
        calc ‖kernelToC μ K ψ x‖ ≤ ‖kernelToC μ K ψ‖ := (kernelToC μ K ψ).norm_coe_le_norm x
          _ ≤ ‖kernelToC μ K‖ * ‖ψ‖ := (kernelToC μ K).le_opNorm ψ
          _ ≤ ‖kernelToC μ K‖ * 1 := by
              gcongr; exact (mem_ball_zero_iff.1 hψ).le
          _ = ‖kernelToC μ K‖ := mul_one _
      rw [mem_closedBall_zero_iff]
      exact h1
    · have hE := equicontinuous_kernelToC μ K
      have hex : ∀ a : A, ∃ ψ : Metric.ball (0 : Lp ℂ 2 μ) 1,
          ((a : BoundedContinuousFunction X ℂ) : X → ℂ) = ((kernelToC μ K ψ : C(X, ℂ)) : X → ℂ) := by
        rintro ⟨_, g, ⟨ψ, hψ, rfl⟩, rfl⟩
        exact ⟨⟨ψ, hψ⟩, rfl⟩
      choose u hu using hex
      have : ((↑) : A → X → ℂ) = fun a => ((kernelToC μ K (u a) : C(X, ℂ)) : X → ℂ) := funext hu
      rw [this]
      exact hE.comp u
  have hcomp : IsCompact (e.symm '' closure A) := hAc.image e.symm.continuous
  have hsub : closure S ⊆ e.symm '' closure A := by
    refine closure_minimal ?_ hcomp.isClosed
    intro f hf
    exact ⟨e f, subset_closure ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩
  exact hcomp.of_isClosed_subset isClosed_closure hsub

/-- **Integral operators with continuous kernels are compact.** -/
theorem isCompactOperator_kernelOp (K : C(X × X, ℂ)) : IsCompactOperator (kernelOp μ K) :=
  (isCompactOperator_kernelToC μ K).clm_comp (ContinuousMap.toLp (E := ℂ) 2 μ ℂ)

section Symmetric

variable [SecondCountableTopology X]

/-- `⟪T_K φ, ψ⟫ = ∫∫ conj K(x, y) conj φ(y) ψ(x)`. -/
lemma inner_kernelOp_left (K : C(X × X, ℂ)) (φ ψ : Lp ℂ 2 μ) :
    inner ℂ (kernelOp μ K φ) ψ =
      ∫ x, ∫ y, starRingEnd ℂ (K (x, y)) * starRingEnd ℂ (φ y) * ψ x ∂μ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [kernelOp_ae_eq μ K φ] with x hx
  rw [RCLike.inner_apply, hx, ← integral_conj, mul_comm, ← integral_mul_const]
  congr 1
  funext y
  simp only [map_mul]

/-- **Hermitian kernels give self-adjoint operators**: if `K(y, x) = conj K(x, y)` then `T_K` is
symmetric. -/
theorem isSymmetric_kernelOp (K : C(X × X, ℂ))
    (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) :
    (kernelOp μ K : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).IsSymmetric := by
  intro φ ψ
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_kernelOp_left, ← inner_conj_symm φ (kernelOp μ K ψ), inner_kernelOp_left,
    ← integral_conj]
  have hint : Integrable (Function.uncurry fun (x y : X) =>
      starRingEnd ℂ (K (x, y)) * starRingEnd ℂ (φ y) * ψ x) (μ.prod μ) := by
    have hφ0 : Integrable (fun y => φ y) μ := (Lp.memLp φ).integrable one_le_two
    have hφ : Integrable (fun y => starRingEnd ℂ (φ y)) μ :=
      Integrable.mono hφ0 (Complex.continuous_conj.comp_aestronglyMeasurable
        (Integrable.aestronglyMeasurable hφ0)) (Filter.Eventually.of_forall fun y => by simp)
    have hψ : Integrable (fun x => ψ x) μ := (Lp.memLp ψ).integrable one_le_two
    have hprod : Integrable (fun z : X × X => ‖ψ z.1‖ * ‖φ z.2‖) (μ.prod μ) :=
      Integrable.mul_prod (Integrable.norm hψ) (Integrable.norm hφ0)
    refine Integrable.mono' (g := fun z : X × X => ‖K‖ * (‖ψ z.1‖ * ‖φ z.2‖))
      (Integrable.const_mul hprod ‖K‖) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact ((Complex.continuous_conj.comp K.continuous).aestronglyMeasurable.mul
        (hφ.aestronglyMeasurable.comp_snd)).mul (hψ.aestronglyMeasurable.comp_fst)
    · simp only [Function.uncurry, norm_mul, Complex.norm_conj]
      have := K.norm_coe_le_norm (z.1, z.2)
      calc ‖K (z.1, z.2)‖ * ‖φ z.2‖ * ‖ψ z.1‖ ≤ ‖K‖ * ‖φ z.2‖ * ‖ψ z.1‖ := by gcongr
        _ = ‖K‖ * (‖ψ z.1‖ * ‖φ z.2‖) := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hK x y, map_mul, Complex.conj_conj]
  ring

end Symmetric

end

end Lightlike.OperatorAlgebras

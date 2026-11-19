import Lightlike.HarmonicAnalysis.MatrixCoefficient
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Convolution operators on `L²` of a compact group

For a compact Hausdorff group `G` with its Haar measure `μ` and a continuous function `φ`, the operator
`(K_φ ψ)(x) = ∫ φ(y⁻¹ x) ψ(y) dμ(y)` on `L²(G, μ)`. It is built without integrals, as
`K_φ ψ = toLp (x ↦ ⟪k_x, ψ⟫)` where `k_x ∈ L²` is the class of the continuous function
`y ↦ conj φ(y⁻¹ x)` and `x ↦ k_x` is continuous into `C(G, ℂ)`.

This is the first step of the separation of points by matrix coefficients (Peter–Weyl): `K_φ` is
compact, self-adjoint for a symmetric `φ`, and commutes with the left regular representation.

Supporting lemmas; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The map `x ↦ (y ↦ conj φ (y⁻¹ x))` into the continuous functions. -/
def kernelMap (φ : C(G, ℂ)) : C(G, C(G, ℂ)) :=
  ContinuousMap.curry ⟨fun p : G × G => starRingEnd ℂ (φ (p.2⁻¹ * p.1)), by fun_prop⟩

lemma kernelMap_apply (φ : C(G, ℂ)) (x y : G) : kernelMap φ x y = starRingEnd ℂ (φ (y⁻¹ * x)) := rfl

/-- The kernel vector `k_x ∈ L²`. -/
def kernelVec (φ : C(G, ℂ)) (x : G) : Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ (kernelMap φ x)

/-- The convolution operator `K_φ`, as a bounded linear map into continuous functions. -/
def convToC (φ : C(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] C(G, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟨fun x => inner ℂ (kernelVec μ φ x) ψ, by
        have hk : Continuous fun x => kernelVec μ φ x :=
          (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp (kernelMap φ).continuous
        exact hk.inner continuous_const⟩
      map_add' := fun ψ χ => by ext x; simp [inner_add_right]
      map_smul' := fun c ψ => by ext x; simp [inner_smul_right] }
    (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelMap φ‖)
    (fun ψ => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
      calc ‖inner ℂ (kernelVec μ φ x) ψ‖ ≤ ‖kernelVec μ φ x‖ * ‖ψ‖ := norm_inner_le_norm _ _
        _ ≤ (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelMap φ‖) * ‖ψ‖ := by
            gcongr
            calc ‖kernelVec μ φ x‖ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelMap φ x‖ :=
                  (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).le_opNorm _
              _ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelMap φ‖ := by
                  gcongr; exact (kernelMap φ).norm_coe_le_norm x)

/-- The convolution operator `K_φ` on `L²(G, μ)`. -/
def convOp (φ : C(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).comp (convToC μ φ)

lemma convToC_apply (φ : C(G, ℂ)) (ψ : Lp ℂ 2 μ) (x : G) :
    convToC μ φ ψ x = inner ℂ (kernelVec μ φ x) ψ := rfl

/-- The images of the unit ball under `convToC φ` form an equicontinuous family. -/
lemma equicontinuous_convToC (φ : C(G, ℂ)) :
    Equicontinuous (fun ψ : Metric.ball (0 : Lp ℂ 2 μ) 1 => ((convToC μ φ ψ : C(G, ℂ)) : G → ℂ)) := by
  have hk : Continuous fun x => kernelVec μ φ x :=
    (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp (kernelMap φ).continuous
  intro x₀ U hU
  have hbase : ∀ᶠ v in nhds (kernelVec μ φ x₀), ∀ ψ : Metric.ball (0 : Lp ℂ 2 μ) 1,
      (inner ℂ (kernelVec μ φ x₀) (ψ : Lp ℂ 2 μ), inner ℂ v (ψ : Lp ℂ 2 μ)) ∈ U := by
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
    exact hlip.equicontinuous (kernelVec μ φ x₀) U hU
  exact (hk.continuousAt.eventually hbase).mono fun y hy ψ => hy ψ

/-- **Compactness.** The convolution operator into continuous functions is compact (Arzelà–Ascoli). -/
theorem isCompactOperator_convToC (φ : C(G, ℂ)) : IsCompactOperator (convToC μ φ) := by
  refine (isCompactOperator_iff_isCompact_closure_image_ball (convToC μ φ).toLinearMap one_pos).2 ?_
  set e := ContinuousMap.isometryEquivBoundedOfCompact G ℂ
  set S : Set C(G, ℂ) := convToC μ φ '' Metric.ball 0 1 with hS
  set A : Set (BoundedContinuousFunction G ℂ) := e '' S with hA
  have hAc : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) ‖convToC μ φ‖)
      (isCompact_closedBall _ _) A ?_ ?_
    · rintro f x ⟨g, ⟨ψ, hψ, rfl⟩, rfl⟩
      have h1 : ‖convToC μ φ ψ x‖ ≤ ‖convToC μ φ‖ :=
        calc ‖convToC μ φ ψ x‖ ≤ ‖convToC μ φ ψ‖ := (convToC μ φ ψ).norm_coe_le_norm x
          _ ≤ ‖convToC μ φ‖ * ‖ψ‖ := (convToC μ φ).le_opNorm ψ
          _ ≤ ‖convToC μ φ‖ * 1 := by
              gcongr; exact (mem_ball_zero_iff.1 hψ).le
          _ = ‖convToC μ φ‖ := mul_one _
      rw [mem_closedBall_zero_iff]
      exact h1
    · have hE := equicontinuous_convToC μ φ
      have hex : ∀ a : A, ∃ ψ : Metric.ball (0 : Lp ℂ 2 μ) 1,
          ((a : BoundedContinuousFunction G ℂ) : G → ℂ) = ((convToC μ φ ψ : C(G, ℂ)) : G → ℂ) := by
        rintro ⟨_, g, ⟨ψ, hψ, rfl⟩, rfl⟩
        exact ⟨⟨ψ, hψ⟩, rfl⟩
      choose u hu using hex
      have : ((↑) : A → G → ℂ) = fun a => ((convToC μ φ (u a) : C(G, ℂ)) : G → ℂ) := funext hu
      rw [this]
      exact hE.comp u
  have hcomp : IsCompact (e.symm '' closure A) := hAc.image e.symm.continuous
  have hsub : closure S ⊆ e.symm '' closure A := by
    refine closure_minimal ?_ hcomp.isClosed
    intro f hf
    exact ⟨e f, subset_closure ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩
  exact hcomp.of_isClosed_subset isClosed_closure hsub

/-- **Compactness of the convolution operator on `L²`.** -/
theorem isCompactOperator_convOp (φ : C(G, ℂ)) : IsCompactOperator (convOp μ φ) :=
  (isCompactOperator_convToC μ φ).clm_comp (ContinuousMap.toLp (E := ℂ) 2 μ ℂ)

end

end Lightlike.HarmonicAnalysis

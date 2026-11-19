import Lightlike.HarmonicAnalysis.ConvolutionOperator

/-!
# Integral operators with continuous kernels on `L²` of a compact group

For a continuous kernel `k : C(G × G, ℂ)` the operator `(T_k ψ)(x) = ∫ k(x, y) ψ(y) dμ(y)` on `L²(G, μ)`,
built as in `ConvolutionOperator` without integrals on `G × G`. The map `k ↦ T_k` is a bounded linear map
(`kerOpL`), and for a pure tensor `k = a ⊗ b` the operator is rank one. Together with Stone–Weierstrass on
`G × G` this gives the adjoint formula `(T_k)* = T_{k†}`, `k†(x, y) = conj k(y, x)`, without Fubini on the
product (which needs second countability).

Supporting lemmas for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The kernel `x ↦ (y ↦ conj k(x, y))` of a continuous kernel `k`. -/
def kerCurry (k : C(G × G, ℂ)) : C(G, C(G, ℂ)) :=
  ContinuousMap.curry ⟨fun p : G × G => starRingEnd ℂ (k p), by fun_prop⟩

lemma kerCurry_apply (k : C(G × G, ℂ)) (x y : G) : kerCurry k x y = starRingEnd ℂ (k (x, y)) := rfl

/-- The adjoint kernel `k†(x, y) = conj k(y, x)`. -/
def kerDagger (k : C(G × G, ℂ)) : C(G × G, ℂ) :=
  ⟨fun p => starRingEnd ℂ (k (p.2, p.1)), by fun_prop⟩

lemma kerDagger_apply (k : C(G × G, ℂ)) (x y : G) :
    kerDagger k (x, y) = starRingEnd ℂ (k (y, x)) := rfl

/-- The operator of the kernel `k`, as a map into continuous functions. -/
def kerToC (k : C(G × G, ℂ)) : Lp ℂ 2 μ →L[ℂ] C(G, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟨fun x => inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kerCurry k x)) ψ, by
        have hk : Continuous fun x => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kerCurry k x) :=
          (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp (kerCurry k).continuous
        exact hk.inner continuous_const⟩
      map_add' := fun ψ χ => by ext x; simp [inner_add_right]
      map_smul' := fun c ψ => by ext x; simp [inner_smul_right] }
    (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kerCurry k‖)
    (fun ψ => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
      calc ‖inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kerCurry k x)) ψ‖
          ≤ ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kerCurry k x)‖ * ‖ψ‖ := norm_inner_le_norm _ _
        _ ≤ (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kerCurry k‖) * ‖ψ‖ := by
            gcongr
            calc ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kerCurry k x)‖
                ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kerCurry k x‖ :=
                  (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).le_opNorm _
              _ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kerCurry k‖ := by
                  gcongr; exact (kerCurry k).norm_coe_le_norm x)

lemma kerToC_apply (k : C(G × G, ℂ)) (ψ : Lp ℂ 2 μ) (x : G) :
    kerToC μ k ψ x = inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kerCurry k x)) ψ := rfl

/-- The integral operator of a continuous kernel on `L²(G, μ)`. -/
def kerOp (k : C(G × G, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).comp (kerToC μ k)

/-- For `k = a ⊗ b` the operator is the rank-one operator `ψ ↦ ⟪conj b, ψ⟫ • a`. -/
lemma kerOp_tensor (a b : C(G, ℂ)) (ψ : Lp ℂ 2 μ) :
    kerOp μ (⟨fun p => a p.1 * b p.2, by fun_prop⟩ : C(G × G, ℂ)) ψ =
      inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (ContinuousMap.mk (fun y => starRingEnd ℂ (b y))
        (by fun_prop))) ψ • ContinuousMap.toLp (E := ℂ) 2 μ ℂ a := by
  rw [← map_smul]
  show ContinuousMap.toLp (E := ℂ) 2 μ ℂ _ = ContinuousMap.toLp (E := ℂ) 2 μ ℂ _
  congr 1
  ext x
  have h : kerCurry (⟨fun p => a p.1 * b p.2, by fun_prop⟩ : C(G × G, ℂ)) x =
      (starRingEnd ℂ (a x)) • (ContinuousMap.mk (fun y => starRingEnd ℂ (b y)) (by fun_prop) : C(G, ℂ)) := by
    ext y
    simp [kerCurry_apply, map_mul]
  change inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kerCurry _ x)) ψ = _
  rw [h, map_smul, inner_smul_left]
  simp [mul_comm]

end

end Lightlike.HarmonicAnalysis

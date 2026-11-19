import Lightlike.HarmonicAnalysis.KernelAdjoint

/-!
# Left translation on `L²` of a compact group

The left regular representation `(L_s ψ)(x) = ψ(s⁻¹ x)` on `L²(G, μ)` is by isometries (Haar measure is
left invariant). It transports a kernel operator to the kernel operator of the translated kernel:
`L_s T_k = T_{k_s} L_s`, `k_s(x, y) = k(s⁻¹ x, s⁻¹ y)`, proved on pure tensors and extended by density.
For the kernel `φ(y⁻¹ x)` of the convolution operator the translated kernel is the kernel itself, so
`K_φ` commutes with left translations and its eigenspaces are left invariant.

Supporting lemmas for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The left translation `ψ ↦ ψ(s⁻¹ ·)` on `L²`, an isometry. -/
def leftTr (s : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => s⁻¹ * x) (measurePreserving_mul_left μ s⁻¹)

/-- Left translation of a continuous function. -/
def trC (s : G) (a : C(G, ℂ)) : C(G, ℂ) := a.comp ⟨fun x => s⁻¹ * x, by fun_prop⟩

lemma trC_apply (s : G) (a : C(G, ℂ)) (x : G) : trC s a x = a (s⁻¹ * x) := rfl

lemma leftTr_toLp (s : G) (a : C(G, ℂ)) :
    leftTr μ s (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a) = ContinuousMap.toLp (E := ℂ) 2 μ ℂ (trC s a) := by
  refine Lp.ext ?_
  have h1 := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a)
    (measurePreserving_mul_left μ s⁻¹)
  have h2 := (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) a)
  filter_upwards [h1, h2, ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (trC s a)]
    with x hx1 hx2 hx3
  rw [hx3]
  exact hx1.trans hx2

/-- The translation of a kernel. -/
def shiftK (s : G) (k : C(G × G, ℂ)) : C(G × G, ℂ) :=
  k.comp ⟨fun p => (s⁻¹ * p.1, s⁻¹ * p.2), by fun_prop⟩

lemma shiftK_apply (s : G) (k : C(G × G, ℂ)) (x y : G) : shiftK s k (x, y) = k (s⁻¹ * x, s⁻¹ * y) := rfl

/-- Translation of kernels, as a bounded linear map. -/
def shiftL (s : G) : C(G × G, ℂ) →L[ℂ] C(G × G, ℂ) :=
  LinearMap.mkContinuous
    { toFun := shiftK s, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    1 (fun k => by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun p => ?_
      exact k.norm_coe_le_norm (s⁻¹ * p.1, s⁻¹ * p.2))

lemma shiftL_apply (s : G) (k : C(G × G, ℂ)) : shiftL s k = shiftK s k := rfl

lemma shiftK_tens (s : G) (a b : C(G, ℂ)) : shiftK s (tens a b) = tens (trC s a) (trC s b) := rfl

lemma trC_star (s : G) (a : C(G, ℂ)) : trC s (star a) = star (trC s a) := rfl

/-- On pure tensors: `L_s T_{a ⊗ b} = T_{(L_s a) ⊗ (L_s b)} L_s`. -/
lemma leftTr_kerOp_tens (s : G) (a b : C(G, ℂ)) (ψ : Lp ℂ 2 μ) :
    leftTr μ s (kerOp μ (tens a b) ψ) = kerOp μ (shiftK s (tens a b)) (leftTr μ s ψ) := by
  rw [shiftK_tens, kerOp_tens, kerOp_tens, map_smul, leftTr_toLp, ← trC_star s b, ← leftTr_toLp μ s (star b)]
  rw [LinearIsometry.inner_map_map]

/-- **Commutation with left translations.** `L_s T_k = T_{k_s} L_s`. -/
theorem leftTr_comp_kerOp (s : G) (k : C(G × G, ℂ)) :
    (leftTr μ s).toContinuousLinearMap.comp (kerOp μ k) =
      (kerOp μ (shiftK s k)).comp (leftTr μ s).toContinuousLinearMap := by
  let A : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    ContinuousLinearMap.compL ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ) (Lp ℂ 2 μ) (leftTr μ s).toContinuousLinearMap
  let B : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    (ContinuousLinearMap.compL ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ) (Lp ℂ 2 μ)).flip (leftTr μ s).toContinuousLinearMap
  have hF : A.comp (kerOpL μ) = B.comp ((kerOpL μ).comp (shiftL s)) := by
    refine ContinuousLinearMap.ext_on dense_tensSpan ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    refine ContinuousLinearMap.ext fun ψ => ?_
    exact leftTr_kerOp_tens μ s a b ψ
  exact congrArg (fun F => F k) hF

end

end Lightlike.HarmonicAnalysis

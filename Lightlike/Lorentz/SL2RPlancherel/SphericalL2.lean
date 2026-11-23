import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.SqrtWeight

/-!
# The spherical Plancherel isometry `L²(1, ∞) → L²(0, ∞)` for `SL(2,ℝ)`

The map `F ↦ √(ρ tanh πρ) f̂(ρ) / (2π)` (`sphL2fun`) preserves the `L²` norm from
`C_c^∞(ℝ)` restricted to `(1, ∞)` (the K-biinvariant functions on `SL(2,ℝ)`, written in the
variable `v = cosh r`) to `L²(0, ∞)`. We extend it by density to a linear isometry
`sphericalL2 : L²(Ioi 1) →ₗᵢ[ℂ] L²(Ioi 0)` (milestone HA3, spherical Plancherel formula with
density `ρ tanh(πρ)`).
-/

open MeasureTheory Set Real
open scoped ContDiff ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The `ℂ`-subspace of smooth compactly supported functions `ℝ → ℂ`. -/
def smoothCS : Submodule ℂ (ℝ → ℂ) where
  carrier := {F | ContDiff ℝ ∞ F ∧ HasCompactSupport F}
  add_mem' := fun {_ _} hF hG => ⟨hF.1.add hG.1, hF.2.add hG.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hF => ⟨hF.1.const_smul c, hF.2.smul_left⟩

theorem mem_smoothCS {F : ℝ → ℂ} : F ∈ smoothCS ↔ ContDiff ℝ ∞ F ∧ HasCompactSupport F :=
  Iff.rfl

/-- A smooth compactly supported function is in `L²(Ioi 1)`. -/
theorem memLp_restrict_Ioi (F : smoothCS) :
    MemLp (F : ℝ → ℂ) 2 (volume.restrict (Ioi (1 : ℝ))) :=
  (F.2.1.continuous.memLp_of_hasCompactSupport (μ := volume.restrict (Ioi (1 : ℝ))) F.2.2)

/-- The embedding of test functions into `L²(1, ∞)`. -/
def sphE : smoothCS →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ))) where
  toFun F := (memLp_restrict_Ioi F).toLp F
  map_add' F G := (MemLp.toLp_add (memLp_restrict_Ioi F) (memLp_restrict_Ioi G)).symm ▸ rfl
  map_smul' c F := by
    exact MemLp.toLp_const_smul c (memLp_restrict_Ioi F)

/-- Squares: norm of the `L²` class in terms of the integral. -/
theorem norm_toLp_two {μ : Measure ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = (∫ a, ‖f a‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

/-- The squared-root-weighted transform of a test function, as an element of `L²(0, ∞)`. -/
def sphF : smoothCS →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun F := (memLp_sphL2fun F F.2.1 F.2.2).toLp (sphL2fun F)
  map_add' F G := by
    have h : sphL2fun ((F + G : smoothCS) : ℝ → ℂ) = sphL2fun F + sphL2fun G := by
      funext ρ
      simp only [sphL2fun, Pi.add_apply]
      rw [← mul_add, ← sphTransformH_add F.2.1 F.2.2 G.2.1 G.2.2 ρ]
      rfl
    rw [← MemLp.toLp_add (memLp_sphL2fun F F.2.1 F.2.2) (memLp_sphL2fun G G.2.1 G.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : sphL2fun ((c • F : smoothCS) : ℝ → ℂ) = c • sphL2fun F := by
      funext ρ
      simp only [sphL2fun, Pi.smul_apply, smul_eq_mul]
      change ((_ : ℝ) : ℂ) * sphTransformH (c • (F : ℝ → ℂ)) ρ = _
      rw [sphTransformH_smul]
      ring
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_sphL2fun F F.2.1 F.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

/-- The isometry property on test functions. -/
theorem norm_sphF (F : smoothCS) : ‖sphF F‖ = ‖sphE F‖ := by
  have h1 : sphF F = (memLp_sphL2fun F F.2.1 F.2.2).toLp (sphL2fun F) := rfl
  have h2 : sphE F = (memLp_restrict_Ioi F).toLp F := rfl
  rw [h1, h2, norm_toLp_two, norm_toLp_two, integral_norm_sq_sphL2fun F F.2.1 F.2.2]

/-- Test functions are dense in `L²(1, ∞)`. -/
theorem denseRange_sphE : DenseRange sphE := by
  have hd := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℂ)
    (μ := volume.restrict (Ioi (1 : ℝ))) (p := 2) (by norm_num)
  refine hd.mono ?_
  rintro f ⟨g, hfg, hgc, hgs⟩
  refine ⟨⟨g, hgs, hgc⟩, ?_⟩
  have hg := memLp_restrict_Ioi ⟨g, hgs, hgc⟩
  show hg.toLp g = f
  rw [← Lp.toLp_coeFn f (Lp.memLp f)]
  exact MemLp.toLp_congr _ _ hfg.symm

/-- **Spherical Plancherel isometry for `SL(2,ℝ)`**: the extension of
`F ↦ √(ρ tanh πρ) f̂(ρ)/(2π)` to a linear isometry `L²(1, ∞) → L²(0, ∞)`. -/
def sphericalL2 : Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ))) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  LinearMap.extendOfIsometry sphF denseRange_sphE norm_sphF

/-- On test functions, `sphericalL2` is the weighted spherical transform. -/
theorem sphericalL2_apply_test (F : smoothCS) :
    sphericalL2 (sphE F) = sphF F :=
  LinearMap.extendOfIsometry_eq sphF denseRange_sphE norm_sphF F

/-- Plancherel identity in `L²`: `‖sphericalL2 f‖ = ‖f‖`. -/
theorem norm_sphericalL2 (f : Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))) :
    ‖sphericalL2 f‖ = ‖f‖ :=
  sphericalL2.norm_map f

/-- Polarised Plancherel identity: `sphericalL2` preserves the `L²` inner product. -/
theorem inner_sphericalL2 (f g : Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))) :
    inner ℂ (sphericalL2 f) (sphericalL2 g) = inner ℂ f g :=
  sphericalL2.inner_map_map f g

theorem injective_sphericalL2 : Function.Injective sphericalL2 :=
  sphericalL2.injective

/-- The range of the spherical Plancherel map is closed in `L²(0, ∞)`. -/
theorem isClosed_range_sphericalL2 : IsClosed (Set.range sphericalL2) :=
  sphericalL2.isometry.isClosedEmbedding.isClosed_range

/-- On a test function, the `L²` class of `sphericalL2` is the function `sphL2fun`
(`√(ρ tanh πρ) f̂(ρ)/(2π)`) almost everywhere on `(0, ∞)`. -/
theorem sphericalL2_apply_test_ae (F : smoothCS) :
    (sphericalL2 (sphE F) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      sphL2fun (F : ℝ → ℂ) := by
  rw [sphericalL2_apply_test]
  exact MemLp.coeFn_toLp (memLp_sphL2fun F F.2.1 F.2.2)

end Lightlike.Lorentz.SL2RPlancherel

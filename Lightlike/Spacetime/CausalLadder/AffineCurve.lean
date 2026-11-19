import Lightlike.Spacetime.Causal.CurveOps

/-!
# Affine reparametrisation of a curve with velocity in a cone

If `σ` has its velocity in `P` on `[α, β]`, with `P` stable under positive multiples (the future causal cone is), then
`u ↦ σ (α + u (β - α))` has its velocity in `P` on `[0, 1]`. Used to bring the limit arcs of the limit-curve theorem
(task `T-GE2-P20`) to unit parameter length.

Supporting lemma for the limit-curve theorem; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {P : ∀ x : M, TangentSpace I x → Prop}

omit [IsManifold I ∞ M] in
/-- **Affine reparametrisation to `[0, 1]`**: if `σ` has its velocity in `P` on `[α, β]`, `α < β`, and `P` is stable
under positive multiples, then `u ↦ σ (α + u (β - α))` has its velocity in `P` on `[0, 1]`. -/
theorem IsCurveWith.affine {σ : ℝ → M} {α β : ℝ}
    (hP : ∀ (x : M) (v : TangentSpace I x) (c : ℝ), 0 < c → P x v → P x (c • v))
    (h : IsCurveWith (I := I) P σ (Icc α β)) (hab : α < β) :
    IsCurveWith (I := I) P (fun u => σ (α + u * (β - α))) (Icc 0 1) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = β - α := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun u => α + u * c := ⟨_, rfl⟩
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, f u ∈ Icc α β := fun u hu => by
    rw [hf]; simp only; constructor <;> nlinarith [hu.1, hu.2]
  have hfcont : Continuous f := by rw [hf]; fun_prop
  rw [← hc]
  have hτ : (fun u => σ (α + u * c)) = σ ∘ f := by rw [hf]; rfl
  rw [hτ]
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro u hu
    obtain ⟨K, U, hU, hm, hl⟩ := h.lipschitz (f u) (hmem u hu)
    refine ⟨K * c.toNNReal, f ⁻¹' U, ?_, fun s hs => hm hs, ?_⟩
    · refine hfcont.continuousWithinAt.preimage_mem_nhdsWithin' ?_
      refine nhdsWithin_mono _ ?_ hU
      rintro _ ⟨s, hs, rfl⟩
      exact hmem s hs
    · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have := hl.dist_le_mul (f x) hx (f y) hy
      have hd : dist (f x) (f y) = c * dist x y := by
        rw [hf]; simp only [Real.dist_eq]
        rw [show α + x * c - (α + y * c) = (x - y) * c by ring, abs_mul, abs_of_pos hc0]; ring
      calc dist (((extChartAt I (σ (f u))) ∘ (σ ∘ f)) x) (((extChartAt I (σ (f u))) ∘ (σ ∘ f)) y)
          = dist (((extChartAt I (σ (f u))) ∘ σ) (f x)) (((extChartAt I (σ (f u))) ∘ σ) (f y)) := rfl
        _ ≤ K * dist (f x) (f y) := this
        _ = ↑(K * c.toNNReal) * dist x y := by
            rw [hd]; push_cast; rw [Real.coe_toNNReal _ hc0.le]; ring
  · have hqmp : QuasiMeasurePreserving f volume volume := by
      have h1 : QuasiMeasurePreserving (fun u : ℝ => u * c) volume volume := by
        refine ⟨by fun_prop, ?_⟩
        rw [Real.map_volume_mul_right hc0.ne']
        intro S hS
        rw [Measure.smul_apply, hS, smul_zero]
      have h2 : MeasurePreserving (fun u : ℝ => α + u) volume volume := measurePreserving_add_left volume α
      have := h2.quasiMeasurePreserving.comp h1
      rw [hf]
      exact this
    have h1 := hqmp.ae ((ae_restrict_iff' measurableSet_Icc).1 h.ae_velocity)
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h1] with u hu h2
    obtain ⟨h3, h4⟩ := h2 (hmem u hu)
    have hun : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) u :=
      (uniqueDiffOn_Icc zero_lt_one u hu).uniqueMDiffWithinAt
    have hfd : HasFDerivWithinAt f (c • ContinuousLinearMap.id ℝ ℝ) (Icc (0 : ℝ) 1) u := by
      have this : HasFDerivWithinAt (fun x : ℝ => α + c • x) (c • ContinuousLinearMap.id ℝ ℝ) (Icc (0 : ℝ) 1) u :=
        ((hasFDerivWithinAt_id u (Icc (0 : ℝ) 1)).const_smul c).const_add α
      convert this using 1
      rw [hf]; funext x; simp [mul_comm]
    have hτ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f (Icc (0 : ℝ) 1) u := by
      rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact hfd.differentiableWithinAt
    have hmaps : Icc (0 : ℝ) 1 ⊆ f ⁻¹' Icc α β := fun s hs => hmem s hs
    refine ⟨h3.comp u hτ hmaps, ?_⟩
    have hc' := mfderivWithin_comp u h3 hτ hmaps hun
    have hd : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f (Icc (0 : ℝ) 1) u 1 = c := by
      rw [mfderivWithin_eq_fderivWithin, hfd.fderivWithin (uniqueDiffOn_Icc zero_lt_one u hu)]
      show (c • ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) = c
      simp
    have hv : velocity I (σ ∘ f) (Icc (0 : ℝ) 1) u = c • velocity I σ (Icc α β) (f u) := by
      unfold velocity
      rw [hc']
      show (mfderivWithin 𝓘(ℝ, ℝ) I σ (Icc α β) (f u)) ((mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f (Icc (0 : ℝ) 1) u) 1)
        = c • (mfderivWithin 𝓘(ℝ, ℝ) I σ (Icc α β) (f u)) 1
      rw [hd]
      have e : (c : ℝ) = c • (1 : ℝ) := by rw [smul_eq_mul, mul_one]
      exact (congrArg (fun z => (mfderivWithin 𝓘(ℝ, ℝ) I σ (Icc α β) (f u)) z) e).trans
        ((mfderivWithin 𝓘(ℝ, ℝ) I σ (Icc α β) (f u)).map_smul c (1 : ℝ))
    rw [hv]
    exact hP _ _ c hc0 h4

end Lightlike.Causal

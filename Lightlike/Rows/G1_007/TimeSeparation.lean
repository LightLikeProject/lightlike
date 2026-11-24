import Lightlike.Rows.G1_007.LorentzLength

/-!
# Time separation (row G1-007)

The Lorentzian length (`Causal.lorentzLength`) does not change when the parameter of a curve is translated
(`Causal.lorentzLength_shift`); this is the step that lets two curves be glued end to end, for the reverse triangle
inequality of the time separation `d(p, q)`.

* `Causal.velocity_shift`: the velocity of `t ↦ γ (t + k)` is the velocity of `γ` at `t + k`;
* `Causal.lorentzLength_shift`: `L(t ↦ γ (t + k)) on [a - k, b - k] = L(γ) on [a, b]`.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.2 (the length of a timelike curve is unchanged by reparametrisation); comparison with
  the page pending (not read).
-/

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} (g : LorentzianMetric I M n)

omit [IsManifold I ∞ M] in
/-- The velocity of a translated curve: where `γ` is differentiable within `[a, b]` at `t + k`, the curve
`s ↦ γ (s + k)` has the same velocity at `t` within `[a - k, b - k]`. -/
theorem velocity_shift {γ : ℝ → M} {a b k t : ℝ} (hab : a < b) (ht : t ∈ Icc (a - k) (b - k))
    (hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Icc a b) (t + k)) :
    velocity I (fun s => γ (s + k)) (Icc (a - k) (b - k)) t = velocity I γ (Icc a b) (t + k) := by
  have hmem : ∀ s, s ∈ Icc (a - k) (b - k) → s + k ∈ Icc a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (a - k) (b - k)) t :=
    (uniqueDiffOn_Icc (by linarith) t ht).uniqueMDiffWithinAt
  have hτ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + k) (Icc (a - k) (b - k)) t := by
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    exact differentiableWithinAt_id.add_const k
  have hmaps : Icc (a - k) (b - k) ⊆ (fun s : ℝ => s + k) ⁻¹' Icc a b := fun s hs => hmem s hs
  have hc := mfderivWithin_comp t hd hτ hmaps hu
  have hd1 : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + k) (Icc (a - k) (b - k)) t 1 = 1 := by
    rw [mfderivWithin_eq_fderivWithin]
    have : HasFDerivWithinAt (fun s : ℝ => s + k) (ContinuousLinearMap.id ℝ ℝ)
        (Icc (a - k) (b - k)) t := (hasFDerivWithinAt_id t _).add_const k
    rw [this.fderivWithin (uniqueDiffOn_Icc (by linarith) t ht)]
    rfl
  unfold velocity
  rw [show (fun s => γ (s + k)) = γ ∘ (fun s : ℝ => s + k) from rfl, hc]
  exact congrArg (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) (t + k)) hd1

/-- **The Lorentzian length is invariant under translation of the parameter.** -/
theorem lorentzLength_shift {P : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {a b : ℝ}
    (h : IsCurveWith (I := I) P γ (Icc a b)) (hab : a < b) (k : ℝ) :
    lorentzLength g (fun s => γ (s + k)) (a - k) (b - k) = lorentzLength g γ a b := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) k
  have hemb : MeasurableEmbedding (fun s : ℝ => s + k) := (Homeomorph.addRight k).measurableEmbedding
  have h1 : ∫⁻ t in (fun s : ℝ => s + k) ⁻¹' Icc a b, lorentzSpeed g γ (Icc a b) (t + k) =
      ∫⁻ t in Icc a b, lorentzSpeed g γ (Icc a b) t :=
    hmp.setLIntegral_comp_preimage_emb hemb (lorentzSpeed g γ (Icc a b)) (Icc a b)
  rw [show (fun s : ℝ => s + k) ⁻¹' Icc a b = Icc (a - k) (b - k) from by
    ext s; simp only [mem_preimage, mem_Icc]; constructor <;> intro hs <;> constructor <;> linarith [hs.1, hs.2]] at h1
  unfold lorentzLength
  rw [← h1]
  have h2 := (measurePreserving_add_right volume k).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Icc).1 h.ae_velocity)
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h2] with t ht h3
  obtain ⟨hd, -⟩ := h3 (show t + k ∈ Icc a b from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  unfold lorentzSpeed
  rw [velocity_shift hab ht hd]

end Causal

end Lightlike

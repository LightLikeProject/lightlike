import Mathlib.Analysis.Complex.Hadamard

/-!
# The strip and a uniqueness principle for KMS functions

Row G1-053 (the KMS condition in infinite dimensions). The KMS condition of an infinite-dimensional
system is stated through a function on the closed strip `0 ≤ Im z ≤ β`, bounded and continuous on the
strip and analytic inside it (Bratteli-Robinson, Definition 5.3.1; Panangaden, Definition 5.8).  Here
we prove the analytic fact that makes this definition usable: such a function that vanishes on the real
line vanishes on the whole closed strip (`eq_zero_of_real_zero`).  The proof is Hadamard's three-lines
theorem (`Complex.HadamardThreeLines`) on the strip turned by `z = i w`.
-/

open Complex Set Filter Topology

namespace Lightlike.OperatorAlgebras.KMSInfiniteDimensions

/-- The closed strip `0 ≤ Im z ≤ β`. -/
def strip (β : ℝ) : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ β}

/-- The open strip `0 < Im z < β`. -/
def openStrip (β : ℝ) : Set ℂ := {z | 0 < z.im ∧ z.im < β}

lemma I_mul_im (w : ℂ) : (I * w).im = w.re := by simp

lemma I_mul_neg_I_mul (z : ℂ) : I * (-I * z) = z := by
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

/-- **A bounded function on the strip, analytic inside and zero on the real line, is zero on the strip.**
Hadamard's three-lines theorem bounds it inside by `0 ^ (1 - s) * C ^ s = 0`; the upper edge follows by
continuity. -/
theorem eq_zero_of_real_zero {β : ℝ} (hβ : 0 < β) {F : ℂ → ℂ}
    (hc : ContinuousOn F (strip β)) (hd : DifferentiableOn ℂ F (openStrip β))
    (hb : ∃ C, ∀ z ∈ strip β, ‖F z‖ ≤ C) (h0 : ∀ t : ℝ, F t = 0) :
    ∀ z ∈ strip β, F z = 0 := by
  obtain ⟨C, hC⟩ := hb
  set f : ℂ → ℂ := fun w => F (I * w) with hf
  have hmapsC : MapsTo (fun w : ℂ => I * w) (re ⁻¹' Icc (0 : ℝ) β) (strip β) := by
    intro w hw
    simp only [strip, mem_ofPred_eq, I_mul_im]
    exact hw
  have hmapsO : MapsTo (fun w : ℂ => I * w) (re ⁻¹' Ioo (0 : ℝ) β) (openStrip β) := by
    intro w hw
    simp only [openStrip, mem_ofPred_eq, I_mul_im]
    exact hw
  have hmul : Differentiable ℂ (fun w : ℂ => I * w) := differentiable_id.const_mul I
  have hdiff : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip 0 β) := by
    refine ⟨hd.comp hmul.differentiableOn hmapsO, ?_⟩
    have hcl : closure (re ⁻¹' Ioo (0 : ℝ) β) ⊆ re ⁻¹' Icc (0 : ℝ) β :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
    exact (hc.comp hmul.continuous.continuousOn hmapsC).mono hcl
  have hbdd : BddAbove ((norm ∘ f) '' HadamardThreeLines.verticalClosedStrip 0 β) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hC _ (hmapsC hw)
  have hbot : ∀ w ∈ re ⁻¹' {(0 : ℝ)}, ‖f w‖ ≤ 0 := by
    intro w hw
    have hw' : w.re = 0 := hw
    have : I * w = (((I * w).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hw']
    rw [hf]
    simp only
    rw [this, h0]
    simp
  have htop : ∀ w ∈ re ⁻¹' {β}, ‖f w‖ ≤ C := by
    intro w hw
    have hw' : w.re = β := hw
    exact hC _ (hmapsC ⟨hw'.symm ▸ hβ.le, hw'.le⟩)
  -- zero on the half-open strip
  have hlow : ∀ z ∈ strip β, z.im < β → F z = 0 := by
    intro z hz hlt
    rcases hz.1.eq_or_lt with h | h
    · have : z = ((z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [← h]
      rw [this, h0]
    · have hmem : (-I * z) ∈ HadamardThreeLines.verticalClosedStrip 0 β := by
        simp only [HadamardThreeLines.verticalClosedStrip, mem_preimage, mem_Icc]
        have : (-I * z).re = z.im := by simp
        rw [this]; exact ⟨hz.1, hz.2⟩
      have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hβ hmem hdiff hbdd hbot htop
      have hre : (-I * z).re = z.im := by simp
      simp only [hre, sub_zero] at h3
      have hs : 0 < 1 - z.im / β := by
        rw [sub_pos, div_lt_one hβ]; exact hlt
      rw [Real.zero_rpow hs.ne', zero_mul] at h3
      have : f (-I * z) = F z := by
        rw [hf]; simp only; rw [I_mul_neg_I_mul]
      rw [this] at h3
      exact norm_le_zero_iff.mp h3
  intro z hz
  rcases hz.2.eq_or_lt with h | h
  · -- upper edge: limit of interior points
    have hT : Tendsto (fun ε : ℝ => z - I * ε) (𝓝[>] 0) (𝓝[strip β] z) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hct : Continuous (fun ε : ℝ => z - I * ε) := by fun_prop
        have := hct.tendsto 0
        simp only [Complex.ofReal_zero, mul_zero, sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT hβ] with ε hε
        simp only [strip, mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        constructor <;> nlinarith [hε.1, hε.2]
    have h1 : Tendsto (F ∘ fun ε : ℝ => z - I * ε) (𝓝[>] 0) (𝓝 (F z)) :=
      (hc z hz).tendsto.comp hT
    have h2 : (F ∘ fun ε : ℝ => z - I * ε) =ᶠ[𝓝[>] 0] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsGT hβ] with ε hε
      have hm : (z - I * ε) ∈ strip β := by
        simp only [strip, mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        constructor <;> nlinarith [hε.1, hε.2, hz.1, h]
      refine hlow _ hm ?_
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      nlinarith [hε.1, h]
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2.symm)
  · exact hlow z hz h

end Lightlike.OperatorAlgebras.KMSInfiniteDimensions

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.I_mul_im := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.I_mul_im
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.I_mul_neg_I_mul := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.I_mul_neg_I_mul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.eq_zero_of_real_zero := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.eq_zero_of_real_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.openStrip := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.openStrip
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.strip := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.strip

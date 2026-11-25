import Lightlike.OperatorAlgebras.KMSInfiniteDimensions.KMSState
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Uniqueness of the strip function from its values on the real line

For the KMS condition in the strip form (`IsKMSState`) the function `F_{A,B}` is part of the data. To read off
consequences of the condition (for instance the relation between the weights of a state, see the sequel) one needs that
`F` is determined by its restriction to the real line.

* `removable_line`: a function continuous on the strip `-β < Im z < β` and holomorphic off the real line is holomorphic
  (Morera's theorem, via `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn` and a splitting of
  rectangles that cross the real line);
* `eqOn_zero_of_eqOn_real`: a function continuous on the closed strip `0 ≤ Im z ≤ β`, holomorphic on the open strip and
  vanishing on `ℝ` vanishes (Schwarz reflection `z ↦ -conj (D (conj z))` plus the identity theorem);
* `eqOn_of_eqOn_real`: two such functions agreeing on `ℝ` agree on the closed strip.

No boundedness is needed.
-/

namespace Lightlike.Rows.G1_053

open Complex Set Topology Filter MeasureTheory ComplexConjugate
open scoped Interval
open Lightlike.OperatorAlgebras.GibbsKMS

/-- The boundary integral of `f` over the rectangle with opposite corners `z`, `w` (the expression of the
Cauchy-Goursat theorem of Mathlib). -/
noncomputable def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, f (re z + y * I))

/-- Vertical segments of a rectangle on which `f` is continuous are interval integrable. -/
lemma vert_intervalIntegrable {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (Rectangle z w)) {a : ℝ}
    (ha : a ∈ [[z.re, w.re]]) {p q : ℝ} (hp : p ∈ [[z.im, w.im]]) (hq : q ∈ [[z.im, w.im]]) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable
  have h1 : ContinuousOn (fun y : ℝ => f (a + y * I)) [[z.im, w.im]] := by
    refine hf.comp (by fun_prop) ?_
    intro y hy
    exact mem_reProdIm.2 ⟨by simpa using ha, by simpa using hy⟩
  exact h1.mono (uIcc_subset_uIcc hp hq)

/-- The boundary integral splits along the real line. -/
lemma rectInt_split {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (Rectangle z w))
    (h0 : (0 : ℝ) ∈ [[z.im, w.im]]) :
    rectInt f z w = rectInt f z (w.re : ℂ) + rectInt f (z.re : ℂ) w := by
  have hzr : z.re ∈ [[z.re, w.re]] := left_mem_uIcc
  have hwr : w.re ∈ [[z.re, w.re]] := right_mem_uIcc
  have hzi : z.im ∈ [[z.im, w.im]] := left_mem_uIcc
  have hwi : w.im ∈ [[z.im, w.im]] := right_mem_uIcc
  have e1 : ∫ y : ℝ in z.im..w.im, f (w.re + y * I) =
      (∫ y : ℝ in z.im..(0:ℝ), f (w.re + y * I)) + ∫ y : ℝ in (0:ℝ)..w.im, f (w.re + y * I) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (vert_intervalIntegrable hf hwr hzi h0) (vert_intervalIntegrable hf hwr h0 hwi)).symm
  have e2 : ∫ y : ℝ in z.im..w.im, f (z.re + y * I) =
      (∫ y : ℝ in z.im..(0:ℝ), f (z.re + y * I)) + ∫ y : ℝ in (0:ℝ)..w.im, f (z.re + y * I) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (vert_intervalIntegrable hf hzr hzi h0) (vert_intervalIntegrable hf hzr h0 hwi)).symm
  unfold rectInt
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [e1, e2, smul_add, smul_add]
  abel

/-- Morera's theorem across the real line: a function continuous on `-β < Im z < β` and holomorphic on both open
half-strips is holomorphic. -/
theorem removable_line {E : ℂ → ℂ} {β : ℝ}
    (hc : ContinuousOn E {z | -β < z.im ∧ z.im < β})
    (hu : DifferentiableOn ℂ E {z | 0 < z.im ∧ z.im < β})
    (hl : DifferentiableOn ℂ E {z | -β < z.im ∧ z.im < 0}) :
    DifferentiableOn ℂ E {z | -β < z.im ∧ z.im < β} := by
  set U : Set ℂ := {z | -β < z.im ∧ z.im < β} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  -- the same-sign case
  have half : ∀ z w : ℂ, Rectangle z w ⊆ U → ((0 ≤ z.im ∧ 0 ≤ w.im) ∨ (z.im ≤ 0 ∧ w.im ≤ 0)) →
      rectInt E z w = 0 := by
    intro z w hzw h
    apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    · exact hc.mono hzw
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine hu.mono ?_
        intro p hp
        have hp' := mem_reProdIm.1 hp
        have hpR : p ∈ Rectangle z w :=
          mem_reProdIm.2 ⟨Ioo_subset_Icc_self hp'.1, Ioo_subset_Icc_self hp'.2⟩
        exact ⟨lt_of_le_of_lt (le_min h1 h2) hp'.2.1, (hzw hpR).2⟩
      · refine hl.mono ?_
        intro p hp
        have hp' := mem_reProdIm.1 hp
        have hpR : p ∈ Rectangle z w :=
          mem_reProdIm.2 ⟨Ioo_subset_Icc_self hp'.1, Ioo_subset_Icc_self hp'.2⟩
        exact ⟨(hzw hpR).1, lt_of_lt_of_le hp'.2.2 (max_le h1 h2)⟩
  rw [← isConservativeOn_and_continuousOn_iff_isDifferentiableOn hUopen]
  refine ⟨?_, hc⟩
  intro z w hzw
  have key : rectInt E z w = 0 := by
    by_cases hs : (0 ≤ z.im ∧ 0 ≤ w.im) ∨ (z.im ≤ 0 ∧ w.im ≤ 0)
    · exact half z w hzw hs
    · have h0 : (0:ℝ) ∈ [[z.im, w.im]] := by
        rw [mem_uIcc]
        by_contra hcon
        apply hs
        rcases le_total 0 z.im with h1 | h1
        · rcases le_total 0 w.im with h2 | h2
          · exact Or.inl ⟨h1, h2⟩
          · exfalso; apply hcon
            right; exact ⟨h2, h1⟩
        · rcases le_total 0 w.im with h2 | h2
          · exfalso; apply hcon
            left; exact ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
      have hs1 : Rectangle z (w.re : ℂ) ⊆ Rectangle z w := by
        intro p hp
        have h1 := (mem_reProdIm.1 hp).1
        have h2 := (mem_reProdIm.1 hp).2
        simp only [ofReal_re, ofReal_im] at h1 h2
        exact mem_reProdIm.2 ⟨h1, uIcc_subset_uIcc left_mem_uIcc h0 h2⟩
      have hs2 : Rectangle (z.re : ℂ) w ⊆ Rectangle z w := by
        intro p hp
        have h1 := (mem_reProdIm.1 hp).1
        have h2 := (mem_reProdIm.1 hp).2
        simp only [ofReal_re, ofReal_im] at h1 h2
        exact mem_reProdIm.2 ⟨h1, uIcc_subset_uIcc h0 right_mem_uIcc h2⟩
      have c1 : (0 ≤ z.im ∧ 0 ≤ ((w.re : ℂ)).im) ∨ (z.im ≤ 0 ∧ ((w.re : ℂ)).im ≤ 0) := by
        rcases le_total 0 z.im with h | h
        · exact Or.inl ⟨h, by simp⟩
        · exact Or.inr ⟨h, by simp⟩
      have c2 : (0 ≤ ((z.re : ℂ)).im ∧ 0 ≤ w.im) ∨ (((z.re : ℂ)).im ≤ 0 ∧ w.im ≤ 0) := by
        rcases le_total 0 w.im with h | h
        · exact Or.inl ⟨by simp, h⟩
        · exact Or.inr ⟨by simp, h⟩
      rw [rectInt_split (hc.mono hzw) h0, half _ _ (hs1.trans hzw) c1, half _ _ (hs2.trans hzw) c2,
        add_zero]
  have hsum := wedgeIntegral_add_wedgeIntegral_eq z w E
  have h2 : wedgeIntegral z w E + wedgeIntegral w z E = 0 := hsum.trans key
  exact eq_neg_of_add_eq_zero_left h2

/-- Schwarz reflection and the identity theorem: a function continuous on the closed strip `0 ≤ Im z ≤ β`,
holomorphic on the open strip and vanishing on the real line vanishes on the closed strip. -/
theorem eqOn_zero_of_eqOn_real {D : ℂ → ℂ} {β : ℝ} (hβ : 0 < β)
    (hc : ContinuousOn D (strip β)) (hd : DifferentiableOn ℂ D (openStrip β))
    (h0 : ∀ t : ℝ, D t = 0) : EqOn D 0 (strip β) := by
  classical
  set E : ℂ → ℂ := fun z => if 0 ≤ z.im then D z else -(conj (D (conj z))) with hE
  have hEu : ∀ z : ℂ, 0 ≤ z.im → E z = D z := fun z hz => by simp [hE, hz]
  have hEl : ∀ z : ℂ, z.im ≤ 0 → E z = -(conj (D (conj z))) := by
    intro z hz
    by_cases h : 0 ≤ z.im
    · have him : z.im = 0 := le_antisymm hz h
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
      have hcz : conj z = z := Complex.conj_eq_iff_im.2 him
      rw [hEu z h, hcz, hzr, h0 z.re]
      simp
    · simp [hE, h]
  have hUopen : IsOpen {z : ℂ | -β < z.im ∧ z.im < β} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hopenS : IsOpen (openStrip β) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  -- continuity
  have hs : ContinuousOn E (strip β) := hc.congr fun z hz => hEu z hz.1
  have ht : ContinuousOn E {z : ℂ | -β ≤ z.im ∧ z.im ≤ 0} := by
    have hmaps : MapsTo (conj : ℂ → ℂ) {z : ℂ | -β ≤ z.im ∧ z.im ≤ 0} (strip β) := by
      intro z hz
      simp only [strip, mem_ofPred_eq, Complex.conj_im]
      constructor <;> linarith [hz.1, hz.2]
    have := (Complex.continuous_conj.comp_continuousOn (hc.comp Complex.continuous_conj.continuousOn
      hmaps)).neg
    exact this.congr fun z hz => hEl z hz.2
  have hcl1 : IsClosed (strip β) :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const)
  have hcl2 : IsClosed {z : ℂ | -β ≤ z.im ∧ z.im ≤ 0} :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const)
  have hcont : ContinuousOn E {z : ℂ | -β < z.im ∧ z.im < β} := by
    refine (hs.union_of_isClosed ht hcl1 hcl2).mono ?_
    intro z hz
    rcases le_total 0 z.im with h | h
    · exact Or.inl ⟨h, hz.2.le⟩
    · exact Or.inr ⟨hz.1.le, h⟩
  have hdu : DifferentiableOn ℂ E {z : ℂ | 0 < z.im ∧ z.im < β} :=
    hd.congr fun z hz => hEu z hz.1.le
  have hdl : DifferentiableOn ℂ E {z : ℂ | -β < z.im ∧ z.im < 0} := by
    have hg : DifferentiableOn ℂ (fun z => -(conj (D (conj z)))) {z : ℂ | -β < z.im ∧ z.im < 0} := by
      intro z hz
      have hmem : conj z ∈ openStrip β := by
        simp only [openStrip, mem_ofPred_eq, Complex.conj_im]
        constructor <;> linarith [hz.1, hz.2]
      have h1 := (hd.differentiableAt (hopenS.mem_nhds hmem)).conj_conj
      rw [Complex.conj_conj] at h1
      exact h1.neg.differentiableWithinAt
    exact hg.congr fun z hz => hEl z hz.2.le
  have hdiff := removable_line hcont hdu hdl
  have han : AnalyticOnNhd ℂ E {z : ℂ | -β < z.im ∧ z.im < β} := hdiff.analyticOnNhd hUopen
  have hconv : Convex ℝ {z : ℂ | -β < z.im ∧ z.im < β} :=
    (convex_Ioo (-β) β).linear_preimage Complex.imLm
  have hmem0 : (0 : ℂ) ∈ {z : ℂ | -β < z.im ∧ z.im < β} := by
    simp only [mem_ofPred_eq, Complex.zero_im]
    constructor <;> linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), E z = 0 := by
    have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2
        ⟨(Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun t ht => by simpa using ht⟩
    refine ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t => ?_))
    show E (t : ℂ) = 0
    rw [hEu _ (by simp)]
    exact h0 t
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hconv.isPreconnected hmem0 hfreq
  -- from the half-open strip to the closed strip
  have hEq : EqOn D 0 {z : ℂ | 0 ≤ z.im ∧ z.im < β} := by
    intro z hz
    have := hzero (show z ∈ {z : ℂ | -β < z.im ∧ z.im < β} from ⟨by linarith [hz.1], hz.2⟩)
    rw [← hEu z hz.1]
    exact this
  refine hEq.of_subset_closure hc continuousOn_const (fun z hz => ⟨hz.1, hz.2.le⟩) ?_
  intro z hz
  have h1 : closure {z : ℂ | 0 ≤ z.im ∧ z.im < β} = {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β} := by
    have e : {z : ℂ | 0 ≤ z.im ∧ z.im < β} = Complex.im ⁻¹' Ico 0 β := rfl
    have e2 : {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β} = Complex.im ⁻¹' Icc 0 β := rfl
    rw [e, e2, ← Complex.isOpenMap_im.preimage_closure_eq_closure_preimage Complex.continuous_im,
      closure_Ico hβ.ne]
  rw [h1]
  exact hz

/-- Two functions continuous on the closed strip `0 ≤ Im z ≤ β`, holomorphic on the open strip and equal on the real
line are equal on the closed strip. -/
theorem eqOn_of_eqOn_real {F G : ℂ → ℂ} {β : ℝ} (hβ : 0 < β)
    (hFc : ContinuousOn F (strip β)) (hGc : ContinuousOn G (strip β))
    (hFd : DifferentiableOn ℂ F (openStrip β)) (hGd : DifferentiableOn ℂ G (openStrip β))
    (h : ∀ t : ℝ, F t = G t) : EqOn F G (strip β) := by
  intro z hz
  have := eqOn_zero_of_eqOn_real hβ (hFc.sub hGc) (hFd.sub hGd) (fun t => by simp [h t]) hz
  simpa [sub_eq_zero] using this

end Lightlike.Rows.G1_053

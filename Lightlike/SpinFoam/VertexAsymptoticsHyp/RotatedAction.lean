import Lightlike.SpinFoam.VertexAsymptoticsHyp.CutAssemble
import Lightlike.SpinFoam.VertexAsymptoticsHyp.LogCut
import Lightlike.Asymptotics.Lorentzian.ActionSmooth

/-!
# The vertex action of rotated data splits as `2 j_k log f + R` (SF10, P2 defect, T5, part 1)

For the boundary data `rotSrc g k c` the chart action is `2 j_k · log (c · w_k) + R`, where `w_k` is
the overlap product of edge `k` for `g` and `R` is smooth at every point where the other edges are off
the cut and the chart is smooth.  This is the decomposition needed to apply `CutAssemble`.
Supporting lemmas only.
-/

open Complex
open scoped ContDiff Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Asymptotics.EPRL
open Lightlike.Lorentz (SL2C)

/-- The part of `triAction` that is smooth wherever the spinors are nonzero: the two norm terms. -/
noncomputable def triRest (k p : ℝ) (Z Z' : Spinor) : ℂ :=
  -(k : ℂ) * Complex.log (((‖Z‖ ^ 2 : ℝ) : ℂ) * ((‖Z'‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * (p : ℂ) * Complex.log (((‖Z'‖ ^ 2 : ℝ) : ℂ) / ((‖Z‖ ^ 2 : ℝ) : ℂ))

theorem triAction_eq_log_add_rest (k p : ℝ) (Z ξ Z' ξ' : Spinor) :
    triAction k p Z ξ Z' ξ' =
      ((2 * k : ℝ) : ℂ) * Complex.log (inner ℂ Z ξ * inner ℂ (jMap ξ') Z') + triRest k p Z Z' := by
  unfold triAction triRest; ring

/-- The triangle action with the source spinor rotated by `c`, as `2k log (c · P) + rest`. -/
theorem triAction_smul_eq (k p : ℝ) (c : ℂ) (Z ξ Z' ξ' : Spinor) :
    triAction k p Z (c • ξ) Z' ξ' =
      ((2 * k : ℝ) : ℂ) * Complex.log (c * (inner ℂ Z ξ * inner ℂ (jMap ξ') Z')) +
        triRest k p Z Z' := by
  rw [triAction_eq_log_add_rest, inner_smul_phase, mul_assoc]

/-- `triRest` is smooth where both spinors are nonzero. -/
theorem contDiffAt_triRest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k p : ℝ)
    {Zs Zt : E → Spinor} {a : E} (hs : ContDiffAt ℝ ∞ Zs a) (ht : ContDiffAt ℝ ∞ Zt a)
    (hZ : Zs a ≠ 0) (hZ' : Zt a ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => triRest k p (Zs y) (Zt y)) a := by
  unfold triRest
  have hz : 0 < ‖Zs a‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Zt a‖ := norm_pos_iff.mpr hZ'
  have hn1 : ContDiffAt ℝ ∞ (fun y => ‖Zs y‖) a := hs.norm ℝ hZ
  have hn2 : ContDiffAt ℝ ∞ (fun y => ‖Zt y‖) a := ht.norm ℝ hZ'
  have hsq1 : ContDiffAt ℝ ∞ (fun y => (((‖Zs y‖ ^ 2 : ℝ) : ℂ))) a :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp a (hn1.pow 2)
  have hsq2 : ContDiffAt ℝ ∞ (fun y => (((‖Zt y‖ ^ 2 : ℝ) : ℂ))) a :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp a (hn2.pow 2)
  have hslit1 : (((‖Zs a‖ ^ 2 : ℝ) : ℂ)) * (((‖Zt a‖ ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_mul]; exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hlog1 : ContDiffAt ℝ ∞ (fun y =>
      Complex.log (((‖Zs y‖ ^ 2 : ℝ) : ℂ) * ((‖Zt y‖ ^ 2 : ℝ) : ℂ))) a :=
    ContDiffAt.comp (g := Complex.log) (f := fun y =>
      ((‖Zs y‖ ^ 2 : ℝ) : ℂ) * ((‖Zt y‖ ^ 2 : ℝ) : ℂ)) a
      ((Complex.contDiffAt_log hslit1).restrict_scalars ℝ) (hsq1.mul hsq2)
  have hslit2 : (((‖Zt a‖ ^ 2 : ℝ) : ℂ)) / (((‖Zs a‖ ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_div]; exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hz0 : (((‖Zs a‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  have hq : ContDiffAt ℝ ∞ (fun y => (((‖Zt y‖ ^ 2 : ℝ) : ℂ)) / (((‖Zs y‖ ^ 2 : ℝ) : ℂ))) a := by
    simp only [div_eq_mul_inv]
    exact hsq2.mul (hsq1.inv hz0)
  have hlog2 : ContDiffAt ℝ ∞ (fun y =>
      Complex.log (((‖Zt y‖ ^ 2 : ℝ) : ℂ) / ((‖Zs y‖ ^ 2 : ℝ) : ℂ))) a :=
    ContDiffAt.comp (g := Complex.log) (f := fun y =>
      ((‖Zt y‖ ^ 2 : ℝ) : ℂ) / ((‖Zs y‖ ^ 2 : ℝ) : ℂ)) a
      ((Complex.contDiffAt_log hslit2).restrict_scalars ℝ) hq
  exact (contDiffAt_const.mul hlog1).add (contDiffAt_const.mul hlog2)

/-- Source spinor `Z = X_{src e}† z_e` of edge `e` at the chart point `x`. -/
noncomputable def edgeZs {n : ℕ} (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor))
    (e : Fin 10) (x : Fin n → ℝ) : Spinor :=
  spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e)

/-- Target spinor `Z' = X_{tgt e}† z_e` of edge `e` at the chart point `x`. -/
noncomputable def edgeZt {n : ℕ} (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor))
    (e : Fin 10) (x : Fin n → ℝ) : Spinor :=
  spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e)

/-- The overlap product `⟨Z,ξ⟩⟨Jξ',Z'⟩` of edge `e` for the boundary data `g`. -/
noncomputable def edgeOverlap {n : ℕ} (g : BdryData)
    (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)) (e : Fin 10) (x : Fin n → ℝ) : ℂ :=
  inner ℂ (edgeZs chart e x) (firstCol (g e 0)) *
    inner ℂ (jMap (firstCol (g e 1))) (edgeZt chart e x)

/-- The chart is smooth at `a` (entries of the five group elements and the ten spinors). -/
theorem contDiffAt_edgeZ {n : ℕ} {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)}
    {a : Fin n → ℝ}
    (hX : ∀ b i k, ContDiffAt ℝ ∞ (fun x => ((chart x).1 b : Matrix (Fin 2) (Fin 2) ℂ) i k) a)
    (hz : ∀ e, ContDiffAt ℝ ∞ (fun x => (chart x).2 e) a) (e : Fin 10) :
    ContDiffAt ℝ ∞ (edgeZs chart e) a ∧ ContDiffAt ℝ ∞ (edgeZt chart e) a := by
  have hM : ∀ b i k, ContDiffAt ℝ ∞
      (fun y => (((chart y).1 b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) i k) a := by
    intro b i k
    have := Complex.conjCLE.contDiff.contDiffAt.comp a (hX b k i)
    simpa [Function.comp_def, Matrix.conjTranspose_apply] using this
  exact ⟨contDiffAt_spinAct (hM _) (hz e), contDiffAt_spinAct (hM _) (hz e)⟩

/-- The overlap product of edge `e` is smooth at `a`. -/
theorem contDiffAt_edgeOverlap {n : ℕ} (g : BdryData)
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)} {a : Fin n → ℝ}
    (hX : ∀ b i k, ContDiffAt ℝ ∞ (fun x => ((chart x).1 b : Matrix (Fin 2) (Fin 2) ℂ) i k) a)
    (hz : ∀ e, ContDiffAt ℝ ∞ (fun x => (chart x).2 e) a) (e : Fin 10) :
    ContDiffAt ℝ ∞ (edgeOverlap g chart e) a := by
  obtain ⟨hs, ht⟩ := contDiffAt_edgeZ hX hz e
  have h1 : ContDiffAt ℝ ∞ (fun y => inner ℂ (edgeZs chart e y) (firstCol (g e 0))) a :=
    (contDiff_inner_left_spinor _).contDiffAt.comp a hs
  have h2 : ContDiffAt ℝ ∞ (fun y => inner ℂ (jMap (firstCol (g e 1))) (edgeZt chart e y)) a :=
    (contDiff_inner_right_spinor _).contDiffAt.comp a ht
  exact h1.mul h2

/-- The smooth remainder: `triRest` on edge `k`, the unrotated `triAction` on the others. -/
noncomputable def rotRemainder {n : ℕ} (j p : Fin 10 → ℝ) (g : BdryData)
    (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)) (k : Fin 10) (x : Fin n → ℝ) : ℂ :=
  ∑ e : Fin 10, if e = k then triRest (j e) (p e) (edgeZs chart e x) (edgeZt chart e x)
    else triAction (j e) (p e) (edgeZs chart e x) (firstCol (g e 0)) (edgeZt chart e x)
      (firstCol (g e 1))

/-- **Decomposition**: the chart action of the rotated data is `2 j_k log (c w_k) + R`. -/
theorem lorChartAction_rotSrc_eq {n : ℕ} (j p : Fin 10 → ℝ) (g : BdryData) (k : Fin 10) (c : ℂ)
    (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)) (x : Fin n → ℝ) :
    lorChartAction j p (rotSrc g k c) chart x =
      ((2 * j k : ℝ) : ℂ) * Complex.log (c * edgeOverlap g chart k x) +
        rotRemainder j p g chart k x := by
  unfold lorChartAction lorAction rotRemainder
  have h : ∀ e : Fin 10,
      triAction (j e) (p e)
        (spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e))
        (firstCol (rotSrc g k c e 0))
        (spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e))
        (firstCol (rotSrc g k c e 1)) =
      (if e = k then ((2 * j k : ℝ) : ℂ) * Complex.log (c * edgeOverlap g chart k x) else 0) +
        (if e = k then triRest (j e) (p e) (edgeZs chart e x) (edgeZt chart e x)
          else triAction (j e) (p e) (edgeZs chart e x) (firstCol (g e 0)) (edgeZt chart e x)
            (firstCol (g e 1))) := by
    intro e
    by_cases he : e = k
    · subst he
      rw [firstCol_rotSrc, firstCol_rotSrc]
      simp only [true_and, ite_true, Fin.one_eq_zero_iff]
      exact triAction_smul_eq _ _ _ _ _ _ _
    · rw [firstCol_rotSrc, firstCol_rotSrc]
      simp [he, edgeZs, edgeZt]
  rw [Finset.sum_congr rfl fun e _ => h e, Finset.sum_add_distrib]
  simp

/-- The remainder is smooth at `a` when the chart is, the spinors of edge `k` are nonzero and the
other edges are off the cut. -/
theorem contDiffAt_rotRemainder {n : ℕ} (j p : Fin 10 → ℝ) (g : BdryData) (k : Fin 10)
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)} {a : Fin n → ℝ}
    (hX : ∀ b i k, ContDiffAt ℝ ∞ (fun x => ((chart x).1 b : Matrix (Fin 2) (Fin 2) ℂ) i k) a)
    (hz : ∀ e, ContDiffAt ℝ ∞ (fun x => (chart x).2 e) a)
    (hZk : edgeZs chart k a ≠ 0) (hZk' : edgeZt chart k a ≠ 0)
    (hP : ∀ e, e ≠ k → edgeOverlap g chart e a ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ (rotRemainder j p g chart k) a := by
  unfold rotRemainder
  refine ContDiffAt.sum fun e _ => ?_
  obtain ⟨hs, ht⟩ := contDiffAt_edgeZ hX hz e
  by_cases he : e = k
  · subst he
    simp only [ite_true]
    exact contDiffAt_triRest _ _ hs ht hZk hZk'
  · simp only [he, ite_false]
    have hP0 := hP e he
    have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
    have hne : edgeOverlap g chart e a ≠ 0 := fun h => h0 (h ▸ hP0)
    have hZ : edgeZs chart e a ≠ 0 := fun h =>
      (left_ne_zero_of_mul hne) (by rw [h]; simp)
    have hZ' : edgeZt chart e a ≠ 0 := fun h =>
      (right_ne_zero_of_mul hne) (by rw [h]; simp)
    exact (contDiffAt_triAction (j e) (p e) (firstCol (g e 0)) (firstCol (g e 1)) hZ hZ' hP0).comp a
      (hs.prodMk ht)

end Lightlike.Asymptotics.Lorentzian

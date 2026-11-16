import Lightlike.Asymptotics.Lorentzian.Vertex

/-!
# Smoothness of the Lorentzian vertex action

The one-triangle action `triAction` is smooth in both spinors where they are nonzero and the product
of the overlaps `⟨Z,ξ⟩⟨Jξ',Z'⟩` is off the cut of the logarithm (`slitPlane`), and the vertex action
pulled back to a chart is smooth on every open set on which these conditions hold for the chart
(`lorChartAction_contDiffOn`). With `VertexLocal.lean` this replaces the global smoothness
hypothesis of the vertex asymptotics.

## Main results

* `contDiffAt_triAction`: smoothness of `triAction` at such a pair of spinors.
* `lorChartAction_contDiffOn`: smoothness of `lorChartAction` on an open set of a smooth chart.
-/

open Complex
open scoped ComplexConjugate ContDiff Matrix
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- `Z ↦ ⟨Z, ξ⟩` is smooth over `ℝ`. -/
theorem contDiff_inner_left_spinor (ξ : Spinor) : ContDiff ℝ ∞ (fun x : Spinor => inner ℂ x ξ) := by
  have : (fun x : Spinor => inner ℂ x ξ) = fun x => (starRingEnd ℂ) (inner ℂ ξ x) := by
    funext x; rw [inner_conj_symm]
  rw [this]
  exact Complex.conjCLE.contDiff.comp ((innerSL ℂ ξ).restrictScalars ℝ).contDiff

/-- `Z ↦ ⟨ξ, Z⟩` is smooth over `ℝ`. -/
theorem contDiff_inner_right_spinor (ξ : Spinor) : ContDiff ℝ ∞ (fun x : Spinor => inner ℂ ξ x) :=
  ((innerSL ℂ ξ).restrictScalars ℝ).contDiff

/-- **`triAction` is smooth** in both spinors where they are nonzero and the product of the
overlaps is off the cut of the logarithm. -/
theorem contDiffAt_triAction (k p : ℝ) (ξ ξ' : Spinor) {Z Z' : Spinor} (hZ : Z ≠ 0)
    (hZ' : Z' ≠ 0) (hP : inner ℂ Z ξ * inner ℂ (jMap ξ') Z' ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ (fun x : Spinor × Spinor => triAction k p x.1 ξ x.2 ξ') (Z, Z') := by
  unfold triAction
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  have hn1 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor => ‖x.1‖) (Z, Z') :=
    contDiffAt_fst.norm ℝ (by simpa using hZ)
  have hn2 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor => ‖x.2‖) (Z, Z') :=
    contDiffAt_snd.norm ℝ (by simpa using hZ')
  have hi1 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor => inner ℂ x.1 ξ) (Z, Z') :=
    (contDiff_inner_left_spinor ξ).contDiffAt.comp (Z, Z') contDiffAt_fst
  have hi2 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor => inner ℂ (jMap ξ') x.2) (Z, Z') :=
    (contDiff_inner_right_spinor (jMap ξ')).contDiffAt.comp (Z, Z') contDiffAt_snd
  have hlogP : ContDiffAt ℝ ∞
      (fun x : Spinor × Spinor => Complex.log (inner ℂ x.1 ξ * inner ℂ (jMap ξ') x.2)) (Z, Z') :=
    ContDiffAt.comp (g := Complex.log) (f := fun x : Spinor × Spinor =>
      inner ℂ x.1 ξ * inner ℂ (jMap ξ') x.2) (Z, Z') ((Complex.contDiffAt_log hP).restrict_scalars ℝ)
      (hi1.mul hi2)
  have hsq1 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor => (((‖x.1‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (Z, Z') (hn1.pow 2)
  have hsq2 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor => (((‖x.2‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (Z, Z') (hn2.pow 2)
  have hslit1 : (((‖Z‖ ^ 2 : ℝ) : ℂ)) * (((‖Z'‖ ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_mul]; exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hlog1 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor =>
      Complex.log (((‖x.1‖ ^ 2 : ℝ) : ℂ) * ((‖x.2‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    ContDiffAt.comp (g := Complex.log) (f := fun x : Spinor × Spinor =>
      ((‖x.1‖ ^ 2 : ℝ) : ℂ) * ((‖x.2‖ ^ 2 : ℝ) : ℂ)) (Z, Z')
      ((Complex.contDiffAt_log hslit1).restrict_scalars ℝ) (hsq1.mul hsq2)
  have hslit2 : (((‖Z'‖ ^ 2 : ℝ) : ℂ)) / (((‖Z‖ ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_div]; exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
  have hz0 : (((‖Z‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : ‖Z‖ ^ 2 ≠ 0)
  have hq : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor =>
      ((‖x.2‖ ^ 2 : ℝ) : ℂ) / ((‖x.1‖ ^ 2 : ℝ) : ℂ)) (Z, Z') := by
    simp only [div_eq_mul_inv]
    exact hsq2.mul (hsq1.inv hz0)
  have hlog2 : ContDiffAt ℝ ∞ (fun x : Spinor × Spinor =>
      Complex.log (((‖x.2‖ ^ 2 : ℝ) : ℂ) / ((‖x.1‖ ^ 2 : ℝ) : ℂ))) (Z, Z') :=
    ContDiffAt.comp (g := Complex.log) (f := fun x : Spinor × Spinor =>
      ((‖x.2‖ ^ 2 : ℝ) : ℂ) / ((‖x.1‖ ^ 2 : ℝ) : ℂ)) (Z, Z')
      ((Complex.contDiffAt_log hslit2).restrict_scalars ℝ) hq
  exact (((contDiffAt_const).mul hlogP).sub ((contDiffAt_const).mul hlog1)).add
    ((contDiffAt_const).mul hlog2)

/-- A spinor curve `x ↦ M x · v x` is smooth when the entries of `M` and the spinor `v` are. -/
theorem contDiff_spinAct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {v : E → Spinor}
    (hM : ∀ i k, ContDiff ℝ ∞ (fun x => M x i k)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun x => spinAct (M x) (v x)) := by
  have hiff : ∀ {w : E → Spinor}, ContDiff ℝ ∞ w ↔ ∀ i, ContDiff ℝ ∞ (fun x => w x i) := by
    intro w
    constructor
    · intro hw i
      exact (((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).contDiff).comp hw
    · intro h
      let L : (Fin 2 → ℂ) →L[ℝ] Spinor :=
        ((EuclideanSpace.equiv (Fin 2) ℂ).symm.toContinuousLinearMap).restrictScalars ℝ
      exact L.contDiff.comp (contDiff_pi.2 h)
  rw [hiff]
  have hv' := hiff.mp hv
  intro i
  fin_cases i
  · simpa [spinAct_zero_apply] using ((hM 0 0).mul (hv' 0)).add ((hM 0 1).mul (hv' 1))
  · simpa [spinAct_one_apply] using ((hM 1 0).mul (hv' 0)).add ((hM 1 1).mul (hv' 1))

/-- **The vertex action in a smooth chart is smooth on an open set** where, on every edge, the
product of the overlaps `⟨Z,ξ⟩⟨Jξ',Z'⟩` is off the cut of the logarithm (this also gives `Z ≠ 0`
and `Z' ≠ 0`). The chart is a map `x ↦ (X(x), z(x))` with smooth matrix entries and smooth spinors. -/
theorem lorChartAction_contDiffOn {n : ℕ} (j p : Fin 10 → ℝ) (g : BdryData)
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)}
    (hX : ∀ a i k, ContDiff ℝ ∞ (fun x => ((chart x).1 a : Matrix (Fin 2) (Fin 2) ℂ) i k))
    (hz : ∀ e, ContDiff ℝ ∞ (fun x => (chart x).2 e)) {U : Set (Fin n → ℝ)}
    (hP : ∀ x ∈ U, ∀ e,
      inner ℂ (spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e))
          (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1)))
          (spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e)) ∈
        Complex.slitPlane) :
    ContDiffOn ℝ ∞ (lorChartAction j p g chart) U := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  unfold lorChartAction lorAction
  refine ContDiffAt.sum fun e _ => ?_
  have hM : ∀ a, ∀ i k, ContDiff ℝ ∞ (fun x => (((chart x).1 a : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) i k) := by
    intro a i k
    have := Complex.conjCLE.contDiff.comp (hX a k i)
    simpa [Function.comp_def, Matrix.conjTranspose_apply] using this
  have hZs := contDiff_spinAct (hM (edgeSrc e)) (hz e)
  have hZt := contDiff_spinAct (hM (edgeTgt e)) (hz e)
  have hP0 := hP x hx e
  have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
  have hne : inner ℂ (spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e))
          (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1)))
          (spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e)) ≠ 0 :=
    fun h => h0 (h ▸ hP0)
  have hZ : spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e) ≠ 0 :=
    fun h => (left_ne_zero_of_mul hne) (by rw [h]; simp)
  have hZ' : spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e) ≠ 0 :=
    fun h => (right_ne_zero_of_mul hne) (by rw [h]; simp)
  exact (contDiffAt_triAction (j e) (p e) (firstCol (g e 0)) (firstCol (g e 1)) hZ hZ' hP0).comp x
    (hZs.contDiffAt.prodMk hZt.contDiffAt)

end Lightlike.Asymptotics.Lorentzian

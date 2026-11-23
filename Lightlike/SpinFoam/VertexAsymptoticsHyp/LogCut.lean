import Lightlike.SpinFoam.VertexAsymptoticsHyp.PhaseRotation

/-!
# Branch-cut lemmas for the triangle action (SF10, T-SF10-P2 statement defect)

L2: after rotating the source spinor of one edge by a phase `c`, `triAction` shifts by the constant
`2k · i · arg c` as long as the arguments add up inside `(-π, π]`.
L3: a function `log ∘ f` which is continuous at a point where `f` is a negative real forces
`Im f ≥ 0` nearby: so `log ∘ f` is not continuous (hence not differentiable) where `Im f` changes
sign through a negative value.  Supporting lemmas only.
-/

open Complex
open scoped Real Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Asymptotics.EPRL

/-- `log c = i arg c` for a unit complex number. -/
lemma log_unit {c : ℂ} (hc : ‖c‖ = 1) : Complex.log c = (Complex.arg c : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, hc]
  · simp [Complex.log_im]

/-- **L2**: rotating the source spinor by a phase `c` shifts `triAction` by `2k · i · arg c`,
provided `arg c + arg w ∈ (-π, π]` for `w = ⟨Z,ξ⟩⟨Jξ',Z'⟩ ≠ 0`. -/
theorem triAction_smul_unit (k p : ℝ) (Z ξ Z' ξ' : Spinor) {c : ℂ} (hc : ‖c‖ = 1)
    (hw : inner ℂ Z ξ * inner ℂ (jMap ξ') Z' ≠ 0)
    (harg : Complex.arg c + Complex.arg (inner ℂ Z ξ * inner ℂ (jMap ξ') Z') ∈
      Set.Ioc (-π) π) :
    triAction k p Z (c • ξ) Z' ξ' =
      triAction k p Z ξ Z' ξ' + ((2 * k : ℝ) : ℂ) * ((Complex.arg c : ℂ) * Complex.I) := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc; simp at hc
  have hlog : Complex.log (c * (inner ℂ Z ξ * inner ℂ (jMap ξ') Z')) =
      Complex.log c + Complex.log (inner ℂ Z ξ * inner ℂ (jMap ξ') Z') :=
    Complex.log_mul hc0 hw harg
  unfold triAction
  rw [inner_smul_phase, mul_assoc, hlog, log_unit hc]
  ring

/-- **L3**: if `log ∘ f` is continuous at `a` and `f a` is a negative real number, then
`Im f ≥ 0` in a neighbourhood of `a`. -/
theorem eventually_im_nonneg_of_continuousAt_log {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    {a : X} (hcont : ContinuousAt (fun y => Complex.log (f y)) a)
    (hre : (f a).re < 0) (him : (f a).im = 0) :
    ∀ᶠ y in nhds a, 0 ≤ (f y).im := by
  have harg : Complex.arg (f a) = π := Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩
  have hc : ContinuousAt (fun y => (Complex.log (f y)).im) a :=
    Complex.continuous_im.continuousAt.comp hcont
  have hpos : ∀ᶠ y in nhds a, 0 < (Complex.log (f y)).im := by
    refine hc.eventually (lt_mem_nhds ?_)
    simpa [Complex.log_im, harg] using Real.pi_pos
  filter_upwards [hpos] with y hy
  rw [Complex.log_im] at hy
  exact Complex.arg_nonneg_iff.mp hy.le

/-- **L3, contrapositive**: if `f a < 0` is a negative real and `Im f` takes a negative value
arbitrarily close to `a`, then `log ∘ f` is not continuous at `a`. -/
theorem not_continuousAt_log_of_frequently_im_neg {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    {a : X} (hre : (f a).re < 0) (him : (f a).im = 0)
    (hfreq : ∃ᶠ y in nhds a, (f y).im < 0) :
    ¬ ContinuousAt (fun y => Complex.log (f y)) a := by
  intro hcont
  have h := eventually_im_nonneg_of_continuousAt_log hcont hre him
  obtain ⟨y, hy1, hy2⟩ := (hfreq.and_eventually h).exists
  exact absurd hy2 (not_le.2 hy1)

/-- **L2 for the vertex action**: `lorAction` of the rotated data is `lorAction` plus the constant
`2 j_k · i · arg c`, whenever the overlap of edge `k` at the point satisfies the argument condition
of `triAction_smul_unit`. -/
theorem lorAction_rotSrc (j p : Fin 10 → ℝ) {c : ℂ} (hc : ‖c‖ = 1) (g : BdryData) (k : Fin 10)
    (X : Fin 5 → Lightlike.Lorentz.SL2C) (z : Fin 10 → Spinor)
    (hw : inner ℂ (spinAct (X (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct (X (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z k)) ≠ 0)
    (harg : Complex.arg c + Complex.arg
        (inner ℂ (spinAct (X (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z k))
            (firstCol (g k 0)) *
          inner ℂ (jMap (firstCol (g k 1)))
            (spinAct (X (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z k))) ∈ Set.Ioc (-π) π) :
    lorAction j p (rotSrc g k c) X z =
      lorAction j p g X z + ((2 * j k : ℝ) : ℂ) * ((Complex.arg c : ℂ) * Complex.I) := by
  unfold lorAction
  have h : ∀ e : Fin 10,
      triAction (j e) (p e)
        (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
        (firstCol (rotSrc g k c e 0))
        (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
        (firstCol (rotSrc g k c e 1)) =
      triAction (j e) (p e)
        (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0))
        (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 1)) +
      if e = k then ((2 * j k : ℝ) : ℂ) * ((Complex.arg c : ℂ) * Complex.I) else 0 := by
    intro e
    by_cases he : e = k
    · subst he
      rw [firstCol_rotSrc, firstCol_rotSrc]
      simp only [true_and, ite_true, Fin.one_eq_zero_iff]
      exact triAction_smul_unit _ _ _ _ _ _ hc hw harg
    · rw [firstCol_rotSrc, firstCol_rotSrc]
      simp [he]
  rw [Finset.sum_congr rfl fun e _ => h e, Finset.sum_add_distrib]
  simp

end Lightlike.Asymptotics.Lorentzian

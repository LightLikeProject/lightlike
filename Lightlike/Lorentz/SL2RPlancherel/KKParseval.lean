module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.PolarTorus
public import Lightlike.Lorentz.SL2RPlancherel.TorusParseval

/-!
# The Plancherel identity of `L²(SL(2,ℝ))` in the `K × K` components

For continuous `f : SL(2,ℝ) → ℂ`, with `P_ξ(x) = f(k_{2π x₀} a(ξ) k_{2π x₁})` and the `(m,n)`-th
`K × K`-Fourier component `f_{m,n}(ξ) = ∫_{(0,1]²} e^{-2πi (m x₀ + n x₁)} P_ξ(x) dx`,
`∫ |f|² d haarR = (2π)² ∫_{ξ>0} sinh ξ ∑_{m,n} |f_{m,n}(ξ)|² dξ`
(`lintegral_norm_sq_eq_kk`).  It follows from the polar formula over the torus of angles
(`lintegral_haarR_torus`) and Parseval on `(0,1]²` (`hasSum_sq_box`).  Layer 2b of the Plancherel
formula on `SL(2,ℝ)`.  The identification of the components `f_{m,n}` with the ladder images of
radial generators, and the sum over all `(m,n)`, are layer 2c.
-/

@[expose] public section

open MeasureTheory Set Real Lightlike.Lorentz.SL2R

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- Iterated form of the integral over the box `(0,1]²`. -/
lemma lintegral_box_eq {h : (Fin 2 → ℝ) → ENNReal} (hm : Measurable h) :
    ∫⁻ x in box, h x = ∫⁻ a in Ioc (0 : ℝ) 1, ∫⁻ b in Ioc (0 : ℝ) 1, h ![a, b] := by
  have hmp := volume_preserving_finTwoArrow ℝ
  have hbox : box = (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    ext x
    simp [box, Fin.forall_fin_two, MeasurableEquiv.finTwoArrow]
  have key := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.finTwoArrow.measurableEmbedding)
    (fun p => h (MeasurableEquiv.finTwoArrow.symm p)) (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
  simp only [MeasurableEquiv.symm_apply_apply] at key
  rw [hbox, key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod _ ?_]
  · rfl
  · exact (hm.comp MeasurableEquiv.finTwoArrow.symm.measurable).aemeasurable

/-- Scaling the angle: `∫_0^{2π} φ = 2π ∫_0^1 φ(2π x) dx`. -/
lemma lintegral_scaled (φ : ℝ → ENNReal) :
    ∫⁻ α in Ioc 0 (2 * π), φ α =
      ENNReal.ofReal (2 * π) * ∫⁻ x in Ioc (0 : ℝ) 1, φ (2 * π * x) := by
  have h2 : 0 < 2 * π := by positivity
  have himg : (fun x : ℝ => 2 * π * x) '' Ioc (0 : ℝ) 1 = Ioc 0 (2 * π) := by
    ext y
    simp only [mem_image, mem_Ioc]
    constructor
    · rintro ⟨x, ⟨h1, h3⟩, rfl⟩
      exact ⟨by positivity, by nlinarith⟩
    · rintro ⟨h1, h3⟩
      exact ⟨y / (2 * π), ⟨by positivity, by rw [div_le_one h2]; exact h3⟩, by field_simp⟩
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun x : ℝ => 2 * π * x)
    (f' := fun _ => 2 * π) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc
    (fun x _ => ((hasDerivAt_id x).const_mul (2 * π)).hasDerivWithinAt.congr_deriv (by simp))
    (fun x _ y _ h => by simpa [h2.ne'] using h) φ
  rw [himg] at key
  rw [key, abs_of_pos h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The double angle integral as an integral over the box. -/
lemma lintegral_angles_eq_box {G : ℝ → ℝ → ENNReal} (hG : Measurable (Function.uncurry G)) :
    ∫⁻ α in Ioc 0 (2 * π), ∫⁻ θ in Ioc 0 (2 * π), G α θ =
      ENNReal.ofReal (2 * π) ^ 2 * ∫⁻ x in box, G (2 * π * x 0) (2 * π * x 1) := by
  have hm : Measurable fun x : Fin 2 → ℝ => G (2 * π * x 0) (2 * π * x 1) := by
    have h1 : Measurable fun p : ℝ × ℝ => (2 * π * p.1, 2 * π * p.2) :=
      (measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd)
    have h2 : Measurable fun x : Fin 2 → ℝ => (x 0, x 1) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    exact hG.comp (h1.comp h2)
  calc ∫⁻ α in Ioc 0 (2 * π), ∫⁻ θ in Ioc 0 (2 * π), G α θ
      = ENNReal.ofReal (2 * π) * ∫⁻ a in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc 0 (2 * π), G (2 * π * a) θ :=
        lintegral_scaled (fun α => ∫⁻ θ in Ioc 0 (2 * π), G α θ)
    _ = ENNReal.ofReal (2 * π) * ∫⁻ a in Ioc (0 : ℝ) 1, ENNReal.ofReal (2 * π) *
          ∫⁻ b in Ioc (0 : ℝ) 1, G (2 * π * a) (2 * π * b) := by
        congr 1
        exact lintegral_congr (fun a => lintegral_scaled (fun θ => G (2 * π * a) θ))
    _ = ENNReal.ofReal (2 * π) * (ENNReal.ofReal (2 * π) *
          ∫⁻ a in Ioc (0 : ℝ) 1, ∫⁻ b in Ioc (0 : ℝ) 1, G (2 * π * a) (2 * π * b)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (2 * π) ^ 2 * ∫⁻ x in box, G (2 * π * x 0) (2 * π * x 1) := by
        rw [lintegral_box_eq hm, pow_two, mul_assoc]
        simp

/-- The function of the angles `x ∈ (0,1]²` at the radius `ξ`: `f(k_{2π x₀} a(ξ) k_{2π x₁})`. -/
def kkProfile (f : SL2R → ℂ) (ξ : ℝ) (x : Fin 2 → ℝ) : ℂ :=
  f (rot (2 * π * x 0) * aR ξ * rot (2 * π * x 1))

/-- The `(m,n)`-th `K × K`-Fourier component of `f` at the radius `ξ`. -/
def kkCoeff (f : SL2R → ℂ) (n : Fin 2 → ℤ) (ξ : ℝ) : ℂ :=
  ∫ x in box, Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) * kkProfile f ξ x

lemma continuous_kkProfile {f : SL2R → ℂ} (hf : Continuous f) (ξ : ℝ) :
    Continuous (kkProfile f ξ) := by
  unfold kkProfile
  refine hf.comp ?_
  exact ((continuous_rot.comp (by fun_prop)).mul continuous_const).mul
    (continuous_rot.comp (by fun_prop))

/-- **Plancherel identity in the `K × K` components**: for continuous `f`,
`∫ |f|² d haarR = (2π)² ∫_{ξ>0} sinh ξ ∑_{m,n} |f_{m,n}(ξ)|² dξ`. -/
theorem lintegral_norm_sq_eq_kk {f : SL2R → ℂ} (hf : Continuous f) :
    ∫⁻ g, ENNReal.ofReal (‖f g‖ ^ 2) ∂haarR =
      ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) *
        ENNReal.ofReal ((2 * π) ^ 2 * ∑' n : Fin 2 → ℤ, ‖kkCoeff f n ξ‖ ^ 2) := by
  have hF : Measurable fun g : SL2R => ENNReal.ofReal (‖f g‖ ^ 2) := by fun_prop
  rw [lintegral_haarR_torus hF]
  refine lintegral_congr (fun ξ => ?_)
  congr 1
  have hP := continuous_kkProfile hf ξ
  have hG : Measurable (Function.uncurry fun α θ : ℝ =>
      ENNReal.ofReal (‖f (rot α * aR ξ * rot θ)‖ ^ 2)) := by
    have : Continuous fun p : ℝ × ℝ => rot p.1 * aR ξ * rot p.2 :=
      ((continuous_rot.comp continuous_fst).mul continuous_const).mul
        (continuous_rot.comp continuous_snd)
    have h2 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (‖f (rot p.1 * aR ξ * rot p.2)‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp ((hf.comp this).norm.pow 2).measurable
    exact h2
  rw [lintegral_angles_eq_box hG]
  have hbound : IntegrableOn (fun x => ‖kkProfile f ξ x‖ ^ 2) box := by
    have hI : IntegrableOn (fun x => ‖kkProfile f ξ x‖ ^ 2) (Icc (0 : Fin 2 → ℝ) 1) :=
      (hP.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    refine hI.mono_set ?_
    intro x hx
    exact ⟨fun i => (hx i).1.le, fun i => by simpa using (hx i).2⟩
  have hint := ofReal_integral_eq_lintegral_ofReal hbound (ae_of_all _ (fun x => by positivity))
  have hsum := (hasSum_sq_box hP).tsum_eq
  have hk : ∀ n, kkCoeff f n ξ = ∫ x in box,
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) * kkProfile f ξ x :=
    fun n => rfl
  have : ∑' n : Fin 2 → ℤ, ‖kkCoeff f n ξ‖ ^ 2 = ∫ x in box, ‖kkProfile f ξ x‖ ^ 2 := by
    simp only [hk]; exact hsum
  show ENNReal.ofReal (2 * π) ^ 2 * ∫⁻ x in box, ENNReal.ofReal (‖kkProfile f ξ x‖ ^ 2) = _
  rw [this, ENNReal.ofReal_mul (p := (2 * π) ^ 2) (by positivity), ← hint,
    ENNReal.ofReal_pow (by positivity)]

end Lightlike.Lorentz.SL2RPlancherel

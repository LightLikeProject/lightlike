import Lightlike.Asymptotics.EPRL.Localise

/-!
# Gauge invariance of the coherent 15j integrand

The propagator `prop g X e = ((g_ab ε)† X_a† X_b g_ba)₀₀` depends on `X` only through the
products `X_a† X_b`, so the integrand `F_n` is invariant under the common left multiplication
`X_a ↦ h X_a` by an element `h` of `SU(2)` (`cohAmp_mul_left`). This is the gauge freedom that the
chart of `Amplitude.lean` removes by fixing `X_4`.
-/

open Matrix MeasureTheory Complex

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

/-- **Gauge invariance of the propagator**: `prop g (h X) e = prop g X e` for `h† h = 1`. -/
theorem prop_mul_left (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : hᴴ * h = 1) (e : Fin 10) :
    prop g (fun a => h * X a) e = prop g X e := by
  have hh' : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, hᴴ * (h * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hh, Matrix.one_mul]
  unfold prop
  rw [Matrix.conjTranspose_mul h (X (edgeSrc e))]
  simp only [Matrix.mul_assoc, hh']

/-- **Gauge invariance of the integrand**: `F_n(h X) = F_n(X)` for `h† h = 1`. -/
theorem cohAmp_mul_left (n : Fin 10 → ℕ) (g : BdryData)
    (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : hᴴ * h = 1) :
    cohAmp n g (fun a => h * X a) = cohAmp n g X := by
  simp only [cohAmp, prop_mul_left g X hh]

/-- **Wrong input**: the unitarity of `h` is needed. For the data `g_ab = -ε`, `g_ba = 1` the
propagator of the tuple `X = 1` is `1`, and `h = 2` (with `h† h = 4`) multiplies it by `4`. -/
theorem prop_mul_left_nonunitary_ne :
    prop (fun _ i => if i = 0 then -epsMat else 1) (fun _ => (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0
      ≠ prop (fun _ i => if i = 0 then -epsMat else 1) (fun _ => 1) 0 := by
  simp [prop, epsMat, Matrix.mul_apply, Matrix.one_apply]
  norm_num

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- The integrand as a function on `SU(2)^5`. -/
noncomputable def cohF (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → SU2) : ℂ :=
  cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))

/-- `cohF` is invariant under the common left multiplication by an element of `SU(2)`. -/
theorem cohF_mul_left (n : Fin 10 → ℕ) (g : BdryData) (x : SU2) (X : Fin 5 → SU2) :
    cohF n g (fun a => x * X a) = cohF n g X :=
  cohAmp_mul_left n g _
    (Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp x.2).1)

/-- **Gauge fixing.** The coherent 15j integral is the integral over `SU(2)^4` of the integrand
with `X_4 = 1`: `∫_{SU(2)^5} F_n = ∫_{SU(2)^4} F_n(Y, 1)`. -/
theorem coh15j_eq_gaugeFixed (n : Fin 10 → ℕ) (g : BdryData) :
    coh15j n g = ∫ Y : Fin 4 → SU2, cohF n g (Fin.snoc Y 1) ∂(haarN (N := 4)) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin 5 => haarSU2) (Fin.last 4)
  have h1 : coh15j n g = ∫ p, cohF n g
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => SU2) (Fin.last 4)).symm p)
      ∂(haarSU2.prod (Measure.pi fun j : Fin 4 => haarSU2)) := by
    rw [← hmp.integral_comp' (g := fun p => cohF n g
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => SU2) (Fin.last 4)).symm p))]
    simp only [MeasurableEquiv.symm_apply_apply]
    rfl
  have hcont : Continuous (cohF n g) := continuous_cohAmp n g
  have hint : Integrable (cohF n g) (haarN (N := 5)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun p => cohF n g
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => SU2) (Fin.last 4)).symm p))
      (haarSU2.prod (Measure.pi fun j : Fin 4 => haarSU2)) :=
    (hmp.symm.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => SU2) (Fin.last 4)).symm.measurableEmbedding).mpr
      hint
  rw [h1, integral_prod _ hint2]
  have h2 : ∀ x : SU2, ∫ Y, cohF n g
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => SU2) (Fin.last 4)).symm (x, Y))
        ∂(Measure.pi fun j : Fin 4 => haarSU2) =
      ∫ Y : Fin 4 → SU2, cohF n g (Fin.snoc Y 1) ∂(haarN (N := 4)) := by
    intro x
    have hsn : ∀ Y : Fin 4 → SU2,
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => SU2) (Fin.last 4)).symm (x, Y) =
          Fin.snoc Y x := fun Y => by
      simp [MeasurableEquiv.piFinSuccAbove]
      exact Fin.insertNth_last' x Y
    have hg : ∀ Y : Fin 4 → SU2, cohF n g (Fin.snoc Y x) =
        cohF n g (Fin.snoc (fun j => x⁻¹ * Y j) 1) := fun Y => by
      rw [← cohF_mul_left n g x (Fin.snoc (fun j => x⁻¹ * Y j) 1)]
      congr 1
      funext a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · simp only [Fin.snoc_last]
        simp
      · simp only [Fin.snoc_castSucc]
        simp
    simp only [hsn, hg]
    have hmp2 : MeasurePreserving
        (MeasurableEquiv.piCongrRight fun _ : Fin 4 => MeasurableEquiv.mulLeft x⁻¹)
        (Measure.pi fun _ : Fin 4 => haarSU2) (Measure.pi fun _ : Fin 4 => haarSU2) :=
      measurePreserving_pi _ _ (fun _ => measurePreserving_mul_left haarSU2 x⁻¹)
    exact hmp2.integral_comp' (g := fun Y : Fin 4 → SU2 => cohF n g (Fin.snoc Y 1))
  simp only [h2]
  simp

/-- **Known value**: with all spins zero the gauge-fixed integral is `1`, as is `coh15j`. -/
theorem gaugeFixed_zero (g : BdryData) :
    ∫ Y : Fin 4 → SU2, cohF 0 g (Fin.snoc Y 1) ∂(haarN (N := 4)) = 1 := by
  rw [← coh15j_eq_gaugeFixed, coh15j_zero]

end Lightlike.Asymptotics.EPRL

module

public import Lightlike.Poincare.WignerRotation

/-!
# The derivative of the standard lift along a curve of momenta

For a curve `c(t)` of momenta with `c(0) = P` on the mass shell and entrywise velocity `ċ`, the standard lift
`L(c(t)) = s(c(t)) (c(t)/m + 1)` with `s = 1/√(tr(c/m) + 2)` has entrywise velocity `dStdLift m P ċ`
(`hasDerivAt_stdLiftMat`), which is real-linear in `ċ` (`dStdLift_add`, `dStdLift_smul`, `dStdLift_zero`).

Supporting lemmas for the generators of the massive induced representations; no catalogue entry.
-/

@[expose] public section

noncomputable section

open Matrix

namespace Lightlike.Poincare

/-- The real part of the normalised trace, as a real-linear function of the velocity. -/
def trVel (m : ℝ) (c' : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((normP m c').trace).re

/-- The derivative of the standard lift at `P` in the direction `c'`. -/
def dStdLift (m : ℝ) (P c' : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((-trVel m c' / (2 * (trN m P + 2) * Real.sqrt (trN m P + 2)) : ℝ) : ℂ) • (normP m P + 1) +
    ((1 / Real.sqrt (trN m P + 2) : ℝ) : ℂ) • normP m c'

lemma trVel_add (m : ℝ) (a b : Matrix (Fin 2) (Fin 2) ℂ) : trVel m (a + b) = trVel m a + trVel m b := by
  simp [trVel, normP, smul_add, Matrix.trace_add]

lemma trVel_smul (m r : ℝ) (a : Matrix (Fin 2) (Fin 2) ℂ) : trVel m ((r : ℂ) • a) = r * trVel m a := by
  simp only [trVel, normP, smul_smul, Matrix.trace_smul, smul_eq_mul]
  simp [Complex.mul_re]; ring

lemma normP_smul (m : ℝ) (c : ℂ) (a : Matrix (Fin 2) (Fin 2) ℂ) : normP m (c • a) = c • normP m a := by
  simp only [normP]; rw [smul_comm]

lemma normP_add (m : ℝ) (a b : Matrix (Fin 2) (Fin 2) ℂ) : normP m (a + b) = normP m a + normP m b := by
  simp only [normP, smul_add]

lemma dStdLift_add (m : ℝ) (P a b : Matrix (Fin 2) (Fin 2) ℂ) :
    dStdLift m P (a + b) = dStdLift m P a + dStdLift m P b := by
  simp only [dStdLift, trVel_add, normP_add]
  rw [show ((-(trVel m a + trVel m b) / (2 * (trN m P + 2) * √(trN m P + 2)) : ℝ) : ℂ) =
      ((-trVel m a / (2 * (trN m P + 2) * √(trN m P + 2)) : ℝ) : ℂ) +
        ((-trVel m b / (2 * (trN m P + 2) * √(trN m P + 2)) : ℝ) : ℂ) by push_cast; ring]
  simp only [add_smul, smul_add]
  abel

lemma dStdLift_smul (m r : ℝ) (P a : Matrix (Fin 2) (Fin 2) ℂ) :
    dStdLift m P ((r : ℂ) • a) = (r : ℂ) • dStdLift m P a := by
  have h1 : ((-(r * trVel m a) / (2 * (trN m P + 2) * √(trN m P + 2)) : ℝ) : ℂ) =
      (r : ℂ) * ((-trVel m a / (2 * (trN m P + 2) * √(trN m P + 2)) : ℝ) : ℂ) := by push_cast; ring
  simp only [dStdLift, trVel_smul, normP_smul]
  rw [h1, smul_comm (((1 / √(trN m P + 2) : ℝ) : ℂ)) (r : ℂ) (normP m a)]
  simp only [smul_add, mul_smul]

lemma dStdLift_zero (m : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) : dStdLift m P 0 = 0 := by
  simp [dStdLift, trVel, normP]

/-- The real part of a complex curve. -/
lemma hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun t => (f t).re) f'.re 0 := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

/-- **The derivative of the standard lift along a curve.** -/
theorem hasDerivAt_stdLiftMat {m : ℝ} (hm : 0 < m) {c : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    {c' : Matrix (Fin 2) (Fin 2) ℂ} (hc : ∀ i j, HasDerivAt (fun t => c t i j) (c' i j) 0)
    (hP : c 0 ∈ MassShellH m) (i j : Fin 2) :
    HasDerivAt (fun t => stdLiftMat m (c t) i j) (dStdLift m (c 0) c' i j) 0 := by
  -- the normalised trace
  have htr : HasDerivAt (fun t => trN m (c t)) (trVel m c') 0 := by
    have h := ((hc 0 0).add (hc 1 1)).const_mul (((1 / m : ℝ) : ℂ))
    have := hasDerivAt_re h
    simpa [trN, trVel, normP, Matrix.trace_fin_two, mul_add] using this
  have hpos : 0 < trN m (c 0) + 2 := by have := (trace_normP hm hP).2; linarith
  have hu : HasDerivAt (fun t => trN m (c t) + 2) (trVel m c') 0 := htr.add_const 2
  have hsq := hu.sqrt hpos.ne'
  have hsqpos : 0 < Real.sqrt (trN m (c 0) + 2) := Real.sqrt_pos.2 hpos
  have hinv := hsq.inv hsqpos.ne'
  have hs : HasDerivAt (fun t => ((1 / Real.sqrt (trN m (c t) + 2) : ℝ) : ℂ))
      (((-trVel m c' / (2 * (trN m (c 0) + 2) * Real.sqrt (trN m (c 0) + 2))) : ℝ) : ℂ) 0 := by
    have h2 : (-(trVel m c' / (2 * √(trN m (c 0) + 2))) / √(trN m (c 0) + 2) ^ 2) =
        -trVel m c' / (2 * (trN m (c 0) + 2) * √(trN m (c 0) + 2)) := by
      rw [Real.sq_sqrt hpos.le]; field_simp
    rw [← h2]
    have := hinv.ofReal_comp
    simpa [one_div] using this
  have hentry : HasDerivAt (fun t => normP m (c t) i j + (1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
      (normP m c' i j) 0 := by
    have := ((hc i j).const_mul (((1 / m : ℝ) : ℂ))).add_const ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
    simpa [normP] using this
  have H := hs.mul hentry
  have e : (fun t => stdLiftMat m (c t) i j) = fun t =>
      ((1 / Real.sqrt (trN m (c t) + 2) : ℝ) : ℂ) * (normP m (c t) i j + (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) := by
    funext t; simp [stdLiftMat]
  rw [e]
  convert H using 1
  simp [dStdLift]
  ring

end Lightlike.Poincare

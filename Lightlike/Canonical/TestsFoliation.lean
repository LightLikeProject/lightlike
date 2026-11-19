import Lightlike.Canonical.Foliation
import Lightlike.Spacetime.Minkowski

/-!
# Trust checks of the ADM data of a foliation

Minkowski space `ℝ^{n+1}` with the time function `τ(x) = x⁰`: the gradient is `∇τ = −e₀`, so `τ` is a time function
(`isTimeFunction_minkowski`), the lapse is `1`, the unit normal is `e₀`, and the induced metric is the Euclidean metric
of the spatial coordinates (`spatialMetric_minkowski`), positive on the spatial basis vectors and zero on the normal. A
function whose gradient is spacelike, `τ(x) = x¹`, is not a time function (`not_isTimeFunction_minkowski_x1`).
-/

open Manifold

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The Minkowski metric on `ℝ^{n+1}` as a `NondegMetric`. -/
abbrev mink (n : ℕ) : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ) :=
  (Lightlike.minkowskiMetric (n + 1)).toNondegMetric

/-- The differential of a coordinate function is the coordinate projection. -/
lemma dTime_coord (k : Fin (n + 1)) (x : Fin (n + 1) → ℝ) (u : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) x) :
    dTime (E := Fin (n + 1) → ℝ) (fun y : Fin (n + 1) → ℝ => y k) x u = u k := by
  have h : HasMFDerivAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) (fun y : Fin (n + 1) → ℝ => y k) x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k) :=
    (hasFDerivAt_apply k x).hasMFDerivAt
  show mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) (fun y : Fin (n + 1) → ℝ => y k) x u = u k
  rw [h.mfderiv]
  rfl

/-- **The gradient of `τ = x⁰` is `−e₀`.** -/
theorem timeGrad_minkowski (x : Fin (n + 1) → ℝ) :
    timeGrad (mink n) (fun y => y 0) x = (-(Pi.single 0 1) : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) x) := by
  apply Lightlike.eq_of_g_eq (mink n) x
  intro u
  rw [g_timeGrad, dTime_coord]
  show (u : Fin (n + 1) → ℝ) 0 = Lightlike.minkowskiForm (n + 1) (-(Pi.single 0 1)) u
  erw [Lightlike.minkowskiForm_apply]
  simp [Pi.single_apply, Lightlike.etaDiag]

/-- `g(∇τ, ∇τ) = −1`. -/
theorem g_timeGrad_minkowski (x : Fin (n + 1) → ℝ) :
    (mink n).g x (timeGrad (mink n) (fun y => y 0) x) (timeGrad (mink n) (fun y => y 0) x) = -1 := by
  rw [timeGrad_minkowski]
  show Lightlike.minkowskiForm (n + 1) (-(Pi.single 0 1)) (-(Pi.single 0 1)) = -1
  simp [Pi.single_apply, Lightlike.etaDiag]

/-- **`τ = x⁰` is a time function of Minkowski space.** -/
theorem isTimeFunction_minkowski : IsTimeFunction (mink n) (fun y : Fin (n + 1) → ℝ => y 0) where
  smooth := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0).contDiff.contMDiff
  timelike x := by rw [g_timeGrad_minkowski]; norm_num

/-- The lapse of `τ = x⁰` is `1`. -/
theorem lapse_minkowski (x : Fin (n + 1) → ℝ) : lapse (mink n) (fun y => y 0) x = 1 := by
  simp [lapse, g_timeGrad_minkowski]

/-- The unit normal of `τ = x⁰` is `e₀`. -/
theorem unitNormal_minkowski (x : Fin (n + 1) → ℝ) :
    unitNormal (mink n) (fun y => y 0) x = (Pi.single 0 1 : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) x) := by
  rw [unitNormal, lapse_minkowski, timeGrad_minkowski]
  show (-(1 : ℝ)) • (-(Pi.single 0 1) : Fin (n + 1) → ℝ) = Pi.single 0 1
  simp

/-- **The induced metric of the slices `x⁰ = const` is the Euclidean metric of the spatial coordinates.** -/
theorem spatialMetric_minkowski (x : Fin (n + 1) → ℝ) (u v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) x) :
    spatialMetric (mink n) (fun y => y 0) x u v = ∑ i : Fin n, u i.succ * v i.succ := by
  simp only [spatialMetric, unitNormal_minkowski]
  show Lightlike.minkowskiForm (n + 1) u v +
      Lightlike.minkowskiForm (n + 1) (Pi.single 0 1) u * Lightlike.minkowskiForm (n + 1) (Pi.single 0 1) v = _
  erw [Lightlike.minkowskiForm_apply, Lightlike.minkowskiForm_apply, Lightlike.minkowskiForm_apply]
  simp [Fin.sum_univ_succ, Pi.single_apply, Lightlike.etaDiag, Fin.succ_ne_zero]

/-- Trust check: a coordinate with a spacelike gradient is not a time function. -/
theorem not_isTimeFunction_minkowski_x1 :
    ¬ IsTimeFunction (mink 1) (fun y : Fin 2 → ℝ => y 1) := by
  intro h
  have hg : timeGrad (mink 1) (fun y : Fin 2 → ℝ => y 1) 0 =
      (Pi.single 1 1 : TangentSpace 𝓘(ℝ, Fin (1 + 1) → ℝ) (0 : Fin 2 → ℝ)) := by
    apply Lightlike.eq_of_g_eq (mink 1) 0
    intro u
    rw [g_timeGrad, dTime_coord]
    show (u : Fin 2 → ℝ) 1 = Lightlike.minkowskiForm (1 + 1) (Pi.single 1 1) u
    erw [Lightlike.minkowskiForm_apply]
    simp [Fin.sum_univ_two, Pi.single_apply, Lightlike.etaDiag]
  have := h.timelike 0
  rw [hg] at this
  change Lightlike.minkowskiForm (1 + 1) (Pi.single 1 1) (Pi.single 1 1) < 0 at this
  simp [Fin.sum_univ_two, Pi.single_apply, Lightlike.etaDiag] at this
  norm_num at this

end Lightlike.Canonical

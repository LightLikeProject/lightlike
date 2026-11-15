import Mathlib
import Lightlike.Regge.Linear.Taylor1D
import Lightlike.Regge.Linear.Model
import Lightlike.Spacetime.Curvature

/-!
# Second-order Taylor bound for smooth compactly supported functions of the plane

For `u` of class `C³` with compact support on `Fin 2 → ℝ` there is a constant `K` with
`|u (P + y) - T₂ u P y| ≤ K ‖y‖³` for all `P` and `y`, where `T₂ u P` is the quadratic Taylor
polynomial given by the `Jet` of `u` at `P`.
-/

open Set

namespace Lightlike.Regge.Linear

noncomputable section

/-- The 2-jet of a scalar function at a point, from its partial derivatives. -/
def jetOf (u : (Fin 2 → ℝ) → ℝ) (P : Fin 2 → ℝ) : Jet :=
  ⟨u P, Lightlike.pd 0 u P, Lightlike.pd 1 u P, Lightlike.pd 0 (Lightlike.pd 0 u) P,
    Lightlike.pd 0 (Lightlike.pd 1 u) P, Lightlike.pd 1 (Lightlike.pd 1 u) P⟩

variable {u : (Fin 2 → ℝ) → ℝ}

/-- The second derivative of `u` at `P` applied to `y, y` is the quadratic form of the jet. -/
lemma sndDeriv_apply (hu : ContDiff ℝ 3 u) (P y : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ u) P y y =
      ((jetOf u P).a * y 0 ^ 2 + 2 * (jetOf u P).b * y 0 * y 1 + (jetOf u P).c * y 1 ^ 2) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) P :=
    ((hu.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) P
  have hsym := (hu.contDiffAt (x := P)).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  have key : ∀ i j : Fin 2, Lightlike.pd i (Lightlike.pd j u) P =
      fderiv ℝ (fderiv ℝ u) P (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    have h1 : HasFDerivAt (fun x => fderiv ℝ u x (Pi.single j 1 : Fin 2 → ℝ))
        ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 2 → ℝ)).comp
          (fderiv ℝ (fderiv ℝ u) P)) P :=
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 2 → ℝ)).hasFDerivAt.comp P
        hd.hasFDerivAt
    have h2 : Lightlike.pd j u = fun x => fderiv ℝ u x (Pi.single j 1 : Fin 2 → ℝ) := rfl
    rw [h2]
    unfold Lightlike.pd
    rw [h1.fderiv]
    rfl
  have hy : y = y 0 • (Pi.single 0 1 : Fin 2 → ℝ) + y 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    funext k; fin_cases k <;> simp
  have s01 : fderiv ℝ (fderiv ℝ u) P (Pi.single 1 1) (Pi.single 0 1) =
      fderiv ℝ (fderiv ℝ u) P (Pi.single 0 1) (Pi.single 1 1) := hsym _ _
  conv_lhs => rw [hy]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  simp only [jetOf, key]
  rw [s01]
  ring

/-- The first derivative of `u` at `P` applied to `y` is the linear part of the jet. -/
lemma fstDeriv_apply (P y : Fin 2 → ℝ) :
    fderiv ℝ u P y = (jetOf u P).g0 * y 0 + (jetOf u P).g1 * y 1 := by
  have hy : y = y 0 • (Pi.single 0 1 : Fin 2 → ℝ) + y 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    funext k; fin_cases k <;> simp
  conv_lhs => rw [hy]
  simp only [map_add, map_smul, smul_eq_mul, jetOf, Lightlike.pd]
  ring

/-- **Second-order Taylor bound.** For `u` of class `C³` with compact support there is `K` with
`|u (P + y) - T₂ u P y| ≤ K ‖y‖³` for all `P` and `y`. -/
theorem taylor_bound (hu : ContDiff ℝ 3 u) (hc : HasCompactSupport u) :
    ∃ K : ℝ, ∀ P y : Fin 2 → ℝ, |u (P + y) - (jetOf u P).eval y| ≤ K * ‖y‖ ^ 3 := by
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hcs : HasCompactSupport (fderiv ℝ (fderiv ℝ u)) := (hc.fderiv ℝ).fderiv ℝ
  have hl := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (n := 1)
    (f := fderiv ℝ (fderiv ℝ u)) hcs hD2 (by simp)
  obtain ⟨Λ, hΛ⟩ := hl
  have hd1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  refine ⟨Λ / 6, fun P y => ?_⟩
  have line : ∀ t : ℝ, HasDerivAt (fun t : ℝ => P + t • y) y t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const y).const_add P
  have hG : ∀ t : ℝ, HasDerivAt (fun t : ℝ => u (P + t • y)) (fderiv ℝ u (P + t • y) y) t :=
    fun t => (hd1 (P + t • y)).hasFDerivAt.comp_hasDerivAt t (line t)
  have hG1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ u (P + t • y) y)
      (fderiv ℝ (fderiv ℝ u) (P + t • y) y y) t := fun t => by
    have h1 : HasFDerivAt (fun x => fderiv ℝ u x y)
        ((ContinuousLinearMap.apply ℝ ℝ y).comp (fderiv ℝ (fderiv ℝ u) (P + t • y)))
        (P + t • y) :=
      (ContinuousLinearMap.apply ℝ ℝ y).hasFDerivAt.comp _ (hd2 _).hasFDerivAt
    exact h1.comp_hasDerivAt t (line t)
  have hL : ∀ t ∈ Icc (0 : ℝ) 1, |fderiv ℝ (fderiv ℝ u) (P + t • y) y y
      - fderiv ℝ (fderiv ℝ u) (P + (0 : ℝ) • y) y y| ≤ (Λ * ‖y‖ ^ 3) * t := by
    intro t ht
    have e : fderiv ℝ (fderiv ℝ u) (P + t • y) y y
        - fderiv ℝ (fderiv ℝ u) (P + (0 : ℝ) • y) y y =
        (fderiv ℝ (fderiv ℝ u) (P + t • y) - fderiv ℝ (fderiv ℝ u) (P + (0 : ℝ) • y)) y y := by
      simp
    rw [e]
    have hn : ‖(fderiv ℝ (fderiv ℝ u) (P + t • y) - fderiv ℝ (fderiv ℝ u) (P + (0 : ℝ) • y))‖
        ≤ Λ * (t * ‖y‖) := by
      have := hΛ.dist_le_mul (P + t • y) (P + (0 : ℝ) • y)
      rw [dist_eq_norm, dist_eq_norm] at this
      have e2 : P + t • y - (P + (0 : ℝ) • y) = t • y := by simp
      rw [e2, norm_smul, Real.norm_of_nonneg ht.1] at this
      simpa using this
    calc _ ≤ ‖(fderiv ℝ (fderiv ℝ u) (P + t • y) - fderiv ℝ (fderiv ℝ u) (P + (0 : ℝ) • y))‖
          * ‖y‖ * ‖y‖ := by
          set A := fderiv ℝ (fderiv ℝ u) (P + t • y) - fderiv ℝ (fderiv ℝ u) (P + (0 : ℝ) • y)
          have h1 : ‖A y y‖ ≤ ‖A y‖ * ‖y‖ := (A y).le_opNorm y
          have h2 : ‖A y‖ ≤ ‖A‖ * ‖y‖ := A.le_opNorm y
          rw [← Real.norm_eq_abs]
          calc ‖A y y‖ ≤ ‖A y‖ * ‖y‖ := h1
            _ ≤ ‖A‖ * ‖y‖ * ‖y‖ := by gcongr
      _ ≤ Λ * (t * ‖y‖) * ‖y‖ * ‖y‖ := by gcongr
      _ = (Λ * ‖y‖ ^ 3) * t := by ring
  have := taylor2_line hG hG1 hL
  simp only [zero_smul, add_zero, one_smul] at this
  rw [fstDeriv_apply, sndDeriv_apply hu] at this
  have e3 : u (P + y) - (jetOf u P).eval y = u (P + y) - u P - ((jetOf u P).g0 * y 0 +
      (jetOf u P).g1 * y 1) - ((jetOf u P).a * y 0 ^ 2 + 2 * (jetOf u P).b * y 0 * y 1 +
        (jetOf u P).c * y 1 ^ 2) / 2 := by
    unfold Jet.eval; simp [jetOf]; ring
  rw [e3]
  calc _ ≤ Λ * ‖y‖ ^ 3 / 6 := this
    _ = _ := by ring

end

end Lightlike.Regge.Linear

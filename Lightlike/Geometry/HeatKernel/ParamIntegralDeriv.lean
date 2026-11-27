import Mathlib
import Lightlike.Lorentz.ParamIntegral

/-!
# Iterated derivatives of parametric integrals

For `Φ : P → E → G` jointly smooth and vanishing for `‖q‖ > R`, the iterated derivatives of `x ↦ ∫ Φ(q, x) dq` are
the integrals of the partial iterated derivatives (`iteratedFDeriv_integral_eq`). The partial iterated derivative in
the second variable is the full one composed with the inclusion `inr` (`iteratedFDeriv_partial_eq`), hence jointly
smooth (`contDiff_iteratedFDeriv_partial`). The first-order step is `Lightlike.Lorentz.hasFDerivAt_parametric_integral`.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- **The partial iterated derivative in the second variable**: the full iterated derivative along `inr`. -/
theorem iteratedFDeriv_partial_eq {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {Φ : P → E → G}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) (m : ℕ) (q : P) (x : E) :
    iteratedFDeriv ℝ m (Φ q) x =
      (iteratedFDeriv ℝ m (Function.uncurry Φ) (q, x)).compContinuousLinearMap
        fun _ => ContinuousLinearMap.inr ℝ P E := by
  have hfun : Φ q = (fun z => Function.uncurry Φ (z + (q, 0))) ∘ (ContinuousLinearMap.inr ℝ P E) := by
    funext x; simp
  have hs : ContDiff ℝ ∞ (fun z : P × E => Function.uncurry Φ (z + (q, 0))) :=
    hΦ.comp (contDiff_id.add contDiff_const)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (f := fun z : P × E => Function.uncurry Φ (z + (q, 0)))
    _ hs x (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]
  congr 2
  simp

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- **The partial iterated derivative is jointly smooth.** -/
theorem contDiff_iteratedFDeriv_partial {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {Φ : P → E → G}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) (m : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry fun q x => iteratedFDeriv ℝ m (Φ q) x) := by
  have hfun : (Function.uncurry fun q x => iteratedFDeriv ℝ m (Φ q) x) = fun z =>
      (ContinuousMultilinearMap.compContinuousLinearMapL (F := G)
        fun _ : Fin m => ContinuousLinearMap.inr ℝ P E) (iteratedFDeriv ℝ m (Function.uncurry Φ) z) := by
    funext z; exact iteratedFDeriv_partial_eq hΦ m z.1 z.2
  rw [hfun]
  exact (ContinuousLinearMap.contDiff _).comp (hΦ.iteratedFDeriv_right (m := ∞) (i := m) (by simp))

variable [MeasureSpace P] [BorelSpace P] [IsFiniteMeasureOnCompacts (volume : Measure P)]

/-- **Iterated derivatives commute with a compactly supported parametric integral.** -/
theorem iteratedFDeriv_integral_eq (m : ℕ) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {Φ : P → E → G} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) {R : ℝ} (h0 : ∀ q, R < ‖q‖ → ∀ x, Φ q x = 0) :
    iteratedFDeriv ℝ m (fun x => ∫ q, Φ q x) = fun x => ∫ q, iteratedFDeriv ℝ m (Φ q) x := by
  induction m generalizing G with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    have := LinearIsometry.integral_comp_comm (μ := (volume : Measure P))
      (continuousMultilinearCurryFin0 ℝ E G).symm.toLinearIsometry (fun q => Φ q x)
    simpa using this.symm
  | succ m ih =>
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hΦ h0]
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hΨ := contDiff_iteratedFDeriv_partial hΦ m
    have hΨ0 : ∀ᵐ q ∂(volume : Measure P), q ∉ closedBall (0 : P) R → ∀ x,
        iteratedFDeriv ℝ m (Φ q) x = 0 := Eventually.of_forall fun q hq x => by
      have hR : R < ‖q‖ := by rw [mem_closedBall, dist_zero_right, not_le] at hq; exact hq
      have : Φ q = fun _ => 0 := funext fun x => h0 q hR x
      rw [this, iteratedFDeriv_fun_zero]; rfl
    have hd := Lightlike.Lorentz.hasFDerivAt_parametric_integral (μ := (volume : Measure P))
      (Φ := fun q x => iteratedFDeriv ℝ m (Φ q) x) (hΨ.of_le (by exact_mod_cast le_top)) aestronglyMeasurable_id
      measurableSet_closedBall measure_closedBall_lt_top.ne
      (Eventually.of_forall fun q hq => by rwa [mem_closedBall, dist_zero_right] at hq) hΨ0 x
    simp only [id] at hd
    rw [hd.fderiv]
    let L : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => E) G) ≃L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) G :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) G).symm.toContinuousLinearEquiv
    have := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := (volume : Measure P)) L
      (fun q => fderiv ℝ (iteratedFDeriv ℝ m (Φ q)) x)
    exact this.symm

end Lightlike

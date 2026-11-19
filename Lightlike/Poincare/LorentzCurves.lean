module

public import Lightlike.Poincare.GeneratorCurves
public import Lightlike.Poincare.PauliLubanskiAlgebra

/-!
# Curves in `SL(2,ℂ)` with the Lorentz generators as velocities

For a traceless `Y` with `det Y = −1/4` the curve `cosh(t/2) + 2 sinh(t/2) Y` lies in `SL(2,ℂ)`, and for
`det Y = 1/4` so does `cos(t/2) + 2 sin(t/2) Y`; both pass through `1` with velocity `Y` (`exists_isCurveAt`).
Every Lorentz generator `lorGen ν ρ` is of one of these kinds or zero, so each has a curve (`exists_lorCurve`): the
boosts `±½ σ_k` and the rotations `±(i/2) σ_k`.

Supporting lemmas; no catalogue entry.
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz Complex

namespace Lightlike.Poincare

lemma det_smul_one_add (a b : ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + b • Y).det = a ^ 2 + a * b * Y.trace + b ^ 2 * Y.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring

/-- The curve `f(t) + g(t) Y` in `SL(2,ℂ)`. -/
def curveOf (Y : Matrix (Fin 2) (Fin 2) ℂ) (f g : ℝ → ℝ)
    (hdet : ∀ t, ((f t : ℂ)) ^ 2 + (g t : ℂ) ^ 2 * Y.det = 1) (htr : Y.trace = 0) : ℝ → SL2C :=
  fun t => ⟨(f t : ℂ) • 1 + (g t : ℂ) • Y, by rw [det_smul_one_add, htr]; simpa using hdet t⟩

lemma isCurveAt_curveOf (Y : Matrix (Fin 2) (Fin 2) ℂ) (f g : ℝ → ℝ)
    (hdet : ∀ t, ((f t : ℂ)) ^ 2 + (g t : ℂ) ^ 2 * Y.det = 1) (htr : Y.trace = 0)
    (hf0 : f 0 = 1) (hg0 : g 0 = 0) (hf : HasDerivAt f 0 0) (hg : HasDerivAt g 1 0) :
    IsCurveAt (curveOf Y f g hdet htr) Y := by
  refine ⟨?_, fun i j => ?_⟩
  · simp [curveOf, hf0, hg0]
  · have h := (hf.ofReal_comp.mul_const ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)).add
      (hg.ofReal_comp.mul_const (Y i j))
    have e : (fun t => ((curveOf Y f g hdet htr t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j) =
        (fun y => ((f y : ℝ) : ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) + fun y => ((g y : ℝ) : ℂ) * Y i j := by
      funext t; simp [curveOf]
    rw [e]
    refine h.congr_deriv ?_
    simp

/-- **Curves with a given velocity**: a traceless `Y` with `det Y = ∓1/4` is the velocity of a curve in `SL(2,ℂ)`
through `1`. -/
theorem exists_isCurveAt (Y : Matrix (Fin 2) (Fin 2) ℂ) (htr : Y.trace = 0)
    (hd : Y.det = -(1 / 4) ∨ Y.det = 1 / 4 ∨ Y = 0) : ∃ γ : ℝ → SL2C, IsCurveAt γ Y := by
  rcases hd with hd | hd | hd
  · have hdet : ∀ t, ((Real.cosh (t / 2) : ℝ) : ℂ) ^ 2 + ((2 * Real.sinh (t / 2) : ℝ) : ℂ) ^ 2 * Y.det = 1 := by
      intro t
      have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.cosh_sq_sub_sinh_sq (t / 2))
      push_cast at h ⊢
      rw [hd]
      linear_combination h
    refine ⟨curveOf Y (fun t => Real.cosh (t / 2)) (fun t => 2 * Real.sinh (t / 2)) hdet htr,
      isCurveAt_curveOf Y _ _ hdet htr (by simp) (by simp) ?_ ?_⟩
    · simpa using ((hasDerivAt_id' (0 : ℝ)).div_const 2).cosh
    · convert (((hasDerivAt_id' (0 : ℝ)).div_const 2).sinh).const_mul 2 using 1
      norm_num
  · have hdet : ∀ t, ((Real.cos (t / 2) : ℝ) : ℂ) ^ 2 + ((2 * Real.sin (t / 2) : ℝ) : ℂ) ^ 2 * Y.det = 1 := by
      intro t
      have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.cos_sq_add_sin_sq (t / 2))
      push_cast at h ⊢
      rw [hd]
      linear_combination h
    refine ⟨curveOf Y (fun t => Real.cos (t / 2)) (fun t => 2 * Real.sin (t / 2)) hdet htr,
      isCurveAt_curveOf Y _ _ hdet htr (by simp) (by simp) ?_ ?_⟩
    · simpa using ((hasDerivAt_id' (0 : ℝ)).div_const 2).cos
    · convert (((hasDerivAt_id' (0 : ℝ)).div_const 2).sin).const_mul 2 using 1
      norm_num
  · subst hd
    exact ⟨fun _ => 1, ⟨rfl, fun i j => by simpa using hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)⟩⟩

/-- **Every Lorentz generator is the velocity of a curve in `SL(2,ℂ)`.** -/
theorem exists_lorCurve (ν ρ : Fin 4) : ∃ γ : ℝ → SL2C, IsCurveAt γ (lorGen ν ρ) := by
  refine exists_isCurveAt _ ?_ ?_
  · fin_cases ν <;> fin_cases ρ <;> simp [lorGen, pauliM, Matrix.trace_fin_two]
  · fin_cases ν <;> fin_cases ρ <;>
      first
      | (right; right; simp [lorGen]; done)
      | (left; simp [lorGen, pauliM, Matrix.det_fin_two]; ring_nf; (try simp [Complex.ext_iff]); (try norm_num); done)
      | (right; left; simp [lorGen, pauliM, Matrix.det_fin_two]; ring_nf; (try simp [Complex.ext_iff]);
          (try norm_num); done)

/-- A choice of curves for the Lorentz generators. -/
def lorCurve (ν ρ : Fin 4) : ℝ → SL2C := (exists_lorCurve ν ρ).choose

lemma isCurveAt_lorCurve (ν ρ : Fin 4) : IsCurveAt (lorCurve ν ρ) (lorGen ν ρ) :=
  (exists_lorCurve ν ρ).choose_spec

end Lightlike.Poincare

module

public import Lightlike.Poincare.WignerRotation

/-!
# Curves in `SL(2,ℂ)` and their action on momenta, to first order

A curve `γ` in `SL(2,ℂ)` through `1` with entrywise velocity `X` (`IsCurveAt γ X`) has a traceless velocity
(`IsCurveAt.trace_eq_zero`), its inverse has velocity `−X` (`IsCurveAt.inv`), and the moved momentum
`t ↦ γ(t)⁻¹ • P = γ(t)⁻¹ P γ(t)⁻¹ᴴ` has velocity `−(X P + P Xᴴ)` (`hasDerivAt_actP_inv`). This is the first-order
calculus behind the generators of the induced representations.

Supporting lemmas; no catalogue entry.
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz

namespace Lightlike.Poincare

/-- A curve through `1` in `SL(2,ℂ)` with entrywise velocity `X` at `0`. -/
structure IsCurveAt (γ : ℝ → SL2C) (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop where
  zero : ((γ 0 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1
  deriv : ∀ i j, HasDerivAt (fun t => ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j) (X i j) 0

/-- The velocity of a curve in `SL(2,ℂ)` is traceless. -/
lemma IsCurveAt.trace_eq_zero {γ : ℝ → SL2C} {X : Matrix (Fin 2) (Fin 2) ℂ} (h : IsCurveAt γ X) :
    X.trace = 0 := by
  have hdet : HasDerivAt (fun t => ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ).det)
      (X 0 0 * 1 + 1 * X 1 1 - (X 0 1 * 0 + 0 * X 1 0)) 0 := by
    have e : ∀ i j, ((γ 0 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j :=
      fun i j => by rw [h.zero]
    have h00 := h.deriv 0 0; have h01 := h.deriv 0 1; have h10 := h.deriv 1 0; have h11 := h.deriv 1 1
    simp only [Matrix.det_fin_two]
    have := ((h00.mul h11).sub (h01.mul h10))
    simp only [e, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at this
    convert this using 1
  have hconst : (fun t => ((γ t : SL2C) : Matrix (Fin 2) (Fin 2) ℂ).det) = fun _ => 1 := by
    funext t; exact (γ t).2
  rw [hconst] at hdet
  have := hdet.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  rw [Matrix.trace_fin_two]
  linear_combination this

/-- The inverse curve has velocity `−X`. -/
lemma IsCurveAt.inv {γ : ℝ → SL2C} {X : Matrix (Fin 2) (Fin 2) ℂ} (h : IsCurveAt γ X) :
    IsCurveAt (fun t => (γ t)⁻¹) (-X) := by
  have htr := h.trace_eq_zero
  rw [Matrix.trace_fin_two] at htr
  refine ⟨?_, fun i j => ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_inv, h.zero, Matrix.adjugate_one]
  · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · simpa [show X 1 1 = -X 0 0 by linear_combination htr] using h.deriv 1 1
    · have := (h.deriv 0 1).neg
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons]
      exact this
    · have := (h.deriv 1 0).neg
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons]
      exact this
    · simpa [show X 0 0 = -X 1 1 by linear_combination htr] using h.deriv 0 0

/-- Product rule for `A(t) P A(t)ᴴ`, entrywise. -/
lemma hasDerivAt_conj_mul {A : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {A' : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀ a b, HasDerivAt (fun t => A t a b) (A' a b) 0) (P : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    HasDerivAt (fun t => (A t * P * (A t)ᴴ) i j) ((A' * P * (A 0)ᴴ + A 0 * P * A'ᴴ) i j) 0 := by
  have h : (fun t => (A t * P * (A t)ᴴ) i j) =
      fun t => ∑ k, ∑ l, A t i l * P l k * star (A t j k) := by
    funext t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [h]
  have e : ((A' * P * (A 0)ᴴ + A 0 * P * A'ᴴ) i j) =
      ∑ k, ∑ l, (A' i l * P l k * star (A 0 j k) + A 0 i l * P l k * star (A' j k)) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      Finset.sum_add_distrib]
  rw [e]
  refine HasDerivAt.fun_sum fun k _ => HasDerivAt.fun_sum fun l _ => ?_
  have := (((hA i l).mul_const (P l k)).mul (hA j k).star)
  convert this using 1

/-- Product rule for `A(t) B(t)`, entrywise. -/
lemma hasDerivAt_mul_entry {A B : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {A' B' : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀ a b, HasDerivAt (fun t => A t a b) (A' a b) 0) (hB : ∀ a b, HasDerivAt (fun t => B t a b) (B' a b) 0)
    (i j : Fin 2) : HasDerivAt (fun t => (A t * B t) i j) ((A' * B 0 + A 0 * B') i j) 0 := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).mul (hB k j)

/-- **The moved momentum to first order**: `d/dt (γ(t)⁻¹ • P) = −(X P + P Xᴴ)` at `t = 0`. -/
lemma hasDerivAt_actP_inv {γ : ℝ → SL2C} {X : Matrix (Fin 2) (Fin 2) ℂ} (h : IsCurveAt γ X)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    HasDerivAt (fun t => actP (γ t)⁻¹ P i j) (-(X * P + P * Xᴴ) i j) 0 := by
  have hi := h.inv
  have H : HasDerivAt (fun t => actP (γ t)⁻¹ P i j)
      ((-X * P * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ + (1 : Matrix (Fin 2) (Fin 2) ℂ) * P * (-X)ᴴ :
        Matrix (Fin 2) (Fin 2) ℂ) i j) 0 := by
    have := hasDerivAt_conj_mul (A := fun t => (((γ t)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) hi.deriv P i j
    rw [hi.zero] at this
    exact this
  refine H.congr_deriv ?_
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_neg,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.add_apply, Matrix.neg_apply]
  ring

end Lightlike.Poincare

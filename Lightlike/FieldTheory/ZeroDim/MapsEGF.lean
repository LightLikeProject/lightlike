import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Counting maps by their fibres: the exponential generating function of a product

For weights `m v : ℕ → A` on the vertices `v : Fin k`, the sum over all maps `f : Fin n → Fin k` of
`∏_v m v |f⁻¹(v)|` is `n!` times the coefficient of `x^n` in `∏_v Σ_d m v d x^d/d!` (`sum_maps_prod_fiber`). This is
the count behind the Feynman rules of a zero-dimensional theory: the half-edges are distributed over the vertices, and
a vertex with `d` half-edges carries the weight of its degree. The proof is by induction on `n`, removing the first
half-edge; on the generating function this is the derivative, through the product rule `derivative_prod_univ`.
-/

open Finset PowerSeries

noncomputable section

namespace Lightlike.FieldTheory.GraphAlg

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- **The product rule** for a product over `Fin k`. -/
theorem derivative_prod_univ {R : Type*} [CommRing R] : ∀ {k : ℕ} (E : Fin k → PowerSeries R),
    d⁄dX (∏ v, E v) = ∑ a, ∏ v, (if v = a then d⁄dX (E v) else E v)
  | 0, E => by simp
  | k + 1, E => by
    rw [Fin.prod_univ_succ, Derivation.leibniz, derivative_prod_univ (fun i => E i.succ), Fin.sum_univ_succ,
      Fin.prod_univ_succ, if_pos rfl, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    have h0 : ∀ i : Fin k, (if i.succ = (0 : Fin (k + 1)) then d⁄dX (E i.succ) else E i.succ) = E i.succ :=
      fun i => if_neg (Fin.succ_ne_zero i)
    simp_rw [h0]
    rw [add_comm]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Fin.prod_univ_succ, if_neg (Fin.succ_ne_zero b).symm]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by simp only [Fin.succ_inj]

/-- The exponential generating function of a weight sequence: `Σ_d g d x^d/d!`. -/
def egf (g : ℕ → A) : PowerSeries A := PowerSeries.mk fun d => algebraMap ℚ A ((d.factorial : ℚ)⁻¹) * g d

lemma coeff_egf (g : ℕ → A) (d : ℕ) : coeff d (egf g) = algebraMap ℚ A ((d.factorial : ℚ)⁻¹) * g d := by
  simp [egf]

/-- The derivative of an exponential generating function shifts the sequence. -/
lemma derivative_egf (g : ℕ → A) : d⁄dX (egf g) = egf (fun d => g (d + 1)) := by
  ext d
  rw [coeff_derivative, coeff_egf, coeff_egf]
  have hd : ((d + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hd' : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have key : ((d + 1).factorial : ℚ)⁻¹ * ((d : ℚ) + 1) = (d.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; field_simp
  calc algebraMap ℚ A (((d + 1).factorial : ℚ)⁻¹) * g (d + 1) * ((d : A) + 1)
      = algebraMap ℚ A (((d + 1).factorial : ℚ)⁻¹ * ((d : ℚ) + 1)) * g (d + 1) := by
        rw [map_mul]; push_cast; ring
    _ = _ := by rw [key]

/-- The fibre of a vertex under `Fin.cons a g`. -/
lemma card_fiber_cons {n k : ℕ} (a : Fin k) (g : Fin n → Fin k) (v : Fin k) :
    (univ.filter fun h => (Fin.cons a g : Fin (n + 1) → Fin k) h = v).card =
      (univ.filter fun h => g h = v).card + if a = v then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- **Counting maps by their fibres**: `Σ_{f : Fin n → Fin k} ∏_v m v |f⁻¹ v| = n! [x^n] ∏_v egf (m v)`. -/
theorem sum_maps_prod_fiber : ∀ (n : ℕ) {k : ℕ} (m : Fin k → ℕ → A),
    ∑ f : Fin n → Fin k, ∏ v, m v (univ.filter fun h => f h = v).card =
      algebraMap ℚ A (n.factorial : ℚ) * coeff n (∏ v, egf (m v))
  | 0, k, m => by
    rw [Fintype.sum_unique, Nat.factorial_zero, Nat.cast_one, map_one, one_mul, coeff_zero_eq_constantCoeff,
      map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_egf, Nat.factorial_zero, Nat.cast_one, inv_one, map_one,
      one_mul]
    simp
  | n + 1, k, m => by
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin k).sum_comp, Fintype.sum_prod_type]
    have hcard : ∀ (a : Fin k) (g : Fin n → Fin k) (v : Fin k),
        (univ.filter fun h => (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k) (a, g)) h = v).card =
          (univ.filter fun h => g h = v).card + if a = v then 1 else 0 := fun a g v => card_fiber_cons a g v
    simp_rw [hcard]
    have step : ∀ a : Fin k, (∑ g : Fin n → Fin k, ∏ v, m v ((univ.filter fun h => g h = v).card +
        if a = v then 1 else 0)) =
        algebraMap ℚ A (n.factorial : ℚ) * coeff n (∏ v, (if v = a then d⁄dX (egf (m v)) else egf (m v))) := by
      intro a
      refine (sum_maps_prod_fiber n (fun v d => m v (d + if a = v then 1 else 0))).trans ?_
      congr 2
      refine Finset.prod_congr rfl fun v _ => ?_
      by_cases h : v = a
      · subst h
        rw [if_pos rfl, derivative_egf]
        simp only [if_true]
      · rw [if_neg h]
        have h' : a ≠ v := fun e => h e.symm
        simp only [h', if_false, add_zero]
    simp_rw [step]
    rw [← Finset.mul_sum, ← map_sum, ← derivative_prod_univ, coeff_derivative, Nat.factorial_succ, Nat.cast_mul,
      map_mul]
    push_cast
    ring

end Lightlike.FieldTheory.GraphAlg

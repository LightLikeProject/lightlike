import Mathlib
import Lightlike.Canonical.HamiltonianDeriv

/-!
# The coefficient `W^b` of the bracket of two Hamiltonian constraints

`W^b = Ψ_b − Θ_a^b − Θ_d^b`: explicit in terms of the 1-jet of the metric, the unit `π`-gradient `P` and its
derivative.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma s3a (b : Fin d) (F : Fin d → Fin d → Fin d → ℝ) :
    (∑ x, ∑ y, ∑ z, if x = b then F x y z else 0) = ∑ y, ∑ z, F b y z := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx; simp [hx]
  · simp

lemma s3b (b : Fin d) (F : Fin d → Fin d → Fin d → ℝ) :
    (∑ x, ∑ y, ∑ z, if y = b then F x y z else 0) = ∑ x, ∑ z, F x b z := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro y _ hy; simp [hy]
  · simp

lemma s2a (b : Fin d) (F : Fin d → Fin d → ℝ) :
    (∑ x, ∑ y, if x = b then F x y else 0) = ∑ y, F b y := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx; simp [hx]
  · simp

lemma s2b (b : Fin d) (F : Fin d → Fin d → ℝ) :
    (∑ x, ∑ y, if y = b then F x y else 0) = ∑ x, F x b := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

/-- `w^ρ` of the jet `δ_b ⊗ P`: `h^{ρl} h^{bν} P_{lν} − h^{ρb} tr (h⁻¹ P)`. -/
lemma wJ_delta {Hi P : Matrix (Fin d) (Fin d) ℝ} (hHi : ∀ a b, Hi a b = Hi b a)
    (hP : ∀ a b, P a b = P b a) (b ρ : Fin d) :
    wJ Hi (fun a i j => if a = b then P i j else 0) ρ =
      (∑ l, ∑ ν, Hi ρ l * Hi b ν * P l ν) - Hi ρ b * ∑ σ, ∑ ν, Hi σ ν * P σ ν := by
  unfold wJ gamJ
  simp only [mul_ite, mul_zero, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, s3a, s3b, s2a, s2b]
  set R1 := ∑ l, ∑ ν, Hi ρ l * Hi b ν * P l ν with hR1
  set tr := ∑ σ, ∑ ν, Hi σ ν * P σ ν with htr
  have fin : ∀ a c : Fin d, ∀ (X Y : ℝ), X = Y → X = Y := fun _ _ _ _ h => h
  have t1 : ∑ y, ∑ z, Hi b y * (1 / 2 * (Hi ρ z * P z y)) = 1 / 2 * R1 := by
    simp only [hR1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    first | ring1 | (rw [hHi c b]; ring1) | (rw [hHi b c]; ring1) | (rw [hP c a]; ring1) | (rw [hP a c]; ring1)
  have t2 : ∑ x, ∑ y, Hi x b * (1 / 2 * (Hi ρ y * P y x)) = 1 / 2 * R1 := by
    simp only [hR1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    first | ring1 | (rw [hHi c b]; ring1) | (rw [hHi b c]; ring1) | (rw [hP c a]; ring1) | (rw [hP a c]; ring1)
  have t3 : ∑ x, ∑ x_1, Hi x x_1 * (1 / 2 * (Hi ρ b * P x x_1)) = 1 / 2 * Hi ρ b * tr := by
    simp only [htr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have t4 : ∑ y, ∑ z, Hi ρ b * (1 / 2 * (Hi y z * P z y)) = 1 / 2 * Hi ρ b * tr := by
    simp only [htr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    first | ring1 | (rw [hP c a]; ring1) | (rw [hP a c]; ring1)
  have t5 : ∑ x, ∑ i, Hi ρ x * (1 / 2 * (Hi b i * P i x)) = 1 / 2 * R1 := by
    simp only [hR1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    first | ring1 | (rw [hP c a]; ring1) | (rw [hP a c]; ring1)
  have t6 : ∑ x, ∑ i, Hi ρ x * (1 / 2 * (Hi i b * P x i)) = 1 / 2 * R1 := by
    simp only [hR1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    first | ring1 | (rw [hHi c b]; ring1) | (rw [hHi b c]; ring1)
  have t7 : ∑ x, ∑ i, Hi ρ b * (Hi x i * P x i) = Hi ρ b * tr := by
    simp only [htr, Finset.mul_sum]
  rw [t1, t2, t3, t4, t5, t6, t7]
  ring

end Lightlike.Canonical

end

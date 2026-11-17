import Mathlib
import Lightlike.Canonical.DensityCovariance

/-!
# The pairing of a covariant tensor with a tensor density is a scalar density

For a covariant tensor field `G` and a symmetric... tensor density `π` of weight one,
`π^{ij} (ℒ_ξ G)_ij + G_ij (ℒ_ξ π)^{ij} = ∂_k (ξ^k π^{ij} G_ij)`.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma sum3_comm13 (f : Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k := by
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

lemma sum3_cyc (f : Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ i, ∑ j, f i j k := by
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm

/-- The algebra of the pairing identity, on arrays. -/
lemma pairing_alg (π G : Fin d → Fin d → ℝ) (ξ : Fin d → ℝ) (X : Fin d → Fin d → ℝ)
    (dπ dG : Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, (π i j * (∑ k, ξ k * dG k i j + ∑ k, G k j * X i k + ∑ k, G i k * X j k) +
        G i j * (∑ k, ξ k * dπ k i j - ∑ k, π k j * X k i - ∑ k, π i k * X k j + (∑ k, X k k) * π i j)) =
      ∑ k, (X k k * ∑ i, ∑ j, π i j * G i j +
        ξ k * ∑ i, ∑ j, (dπ k i j * G i j + π i j * dG k i j)) := by
  have e1 : ∑ i, ∑ j, ∑ k, G i j * (π k j * X k i) = ∑ i, ∑ j, ∑ k, π i j * (G k j * X i k) := by
    rw [sum3_comm13 (fun i j k => G i j * (π k j * X k i))]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ i, ∑ j, ∑ k, G i j * (π i k * X k j) = ∑ i, ∑ j, ∑ k, π i j * (G i k * X j k) := by
    calc ∑ i, ∑ j, ∑ k, G i j * (π i k * X k j) = ∑ i, ∑ k, ∑ j, G i j * (π i k * X k j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, π i j * (G i k * X j k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have e3 : ∑ i, ∑ j, ∑ k, π i j * (ξ k * dG k i j) = ∑ k, ∑ i, ∑ j, ξ k * (π i j * dG k i j) := by
    rw [sum3_cyc]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ i, ∑ j, ∑ k, G i j * (ξ k * dπ k i j) = ∑ k, ∑ i, ∑ j, ξ k * (dπ k i j * G i j) := by
    rw [sum3_cyc]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e5 : ∑ i, ∑ j, ∑ k, G i j * (X k k * π i j) = ∑ k, ∑ i, ∑ j, X k k * (π i j * G i j) := by
    rw [sum3_cyc]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith [e1, e2, e3, e4, e5]

/-- **The pairing of a tensor with a tensor density is a scalar density**, pointwise. -/
theorem pairing_covariance {G π : TensorField d} {ξ : VectorField d} (hξ : SmoothVec ξ) (hG : SmoothTensor G)
    (hπ : SmoothTensor π) (x : Fin d → ℝ) :
    ∑ i, ∑ j, (π x i j * lieDeriv ξ G i j x + G x i j * lieDens ξ π x i j) =
      ∑ k, Lightlike.pd k (fun y => ξ y k * ∑ i, ∑ j, π y i j * G y i j) x := by
  -- the derivative of the right-hand side
  have dG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x := fun i j => diff_of_smooth (hG i j) x
  have dπ : ∀ i j, DifferentiableAt ℝ (fun y => π y i j) x := fun i j => diff_of_smooth (hπ i j) x
  have dΦ : DifferentiableAt ℝ (fun y => ∑ i, ∑ j, π y i j * G y i j) x :=
    DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => (dπ i j).mul (dG i j)
  have hpdΦ : ∀ k, Lightlike.pd k (fun y => ∑ i, ∑ j, π y i j * G y i j) x =
      ∑ i, ∑ j, (Lightlike.pd k (fun y => π y i j) x * G x i j + π x i j * Lightlike.pd k (fun y => G y i j) x) := by
    intro k
    rw [Lightlike.pd_sum Finset.univ (f := fun i y => ∑ j, π y i j * G y i j)
      (fun i _ => DifferentiableAt.fun_sum fun j _ => (dπ i j).mul (dG i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Lightlike.pd_sum Finset.univ (f := fun j y => π y i j * G y i j) (fun j _ => (dπ i j).mul (dG i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Lightlike.pd_mul (dπ i j) (dG i j) k
  have hRHS : ∀ k, Lightlike.pd k (fun y => ξ y k * ∑ i, ∑ j, π y i j * G y i j) x =
      Lightlike.pd k (fun y => ξ y k) x * ∑ i, ∑ j, π x i j * G x i j +
        ξ x k * ∑ i, ∑ j, (Lightlike.pd k (fun y => π y i j) x * G x i j +
          π x i j * Lightlike.pd k (fun y => G y i j) x) := by
    intro k
    rw [Lightlike.pd_mul (diff_of_smooth (hξ k) x) dΦ, hpdΦ k]
  simp only [hRHS]
  unfold lieDeriv lieDens
  simp only [Matrix.of_apply]
  exact pairing_alg (π x) (G x) (ξ x) (dVec ξ x) (fun k i j => Lightlike.pd k (fun y => π y i j) x)
    (fun k i j => Lightlike.pd k (fun y => G y i j) x)

end Lightlike.Canonical

end

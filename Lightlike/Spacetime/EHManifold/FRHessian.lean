import Lightlike.Spacetime.VariationInverse
import Lightlike.Spacetime.EHManifold.FRSecondParts

/-!
# Towards the Hessian form of the `f(R)` field equations

* `dChristoffel0_eq`: `δΓ₀^i_{jk} = -g^{ia} h_{ab} Γ^b_{jk}`.
* `pd_sum_of_differentiableAt`, `pd_sub_of_differentiableAt`: linearity of the partial derivative.
* `pd_hessCoeff`: the derivative of `c^{μαβ} = √|g| (g^{ρα} g^{μβ} - g^{ρμ} g^{αβ}) ∂_ρ φ` by the product
  rule, in terms of the derivatives of `√|g|`, of the inverse metric and of `∂φ`.

Supporting lemma for the `f(R)` field equations; no catalogue entry.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **The values part of the variation of the Christoffel symbols**:
`δΓ₀^i_{jk} = -g^{ia} h_{ab} Γ^b_{jk}`. -/
theorem dChristoffel0_eq (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (y : Fin n → ℝ) :
    dChristoffel0 g h i j k y = -∑ a, ∑ b, (g y)⁻¹ i a * h y a b * christoffel g b j k y := by
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, c = fun l =>
      pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y := ⟨_, rfl⟩
  have hL : dChristoffel0 g h i j k y =
      -((1 / 2) * ∑ l, ∑ b, ∑ a, (g y)⁻¹ i a * h y a b * (g y)⁻¹ b l * c l) := by
    unfold dChristoffel0
    rw [hc, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  have hR : ∑ a, ∑ b, (g y)⁻¹ i a * h y a b * christoffel g b j k y =
      (1 / 2) * ∑ a, ∑ b, ∑ l, (g y)⁻¹ i a * h y a b * (g y)⁻¹ b l * c l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold christoffel
    rw [hc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hL, hR]
  congr 2
  calc ∑ l, ∑ b, ∑ a, (g y)⁻¹ i a * h y a b * (g y)⁻¹ b l * c l
      = ∑ b, ∑ l, ∑ a, (g y)⁻¹ i a * h y a b * (g y)⁻¹ b l * c l := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ l, (g y)⁻¹ i a * h y a b * (g y)⁻¹ b l * c l :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ l, (g y)⁻¹ i a * h y a b * (g y)⁻¹ b l * c l := Finset.sum_comm

/-- The partial derivative of a finite sum of differentiable functions. -/
lemma pd_sum_of_differentiableAt {ι : Type*} (t : Finset ι) (F : ι → (Fin n → ℝ) → ℝ)
    {x : Fin n → ℝ} (hF : ∀ i ∈ t, DifferentiableAt ℝ (F i) x) (μ : Fin n) :
    pd μ (fun y => ∑ i ∈ t, F i y) x = ∑ i ∈ t, pd μ (F i) x := by
  unfold pd
  have h := (HasFDerivAt.fun_sum fun i hi => (hF i hi).hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.sum_apply]

/-- The partial derivative of a difference of differentiable functions. -/
lemma pd_sub_of_differentiableAt {u v : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (μ : Fin n) :
    pd μ (fun y => u y - v y) x = pd μ u x - pd μ v x := by
  unfold pd
  have h := (hu.hasFDerivAt.fun_sub hv.hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.sub_apply]

/-- **The derivative of the coefficient `c^{μαβ}`**, by the product rule. -/
theorem pd_hessCoeff (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hdet : ∀ x, (g x).det ≠ 0)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (μ' μ α β : Fin n) (x : Fin n → ℝ) :
    pd μ' (hessCoeff g φ μ α β) x =
      pd μ' (fun y => √|(g y).det|) x *
          ∑ ρ, ((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x +
        √|(g x).det| * ∑ ρ,
          ((pd μ' (fun y => (g y)⁻¹ ρ α) x * (g x)⁻¹ μ β + (g x)⁻¹ ρ α * pd μ' (fun y => (g y)⁻¹ μ β) x -
              (pd μ' (fun y => (g y)⁻¹ ρ μ) x * (g x)⁻¹ α β +
                (g x)⁻¹ ρ μ * pd μ' (fun y => (g y)⁻¹ α β) x)) * pd ρ φ x +
            ((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) *
              pd μ' (fun y => pd ρ φ y) x) := by
  have hinv : ∀ a b, DifferentiableAt ℝ (fun y => (g y)⁻¹ a b) x := fun a b =>
    ((contDiff_inv_entry g hg hdet a b).differentiable (by simp)).differentiableAt
  have hsq : DifferentiableAt ℝ (fun y => √|(g y).det|) x :=
    ((contDiffAt_sqrt_abs ((contDiff_det_of (f := g) (m := ⊤) hg).contDiffAt) (hdet x)).differentiableAt
      (by simp))
  have hpφ : ∀ ρ, DifferentiableAt ℝ (fun y => pd ρ φ y) x := fun ρ =>
    ((contDiff_pd_one hφ ρ).differentiable (by simp)).differentiableAt
  have hB : ∀ ρ, DifferentiableAt ℝ
      (fun y => (g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) x := fun ρ =>
    ((hinv ρ α).mul (hinv μ β)).sub ((hinv ρ μ).mul (hinv α β))
  have hterm : ∀ ρ, DifferentiableAt ℝ
      (fun y => ((g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) * pd ρ φ y) x := fun ρ =>
    (hB ρ).mul (hpφ ρ)
  have hsum : DifferentiableAt ℝ (fun y => ∑ ρ,
      ((g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) * pd ρ φ y) x :=
    DifferentiableAt.fun_sum fun ρ _ => hterm ρ
  have hBpd : ∀ ρ, pd μ' (fun y => (g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) x =
      pd μ' (fun y => (g y)⁻¹ ρ α) x * (g x)⁻¹ μ β + (g x)⁻¹ ρ α * pd μ' (fun y => (g y)⁻¹ μ β) x -
        (pd μ' (fun y => (g y)⁻¹ ρ μ) x * (g x)⁻¹ α β +
          (g x)⁻¹ ρ μ * pd μ' (fun y => (g y)⁻¹ α β) x) := by
    intro ρ
    have e1 := pd_mul_of_differentiableAt (u := fun y => (g y)⁻¹ ρ α) (F := fun y => (g y)⁻¹ μ β)
      (hinv ρ α) (hinv μ β) μ'
    have e2 := pd_mul_of_differentiableAt (u := fun y => (g y)⁻¹ ρ μ) (F := fun y => (g y)⁻¹ α β)
      (hinv ρ μ) (hinv α β) μ'
    have e3 := pd_sub_of_differentiableAt (u := fun y => (g y)⁻¹ ρ α * (g y)⁻¹ μ β)
      (v := fun y => (g y)⁻¹ ρ μ * (g y)⁻¹ α β) ((hinv ρ α).mul (hinv μ β))
      ((hinv ρ μ).mul (hinv α β)) μ'
    rw [e3, e1, e2]
  have m1 := pd_mul_of_differentiableAt (u := fun y => √|(g y).det|)
    (F := fun y => ∑ ρ, ((g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) * pd ρ φ y) hsq hsum μ'
  have m2 := pd_sum_of_differentiableAt Finset.univ
    (fun ρ y => ((g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) * pd ρ φ y)
    (fun ρ _ => hterm ρ) μ'
  have m3 : ∀ ρ, pd μ' (fun y => ((g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) *
        pd ρ φ y) x =
      (pd μ' (fun y => (g y)⁻¹ ρ α) x * (g x)⁻¹ μ β + (g x)⁻¹ ρ α * pd μ' (fun y => (g y)⁻¹ μ β) x -
          (pd μ' (fun y => (g y)⁻¹ ρ μ) x * (g x)⁻¹ α β +
            (g x)⁻¹ ρ μ * pd μ' (fun y => (g y)⁻¹ α β) x)) * pd ρ φ x +
        ((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd μ' (fun y => pd ρ φ y) x := by
    intro ρ
    have e4 := pd_mul_of_differentiableAt
      (u := fun y => (g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β)
      (F := fun y => pd ρ φ y) (hB ρ) (hpφ ρ) μ'
    rw [e4, hBpd ρ]
  show pd μ' (fun y => √|(g y).det| * ∑ ρ,
    ((g y)⁻¹ ρ α * (g y)⁻¹ μ β - (g y)⁻¹ ρ μ * (g y)⁻¹ α β) * pd ρ φ y) x = _
  rw [m1, m2, Finset.sum_congr rfl fun ρ _ => m3 ρ]

end Lightlike

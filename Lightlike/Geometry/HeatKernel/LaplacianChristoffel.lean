import Mathlib
import Lightlike.Geometry.HeatKernel.CoordDensityDeriv
import Lightlike.Geometry.HeatKernel.JetInvariants

/-!
# The coordinate Laplacian in Christoffel form

`Δf = -g^{ij} (∂ᵢ∂ⱼf - Γ^k_{ij} ∂ₖf)` at every point of `U` for a coordinate metric of any signature
(`IsCoordMetric.coordLaplacian_eq_christoffel`): the non-divergence form `coordLaplacian_eq_sum` with Jacobi's formula
`∂ᵢρ/ρ = ½ tr(g⁻¹∂ᵢg)` and the contraction `Σᵢ (½ tr(g⁻¹∂ᵢg) g^{ij} + ∂ᵢg^{ij}) = -g^{kl} Γ^j_{kl}`.
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- A three-fold nested sum as one sum over `Fin 3 → Fin n`. -/
lemma sum_nest3 (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ x : Fin 3 → Fin n, F (x 0) (x 1) (x 2) := by
  simp only [sum_fin_succ_pi, Fin.cons_zero]
  simp
  rfl

/-- **The contracted Christoffel symbols**: `Σᵢ (½ tr(g⁻¹ ∂ᵢg) g^{ij} + ∂ᵢ g^{ij}) = -Σ_{kl} g^{kl} Γ^j_{kl}` on `U`. -/
lemma IsCoordMetric.sum_lam_add_pd_inv (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U) (j : Fin n) :
    ∑ i, ((1 / 2) * ((g y)⁻¹ * Matrix.of fun k l => pd i (fun z => g z k l) y).trace * (g y)⁻¹ i j +
        pd i (fun z => (g z)⁻¹ i j) y) =
      -∑ k, ∑ l, (g y)⁻¹ k l * christoffel g j k l y := by
  have hL : ∑ i, ((1 / 2) * ((g y)⁻¹ * Matrix.of fun k l => pd i (fun z => g z k l) y).trace * (g y)⁻¹ i j +
        pd i (fun z => (g z)⁻¹ i j) y) =
      ∑ i, ∑ a, ∑ b, (1 / 2 * ((g y)⁻¹ a b * pd i (fun z => g z b a) y * (g y)⁻¹ i j) -
        (g y)⁻¹ i a * pd i (fun z => g z a b) y * (g y)⁻¹ b j) := by
    simp only [Regge.Conv3.pd_inv hg hy, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply,
      Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, sub_eq_add_neg]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hR : -∑ k, ∑ l, (g y)⁻¹ k l * christoffel g j k l y =
      ∑ k, ∑ l, ∑ m, (-(1 / 2) * ((g y)⁻¹ k l * (g y)⁻¹ j m * pd k (fun z => g z m l) y) -
        1 / 2 * ((g y)⁻¹ k l * (g y)⁻¹ j m * pd l (fun z => g z m k) y) +
        1 / 2 * ((g y)⁻¹ k l * (g y)⁻¹ j m * pd m (fun z => g z k l) y)) := by
    simp only [christoffel, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hL, hR, sum_nest3 (fun i a b => 1 / 2 * ((g y)⁻¹ a b * pd i (fun z => g z b a) y * (g y)⁻¹ i j) -
        (g y)⁻¹ i a * pd i (fun z => g z a b) y * (g y)⁻¹ b j),
    sum_nest3 (fun k l m => -(1 / 2) * ((g y)⁻¹ k l * (g y)⁻¹ j m * pd k (fun z => g z m l) y) -
        1 / 2 * ((g y)⁻¹ k l * (g y)⁻¹ j m * pd l (fun z => g z m k) y) +
        1 / 2 * ((g y)⁻¹ k l * (g y)⁻¹ j m * pd m (fun z => g z k l) y))]
  set H : Fin n → Fin n → ℝ := fun a b => (g y)⁻¹ a b with hHdef
  set D : Fin n → Fin n → Fin n → ℝ := fun i a b => pd i (fun z => g z a b) y with hDdef
  have hH : ∀ a b, H a b = H b a := fun a b => by
    have hs : ((g y)⁻¹).transpose = (g y)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm y hy]
    have := congrFun (congrFun hs b) a
    rwa [Matrix.transpose_apply] at this
  have hD : ∀ i a b, D i a b = D i b a := fun i a b =>
    pd_congr_on hg.isOpen hy (fun z hz => by
      have := congrFun (congrFun (hg.symm z hz) b) a
      rwa [Matrix.transpose_apply] at this) i
  change ∑ x : Fin 3 → Fin n, (1 / 2 * (H (x 1) (x 2) * D (x 0) (x 2) (x 1) * H (x 0) j) -
      H (x 0) (x 1) * D (x 0) (x 1) (x 2) * H (x 2) j) =
    ∑ x : Fin 3 → Fin n, (-(1 / 2) * (H (x 0) (x 1) * H j (x 2) * D (x 0) (x 2) (x 1)) -
      1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 1) (x 2) (x 0)) +
      1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 2) (x 0) (x 1)))
  have p1 : ∑ x : Fin 3 → Fin n, 1 / 2 * (H (x 1) (x 2) * D (x 0) (x 2) (x 1) * H (x 0) j) =
      ∑ x : Fin 3 → Fin n, 1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 2) (x 0) (x 1)) :=
    sum_reindex _ _ ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ fun x => by
      simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.isValue]
      rw [hD (x 2) (x 1) (x 0), hH (x 2) j]
      ring
  have p2 : ∑ x : Fin 3 → Fin n, 1 / 2 * (H (x 0) (x 1) * D (x 0) (x 1) (x 2) * H (x 2) j) =
      ∑ x : Fin 3 → Fin n, 1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 0) (x 2) (x 1)) :=
    Finset.sum_congr rfl fun x _ => by rw [hD (x 0) (x 2) (x 1), hH j (x 2)]; ring
  have p3 : ∑ x : Fin 3 → Fin n, 1 / 2 * (H (x 0) (x 1) * D (x 0) (x 1) (x 2) * H (x 2) j) =
      ∑ x : Fin 3 → Fin n, 1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 1) (x 2) (x 0)) :=
    sum_reindex _ _ ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩ fun x => by
      simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.isValue]
      rw [hD (x 1) (x 2) (x 0), hH (x 1) (x 0), hH j (x 2)]
      ring
  have sL : ∀ x : Fin 3 → Fin n, (1 / 2 * (H (x 1) (x 2) * D (x 0) (x 2) (x 1) * H (x 0) j) -
      H (x 0) (x 1) * D (x 0) (x 1) (x 2) * H (x 2) j) =
      1 / 2 * (H (x 1) (x 2) * D (x 0) (x 2) (x 1) * H (x 0) j) -
      1 / 2 * (H (x 0) (x 1) * D (x 0) (x 1) (x 2) * H (x 2) j) -
      1 / 2 * (H (x 0) (x 1) * D (x 0) (x 1) (x 2) * H (x 2) j) := fun x => by ring
  have sR : ∀ x : Fin 3 → Fin n, (-(1 / 2) * (H (x 0) (x 1) * H j (x 2) * D (x 0) (x 2) (x 1)) -
      1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 1) (x 2) (x 0)) +
      1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 2) (x 0) (x 1))) =
      1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 2) (x 0) (x 1)) -
      1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 0) (x 2) (x 1)) -
      1 / 2 * (H (x 0) (x 1) * H j (x 2) * D (x 1) (x 2) (x 0)) := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => sL x, Finset.sum_congr rfl fun x _ => sR x, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith

/-- **The coordinate Laplacian in Christoffel form**: `Δf = -Σ_{ij} g^{ij} (∂ᵢ∂ⱼf - Σₖ Γ^k_{ij} ∂ₖf)` on `U`. -/
theorem IsCoordMetric.coordLaplacian_eq_christoffel (hg : IsCoordMetric g U) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordLaplacian g f y = -∑ i, ∑ j, (g y)⁻¹ i j * (pd i (pd j f) y - ∑ k, christoffel g k i j y * pd k f y) := by
  rw [hg.coordLaplacian_eq_sum hf hy]
  have hρ0 : coordDensity g y ≠ 0 := (hg.coordDensity_pos hy).ne'
  have hlam : ∀ i, pd i (coordDensity g) y / coordDensity g y =
      (1 / 2) * ((g y)⁻¹ * Matrix.of fun k l => pd i (fun z => g z k l) y).trace := fun i => by
    rw [hg.pd_coordDensity hy i]; field_simp
  simp only [hlam]
  congr 1
  set lam : Fin n → ℝ := fun i => (1 / 2) * ((g y)⁻¹ * Matrix.of fun k l => pd i (fun z => g z k l) y).trace
    with hlamdef
  have hL : ∑ i, (lam i * ∑ j, (g y)⁻¹ i j * pd j f y +
      ∑ j, (pd i (fun z => (g z)⁻¹ i j) y * pd j f y + (g y)⁻¹ i j * pd i (pd j f) y)) =
      ∑ j, (∑ i, (lam i * (g y)⁻¹ i j + pd i (fun z => (g z)⁻¹ i j) y)) * pd j f y +
        ∑ i, ∑ j, (g y)⁻¹ i j * pd i (pd j f) y := by
    have h1 : ∑ i, (lam i * ∑ j, (g y)⁻¹ i j * pd j f y +
        ∑ j, (pd i (fun z => (g z)⁻¹ i j) y * pd j f y + (g y)⁻¹ i j * pd i (pd j f) y)) =
        ∑ i, ∑ j, (lam i * (g y)⁻¹ i j + pd i (fun z => (g z)⁻¹ i j) y) * pd j f y +
          ∑ i, ∑ j, (g y)⁻¹ i j * pd i (pd j f) y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, Finset.sum_comm (f := fun i j => (lam i * (g y)⁻¹ i j + pd i (fun z => (g z)⁻¹ i j) y) * pd j f y)]
    simp only [Finset.sum_mul]
  have hkey : ∀ j, ∑ i, (lam i * (g y)⁻¹ i j + pd i (fun z => (g z)⁻¹ i j) y) =
      -∑ k, ∑ l, (g y)⁻¹ k l * christoffel g j k l y := fun j => hg.sum_lam_add_pd_inv hy j
  rw [hL, Finset.sum_congr rfl fun j _ => by rw [hkey j]]
  have hR : ∑ i, ∑ j, (g y)⁻¹ i j * (pd i (pd j f) y - ∑ k, christoffel g k i j y * pd k f y) =
      ∑ i, ∑ j, (g y)⁻¹ i j * pd i (pd j f) y - ∑ i, ∑ j, ∑ k, (g y)⁻¹ i j * christoffel g k i j y * pd k f y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hR]
  have hperm : ∑ j, (-∑ k, ∑ l, (g y)⁻¹ k l * christoffel g j k l y) * pd j f y =
      -∑ i, ∑ j, ∑ k, (g y)⁻¹ i j * christoffel g k i j y * pd k f y := by
    have : ∑ j, (-∑ k, ∑ l, (g y)⁻¹ k l * christoffel g j k l y) * pd j f y =
        -∑ j, ∑ k, ∑ l, (g y)⁻¹ k l * christoffel g j k l y * pd j f y := by
      simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    rw [this, sum_nest3 (fun j k l => (g y)⁻¹ k l * christoffel g j k l y * pd j f y),
      sum_nest3 (fun i j k => (g y)⁻¹ i j * christoffel g k i j y * pd k f y)]
    congr 1
    exact sum_reindex _ _ ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ fun x => by
      simp only [Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.isValue]
  rw [hperm]
  ring

end Lightlike

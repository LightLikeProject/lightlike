import Lightlike.Regge.CMS4.JetCore4

/-!
# The first derivative of the metric is a gauge in dimension 4

The first-order coefficient `edgeC g m s Δ = ∂_s g_m(Δ, Δ)` of the squared length of an edge with
midpoint offset `s` and edge vector `Δ` is `2 G(Δ, B(Δ, s))`, where `B(Δ, s) = G⁻¹ Γ₁(Δ, s)` and
`Γ₁` is the Christoffel symbol of the first kind. Equivalently, moving each vertex `x` to
`x + (t/2) B(x, x)` changes the squared length of each edge by `t · edgeC` to first order, with the
exact second-order remainder `t² |B(Δ, s)|²_G`. A first-order metric perturbation is thus a
diffeomorphism of the star (normal coordinates at the base point).

## Main results

* `chr1`: the Christoffel contraction of the first kind built from `pd`.
* `edgeC_eq_chr1`: `edgeC g m s Δ = 2 Δ · Γ₁(Δ, s)`.
* `chr1_symm`: `Γ₁(Δ, s) = Γ₁(s, Δ)` for a symmetric metric.
* `chr1_diff`: `Γ₁(y - x, (x + y)/2) = (Γ₁(y, y) - Γ₁(x, x))/2`.
* `sq_Phi`: the squared length of the moved edge is `edgeQ + t edgeC + t² R`.
-/

open Lightlike Real
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The partial derivative `∂_j g_{ik}` at `m`. -/
noncomputable def gD (m : Fin 4 → ℝ) (j i k : Fin 4) : ℝ := Lightlike.pd j (fun y => g y i k) m

/-- The Christoffel contraction of the first kind: `Γ₁(Δ, s)_i = ½ ∑ (∂_j g_ik + ∂_k g_ij - ∂_i g_jk) Δ_j s_k`. -/
noncomputable def chr1 (m : Fin 4 → ℝ) (Δ s : Fin 4 → ℝ) : Fin 4 → ℝ := fun i =>
  (1 / 2) * ∑ j, ∑ k, (gD g m j i k + gD g m k i j - gD g m i j k) * Δ j * s k

/-- The first-order edge coefficient is twice the Christoffel contraction paired with `Δ`. -/
theorem edgeC_eq_chr1 (m s Δ : Fin 4 → ℝ) : edgeC g m s Δ = 2 * (Δ ⬝ᵥ chr1 g m Δ s) := by
  have e1 : edgeC g m s Δ = ∑ i, ∑ j, ∑ k, Δ i * Δ j * s k * gD g m k i j := by
    simp only [edgeC, dmat, gD, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have e2 : 2 * (Δ ⬝ᵥ chr1 g m Δ s) =
      ∑ i, ∑ j, ∑ k, Δ i * Δ j * s k * (gD g m j i k + gD g m k i j - gD g m i j k) := by
    simp only [chr1, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2]
  have key : ∑ i, ∑ j, ∑ k, Δ i * Δ j * s k * gD g m j i k
      = ∑ i, ∑ j, ∑ k, Δ i * Δ j * s k * gD g m i j k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have h3 : ∀ i j k, Δ i * Δ j * s k * (gD g m j i k + gD g m k i j - gD g m i j k)
      = Δ i * Δ j * s k * gD g m j i k + Δ i * Δ j * s k * gD g m k i j
        - Δ i * Δ j * s k * gD g m i j k := fun i j k => by ring
  simp only [h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, key]
  ring

/-- For a symmetric metric, `∂_i g_{jk} = ∂_i g_{kj}`. -/
theorem gD_symm (hs : ∀ y, (g y)ᵀ = g y) (m : Fin 4 → ℝ) (i j k : Fin 4) :
    gD g m i j k = gD g m i k j := by
  unfold gD
  congr 1
  funext y
  have := congrFun (congrFun (hs y) j) k
  simpa [Matrix.transpose_apply] using this.symm

/-- A symmetric double sum identity: the cross terms of `(y - x)(x + y)/2` cancel. -/
theorem bil_diff (c : Fin 4 → Fin 4 → ℝ) (hc : ∀ j k, c j k = c k j) (x y : Fin 4 → ℝ) :
    ∑ j, ∑ k, c j k * (y j - x j) * ((x k + y k) / 2)
      = ((∑ j, ∑ k, c j k * (y j * y k)) - ∑ j, ∑ k, c j k * (x j * x k)) / 2 := by
  have cross : ∑ j, ∑ k, c j k * (y j * x k) = ∑ j, ∑ k, c j k * (x j * y k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hc j k]; ring
  have h : ∀ j k, c j k * (y j - x j) * ((x k + y k) / 2)
      = (c j k * (y j * y k) - c j k * (x j * x k)) / 2
        + (c j k * (y j * x k) - c j k * (x j * y k)) / 2 := fun j k => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, cross]
  ring

/-- The Christoffel contraction is symmetric. -/
theorem chr1_symm (hs : ∀ y, (g y)ᵀ = g y) (m Δ s : Fin 4 → ℝ) : chr1 g m Δ s = chr1 g m s Δ := by
  funext i
  simp only [chr1]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [gD_symm g hs m i j k]
  ring

/-- The Christoffel contraction of an edge with its midpoint offset is half the difference of the
quadratic values at its end points. -/
theorem chr1_diff (hs : ∀ y, (g y)ᵀ = g y) (m x y : Fin 4 → ℝ) :
    chr1 g m (fun i => y i - x i) (fun i => (x i + y i) / 2)
      = fun i => (chr1 g m y y i - chr1 g m x x i) / 2 := by
  funext i
  have hc : ∀ j k, (gD g m j i k + gD g m k i j - gD g m i j k)
      = (gD g m k i j + gD g m j i k - gD g m i k j) := fun j k => by
    rw [gD_symm g hs m i j k]; ring
  have := bil_diff (fun j k => gD g m j i k + gD g m k i j - gD g m i j k) hc x y
  simp only [chr1]
  simp only [mul_assoc] at this ⊢
  rw [this]
  ring

/-- Expanding the quadratic form on a shifted vector. -/
theorem quad_shift {G : Matrix (Fin 4) (Fin 4) ℝ} (hs : Gᵀ = G) (hdet : IsUnit G.det)
    (Δ Γ : Fin 4 → ℝ) (t : ℝ) :
    (Δ + t • (G⁻¹ *ᵥ Γ)) ⬝ᵥ (G *ᵥ (Δ + t • (G⁻¹ *ᵥ Γ)))
      = Δ ⬝ᵥ (G *ᵥ Δ) + 2 * t * (Δ ⬝ᵥ Γ) + t ^ 2 * (Γ ⬝ᵥ (G⁻¹ *ᵥ Γ)) := by
  have hGu : G *ᵥ (G⁻¹ *ᵥ Γ) = Γ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h1 : (G⁻¹ *ᵥ Γ) ⬝ᵥ (G *ᵥ Δ) = Δ ⬝ᵥ Γ := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, hGu, dotProduct_comm]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hGu, add_dotProduct, dotProduct_add, dotProduct_add,
    smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, h1, dotProduct_comm Γ,
    dotProduct_comm (G⁻¹ *ᵥ Γ) Γ]
  simp only [smul_eq_mul]
  ring

/-- The vertex move `x ↦ x + (t/2) G⁻¹ Γ₁(x, x)`, a normal-coordinate change at `m`. -/
noncomputable def Phi (m : Fin 4 → ℝ) (t : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  x + t • ((1 / 2 : ℝ) • ((g m)⁻¹ *ᵥ chr1 g m x x))

/-- The edge vector after the vertex move is the old edge vector plus `t G⁻¹ Γ₁(Δ, s)`. -/
theorem Phi_sub (hs : ∀ y, (g y)ᵀ = g y) (m : Fin 4 → ℝ) (t : ℝ) (x y : Fin 4 → ℝ) :
    Phi g m t y - Phi g m t x = (fun i => y i - x i) +
      t • ((g m)⁻¹ *ᵥ chr1 g m (fun i => y i - x i) (fun i => (x i + y i) / 2)) := by
  rw [chr1_diff g hs m x y]
  have h : (fun i => (chr1 g m y y i - chr1 g m x x i) / 2)
      = (1 / 2 : ℝ) • (chr1 g m y y - chr1 g m x x) := by
    funext i; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [h, Matrix.mulVec_smul, Matrix.mulVec_sub]
  funext i
  simp only [Phi, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Squared length of a moved edge.** After the vertex move `Phi`, the squared `g m`-length of the
edge `x → y` is `edgeQ + t edgeC + t² R` with `R = |Γ₁(Δ, s)|²_{G⁻¹}`. -/
theorem sq_Phi (hs : ∀ y, (g y)ᵀ = g y) (m : Fin 4 → ℝ) (hdet : IsUnit (g m).det) (t : ℝ)
    (x y : Fin 4 → ℝ) :
    (Phi g m t y - Phi g m t x) ⬝ᵥ ((g m) *ᵥ (Phi g m t y - Phi g m t x))
      = edgeQ g m (fun i => y i - x i) + t * edgeC g m (fun i => (x i + y i) / 2) (fun i => y i - x i)
        + t ^ 2 * (chr1 g m (fun i => y i - x i) (fun i => (x i + y i) / 2) ⬝ᵥ
          ((g m)⁻¹ *ᵥ chr1 g m (fun i => y i - x i) (fun i => (x i + y i) / 2))) := by
  rw [Phi_sub g hs m t x y, quad_shift (by simpa using hs m) hdet, edgeC_eq_chr1]
  simp only [edgeQ]
  ring

end Lightlike.Regge4

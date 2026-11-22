import Lightlike.Spacetime.GE3Row.Jacobi
import Lightlike.Spacetime.RicciContinuous

/-!
# Jacobi fields from variations through geodesics (row G1-006, GE3)

Algebra of the connection terms: the expansion of `R(J, w) w` in terms of `Γ` and `∂Γ`.
-/

open Set Filter Topology Matrix
open scoped ContDiff

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The directional derivative of the connection term: `(∂_y Γ)(x)(v, u)^i = Σ ∂_y Γ^i_{jk} v^j u^k`. -/
noncomputable def gammaDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x y v u : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, ∑ k, fderiv ℝ (Lightlike.christoffel g i j k) x y * v j * u k

/-- A directional derivative is the sum of the coordinate partial derivatives. -/
theorem fderiv_eq_sum_pd (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ m, v m * Lightlike.pd m f x := by
  have hv : v = ∑ m, v m • (Pi.single m (1 : ℝ) : Fin n → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, Lightlike.pd]

section sums

variable {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℝ)

theorem sum3_cyc : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum3_rev : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_comm

variable (h : ι → ι → ι → ι → ℝ)

theorem sum4_bdca : ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ b, ∑ d, ∑ c, ∑ a, h a b c d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => sum3_rev (fun a c d => h a b c d)

theorem sum4_cdba : ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ c, ∑ d, ∑ b, ∑ a, h a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ a, ∑ c, ∑ b, ∑ d, h a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, h a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, h a b c d :=
        Finset.sum_congr rfl fun c _ => sum3_rev (fun a b d => h a b c d)

end sums

/-- `R(J, w) w = (∂_J Γ)(w, w) - (∂_w Γ)(J, w) + Γ(J, Γ(w, w)) - Γ(w, Γ(J, w))`. -/
theorem riemannApply_eq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w J : Fin n → ℝ) :
    riemannApply g x w J = gammaDeriv g x J w w - gammaDeriv g x w J w
      + gammaApply g x J (gammaApply g x w w) - gammaApply g x w (gammaApply g x J w) := by
  funext i
  simp only [riemannApply, gammaDeriv, gammaApply, Lightlike.riemann, Pi.add_apply, Pi.sub_apply,
    fderiv_eq_sum_pd, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  have e1 : ∑ s, ∑ m, ∑ v, Lightlike.pd m (Lightlike.christoffel g i v s) x * w s * J m * w v =
      ∑ j, ∑ k, ∑ m, J m * Lightlike.pd m (Lightlike.christoffel g i j k) x * w j * w k := by
    rw [sum3_cyc (fun j k m => J m * Lightlike.pd m (Lightlike.christoffel g i j k) x * w j * w k)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ s, ∑ m, ∑ v, Lightlike.pd v (Lightlike.christoffel g i m s) x * w s * J m * w v =
      ∑ j, ∑ k, ∑ m, w m * Lightlike.pd m (Lightlike.christoffel g i j k) x * J j * w k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ s, ∑ m, ∑ v, ∑ l, Lightlike.christoffel g i m l x * Lightlike.christoffel g l v s x *
        w s * J m * w v =
      ∑ x_1, ∑ k, ∑ x_2, ∑ i_1, Lightlike.christoffel g i x_1 k x * J x_1 *
        (Lightlike.christoffel g k x_2 i_1 x * w x_2 * w i_1) := by
    rw [sum4_bdca (fun s m v l => Lightlike.christoffel g i m l x *
      Lightlike.christoffel g l v s x * w s * J m * w v)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e4 : ∑ s, ∑ m, ∑ v, ∑ l, Lightlike.christoffel g i v l x * Lightlike.christoffel g l m s x *
        w s * J m * w v =
      ∑ x_1, ∑ k, ∑ x_2, ∑ i_1, Lightlike.christoffel g i x_1 k x * w x_1 *
        (Lightlike.christoffel g k x_2 i_1 x * J x_2 * w i_1) := by
    rw [sum4_cdba (fun s m v l => Lightlike.christoffel g i v l x *
      Lightlike.christoffel g l m s x * w s * J m * w v)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3, e4]
  ring

end Lightlike.Geodesic

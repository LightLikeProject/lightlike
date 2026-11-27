import Lightlike.SpinFoam.EPRLStateSum.SimplexAmpP
import Lightlike.Recoupling.Span

/-!
# The 15j symbol as a contraction of five intertwiners on `K₅`

`contract5 j T` is the contraction of five node tensors `T a` along the ten edges of `K₅`: the sum over the projections `m_e` of the
edges, with the edge sign `edgeSign (j_e) (m_e)` and the node `a` reading the projection `m_{ab}` on its leg `b` for `a < b`,
`-m_{ba}` for `b < a`. `fifteenJSimplex` is `contract5` of the intertwiners in the cyclic leg order (`fifteenJSimplex_eq_contract5`).
-/

open Finset Lightlike.Recoupling Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

/-- The index in `Fin 10` of the edge `p < q` of `K₅`, in the order `01, 02, 03, 04, 12, 13, 14, 23, 24, 34`. -/
def eidx (p q : Fin 5) : Fin 10 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 4, 5, 6], ![0, 0, 0, 7, 8], ![0, 0, 0, 0, 9], ![0, 0, 0, 0, 0]] p q

/-- The projection read by the node `a` on its leg `b`, from the edge projections `m`: `m_{ab}` for `a < b`, `-m_{ba}` for `b < a`. -/
def legProj (m : Fin 10 → ℤ) (a b : Fin 5) : ℤ :=
  if a < b then m (eidx a b) else if b < a then - m (eidx b a) else 0

/-- The pair `p < q` of the edge `e : Fin 10`, in the order `01, 02, 03, 04, 12, 13, 14, 23, 24, 34`. -/
def epr : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The spin of the edge `e : Fin 10`. -/
def jE (j : Fin 5 → Fin 5 → ℕ) (e : Fin 10) : ℕ := j (epr e).1 (epr e).2

/-- **The contraction of five node tensors on `K₅`.** -/
noncomputable def contract5 (j : Fin 5 → Fin 5 → ℕ) (T : Fin 5 → (Fin 5 → ℤ) → ℝ) : ℝ :=
  ∑ m ∈ Fintype.piFinset (fun e : Fin 10 => Icc (-(jE j e : ℤ)) (jE j e)),
    (∏ e : Fin 10, edgeSign (jE j e) (m e)) * ∏ a : Fin 5, T a (legProj m a)

/-- The node tensors of `fifteenJSimplex`: the intertwiner of node `a` in the cyclic leg order `a+1, a+2, a+3, a+4`. -/
noncomputable def cycT (j : Fin 5 → Fin 5 → ℕ) (i : Fin 5 → ℕ) : Fin 5 → (Fin 5 → ℤ) → ℝ :=
  fun a μ => fourJ (j a (a + 1)) (j a (a + 2)) (j a (a + 3)) (j a (a + 4)) (i a) (μ (a + 1)) (μ (a + 2)) (μ (a + 3)) (μ (a + 4))

/-- A sum over a box of projections on `Fin (n + 1)`, peeled at the first coordinate, with `Matrix.vecCons`. -/
lemma sum_piFinset_vecCons' {n : ℕ} (B : Fin (n + 1) → Finset ℤ) (G : (Fin (n + 1) → ℤ) → ℝ) :
    ∑ x ∈ Fintype.piFinset B, G x =
      ∑ a ∈ B 0, ∑ y ∈ Fintype.piFinset (fun i => B i.succ), G (Matrix.vecCons a y) :=
  sum_piFinset_fin_succ B G

/-- **`fifteenJSimplex` is the contraction of the cyclic-order intertwiners.** -/
theorem fifteenJSimplex_eq_contract5 (j : Fin 5 → Fin 5 → ℕ) (hj : ∀ p q, j p q = j q p) (i : Fin 5 → ℕ) :
    fifteenJSimplex (j 0 1) (j 0 2) (j 0 3) (j 0 4) (j 1 2) (j 1 3) (j 1 4) (j 2 3) (j 2 4) (j 3 4)
      (i 0) (i 1) (i 2) (i 3) (i 4) = contract5 j (cycT j i) := by
  unfold fifteenJSimplex contract5
  simp only [sum_piFinset_vecCons', sum_piFinset_fin_zero]
  refine Finset.sum_congr rfl fun a0 _ => Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun a2 _ =>
    Finset.sum_congr rfl fun a3 _ => Finset.sum_congr rfl fun a4 _ => Finset.sum_congr rfl fun a5 _ =>
    Finset.sum_congr rfl fun a6 _ => Finset.sum_congr rfl fun a7 _ => Finset.sum_congr rfl fun a8 _ =>
    Finset.sum_congr rfl fun a9 _ => ?_
  have h10 := hj 1 0
  have h20 := hj 2 0
  have h21 := hj 2 1
  have h30 := hj 3 0
  have h31 := hj 3 1
  have h32 := hj 3 2
  have h40 := hj 4 0
  have h41 := hj 4 1
  have h42 := hj 4 2
  have h43 := hj 4 3
  simp [Fin.prod_univ_succ, legProj, eidx, cycT, jE, epr, mul_assoc, h10, h20, h21, h30, h31, h32, h40, h41, h42, h43]

/-- **The contraction is multilinear in the node tensors**: a sum over `k` in the box of each node of the products of coefficients
and tensors contracts to the sum over the boxes of the products of the coefficients times the contractions. -/
theorem contract5_sum (j : Fin 5 → Fin 5 → ℕ) (B : Fin 5 → Finset ℕ) (c : Fin 5 → ℕ → ℝ)
    (T : Fin 5 → ℕ → (Fin 5 → ℤ) → ℝ) :
    contract5 j (fun a μ => ∑ k ∈ B a, c a k * T a k μ) =
      ∑ i ∈ Fintype.piFinset B, (∏ a, c a (i a)) * contract5 j (fun a μ => T a (i a) μ) := by
  unfold contract5
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.prod_univ_sum (t := B) (f := fun a k => c a k * T a k (legProj m a))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end Lightlike.SpinFoam.EPRLStateSum

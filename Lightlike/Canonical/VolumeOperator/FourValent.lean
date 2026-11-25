import Lightlike.Canonical.VolumeOperator.SpinHalf
import Lightlike.Canonical.VolumeOperator.VolumeOp

/-!
# Four-valent nodes: reduction of `Q` to a single density `q_{012}`

Sixth piece of row G2-014 (milestone CA4). At a four-valent node with the orientation signs
`sgn4` (`+, -, +, -` on the triples `012, 013, 023, 123`), the operator `Q` acts on a gauge-invariant
vector `ψ` as `4 q_{012}`: `Qnode_four_mulVec`. The proof uses only the commutation relations and
`∑_e J_e ψ = 0`.
-/

open Matrix

namespace Lightlike.Rows.G2_014

variable {n : Fin 4 → ℕ}

/-- Orientation signs for the four triples of a four-valent node: `(-1)^(I+J+K+1)`. -/
noncomputable def sgn4 (i j k : Fin 4) : ℝ := (-1) ^ ((i : ℕ) + j + k + 1)

/-- `q_{IJK} ψ = - q_{IJL} ψ` when `J_K ψ = -(J_I + J_J + J_L) ψ` (here `K = 3`). -/
lemma qOp_reduce {ψ : Idx n → ℂ} (i j l : Fin 4) (hij : i ≠ j)
    (hZ : ∀ c, edgeOp n 3 c *ᵥ ψ
      = -(edgeOp n i c *ᵥ ψ) - edgeOp n j c *ᵥ ψ - edgeOp n l c *ᵥ ψ) :
    qOp n i j 3 *ᵥ ψ = -(qOp n i j l *ᵥ ψ) := by
  have key : ∀ a b c, (edgeOp n i a * edgeOp n j b * edgeOp n 3 c) *ᵥ ψ
      = -((edgeOp n i a * edgeOp n j b * edgeOp n i c) *ᵥ ψ)
        - ((edgeOp n i a * edgeOp n j b * edgeOp n j c) *ᵥ ψ)
        - ((edgeOp n i a * edgeOp n j b * edgeOp n l c) *ᵥ ψ) := by
    intro a b c
    rw [← mulVec_mulVec, hZ c, mulVec_sub, mulVec_sub, mulVec_neg, mulVec_mulVec, mulVec_mulVec,
      mulVec_mulVec]
  have hS := Lightlike.Rows.G2_014.six_term_zero (edgeOp n i) (edgeOp n j)
    (fun a b => edgeOp_comm_of_ne hij a b)
    (edgeOp_comm_xy i) (edgeOp_comm_yz i) (edgeOp_comm_zx i)
    (edgeOp_comm_xy j) (edgeOp_comm_yz j) (edgeOp_comm_zx j)
  have hSv := congrArg (fun M => M *ᵥ ψ) hS
  simp only [mul_add, add_mulVec, sub_mulVec, zero_mulVec] at hSv
  simp only [qOp, add_mulVec, sub_mulVec, key]
  rw [← neg_eq_zero] at hSv
  rw [eq_neg_iff_add_eq_zero, ← hSv]
  abel

/-- `q_{IKJ} = - q_{IJK}` for distinct edges. -/
lemma qOp_swap {i j k : Fin 4} (hjk : j ≠ k) : qOp n i k j = -qOp n i j k := by
  have h1 : ∀ a b c, edgeOp n i a * edgeOp n k b * edgeOp n j c
      = edgeOp n i a * edgeOp n j c * edgeOp n k b := by
    intro a b c
    rw [mul_assoc, ← edgeOp_comm_of_ne hjk c b, ← mul_assoc]
  simp only [qOp, h1]
  abel

/-- `q_{JKI} = q_{IJK}` for distinct edges (cyclic invariance). -/
lemma qOp_cyc {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) :
    qOp n j k i = qOp n i j k := by
  have h2 : ∀ a b c, edgeOp n j a * edgeOp n k b * edgeOp n i c
      = edgeOp n i c * edgeOp n j a * edgeOp n k b := by
    intro a b c
    calc edgeOp n j a * edgeOp n k b * edgeOp n i c
        = edgeOp n j a * (edgeOp n k b * edgeOp n i c) := mul_assoc _ _ _
      _ = edgeOp n j a * (edgeOp n i c * edgeOp n k b) := by
        rw [edgeOp_comm_of_ne hik.symm b c]
      _ = (edgeOp n j a * edgeOp n i c) * edgeOp n k b := (mul_assoc _ _ _).symm
      _ = (edgeOp n i c * edgeOp n j a) * edgeOp n k b := by
        rw [edgeOp_comm_of_ne hij.symm a c]
  simp only [qOp, h2]
  abel

/-- The four triples of a four-valent node, with the signs `sgn4`. -/
lemma Qnode_four (n : Fin 4 → ℕ) :
    Qnode n sgn4 = (1 : ℂ) • qOp n 0 1 2 + (-1 : ℂ) • qOp n 0 1 3 + (1 : ℂ) • qOp n 0 2 3
      + (-1 : ℂ) • qOp n 1 2 3 := by
  have hS : Finset.univ.filter
      (fun t : Fin 4 × Fin 4 × Fin 4 => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
      = {((0 : Fin 4), 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)} := by
    decide
  unfold Qnode
  rw [hS, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : sgn4 0 1 2 = 1 := by norm_num [sgn4]
  have e2 : sgn4 0 1 3 = -1 := by norm_num [sgn4]
  have e3 : sgn4 0 2 3 = 1 := by norm_num [sgn4]
  have e4 : sgn4 1 2 3 = -1 := by norm_num [sgn4]
  simp only [e1, e2, e3, e4, Complex.ofReal_one, Complex.ofReal_neg]
  abel

/-- On a gauge-invariant vector, `Q = 4 q_{012}` at a four-valent node. -/
theorem Qnode_four_mulVec {ψ : Idx n → ℂ} (hψ : IsInvariant n ψ) :
    Qnode n sgn4 *ᵥ ψ = (4 : ℂ) • (qOp n 0 1 2 *ᵥ ψ) := by
  have hZ : ∀ c, edgeOp n 3 c *ᵥ ψ
      = -(edgeOp n 0 c *ᵥ ψ) - edgeOp n 1 c *ᵥ ψ - edgeOp n 2 c *ᵥ ψ := by
    intro c
    have h := hψ c
    simp only [totalOp, Fin.sum_univ_four, add_mulVec] at h
    rw [← sub_eq_zero, ← h]
    abel
  have h013 : qOp n 0 1 3 *ᵥ ψ = -(qOp n 0 1 2 *ᵥ ψ) :=
    qOp_reduce 0 1 2 (by decide) hZ
  have h023 : qOp n 0 2 3 *ᵥ ψ = qOp n 0 1 2 *ᵥ ψ := by
    have := qOp_reduce (n := n) (ψ := ψ) 0 2 1 (by decide)
      (fun c => by rw [hZ c]; abel)
    rw [this, qOp_swap (i := 0) (j := 1) (k := 2) (by decide), neg_mulVec, neg_neg]
  have h123 : qOp n 1 2 3 *ᵥ ψ = -(qOp n 0 1 2 *ᵥ ψ) := by
    have := qOp_reduce (n := n) (ψ := ψ) 1 2 0 (by decide)
      (fun c => by rw [hZ c]; abel)
    rw [this, qOp_cyc (by decide) (by decide)]
  rw [Qnode_four, add_mulVec, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec,
    smul_mulVec, h013, h023, h123]
  module

end Lightlike.Rows.G2_014

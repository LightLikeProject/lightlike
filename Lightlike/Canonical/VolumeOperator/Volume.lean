import Lightlike.Canonical.VolumeOperator.NodeOps

/-!
# The volume-operator density `q_{IJK}` at a node, and its vanishing at trivalent nodes

Third piece of row G2-014 (milestone CA4, the volume operator of Ashtekar–Lewandowski).
At a node with edges `e : Fin K`, with edge angular momenta `J_e^a = edgeOp n e a`, the
volume density is the triple product
`q_{IJK} = ε_{abc} J_I^a J_J^b J_K^c`
(`qOp`, written out as its six terms). It is Hermitian when `I, J, K` are distinct, because then
the three factors commute (`qOp_conjTranspose`).

A vector is gauge invariant (`IsInvariant`) when the total angular momentum
`totalOp n a = ∑_e J_e^a` annihilates it. For three edges, `q_{012}` vanishes on invariant
vectors (`qOp_three_mulVec_eq_zero`): this is the algebraic reason why the volume operator is
zero on gauge-invariant trivalent nodes.
-/

open Matrix

namespace Lightlike.Canonical.VolumeOperator

variable {K : ℕ} {n : Fin K → ℕ}

/-- The total angular momentum `∑_e J_e^a` of a node. -/
noncomputable def totalOp (n : Fin K → ℕ) (a : Fin 3) : Matrix (Idx n) (Idx n) ℂ :=
  ∑ e, edgeOp n e a

/-- Gauge invariance at the node: the total angular momentum annihilates the vector. -/
def IsInvariant (n : Fin K → ℕ) (ψ : Idx n → ℂ) : Prop :=
  ∀ a, totalOp n a *ᵥ ψ = 0

/-- The volume density `q_{IJK} = ε_{abc} J_I^a J_J^b J_K^c`, written as its six terms
(three even, three odd permutations of `(x, y, z)`). -/
noncomputable def qOp (n : Fin K → ℕ) (i j k : Fin K) : Matrix (Idx n) (Idx n) ℂ :=
  edgeOp n i 0 * edgeOp n j 1 * edgeOp n k 2 + edgeOp n i 1 * edgeOp n j 2 * edgeOp n k 0
    + edgeOp n i 2 * edgeOp n j 0 * edgeOp n k 1 - edgeOp n i 0 * edgeOp n j 2 * edgeOp n k 1
    - edgeOp n i 2 * edgeOp n j 1 * edgeOp n k 0 - edgeOp n i 1 * edgeOp n j 0 * edgeOp n k 2

/-- A product of three edge operators of distinct edges is Hermitian. -/
lemma triple_conjTranspose {i j k : Fin K} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b c : Fin 3) :
    (edgeOp n i a * edgeOp n j b * edgeOp n k c)ᴴ = edgeOp n i a * edgeOp n j b * edgeOp n k c := by
  rw [conjTranspose_mul, conjTranspose_mul, edgeOp_conjTranspose, edgeOp_conjTranspose,
    edgeOp_conjTranspose]
  calc edgeOp n k c * (edgeOp n j b * edgeOp n i a)
      = edgeOp n k c * (edgeOp n i a * edgeOp n j b) := by
        rw [edgeOp_comm_of_ne hij.symm b a]
    _ = (edgeOp n k c * edgeOp n i a) * edgeOp n j b := (mul_assoc _ _ _).symm
    _ = (edgeOp n i a * edgeOp n k c) * edgeOp n j b := by
        rw [edgeOp_comm_of_ne hik.symm c a]
    _ = edgeOp n i a * (edgeOp n k c * edgeOp n j b) := mul_assoc _ _ _
    _ = edgeOp n i a * (edgeOp n j b * edgeOp n k c) := by
        rw [edgeOp_comm_of_ne hjk.symm c b]
    _ = edgeOp n i a * edgeOp n j b * edgeOp n k c := (mul_assoc _ _ _).symm

/-- `q_{IJK}` is Hermitian for distinct edges. -/
theorem qOp_conjTranspose {i j k : Fin K} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (qOp n i j k)ᴴ = qOp n i j k := by
  simp only [qOp, conjTranspose_add, conjTranspose_sub, triple_conjTranspose hij hik hjk]

section Algebra

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Pure algebra behind the vanishing of the volume at trivalent nodes: if `X`, `Y` are two
commuting `su(2)` representations, the triple product of `X`, `Y`, `X + Y` vanishes. -/
lemma six_term_zero (X Y : Fin 3 → Matrix m m ℂ)
    (hXY : ∀ a b, X a * Y b = Y b * X a)
    (hX01 : X 0 * X 1 - X 1 * X 0 = Complex.I • X 2)
    (hX12 : X 1 * X 2 - X 2 * X 1 = Complex.I • X 0)
    (hX20 : X 2 * X 0 - X 0 * X 2 = Complex.I • X 1)
    (hY01 : Y 0 * Y 1 - Y 1 * Y 0 = Complex.I • Y 2)
    (hY12 : Y 1 * Y 2 - Y 2 * Y 1 = Complex.I • Y 0)
    (hY20 : Y 2 * Y 0 - Y 0 * Y 2 = Complex.I • Y 1) :
    X 0 * Y 1 * (X 2 + Y 2) + X 1 * Y 2 * (X 0 + Y 0) + X 2 * Y 0 * (X 1 + Y 1)
      - X 0 * Y 2 * (X 1 + Y 1) - X 2 * Y 1 * (X 0 + Y 0) - X 1 * Y 0 * (X 2 + Y 2) = 0 := by
  have e : ∀ a b c, X a * Y b * X c = X a * X c * Y b := by
    intro a b c
    rw [mul_assoc, ← hXY c b, ← mul_assoc]
  have hx : X 0 * Y 1 * X 2 + X 1 * Y 2 * X 0 + X 2 * Y 0 * X 1 - X 0 * Y 2 * X 1
      - X 2 * Y 1 * X 0 - X 1 * Y 0 * X 2
      = -(Complex.I • (X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2)) := by
    simp only [e]
    have step : X 0 * X 2 * Y 1 + X 1 * X 0 * Y 2 + X 2 * X 1 * Y 0 - X 0 * X 1 * Y 2
        - X 2 * X 0 * Y 1 - X 1 * X 2 * Y 0
        = (X 0 * X 2 - X 2 * X 0) * Y 1 + (X 1 * X 0 - X 0 * X 1) * Y 2
          + (X 2 * X 1 - X 1 * X 2) * Y 0 := by noncomm_ring
    rw [step]
    have h1 : X 0 * X 2 - X 2 * X 0 = -(Complex.I • X 1) := by rw [← hX20, neg_sub]
    have h2 : X 1 * X 0 - X 0 * X 1 = -(Complex.I • X 2) := by rw [← hX01, neg_sub]
    have h3 : X 2 * X 1 - X 1 * X 2 = -(Complex.I • X 0) := by rw [← hX12, neg_sub]
    rw [h1, h2, h3]
    simp only [neg_mul, smul_mul_assoc, smul_add]
    abel
  have hy : X 0 * Y 1 * Y 2 + X 1 * Y 2 * Y 0 + X 2 * Y 0 * Y 1 - X 0 * Y 2 * Y 1
      - X 2 * Y 1 * Y 0 - X 1 * Y 0 * Y 2
      = Complex.I • (X 0 * Y 0 + X 1 * Y 1 + X 2 * Y 2) := by
    have step : X 0 * Y 1 * Y 2 + X 1 * Y 2 * Y 0 + X 2 * Y 0 * Y 1 - X 0 * Y 2 * Y 1
        - X 2 * Y 1 * Y 0 - X 1 * Y 0 * Y 2
        = X 0 * (Y 1 * Y 2 - Y 2 * Y 1) + X 1 * (Y 2 * Y 0 - Y 0 * Y 2)
          + X 2 * (Y 0 * Y 1 - Y 1 * Y 0) := by noncomm_ring
    rw [step, hY12, hY20, hY01]
    simp only [mul_smul_comm, smul_add]
  have split : X 0 * Y 1 * (X 2 + Y 2) + X 1 * Y 2 * (X 0 + Y 0) + X 2 * Y 0 * (X 1 + Y 1)
      - X 0 * Y 2 * (X 1 + Y 1) - X 2 * Y 1 * (X 0 + Y 0) - X 1 * Y 0 * (X 2 + Y 2)
      = (X 0 * Y 1 * X 2 + X 1 * Y 2 * X 0 + X 2 * Y 0 * X 1 - X 0 * Y 2 * X 1
          - X 2 * Y 1 * X 0 - X 1 * Y 0 * X 2)
        + (X 0 * Y 1 * Y 2 + X 1 * Y 2 * Y 0 + X 2 * Y 0 * Y 1 - X 0 * Y 2 * Y 1
          - X 2 * Y 1 * Y 0 - X 1 * Y 0 * Y 2) := by noncomm_ring
  rw [split, hx, hy, neg_add_cancel]

end Algebra

/-- For three edges, the density `q_{012}` vanishes on gauge-invariant vectors: the volume
operator is zero on gauge-invariant trivalent nodes. -/
theorem qOp_three_mulVec_eq_zero {n : Fin 3 → ℕ} {ψ : Idx n → ℂ} (hψ : IsInvariant n ψ) :
    qOp n 0 1 2 *ᵥ ψ = 0 := by
  have hZ : ∀ c, edgeOp n 2 c *ᵥ ψ = -((edgeOp n 0 c + edgeOp n 1 c) *ᵥ ψ) := by
    intro c
    have h := hψ c
    simp only [totalOp, Fin.sum_univ_three, add_mulVec] at h
    rw [add_mulVec]
    exact eq_neg_of_add_eq_zero_right h
  have key : ∀ a b c, (edgeOp n 0 a * edgeOp n 1 b * edgeOp n 2 c) *ᵥ ψ
      = -((edgeOp n 0 a * edgeOp n 1 b * (edgeOp n 0 c + edgeOp n 1 c)) *ᵥ ψ) := by
    intro a b c
    rw [← mulVec_mulVec, hZ c, mulVec_neg, mulVec_mulVec]
  have hS := six_term_zero (edgeOp n 0) (edgeOp n 1)
    (fun a b => edgeOp_comm_of_ne (by decide) a b)
    (edgeOp_comm_xy 0) (edgeOp_comm_yz 0) (edgeOp_comm_zx 0)
    (edgeOp_comm_xy 1) (edgeOp_comm_yz 1) (edgeOp_comm_zx 1)
  have hSv := congrArg (fun M => M *ᵥ ψ) hS
  simp only [add_mulVec, sub_mulVec, zero_mulVec] at hSv
  simp only [qOp, add_mulVec, sub_mulVec, key]
  rw [← neg_eq_zero] at hSv
  rw [← hSv]
  abel

end Lightlike.Canonical.VolumeOperator

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.IsInvariant := _root_.Lightlike.Canonical.VolumeOperator.IsInvariant
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.qOp := _root_.Lightlike.Canonical.VolumeOperator.qOp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.qOp_conjTranspose := _root_.Lightlike.Canonical.VolumeOperator.qOp_conjTranspose
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.qOp_three_mulVec_eq_zero := _root_.Lightlike.Canonical.VolumeOperator.qOp_three_mulVec_eq_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.six_term_zero := _root_.Lightlike.Canonical.VolumeOperator.six_term_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.totalOp := _root_.Lightlike.Canonical.VolumeOperator.totalOp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.triple_conjTranspose := _root_.Lightlike.Canonical.VolumeOperator.triple_conjTranspose

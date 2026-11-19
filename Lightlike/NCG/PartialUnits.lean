import Lightlike.NCG.MatrixUnits

/-!
# Partial systems of matrix units

A **partial system of matrix units** has the relations of `MatrixUnits` except `∑ₖ ∑ₓ U k x x = 1`. Two partial systems
whose units multiply to `0` across combine into one over the sum of the index types (`PartialUnits.sum`), and a partial
system whose block units add to `1` is a system of matrix units (`PartialUnits.toMatrixUnits`). This assembles the
irreducible representations of the factors of a mixed algebra `⊕ Mₙ(ℝ) × ⊕ Mₙ(ℂ) × ⊕ Mₙ(ℍ)` (T. Krajewski,
arXiv:hep-th/9701081, Section 2, p. 2, and Section 3.1, p. 10).

* `PartialUnits`, `PartialUnits.sum`, `PartialUnits.sum_U_inl`, `PartialUnits.sum_U_inr`, `PartialUnits.toMatrixUnits`.
-/

namespace Lightlike.NCG

noncomputable section

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]

variable (d H) in
/-- **A partial system of matrix units**: the relations of `MatrixUnits` without `∑ₖ ∑ₓ U k x x = 1`. -/
structure PartialUnits where
  /-- The units. -/
  U : ∀ k, Fin (d k) → Fin (d k) → (H →L[ℂ] H)
  /-- `U k x y U k z w = δ_yz U k x w`. -/
  mul_same : ∀ k x y z w, U k x y * U k z w = if y = z then U k x w else 0
  /-- Units of different blocks multiply to `0`. -/
  mul_ne : ∀ k l, k ≠ l → ∀ x y z w, U k x y * U l z w = 0
  /-- `U k x y* = U k y x`. -/
  star_U : ∀ k x y, star (U k x y) = U k y x

end

namespace PartialUnits

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {d : ι → ℕ} {e : κ → ℕ}

/-- **The sum of two partial systems** whose units multiply to `0` across. -/
def sum (M : PartialUnits d H) (N : PartialUnits e H)
    (hMN : ∀ k x y l z w, M.U k x y * N.U l z w = 0) (hNM : ∀ l z w k x y, N.U l z w * M.U k x y = 0) :
    PartialUnits (Sum.elim d e) H where
  U p := match p with
    | .inl k => M.U k
    | .inr l => N.U l
  mul_same p x y z w := by
    cases p with
    | inl k => exact M.mul_same k x y z w
    | inr l => exact N.mul_same l x y z w
  mul_ne p q hpq x y z w := by
    cases p with
    | inl k =>
      cases q with
      | inl k' => exact M.mul_ne k k' (fun h => hpq (congrArg Sum.inl h)) x y z w
      | inr l => exact hMN k x y l z w
    | inr l =>
      cases q with
      | inl k => exact hNM l x y k z w
      | inr l' => exact N.mul_ne l l' (fun h => hpq (congrArg Sum.inr h)) x y z w
  star_U p x y := by
    cases p with
    | inl k => exact M.star_U k x y
    | inr l => exact N.star_U l x y

/-- The units of `sum` on the first summand. -/
lemma sum_U_inl (M : PartialUnits d H) (N : PartialUnits e H) (hMN hNM) (k : ι) :
    (M.sum N hMN hNM).U (.inl k) = M.U k := rfl

/-- The units of `sum` on the second summand. -/
lemma sum_U_inr (M : PartialUnits d H) (N : PartialUnits e H) (hMN hNM) (l : κ) :
    (M.sum N hMN hNM).U (.inr l) = N.U l := rfl

/-- **A partial system with `∑ₖ ∑ₓ U k x x = 1` is a system of matrix units.** -/
def toMatrixUnits (M : PartialUnits d H) (h : ∑ k, ∑ x, M.U k x x = 1) : MatrixUnits d H where
  U := M.U
  mul_same := M.mul_same
  mul_ne := M.mul_ne
  star_U := M.star_U
  sum_U := h

end PartialUnits

end

end Lightlike.NCG

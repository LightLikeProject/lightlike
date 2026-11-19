import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# A matrix of rank `r` has a nonzero `r × r` minor

For a real matrix `A` of rank `r` there are `r` rows and `r` columns such that the `r × r` submatrix has nonzero
determinant (`exists_isUnit_det_submatrix`). Used to turn the constant-rank hypothesis of the Dirac algorithm into the
existence of an invertible block `B` at each point; as the determinant is continuous, the block stays invertible nearby.
(No such lemma is in the pinned Mathlib: this is a proof from `exists_linearIndependent'` and
`Matrix.linearIndependent_row_iff_isUnit`.)
-/

open Matrix

namespace Lightlike.Gauge

variable {n l : Type} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]

/-- **A nonzero minor of the size of the rank**. -/
theorem exists_isUnit_det_submatrix (A : Matrix n l ℝ) :
    ∃ (R : Fin A.rank → n) (C : Fin A.rank → l), Function.Injective R ∧ Function.Injective C ∧
      IsUnit (A.submatrix R C).det := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ A.col
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcardκ : Fintype.card κ = A.rank := by
    rw [rank_eq_finrank_span_cols, ← hsp, finrank_span_eq_card hli]
  let B : Matrix n κ ℝ := A.submatrix id a
  have hBcol : B.col = A.col ∘ a := rfl
  have hrankB : B.rank = Fintype.card κ := by
    rw [rank_eq_finrank_span_cols, hBcol, finrank_span_eq_card hli]
  obtain ⟨ρ, b, hb, hsp2, hli2⟩ := exists_linearIndependent' ℝ B.row
  haveI : Fintype ρ := Fintype.ofInjective b hb
  have hcardρ : Fintype.card ρ = B.rank := by
    rw [rank_eq_finrank_span_row, ← hsp2, finrank_span_eq_card hli2]
  have hcard : Fintype.card ρ = Fintype.card κ := by rw [hcardρ, hrankB]
  let e : ρ ≃ κ := Fintype.equivOfCardEq hcard
  let M : Matrix ρ ρ ℝ := A.submatrix b (a ∘ e)
  have hMrow : LinearIndependent ℝ M.row := by
    have := hli2.map' (LinearEquiv.funCongrLeft ℝ ℝ e).toLinearMap (LinearEquiv.ker _)
    convert this using 1
    ext i j
    simp [M, B, Matrix.row, LinearEquiv.funCongrLeft_apply, Function.comp]
  have hM : IsUnit M := Matrix.linearIndependent_row_iff_isUnit.mp hMrow
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  let eρ : Fin A.rank ≃ ρ := (Fintype.equivFinOfCardEq (hcard.trans hcardκ)).symm
  refine ⟨b ∘ eρ, a ∘ e ∘ eρ, hb.comp eρ.injective, ha.comp (e.injective.comp eρ.injective), ?_⟩
  have : A.submatrix (b ∘ eρ) (a ∘ e ∘ eρ) = M.submatrix eρ eρ := rfl
  rw [this, Matrix.det_submatrix_equiv_self]
  exact hdet

section Nearby

variable {X : Type*} [TopologicalSpace X] {m : Type} [Fintype m] [DecidableEq m]

/-- **An invertible block stays invertible nearby**: if the entries of a matrix-valued function are continuous at `x₀`
and its determinant is nonzero there, it is nonzero on a neighbourhood. -/
theorem eventually_isUnit_det {B : X → Matrix m m ℝ} {x₀ : X} (hB : ∀ i j, ContinuousAt (fun x => B x i j) x₀)
    (h : IsUnit (B x₀).det) : ∀ᶠ x in nhds x₀, IsUnit (B x).det := by
  have hcont : ContinuousAt (fun x => (B x).det) x₀ := by
    have : ContinuousAt B x₀ := continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => hB i j
    exact (continuous_id.matrix_det).continuousAt.comp this
  have hne : (B x₀).det ≠ 0 := h.ne_zero
  filter_upwards [hcont.eventually_ne hne] with x hx using isUnit_iff_ne_zero.mpr hx

end Nearby

end Lightlike.Gauge

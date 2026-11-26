module

public import Lightlike.Spacetime.Curvature

/-!
# Hyperbolic space, de Sitter and anti-de Sitter space as coordinate metrics

Each space is given by one chart, as a coordinate metric `g : ℝⁿ → Matrix` on an open set
(`IsCoordMetric`, `Lightlike/Spacetime/Curvature.lean`); all three are conformally flat.

* `hyperbolicMetric n`: the Poincaré ball model `4 δ / (1 - |x|²)²` on the open unit ball of `ℝⁿ`,
  of constant sectional curvature `-1` (the standard formula; see Carroll, gr-qc/9712019, §8; the source
  comparison of the curvature value is pending, it is proven in the maximal-symmetry file).
* `deSitterMetric L`: the flat-slicing (conformal time) chart `(L²/η²) · η_{μν}` on `x₀ < 0`
  of de Sitter space of radius `L`, curvature `+1/L²`.
* `antiDeSitterMetric L`: the Poincaré patch `(L²/z²) · η_{μν}` on `x_last > 0` (the last
  coordinate is the radial one `z`), curvature `-1/L²`.

Only the definitions and their being coordinate metrics are here; the Killing fields and the
curvature are in the files that prove maximal symmetry.
-/

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

/-- The open unit ball of `ℝⁿ`, the domain of the Poincaré ball model. -/
def hyperbolicDomain (n : ℕ) : Set (Fin n → ℝ) := {x | ∑ i, x i ^ 2 < 1}

/-- The **hyperbolic metric** `4 δ / (1 - |x|²)²` of the Poincaré ball model of `Hⁿ`
(curvature `-1`), as a coordinate metric on `hyperbolicDomain n`. -/
def hyperbolicMetric (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun _ => 4 / (1 - ∑ i, x i ^ 2) ^ 2

/-- The conformal-time chart domain `x₀ < 0` of de Sitter space in `m + 1` dimensions. -/
def deSitterDomain (m : ℕ) : Set (Fin (m + 1) → ℝ) := {x | x 0 < 0}

/-- The **de Sitter metric** `(L²/η²) η_{μν}`, `η = x₀ < 0` the conformal time, of the flat slicing
of de Sitter space of radius `L` in `m + 1` dimensions (curvature `+1/L²`). -/
def deSitterMetric (m : ℕ) (L : ℝ) (x : Fin (m + 1) → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.diagonal fun i => L ^ 2 / (x 0) ^ 2 * etaDiag i

/-- The Poincaré-patch domain `z = x_last > 0` of anti-de Sitter space in `m + 1` dimensions. -/
def antiDeSitterDomain (m : ℕ) : Set (Fin (m + 1) → ℝ) := {x | 0 < x (Fin.last m)}

/-- The **anti-de Sitter metric** `(L²/z²) η_{μν}`, `z = x_last > 0` the radial coordinate, of the
Poincaré patch of anti-de Sitter space of radius `L` in `m + 1` dimensions (curvature `-1/L²`). -/
def antiDeSitterMetric (m : ℕ) (L : ℝ) (x : Fin (m + 1) → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.diagonal fun i => L ^ 2 / (x (Fin.last m)) ^ 2 * etaDiag i

theorem isOpen_hyperbolicDomain (n : ℕ) : IsOpen (hyperbolicDomain n) :=
  isOpen_lt (by fun_prop) continuous_const

theorem isCoordMetric_hyperbolic (n : ℕ) :
    IsCoordMetric (hyperbolicMetric n) (hyperbolicDomain n) := by
  have hne : ∀ x ∈ hyperbolicDomain n, 1 - ∑ i, x i ^ 2 ≠ 0 := fun x hx =>
    (sub_pos.2 hx).ne'
  refine isCoordMetric_diagonal (fun x _ => 4 / (1 - ∑ i, x i ^ 2) ^ 2)
    (isOpen_hyperbolicDomain n) (fun i => ?_) (fun x hx i => ?_)
  · refine ContDiffOn.div contDiffOn_const (by fun_prop) fun x hx => pow_ne_zero _ (hne x hx)
  · exact div_ne_zero (by norm_num) (pow_ne_zero _ (hne x hx))

theorem isCoordMetric_deSitter (m : ℕ) {L : ℝ} (hL : L ≠ 0) :
    IsCoordMetric (deSitterMetric m L) (deSitterDomain m) := by
  have hne : ∀ x ∈ deSitterDomain m, x 0 ≠ 0 := fun x hx => hx.ne
  refine isCoordMetric_diagonal (fun x i => L ^ 2 / (x 0) ^ 2 * etaDiag i)
    (isOpen_lt (by fun_prop) continuous_const) (fun i => ?_) (fun x hx i => ?_)
  · exact (ContDiffOn.div contDiffOn_const (by fun_prop) fun x hx => pow_ne_zero _ (hne x hx)).mul
      contDiffOn_const
  · exact mul_ne_zero (div_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ (hne x hx)))
      (etaDiag_ne_zero i)

theorem isCoordMetric_antiDeSitter (m : ℕ) {L : ℝ} (hL : L ≠ 0) :
    IsCoordMetric (antiDeSitterMetric m L) (antiDeSitterDomain m) := by
  have hne : ∀ x ∈ antiDeSitterDomain m, x (Fin.last m) ≠ 0 := fun x hx => hx.ne'
  refine isCoordMetric_diagonal (fun x i => L ^ 2 / (x (Fin.last m)) ^ 2 * etaDiag i)
    (isOpen_lt continuous_const (by fun_prop)) (fun i => ?_) (fun x hx i => ?_)
  · exact (ContDiffOn.div contDiffOn_const (by fun_prop) fun x hx => pow_ne_zero _ (hne x hx)).mul
      contDiffOn_const
  · exact mul_ne_zero (div_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ (hne x hx)))
      (etaDiag_ne_zero i)

end Lightlike

end

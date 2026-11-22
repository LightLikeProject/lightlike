import Lightlike.OperatorAlgebras.FockExists
import Lightlike.OperatorAlgebras.ShaleSufficiency
import Lightlike.OperatorAlgebras.TestsShaleInfinite
import Lightlike.OperatorAlgebras.TestsShaleSqueeze

/-!
# Milestone OP2: one place for the done-when and the trust checks

Done-when: a Fock representation exists on every complex Hilbert space (`fockRepOf`), and a Bogoliubov
transformation is implemented in a Fock representation if and only if its antilinear part is
Hilbert-Schmidt (`shale_criterion`, Shale 1962).

Trust checks: for one mode `|α|² - |β|² = 1` (the general identity `Bogoliubov.norm_alpha_sq_sub_norm_beta_sq`,
here for the squeezing with `α z = a z`, `β z = b z̄`); the one-mode squeezing is implemented
(`implements_squeeze`); the squeezing of every mode of `ℓ²(ℕ)` with constant `|β| = |b| ≠ 0` is not
implemented (`not_implements_squeezeEllTwo`).

The statements below only restate existing results in the form of the milestone line, so a change in one of
them breaks this file.
-/

universe u

namespace Lightlike.OperatorAlgebras

/-- **OP2, done-when**: a Fock representation on every complex Hilbert space, and Shale's criterion in it. -/
theorem op2_fock_and_shale (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    (T : Bogoliubov h) :
    Implements (fockRepOf h).toCCRRep T ↔ IsHilbertSchmidt T.betaPart :=
  shale_criterion (fockRepOf h) T

/-- **One mode**: the squeezing with `a² - b² = 1` has `|α|² - |β|² = 1` on the unit vector `1 : ℂ`. -/
theorem op2_one_mode_alpha_beta (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) :
    ‖(Bogoliubov.squeeze a b hab).alphaPart 1‖ ^ 2 - ‖(Bogoliubov.squeeze a b hab).betaPart 1‖ ^ 2 = 1 := by
  have := (Bogoliubov.squeeze a b hab).norm_alpha_sq_sub_norm_beta_sq 1
  simpa using this

/-- **Infinitely many modes with constant `|β|`** are not implementable, in any Fock representation. -/
theorem op2_infinite_modes_not_implementable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (R : FockRep EllTwo K) (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (hb : b ≠ 0) :
    ¬ Implements R.toCCRRep (squeezeEllTwo a b hab) :=
  not_implements_squeezeEllTwo R a b hab hb

/-- The same squeezing of one mode is implemented (the control of the previous theorem). -/
theorem op2_one_mode_implementable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (R : FockRep ℂ K) (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) :
    Implements R.toCCRRep (Bogoliubov.squeeze a b hab) :=
  implements_squeeze R a b hab

end Lightlike.OperatorAlgebras

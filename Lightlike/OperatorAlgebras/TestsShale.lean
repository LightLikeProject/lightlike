import Lightlike.OperatorAlgebras.ShaleSufficiency
import Lightlike.OperatorAlgebras.TestsFockReduction

/-!
# Trust checks for Shale's criterion

* Non-vacuity of the necessity part: the identity transformation is implemented (`implements_id`), and its
  antilinear part vanishes, in agreement with the criterion.
* Non-vacuity of the sufficiency part: the parity transformation `f ↦ -f` is complex-linear, so its antilinear
  part vanishes and the criterion gives a unitary `U` with `U W f = W (-f) U` (`implements_neg`).

A transformation whose antilinear part is not Hilbert-Schmidt (a squeezing of infinitely many modes), which the
criterion says is not implemented, is in Lightlike/OperatorAlgebras/TestsShaleInfinite.lean.
-/

open scoped InnerProductSpace
open Complex

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma Bogoliubov.id_betaPart (f : h) : (Bogoliubov.id h).betaPart f = 0 := by
  simp [Bogoliubov.betaPart, Bogoliubov.id, smul_smul]

/-- The parity transformation `f ↦ -f`. -/
noncomputable def Bogoliubov.neg (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] :
    Bogoliubov h where
  toEquiv := ContinuousLinearEquiv.neg ℝ
  symp_map f g := by simp [symp, inner_neg_left, inner_neg_right]

lemma Bogoliubov.neg_betaPart (f : h) : (Bogoliubov.neg h).betaPart f = 0 := by
  simp [Bogoliubov.betaPart, Bogoliubov.neg, smul_smul]

/-- **Check of the necessity part on the identity**: the criterion gives a Hilbert-Schmidt antilinear part,
which is zero. -/
theorem isHilbertSchmidt_id_betaPart [CompleteSpace h] (R : FockRep h K) :
    IsHilbertSchmidt (Bogoliubov.id h).betaPart :=
  shale_necessity_of_implements R _ (implements_id R)

/-- **Non-vacuity of the sufficiency part**: the parity transformation `f ↦ -f` is implemented in every Fock
representation. -/
theorem implements_neg [CompleteSpace h] (R : FockRep h K) : Implements R.toCCRRep (Bogoliubov.neg h) := by
  refine shale_sufficiency_of_hilbertSchmidt R _ fun ι b => ?_
  simpa [Bogoliubov.neg_betaPart] using (summable_zero : Summable fun _ : ι => (0 : ℝ))

end Lightlike.OperatorAlgebras

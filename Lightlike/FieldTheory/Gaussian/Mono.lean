import Lightlike.FieldTheory.Gaussian.Ibp

/-!
# Monomials in the coordinates and their line derivatives

`mono l x = ∏ₖ∈l x_k` is the monomial of a list of indices, and `dmono j l` its derivative along `eⱼ`:
the sum over the positions `m` of `l` carrying the index `j` of the monomial of `l` without the
position `m`.
-/

open MeasureTheory ProbabilityTheory Matrix Real

noncomputable section

namespace Lightlike.FieldTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The monomial of a list of indices. -/
def mono (l : List ι) (x : EuclideanSpace ℝ ι) : ℝ := (l.map fun k => x k).prod

/-- Its derivative along `eⱼ`. -/
def dmono (j : ι) (l : List ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ m ∈ Finset.range l.length, if l[m]? = some j then mono (l.eraseIdx m) x else 0

@[simp] lemma mono_nil (x : EuclideanSpace ℝ ι) : mono ([] : List ι) x = 1 := rfl

@[simp] lemma mono_cons (k : ι) (l : List ι) (x : EuclideanSpace ℝ ι) :
    mono (k :: l) x = x k * mono l x := by simp [mono]

@[simp] lemma dmono_nil (j : ι) (x : EuclideanSpace ℝ ι) : dmono j ([] : List ι) x = 0 := by
  simp [dmono]

lemma dmono_cons (j k : ι) (l : List ι) (x : EuclideanSpace ℝ ι) :
    dmono j (k :: l) x = (if k = j then mono l x else 0) + x k * dmono j l x := by
  unfold dmono
  rw [List.length_cons, Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [List.getElem?_cons_succ, List.eraseIdx_cons_succ, mono_cons]
    split_ifs <;> simp

lemma hasLineDerivAt_coord (k j : ι) (x : EuclideanSpace ℝ ι) :
    HasLineDerivAt ℝ (fun x : EuclideanSpace ℝ ι => x k) (if k = j then 1 else 0) x (e j) := by
  unfold HasLineDerivAt
  have : (fun t : ℝ => (x + t • e j) k) = fun t => x k + t * (if k = j then 1 else 0) := by
    ext t
    simp [e, PiLp.single_apply]
  rw [this]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (if k = j then (1 : ℝ) else 0)).const_add (x k)

lemma hasLineDerivAt_mono (j : ι) (l : List ι) (x : EuclideanSpace ℝ ι) :
    HasLineDerivAt ℝ (mono l) (dmono j l x) x (e j) := by
  induction l with
  | nil =>
    unfold HasLineDerivAt
    simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | cons k l ih =>
    have h1 := hasLineDerivAt_coord k j x
    unfold HasLineDerivAt at *
    have := h1.mul ih
    convert this using 1
    · ext t; simp
    · rw [dmono_cons]; simp [mono]

end Lightlike.FieldTheory

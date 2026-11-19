import Lightlike.HarmonicAnalysis.CharacterOrthogonality
import Lightlike.HarmonicAnalysis.PeterWeylCircle

/-!
# Check: the non-compact group `ℝ` has no square-integrable matrix coefficients

The Peter–Weyl theorem needs compactness. For the additive group `ℝ` (as the multiplicative group
`Multiplicative ℝ`, with Lebesgue measure as Haar measure):

* `real_not_forall_memLp_two`: no row of a finite-dimensional unitary matrix representation of `ℝ` consists of
  square-integrable functions;
* `real_character_not_memLp_two`: the unitary characters `x ↦ e^{itx}` (`realChar t`), which are the
  irreducible unitary representations of `ℝ`, are not in `L²(ℝ)`.

Checks of the milestone; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

open UnitaryMatrixRep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Check: `ℝ` has no square-integrable row of matrix coefficients.** -/
theorem real_not_forall_memLp_two (ρ : UnitaryMatrixRep (Multiplicative ℝ) ι) (i : ι) :
    ¬ ∀ j, MemLp (fun x : ℝ => ρ.mat (Multiplicative.ofAdd x) i j) 2 (volume : Measure ℝ) := by
  intro h
  have hint : Integrable (fun x : ℝ => ∑ j, ‖ρ.mat (Multiplicative.ofAdd x) i j‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => by
      have h2 : MemLp (fun x : ℝ => ρ.mat (Multiplicative.ofAdd x) i j) ((2 : ℕ) : ENNReal) volume := by
        simpa using h j
      exact h2.integrable_norm_pow (by norm_num)
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) volume :=
    hint.congr (Filter.Eventually.of_forall fun x => ρ.sum_norm_sq_row _ i)
  rcases integrable_const_iff.1 h1 with h0 | h0
  · exact one_ne_zero h0
  · exact absurd Real.volume_univ (measure_ne_top volume Set.univ)

/-- The homomorphism `x ↦ e^{itx}` from `ℝ` to the circle. -/
def realCharHom (t : ℝ) : Multiplicative ℝ →* Circle where
  toFun x := Circle.exp (t * x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add, Circle.exp_add]

/-- The unitary character `x ↦ e^{itx}` of `ℝ`, as a one-dimensional unitary representation. -/
def realChar (t : ℝ) : UnitaryMatrixRep (Multiplicative ℝ) Unit :=
  ofCircleHom (realCharHom t) (Circle.exp.continuous.comp (continuous_const.mul continuous_toAdd))

/-- **Check: the unitary characters of `ℝ` are not square-integrable.** -/
theorem real_character_not_memLp_two (t : ℝ) :
    ¬ MemLp (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) 2 (volume : Measure ℝ) := by
  intro h
  exact real_not_forall_memLp_two (realChar t) () fun _ => h

end

end Lightlike.HarmonicAnalysis

import Lightlike.Spacetime.Causal.MinkowskiCausal

/-!
# Checks of the causal definitions on Minkowski space

Non-vacuity and wrong-model checks of the definitions of `Lightlike/Spacetime/Causal/`.

* `minkowskiOrientation d`: Minkowski space `ℝ^{d+1}` is time oriented by the constant field `∂₀`
  (defined in `MinkowskiCausal.lean`).
* A straight line with a future-directed timelike direction is a future-directed timelike curve
  (`isFutureTimelikeCurve_line`), so `x + v ∈ I⁺(x)` (`line_mem_chronFuture`) and the future
  cone of `∂₀` is nonempty: the hypotheses of the curve definitions are satisfiable by genuine,
  non-constant curves.
* Wrong-model: a spacelike vector is not future causal; `∂₀` is not past causal.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {d : ℕ}

lemma form_e0 : minkowskiForm (d + 1) (Pi.single 0 1) (Pi.single 0 1) = -1 := by
  rw [minkowskiForm_eq]
  simp

lemma form_e1 : minkowskiForm (d + 2) (Pi.single (Fin.succ 0) 1) (Pi.single (Fin.succ 0) 1) = 1 := by
  rw [minkowskiForm_eq]
  have h0 : (Pi.single (Fin.succ 0) 1 : Fin (d + 2) → ℝ) 0 = 0 :=
    Pi.single_eq_of_ne (Fin.succ_ne_zero 0).symm _
  rw [h0, Finset.sum_eq_single (0 : Fin (d + 1))]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne (fun h => hi (Fin.succ_inj.1 h)), zero_mul]
  · simp

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity: `x + ∂₀ ∈ I⁺(x)` in Minkowski space. -/
example (x : Fin (d + 1) → ℝ) : x + Pi.single 0 1 ∈ chronFuture (minkowskiOrientation d) x :=
  line_mem_chronFuture x _ ⟨form_e0.trans_lt (by norm_num), form_e0.trans_lt (by norm_num)⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- Wrong model: a spacelike vector (`e₁`, in dimension `d + 2`) is not future-directed causal. -/
example (x : Fin (d + 2) → ℝ) :
    ¬ (minkowskiOrientation (d + 1)).IsFutureCausal (x := x) (Pi.single (Fin.succ 0) 1 : Fin (d + 2) → ℝ) := by
  rintro ⟨-, h, -⟩
  change minkowskiForm (d + 2) _ _ ≤ 0 at h
  linarith [form_e1 (d := d)]

set_option synthInstance.maxHeartbeats 200000 in
/-- Wrong model: the field `∂₀` itself is future-directed, not past-directed, timelike. -/
example (x : Fin (d + 1) → ℝ) :
    (minkowskiOrientation d).IsFutureTimelike (x := x) (Pi.single 0 1 : Fin (d + 1) → ℝ) ∧
      ¬ (minkowskiOrientation d).IsPastTimelike (x := x) (Pi.single 0 1 : Fin (d + 1) → ℝ) := by
  have h := form_e0 (d := d)
  refine ⟨⟨?_, ?_⟩, fun ⟨_, h2⟩ => ?_⟩
  · change minkowskiForm (d + 1) _ _ < 0
    linarith
  · change minkowskiForm (d + 1) (Pi.single 0 1) (Pi.single 0 1) < 0
    linarith
  · change 0 < minkowskiForm (d + 1) (Pi.single 0 1) (Pi.single 0 1) at h2
    linarith

end Lightlike.Causal

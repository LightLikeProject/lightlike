import Lightlike.CausalSets.Basic
import Lightlike.Spacetime.Causal.MinkowskiCausal

/-!
# The causal order of Minkowski space as a partial order

This file is the geometric half of the bridge between Lorentzian geometry and causal sets. The
causal future `J⁺(x)` of a point of Minkowski space `ℝ^{d+1}` is the closed future light cone
(the statement `Causal.minkowski_causalFuture` is an open proof task of the causal-structure
interface). Here the cone is used directly: `coneLE x y` says that `y - x` is in the closed future
cone, `0 ≤ (y - x)⁰` and `η(y - x, y - x) ≤ 0`. It is shown to be a partial order, so any finite
subset of Minkowski space, with the induced order, is a causal set.

## References

* L. Bombelli, J. Lee, D. Meyer, R. D. Sorkin, *Space-time as a causal set*, Phys. Rev. Lett. 59
  (1987) 521.
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

namespace Lightlike.CausalSets

variable {d : ℕ}

/-- **Minkowski space with its causal order**: the type `ℝ^{d+1}` (index `0` is time), kept apart
from the product order of `Fin (d+1) → ℝ`. -/
def ConeSpace (d : ℕ) : Type := Fin (d + 1) → ℝ

instance : AddCommGroup (ConeSpace d) := inferInstanceAs (AddCommGroup (Fin (d + 1) → ℝ))

/-- `y` is in the causal future of `x` in Minkowski space: `y - x` is a future-directed causal
vector, `0 ≤ (y - x)⁰` and `η(y - x, y - x) ≤ 0`. -/
def coneLE (x y : Fin (d + 1) → ℝ) : Prop :=
  0 ≤ (y - x) 0 ∧ minkowskiForm (d + 1) (y - x) (y - x) ≤ 0

/-- The cone order is the causal future of Minkowski space (the right-hand side of the open task
`Causal.minkowski_causalFuture`). -/
lemma coneLE_iff (x y : Fin (d + 1) → ℝ) :
    coneLE x y ↔ y ∈ {y | 0 ≤ (y - x) 0 ∧ minkowskiForm (d + 1) (y - x) (y - x) ≤ 0} := Iff.rfl

/-- Cone order in terms of the spatial length: `|y - x| ≤ (y - x)⁰`. -/
lemma coneLE_iff_spatial (x y : Fin (d + 1) → ℝ) :
    coneLE x y ↔ 0 ≤ (y - x) 0 ∧ spatialSq (y - x) ≤ ((y - x) 0) ^ 2 := by
  have : minkowskiForm (d + 1) (y - x) (y - x) = mSq (y - x) := rfl
  unfold coneLE; rw [this, mSq_eq]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

lemma spatialSq_nonneg (v : Fin (d + 1) → ℝ) : 0 ≤ spatialSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma spatialSq_add_le (u v : Fin (d + 1) → ℝ) :
    spatialSq (u + v) ≤ (√(spatialSq u) + √(spatialSq v)) ^ 2 := by
  have hcs : (∑ i : Fin d, u i.succ * v i.succ) ^ 2 ≤ spatialSq u * spatialSq v :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have ha := spatialSq_nonneg u
  have hb := spatialSq_nonneg v
  have h1 : (√(spatialSq u) * √(spatialSq v)) ^ 2 = spatialSq u * spatialSq v := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  have h2 : ∑ i : Fin d, u i.succ * v i.succ ≤ √(spatialSq u) * √(spatialSq v) :=
    abs_le_of_sq_le_sq' (by rw [h1]; exact hcs) (by positivity) |>.2
  have h3 : spatialSq (u + v) = spatialSq u + 2 * ∑ i : Fin d, u i.succ * v i.succ + spatialSq v := by
    simp only [spatialSq, Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; congr 1; refine Finset.sum_congr rfl fun i _ => by ring
  rw [h3, add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  linarith

/-- The cone order is reflexive. -/
lemma coneLE_refl (x : Fin (d + 1) → ℝ) : coneLE x x := by
  rw [coneLE_iff_spatial]; simp [spatialSq]

/-- The cone order is transitive (the triangle inequality for the spatial length). -/
lemma coneLE_trans {x y z : Fin (d + 1) → ℝ} (h1 : coneLE x y) (h2 : coneLE y z) : coneLE x z := by
  rw [coneLE_iff_spatial] at *
  obtain ⟨a0, a1⟩ := h1
  obtain ⟨b0, b1⟩ := h2
  have e : z - x = (y - x) + (z - y) := by abel
  have sa : √(spatialSq (y - x)) ≤ (y - x) 0 := Real.sqrt_le_iff.2 ⟨a0, a1⟩
  have sb : √(spatialSq (z - y)) ≤ (z - y) 0 := Real.sqrt_le_iff.2 ⟨b0, b1⟩
  rw [e]
  refine ⟨by simpa using add_nonneg a0 b0, ?_⟩
  calc spatialSq ((y - x) + (z - y)) ≤ _ := spatialSq_add_le _ _
    _ ≤ ((y - x) 0 + (z - y) 0) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity); linarith
    _ = _ := by simp

/-- The cone order is antisymmetric. -/
lemma coneLE_antisymm {x y : Fin (d + 1) → ℝ} (h1 : coneLE x y) (h2 : coneLE y x) : x = y := by
  rw [coneLE_iff_spatial] at *
  obtain ⟨a0, a1⟩ := h1
  obtain ⟨b0, b1⟩ := h2
  have t0 : (y - x) 0 = 0 := by simp only [Pi.sub_apply] at *; linarith
  have : spatialSq (y - x) = 0 :=
    le_antisymm (by rw [t0] at a1; simpa using a1) (spatialSq_nonneg _)
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Pi.sub_apply] at t0; linarith
  · have h := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ((y - x) k.succ))).1 this j
      (Finset.mem_univ _)
    have : (y - x) j.succ = 0 := by simpa using h
    simp only [Pi.sub_apply] at this; linarith

/-- **The causal order of Minkowski space** as a partial order on `ConeSpace d`. -/
instance : PartialOrder (ConeSpace d) where
  le x y := coneLE (show Fin (d + 1) → ℝ from x) (show Fin (d + 1) → ℝ from y)
  le_refl x := coneLE_refl _
  le_trans _ _ _ h1 h2 := coneLE_trans h1 h2
  le_antisymm _ _ h1 h2 := coneLE_antisymm h1 h2

lemma ConeSpace.le_iff (x y : ConeSpace d) :
    x ≤ y ↔ coneLE (show Fin (d + 1) → ℝ from x) (show Fin (d + 1) → ℝ from y) := Iff.rfl

/-- **Any subset of Minkowski space, with the induced causal order, is a causal set when it is
finite**: the order of a finite subset has finite intervals. -/
instance (s : Set (ConeSpace d)) [Finite s] : CausalSet s := inferInstance

end Lightlike.CausalSets

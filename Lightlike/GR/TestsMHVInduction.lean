import Lightlike.GR.MHVInduction
import Lightlike.GR.MHVFour

/-!
# Non-vacuity of the Parke-Taylor theorem for the true amplitudes

The class `G₀` of three-gluon kinematics (momentum conservation, nonzero angle brackets) is closed under the
reductions (the clauses for `m + 1` gluons are vacuous), `G₀` contains an explicit kinematic point, and
`trueAmp_eq_ptN` applied to it is the three-gluon Parke-Taylor amplitude.
-/

noncomputable section

namespace Lightlike.SpinorHelicity.Tests

open Lightlike.SpinorHelicity

/-- The class of three-gluon kinematics with the negative gluons `0` and `j ∈ {1, 2}`. -/
def G₀ : ℕ → ℕ → (ℕ → Fin 2 → ℂ) → (ℕ → Fin 2 → ℂ) → Prop := fun m j l lt =>
  m = 0 ∧ (j = 1 ∨ j = 2) ∧ momRange (fun t => nullMom (l t) (lt t)) 0 2 = 0 ∧ angleBr (lt 0) (lt 1) ≠ 0 ∧
    angleBr (lt 1) (lt 2) ≠ 0 ∧ angleBr (lt 2) (lt 0) ≠ 0

/-- The class `G₀` is closed under the reductions of the induction. -/
theorem G₀_closed : ClosedClass G₀ := by
  refine ⟨fun m j l lt h => ?_, fun j l lt h => ?_, fun m j l lt h _ => ?_, fun m l lt h => ?_⟩
  · obtain ⟨rfl, hj, -⟩ := h
    omega
  · obtain ⟨-, -, h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4⟩
  · exact absurd h.1 (by omega)
  · exact absurd h.1 (by omega)

/-- Spinors of a three-gluon point: `|i] ∝ (1, 0)`, `⟨0| = (1, 0)`, `⟨1| = (0, 1)`, `⟨2| = (1, 1)`. -/
def l₃ : ℕ → Fin 2 → ℂ := fun t => if t = 2 then ![1, 0] else ![-1, 0]

/-- The angle spinors of the three-gluon point. -/
def lt₃ : ℕ → Fin 2 → ℂ := fun t => if t = 0 then ![1, 0] else if t = 1 then ![0, 1] else ![1, 1]

/-- **Non-vacuity**: the class `G₀` contains an explicit point, and the theorem evaluates the true amplitude there. -/
theorem G₀_point : G₀ 0 1 l₃ lt₃ := by
  refine ⟨rfl, Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · have : momRange (fun t => nullMom (l₃ t) (lt₃ t)) 0 2 =
        nullMom (l₃ 0) (lt₃ 0) + nullMom (l₃ 1) (lt₃ 1) + nullMom (l₃ 2) (lt₃ 2) := by
      simp [momRange, Finset.sum_range_succ]
    rw [this]
    funext μ
    fin_cases μ <;> simp [nullMom, momOf, l₃, lt₃] <;> field_simp <;> ring_nf <;> simp [Complex.ext_iff]
  all_goals simp [angleBr_eq, lt₃]

/-- The three-gluon amplitude at the explicit point is its Parke-Taylor amplitude. -/
example : trueAmp 0 1 l₃ lt₃ ![0, 1] ![1, 0] = ptN 0 1 lt₃ := by
  refine trueAmp_eq_ptN G₀ G₀_closed 0 1 l₃ lt₃ _ _ G₀_point ?_ ?_
  · intro t ht hneg
    have : t = 0 ∨ t = 1 := by rcases hneg with h | h <;> omega
    rcases this with rfl | rfl <;> simp [squareBr_eq, l₃]
  · intro t ht hneg
    have : t = 2 := by omega
    subst this
    simp [angleBr_eq, lt₃]

/-- Square spinors of a four-gluon point. -/
def l₄ : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![-1, -1] else if t = 1 then ![-1, -2] else if t = 2 then ![1, 0] else ![0, 1]

/-- Angle spinors of a four-gluon point. -/
def lt₄ : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![1, 0] else if t = 1 then ![0, 1] else if t = 2 then ![1, 1] else ![1, 2]

/-- **Non-vacuity at four gluons**: the explicit point is generic (momentum conserving, all brackets nonzero), so
`trueAmp_four` gives the Parke-Taylor amplitude of the Feynman rules there. -/
example : trueAmp 1 2 l₄ lt₄ ![1, 3] ![1, 3] = ptN 1 2 lt₄ := by
  refine trueAmp_four 2 l₄ lt₄ _ _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_
  · have : momRange (fun t => nullMom (l₄ t) (lt₄ t)) 0 3 =
        nullMom (l₄ 0) (lt₄ 0) + nullMom (l₄ 1) (lt₄ 1) + nullMom (l₄ 2) (lt₄ 2) + nullMom (l₄ 3) (lt₄ 3) := by
      simp [momRange, Finset.sum_range_succ]
    rw [this]
    funext μ
    fin_cases μ <;> simp [nullMom, momOf, l₄, lt₄] <;> field_simp <;> ring_nf <;> simp [Complex.ext_iff]
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | (simp [angleBr_eq, lt₄]; try norm_num)
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | (simp [squareBr_eq, l₄]; try norm_num)
  · intro t ht
    interval_cases t <;> simp [squareBr_eq, l₄] <;> norm_num
  · intro t ht
    interval_cases t <;> simp [angleBr_eq, lt₄] <;> norm_num

end Lightlike.SpinorHelicity.Tests

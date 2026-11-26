import Lightlike.GR.MHVFive

/-!
# Non-vacuity at five gluons

An explicit rational five-gluon point is in the closed class `Gen5`, for every position of the second negative gluon,
so the Parke-Taylor theorem for the true amplitudes is not vacuous for five gluons.
-/

noncomputable section

namespace Lightlike.SpinorHelicity.Tests

open Lightlike.SpinorHelicity

/-- Square spinors of the five-gluon point. -/
def l5 : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![-9, -7] else if t = 1 then ![3, 11] else if t = 2 then ![3, 0] else if t = 3 then ![0, 1]
  else ![3, 3]

/-- Angle spinors of the five-gluon point. -/
def lt5 : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![1, 0] else if t = 1 then ![0, 1] else if t = 2 then ![1, 2] else if t = 3 then ![1, -2]
  else ![2, -3]

/-- Momentum conservation of the five-gluon point. -/
lemma cons5 : momRange (fun t => nullMom (l5 t) (lt5 t)) 0 4 = 0 := by
  have : momRange (fun t => nullMom (l5 t) (lt5 t)) 0 4 = nullMom (l5 0) (lt5 0) + nullMom (l5 1) (lt5 1) +
      nullMom (l5 2) (lt5 2) + nullMom (l5 3) (lt5 3) + nullMom (l5 4) (lt5 4) := by
    simp [momRange, Finset.sum_range_succ]
  rw [this]
  funext μ
  fin_cases μ <;> simp [nullMom, momOf, l5, lt5] <;> field_simp <;> ring_nf <;> simp [Complex.ext_iff]

/-- The poles of the channels `[1,2]` and `[1,3]` of the point. -/
lemma zpole5 : zpole l5 lt5 2 = -1 / 2 ∧ zpole l5 lt5 3 = -1 / 4 := by
  constructor
  · rw [zpole_two l5 lt5 (by simp [angleBr_eq, lt5]; try norm_num) (by simp [squareBr_eq, l5]; try norm_num)]
    simp [angleBr_eq, lt5]; try norm_num
  · rw [zpole_three]
    simp [angleBr_eq, squareBr_eq, l5, lt5]; try norm_num

/-- The point satisfies the bracket conditions. -/
lemma five5 : Five l5 lt5 := by
  refine ⟨cons5, ?_, ?_, ⟨![-6, -5], ![-6, -6], ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [angleBr_eq, lt5]; try norm_num)
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [squareBr_eq, l5]; try norm_num)
  · intro t ht
    interval_cases t <;> simp [squareBr_eq, l5] <;> norm_num
  · intro t ht
    interval_cases t <;> simp [angleBr_eq, lt5] <;> norm_num
  · simp [angleBr_eq, squareBr_eq, l5, lt5]; norm_num
  · simp [angleBr_eq, squareBr_eq, l5, lt5]; norm_num
  · simp [angleBr_eq, squareBr_eq, l5, lt5]; norm_num
  · rw [zpole5.1, zpole5.2]; norm_num
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [redL, angleBr_eq, squareBr_eq, l5, lt5]; try norm_num)
  · refine ⟨![-6, -5], ![-6, -6], ?_, ?_⟩
    · intro t ht
      interval_cases t <;> simp [redL, angleBr_eq, squareBr_eq, l5, lt5] <;> norm_num
    · intro t ht
      interval_cases t <;> simp [redLt, angleBr_eq, lt5] <;> norm_num

/-- The cyclically relabelled point `(1, 2, 3, 4, 0)`. -/
abbrev l5r : ℕ → Fin 2 → ℂ := rotLabels l5 4

/-- The angle spinors of the cyclically relabelled point. -/
abbrev lt5r : ℕ → Fin 2 → ℂ := rotLabels lt5 4

/-- The poles of the relabelled point. -/
lemma zpole5r : zpole l5r lt5r 2 = 4 ∧ zpole l5r lt5r 3 = 26 / 7 := by
  constructor
  · rw [zpole_two l5r lt5r (by simp [angleBr_eq, rotLabels, lt5]; try norm_num)
      (by simp [squareBr_eq, rotLabels, l5]; try norm_num)]
    simp [angleBr_eq, rotLabels, lt5]; try norm_num
  · rw [zpole_three]
    simp [angleBr_eq, squareBr_eq, rotLabels, l5, lt5]; try norm_num

/-- The relabelled point satisfies the bracket conditions. -/
lemma five5r : Five l5r lt5r := by
  refine ⟨?_, ?_, ?_, ⟨![-6, -5], ![-6, -6], ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cons5]
    simp [momRange, Finset.sum_range_succ, rotLabels]
    abel
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [rotLabels, angleBr_eq, lt5]; try norm_num)
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [rotLabels, squareBr_eq, l5]; try norm_num)
  · intro t ht
    interval_cases t <;> simp [rotLabels, squareBr_eq, l5] <;> norm_num
  · intro t ht
    interval_cases t <;> simp [rotLabels, angleBr_eq, lt5] <;> norm_num
  · simp [rotLabels, angleBr_eq, squareBr_eq, l5, lt5]; try norm_num
  · simp [rotLabels, angleBr_eq, squareBr_eq, l5, lt5]; try norm_num
  · simp [rotLabels, angleBr_eq, squareBr_eq, l5, lt5]; try norm_num
  · rw [zpole5r.1, zpole5r.2]; norm_num
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [redL, rotLabels, angleBr_eq, squareBr_eq, l5, lt5]; try norm_num)
  · refine ⟨![-6, -5], ![-6, -6], ?_, ?_⟩
    · intro t ht
      interval_cases t <;> simp [redL, rotLabels, angleBr_eq, squareBr_eq, l5, lt5] <;> norm_num
    · intro t ht
      interval_cases t <;> simp [redLt, rotLabels, angleBr_eq, lt5] <;> norm_num

/-- The shifted momentum of the channel `[1, 3]` at its pole is null. -/
lemma pole3_5 : momRange (shiftedMom l5 lt5 (zpole l5 lt5 3)) 1 3 = nullMom ![1, 1] ![15 / 4, 9] := by
  rw [zpole5.2]
  funext μ
  fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, shiftedMom, nullMom, momOf, l5, lt5] <;> field_simp <;>
    ring_nf <;> simp [Complex.ext_iff] <;> norm_num

/-- The pole spinors of the channel `[1, 3]` of the point, for every position of the second negative gluon. -/
lemma poles5 (j : ℕ) (hj : 2 ≤ j) (hj4 : j ≤ 4) : PolesData j l5 lt5 := by
  refine ⟨fun _ => ![1, 1], fun _ => ![15 / 4, 9], ?_, ?_, ?_, ?_, ?_⟩
  · intro d h1 h2
    obtain rfl : d = 3 := by omega
    exact pole3_5
  · intro d h1 h2
    simp [angleBr_eq, lt5]; try norm_num
  · intro d h1 h2
    simp [squareBr_eq, l5]; try norm_num
  · intro d h1 h2 hd s hs1 hs2
    obtain rfl : d = 3 := by omega
    rw [zpole5.2]
    interval_cases s <;> simp [ltHat, angleBr_eq, lt5] <;> norm_num
  · intro d h1 h2 hd
    obtain rfl : d = 3 := by omega
    rw [zpole5.2]
    refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
    · interval_cases j <;> interval_cases s <;>
        first | exact absurd rfl hsj | (simp [ltHat, angleBr_eq, lt5]; try norm_num)
    · interval_cases j <;> simp [angleBr_eq, lt5] <;> norm_num

/-- The shifted momentum of the channel `[1, 3]` of the relabelled point at its pole is null. -/
lemma pole3_5r : momRange (shiftedMom l5r lt5r (zpole l5r lt5r 3)) 1 3 = nullMom ![1, 7 / 9] ![9, -99 / 7] := by
  rw [zpole5r.2]
  funext μ
  fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, shiftedMom, nullMom, momOf, rotLabels, l5, lt5] <;>
    field_simp <;> ring_nf <;> simp [Complex.ext_iff] <;> norm_num

/-- The pole spinors of the channel `[1, 3]` of the relabelled point, the second negative gluon being `4`. -/
lemma poles5r : PolesData 4 l5r lt5r := by
  refine ⟨fun _ => ![1, 7 / 9], fun _ => ![9, -99 / 7], ?_, ?_, ?_, ?_, ?_⟩
  · intro d h1 h2
    obtain rfl : d = 3 := by omega
    exact pole3_5r
  · intro d h1 h2
    simp [angleBr_eq, rotLabels, lt5]; try norm_num
  · intro d h1 h2
    simp [squareBr_eq, rotLabels, l5]; try norm_num
  · intro d h1 h2 hd s hs1 hs2
    obtain rfl : d = 3 := by omega
    rw [zpole5r.2]
    interval_cases s <;> simp [ltHat, rotLabels, angleBr_eq, lt5] <;> norm_num
  · intro d h1 h2 hd
    omega

/-- **The point is in the closed class** for every position of the second negative gluon. -/
lemma gen5_point (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) : Gen5 2 j l5 lt5 := by
  right
  refine ⟨rfl, hj, hj4, five5, fun h => poles5 j h hj4, fun h => ?_⟩
  subst h
  exact ⟨five5r, poles5r⟩

/-- **Non-vacuity at five gluons**: the Parke-Taylor amplitude of the Feynman rules at the explicit point. -/
example (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) :
    trueAmp 2 j l5 lt5 ![-6, -5] ![-6, -6] = ptN 2 j lt5 := by
  refine trueAmp_eq_ptN Gen5 Gen5_closed 2 j l5 lt5 _ _ (gen5_point j hj hj4) ?_ ?_
  · intro t ht hneg
    interval_cases t <;> simp [squareBr_eq, l5] <;> norm_num
  · intro t ht hneg
    interval_cases t <;> simp_all [angleBr_eq, lt5] <;> norm_num

end Lightlike.SpinorHelicity.Tests

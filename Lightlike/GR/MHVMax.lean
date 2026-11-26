import Lightlike.GR.MHVBrackets

/-!
# The maximal closed class of kinematics for the Parke-Taylor induction

`Gmax m j l lt` unfolds the conditions of the induction along the reductions: at each level the far step (`FarData`) or,
for the second negative gluon next to the first, the cyclic step (`RotData`) followed by the far step of the rotated
kinematics, and then the same conditions for the reduced kinematics, down to the three-point data. It is a closed class
(`closedClass_Gmax`), so `trueAmp_eq_ptN` applies to it, and the non-vacuity of the theorem at `m + 3` gluons is the
non-emptiness of `Gmax m j` for explicit kinematics.
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The class of kinematics all of whose reductions satisfy the hypotheses of the induction. -/
def Gmax : ℕ → ℕ → (ℕ → Fin 2 → ℂ) → (ℕ → Fin 2 → ℂ) → Prop
  | 0, j, l, lt => (1 ≤ j ∧ j ≤ 2) ∧ momRange (fun t => nullMom (l t) (lt t)) 0 2 = 0 ∧
      angleBr (lt 0) (lt 1) ≠ 0 ∧ angleBr (lt 1) (lt 2) ≠ 0 ∧ angleBr (lt 2) (lt 0) ≠ 0
  | m + 1, j, l, lt => (1 ≤ j ∧ j ≤ m + 3) ∧
      (if 2 ≤ j then FarData m j l lt ∧ Gmax m (j - 1) (redL l lt) (redLt lt)
       else RotData (m + 1) l lt ∧ GenericAngles (fun i : Fin (m + 4) => lt i) ∧
        FarData m (m + 3) (rotLabels l (m + 3)) (rotLabels lt (m + 3)) ∧
        Gmax m (m + 2) (redL (rotLabels l (m + 3)) (rotLabels lt (m + 3))) (redLt (rotLabels lt (m + 3))))

/-- **`Gmax` is a closed class.** -/
theorem closedClass_Gmax : ClosedClass Gmax := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m j l lt h
    cases m with
    | zero => obtain ⟨⟨h1, h2⟩, -⟩ := h; exact ⟨h1, h2⟩
    | succ m => obtain ⟨⟨h1, h2⟩, -⟩ := h; exact ⟨h1, by omega⟩
  · intro j l lt h
    obtain ⟨-, h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4⟩
  · intro m j l lt h hj
    obtain ⟨-, h⟩ := h
    rw [if_pos hj] at h
    exact h
  · intro m l lt h
    obtain ⟨-, h⟩ := h
    rw [if_neg (by omega)] at h
    obtain ⟨hr, hg, hf, hG⟩ := h
    refine ⟨hr, hg, ?_⟩
    show (1 ≤ m + 3 ∧ m + 3 ≤ m + 1 + 2) ∧ _
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [if_pos (by omega)]
    exact ⟨hf, by simpa using hG⟩

end Lightlike.SpinorHelicity

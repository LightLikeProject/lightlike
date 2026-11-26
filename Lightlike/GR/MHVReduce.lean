import Lightlike.GR.MHVChannelTwo
import Lightlike.GR.MHVBase

/-!
# The reduced kinematics of the channel `[1, 2]`

On the pole of the channel `[1, 2]` the right factor of the recursion for the true amplitudes is the true amplitude of
the `(n − 1)`-gluon kinematics in which the gluons `1, 2` are replaced by the on-shell gluon `P`,
`|P] = c|1] + |2]`, `⟨P| = ⟨2|`, `c = ⟨01⟩/⟨02⟩`, and the gluon `0` is shifted to `|0̂] = |0] + z|1]`,
`z = ⟨12⟩/⟨02⟩` (Elvang-Huang (3.17)–(3.18)).
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The square spinors of the reduced kinematics of the channel `[1, 2]`: `0̂`, `P`, `3, 4, …`. -/
def redL (l lt : ℕ → Fin 2 → ℂ) : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then l 0 + (angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)) • l 1
  else if t = 1 then (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2 else l (t + 1)

/-- The angle spinors of the reduced kinematics of the channel `[1, 2]`: `⟨0|`, `⟨2|`, `⟨3|, …`. -/
def redLt (lt : ℕ → Fin 2 → ℂ) : ℕ → Fin 2 → ℂ := fun t => if t = 0 then lt 0 else lt (t + 1)

/-- **The reduced momenta**: the collapse of the shifted momenta at the pole of `[1, 2]` is `0̂, P, 3, 4, …`. -/
lemma collapse_pole_two (l lt : ℕ → Fin 2 → ℂ) (h02 : angleBr (lt 0) (lt 2) ≠ 0)
    (h12 : squareBr (l 1) (l 2) ≠ 0) (t : ℕ) :
    collapse (shiftedMom l lt (zpole l lt 2)) 1 2 (momRange (shiftedMom l lt (zpole l lt 2)) 1 2) t =
      nullMom (redL l lt t) (redLt lt t) := by
  rw [momRange_pole_two l lt h02 h12, zpole_two l lt h02 h12]
  by_cases h0 : t = 0
  · subst h0
    simp [collapse, redL, redLt, shiftedMom]
  by_cases h1 : t = 1
  · subst h1
    simp [collapse, redL, redLt]
  · rw [collapse_of_gt _ _ (show 1 < t by omega)]
    simp [redL, redLt, shiftedMom, h0, h1, show t + (2 - 1) ≠ 0 by omega, show t + (2 - 1) ≠ 1 by omega]

/-- **The reduced polarizations**: the collapse of the shifted polarizations, with the internal gluon negative if
`j = 2` and positive if `j ≥ 3`, is the good-gauge polarization of the reduced kinematics with the negative gluons
`0` and `j − 1`. -/
lemma collapse_pol_two (l lt : ℕ → Fin 2 → ℂ) (j : ℕ) (hj : 2 ≤ j) (h02 : angleBr (lt 0) (lt 2) ≠ 0)
    (h12 : squareBr (l 1) (l 2) ≠ 0) (t : ℕ) :
    collapse (shiftedPol l lt (l 1) (lt 0) j (zpole l lt 2)) 1 2
        (if j = 2 then epsMinus ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (l 1)
          else epsPlus ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (lt 0)) t =
      polRef (fun t => t = 0 ∨ t = j - 1) (redL l lt) (redLt lt) (fun _ => l 1) (fun _ => lt 0) t := by
  rw [zpole_two l lt h02 h12]
  by_cases h0 : t = 0
  · subst h0
    simp [collapse, polRef, redL, redLt, shiftedPol]
  by_cases h1 : t = 1
  · subst h1
    by_cases hj2 : j = 2
    · subst hj2; simp [collapse, polRef, redL, redLt]
    · simp [collapse, polRef, redL, redLt, hj2, show (1 : ℕ) ≠ j - 1 by omega]
  · rw [collapse_of_gt _ _ (show 1 < t by omega)]
    have hs : shiftedPol l lt (l 1) (lt 0) j (angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)) (t + (2 - 1)) =
        if t + 1 = j then epsMinus (l (t + 1)) (lt (t + 1)) (l 1) else epsPlus (l (t + 1)) (lt (t + 1)) (lt 0) := by
      simp [shiftedPol, show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega, h0]
    rw [hs]
    by_cases hj' : t + 1 = j
    · have hjt : t = j - 1 := by omega
      subst hjt
      have e1 : j - 1 + 1 = j := by omega
      simp [polRef, redL, redLt, h0, h1, e1, show j ≠ 2 by omega]
    · simp [polRef, redL, redLt, h0, h1, hj', show t ≠ j - 1 by omega]

end Lightlike.SpinorHelicity

import Lightlike.GR.MHVReduce
import Lightlike.GR.ParkeTaylorAll

/-!
# The Parke-Taylor recursion in the form of the reduced kinematics

`parkeTaylor_bcfw_far` for the angle spinors of the gluons `0, 1, 2, …` against the reduced angle spinors
`⟨0|, ⟨2|, ⟨3|, …` of the channel `[1, 2]`.
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **The Parke-Taylor amplitude satisfies the recursion of the reduced kinematics** (`2 ≤ j`). -/
theorem ptN_step (m j : ℕ) (hj : 2 ≤ j) (hjm : j ≤ m + 3) (l lt : ℕ → Fin 2 → ℂ)
    (hg : GenericAngles (fun i : Fin (m + 4) => lt i)) (hs12 : squareBr (l 1) (l 2) ≠ 0) :
    ptN (m + 1) j lt = ptN m (j - 1) (redLt lt) *
      ((squareBr (l 1) (l 2) / (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2))) /
        (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2))) := by
  have c0 : ((0 : Fin (m + 4)) : ℕ) = 0 := rfl
  have c1 : ((1 : Fin (m + 4)) : ℕ) = 1 := by show 1 % (m + 4) = 1; exact Nat.mod_eq_of_lt (by omega)
  have c2 : ((2 : Fin (m + 4)) : ℕ) = 2 := by show 2 % (m + 4) = 2; exact Nat.mod_eq_of_lt (by omega)
  have c3 : ((3 : Fin (m + 4)) : ℕ) = 3 := by show 3 % (m + 4) = 3; exact Nat.mod_eq_of_lt (by omega)
  have ne : ∀ a b : Fin (m + 4), (a : ℕ) ≠ b → a ≠ b := fun a b h e => h (by rw [e])
  have h01 : angleBr (lt 0) (lt 1) ≠ 0 := by
    have := hg 0 1 (ne _ _ (by rw [c0, c1]; omega)); simp only [c0, c1] at this; exact this
  have h02 : angleBr (lt 0) (lt 2) ≠ 0 := by
    have := hg 0 2 (ne _ _ (by rw [c0, c2]; omega)); simp only [c0, c2] at this; exact this
  have h12 : angleBr (lt 1) (lt 2) ≠ 0 := by
    have := hg 1 2 (ne _ _ (by rw [c1, c2]; omega)); simp only [c1, c2] at this; exact this
  have h23 : angleBr (lt 2) (lt 3) ≠ 0 := by
    have := hg 2 3 (ne _ _ (by rw [c2, c3]; omega)); simp only [c2, c3] at this; exact this
  have key := parkeTaylor_bcfw_far (fun i : Fin (m + 4) => l i) (fun i : Fin (m + 4) => lt i)
    ⟨j, by omega⟩ h01 h02 h12 h23 (restProd_ne_zero hg) hs12
  simp only [c0, c1, c2, Fin.val_mk] at key
  rw [mul_div_assoc] at key
  unfold ptN
  have hsa : (fun i : Fin (m + 3) => redLt lt i) = (fun i : Fin (m + 4) => lt i) ∘ (1 : Fin (m + 4)).succAbove := by
    funext i
    simp only [Function.comp_apply, redLt]
    by_cases h0 : (i : ℕ) = 0
    · have : i = 0 := Fin.ext (by simpa using h0)
      subst this
      simp [Fin.succAbove_of_castSucc_lt _ _ (show (Fin.castSucc 0 : Fin (m + 4)) < 1 from by
        rw [Fin.lt_def]; simp)]
    · rw [if_neg h0]
      congr 1
      rw [succAbove_one_of_pos (by omega)]
  rw [show (m + 1 + 3) = m + 4 from rfl]
  rw [show redLt lt 0 = lt 0 by simp [redLt], show redLt lt (j - 1) = lt j by
    simp [redLt, show j - 1 ≠ 0 by omega, show j - 1 + 1 = j by omega]]
  rw [hsa]
  exact key

end Lightlike.SpinorHelicity

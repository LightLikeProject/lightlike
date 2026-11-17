import Lightlike.TuraevViro.Reflect.RacahPhi43

/-!
# Non-vacuity of the `₄φ₃` form of the q-Racah sum

At level `7` the 6j symbol with all six doubled spins `2` has triad sums `3, 3, 3, 3` and quadrilateral sums
`4, 4, 4`, so `a1 = 3`, `n = 1`; every hypothesis of `racahSum_eq_phi43` holds.
-/

namespace Lightlike.TV.Refl

/-- The hypotheses of `racahSum_eq_phi43` are satisfied at level `7` by the 6j symbol with all spins `2`. -/
theorem racahSum_eq_phi43_seven :
    ((∑ z ∈ Finset.range 5, qRacahTerm 7 3 3 3 3 4 4 4 z : ℝ) : ℂ) =
      ((qRacahTerm 7 3 3 3 3 4 4 4 3 : ℝ) : ℂ) *
        ∑ k ∈ Finset.range 2, phi43Term 7 (3 + 2) (4 - 3) (4 - 3) (4 - 3) (3 + 1 - 3) (3 + 1 - 3)
          (3 + 1 - 3) k :=
  racahSum_eq_phi43 (r := 7) (by norm_num) (a1 := 3) (a2 := 3) (a3 := 3) (a4 := 3) (b1 := 4) (b2 := 4)
    (b3 := 4) (n := 1) (N := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Lightlike.TV.Refl

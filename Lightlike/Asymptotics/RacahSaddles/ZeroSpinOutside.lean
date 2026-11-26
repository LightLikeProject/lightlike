import Lightlike.Asymptotics.SaddleAssembly

/-!
# A zero spin lies outside the saddle-point theorem

Racah's sum with a zero spin has a single term and an exact value, so it is a natural second test
of the saddle-point asymptotics. This file shows that the theorem does not apply to it: a
tetrahedron with a zero edge opposite to an edge of a face with two equal remaining edges has a
degenerate face, so it is not Euclidean.
-/

namespace Lightlike.Asymptotics

/-- A tetrahedron with `j₃ = 0` and `j₁ = j₅` has the degenerate face `(j₃, j₁, j₅)`, so it is not
Euclidean and the saddle-point theorem does not apply to it. -/
theorem not_isEuclid_toReal_zero_spin (j : Fin 6 → ℕ) (h3 : j 3 = 0) (h15 : j 1 = j 5) :
    ¬ IsEuclid (toReal j) := by
  intro h
  have h0 := h.1 0 2
  obtain ⟨-, -, h3', -⟩ := quadSum_sub_faceSum (toReal j)
  simp only [toReal, h3, h15, Nat.cast_zero] at h3' h0
  simp only [faceSum_zero, quadSum_two, toReal, h3, h15, Nat.cast_zero] at h0
  linarith

end Lightlike.Asymptotics

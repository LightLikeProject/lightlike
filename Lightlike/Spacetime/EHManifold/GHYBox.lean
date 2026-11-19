import Lightlike.Spacetime.EHManifold.GibbonsHawkingYork

/-!
# The Einstein–Hilbert action with the Gibbons–Hawking–York term on a coordinate box

`sum_faceHup_dChristoffel`: at a point of the hyperplane `x^i = const` on which the perturbation vanishes,
`h^{αβ} δΓ^i_{αβ} = ½ W^i`. Hence the slope of the Gibbons–Hawking–York density, `-2 √|g| h^{αβ} δΓ^i_{αβ}`,
is `-√|g| W^i`: minus the flux of the Palatini identity (`ghySlope_eq_neg_ehFlux`). This is the cancellation
in Dyer–Hinterbichler (4.2) to (4.4), pointwise on a coordinate face.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.2) to (4.4), p. 20.
-/

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **`h^{αβ} δΓ^i_{αβ} = ½ W^i`** at a point of a face on which the perturbation vanishes. -/
theorem sum_faceHup_dChristoffel (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) (hx0 : h x = 0) (htan : ∀ σ a b, σ ≠ i → pd σ (fun z => h z a b) x = 0)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (hii : (g x)⁻¹ i i ≠ 0) :
    ∑ α, ∑ β, faceHup g i x α β * dChristoffel g h i α β x = (1 / 2) * Wvec g h i x := by
  have hterm : ∀ α β, faceHup g i x α β * dChristoffel g h i α β x =
      (1 / 2) * (((g x)⁻¹ i α * (g x)⁻¹ i β - (g x)⁻¹ i i * (g x)⁻¹ α β) *
        pd i (fun z => h z α β) x) := by
    intro α β
    rw [dChristoffel_of_vanishing_on_face g h x i hx0 htan]
    by_cases hα : α = i
    · rw [hα, faceHup_left g i x hii hinv β, zero_mul, hinv i β]
      ring
    · by_cases hβ : β = i
      · rw [hβ, faceHup_right g i x hii α, zero_mul, hinv i α]
        ring
      · simp only [hα, hβ, if_false, add_zero]
        unfold faceHup
        rw [hinv α i, hinv β i]
        field_simp
        ring
  simp only [hterm, ← Finset.mul_sum]
  rw [Wvec_of_vanishing_on_face g h x i hx0 htan hinv]

/-- **The slope of the Gibbons–Hawking–York density is minus the Palatini flux**, at a point of a face on
which the perturbation vanishes. -/
theorem ghySlope_eq_neg_ehFlux (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) (hx0 : h x = 0) (htan : ∀ σ a b, σ ≠ i → pd σ (fun z => h z a b) x = 0)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (hii : (g x)⁻¹ i i ≠ 0) :
    -2 * √|(g x).det| * ∑ α, ∑ β, faceHup g i x α β * dChristoffel g h i α β x = -ehFlux g h i x := by
  rw [sum_faceHup_dChristoffel g h x i hx0 htan hinv hii]
  unfold ehFlux
  ring

end Lightlike

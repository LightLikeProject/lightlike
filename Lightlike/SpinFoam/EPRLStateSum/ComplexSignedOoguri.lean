import Lightlike.SpinFoam.EPRLStateSum.ComplexOoguriShape

/-!
# The EPRL (γ = 1) tetrahedron-label sum as an Ooguri sum with the sign of the link orientations

`complex_tetSum_labels_ooguri` writes the tetrahedron-label sum of the glued intrinsic EPRL vertex weights as a
sum over virtual spins `L` of `Π_t [triangle constraints] · (Π_s (-1)^(triPart J_s)) · Π_s simpW (extL K col L) s`.
The sign `Π_s (-1)^(triPart J_s)` does not depend on `L`: it is `linkSign K col`, a function of the colouring only.
So the intrinsic EPRL amplitude at `γ = 1` is the Ooguri amplitude of the coloured complex `(col, L)` with the sign
`linkSign K col` per colouring (`complex_tetSum_labels_ooguri_explicit`).
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- **The sign of the link orientations** of a colouring: `(-1)^(Σ_s triPart J_s)`, a function of the colouring
only (not of the virtual spins of the tetrahedra). -/
noncomputable def linkSign (K : Complex4 V) (col : Finset V → ℕ) : ℝ :=
  (-1 : ℝ) ^ (∑ s : K.simps, triPart (complexJ K col s))

/-- `linkSign` is the product of the signs `(-1)^(triPart J_s)` of the 4-simplices. -/
theorem linkSign_eq_prod (K : Complex4 V) (col : Finset V → ℕ) :
    linkSign K col = ∏ s : K.simps, (-1 : ℝ) ^ triPart (complexJ K col s) := by
  unfold linkSign
  rw [Finset.prod_pow_eq_pow_sum]

/-- **The tetrahedron-label sum of the EPRL weight at `γ = 1` with the explicit sign**: the right-hand side is the
Ooguri vertex factor of the coloured complex `(col, L)` times the sign `linkSign K col`. -/
theorem complex_tetSum_labels_ooguri_explicit (K : Complex4 V) (col : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    ∑ i ∈ Fintype.piFinset (fun t : K.tets =>
        range (complexJ K col (e (t, false)).1 (e (t, false)).2
          ((e (t, false)).2.succAbove 0) +
          complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1) + 1)),
      tetSumTerm K col i =
    ∑ L ∈ Fintype.piFinset (fun t : K.tets =>
        simpBox (complexJ K col (e (t, false)).1) (e (t, false)).2 ∩
          simpBox (complexJ K col (e (t, true)).1) (e (t, true)).2),
      (∏ t : K.tets, if
            Lightlike.Pentagon.Tri
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
              (L t) ∧
            Lightlike.Pentagon.Tri (L t)
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
          then (1 : ℝ) else 0) *
        (linkSign K col * ∏ s : K.simps, simpW (extL K col L) s.1) := by
  rw [complex_tetSum_labels_ooguri K col e he]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [linkSign_eq_prod]

end Lightlike.SpinFoam.EPRLStateSum

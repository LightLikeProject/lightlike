import Lightlike.SpinFoam.EPRLStateSum.ComplexLegs
import Lightlike.SpinFoam.EPRLStateSum.SimplexBox

/-!
# The sum over tetrahedron labels of the intrinsic EPRL weight on a closed complex

`tetSumTerm K col i` is the product over the 4-simplices `s` of `K` of the intrinsic vertex sum
`simpEIAux (complexJ K col s)` with the tetrahedron labels `i : K.tets → ℕ` at the five tetrahedra
of `s`. `complex_tetSum` is `global_gluing_nodeI` for `K` with the incidences `incTet`, the
bijection `e` of `exists_complex_incidence` and `J = complexJ K col`: the sum over `i` of
`tetSumTerm` is the sum over the global virtual spins `l` with the gluing constraints at each
tetrahedron and the Ooguri-type vertex weights `vertexF`.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The product over the 4-simplices of the intrinsic vertex sums, with the tetrahedron labels
`i : K.tets → ℕ` at the tetrahedra `incTet K (s, a)`. -/
noncomputable def tetSumTerm (K : Complex4 V) (col : Finset V → ℕ) (i : K.tets → ℕ) : ℝ :=
  ∏ s : K.simps, simpEIAux (complexJ K col s) (fun a => i (incTet K (s, a)))

/-- **The tetrahedron-label sum on a complex with an incidence bijection.** -/
theorem complex_tetSum (K : Complex4 V) (col : Finset V → ℕ) (e : K.tets × Bool ≃ K.simps × Fin 5)
    (he : ∀ t b, incTet K (e (t, b)) = t) :
    ∑ i ∈ Fintype.piFinset (fun t : K.tets =>
        range (complexJ K col (e (t, false)).1 (e (t, false)).2
          ((e (t, false)).2.succAbove 0) +
          complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1) + 1)),
      tetSumTerm K col i =
    ∑ l ∈ Fintype.piFinset (fun s : K.simps => Fintype.piFinset (simpBox (complexJ K col s))),
      (∏ t : K.tets, if l (e (t, false)).1 (e (t, false)).2 = l (e (t, true)).1 (e (t, true)).2 ∧
            Lightlike.Pentagon.Tri
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
              (l (e (t, false)).1 (e (t, false)).2) ∧
            Lightlike.Pentagon.Tri (l (e (t, false)).1 (e (t, false)).2)
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
          then (1 : ℝ) else 0) *
        ∏ s : K.simps, vertexF (complexJ K col s) (l s) := by
  classical
  unfold tetSumTerm
  simp only [simpEIAux_eq_sum_box]
  exact global_gluing_nodeI (fun s a => incTet K (s, a)) e he (complexJ K col)
    (fun s => Fintype.piFinset (simpBox (complexJ K col s)))
    (fun s l => vertexF (complexJ K col s) l) (complex_hleg K col e he)

end Lightlike.SpinFoam.EPRLStateSum

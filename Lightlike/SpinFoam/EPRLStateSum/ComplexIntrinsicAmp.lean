import Lightlike.SpinFoam.EPRLStateSum.ComplexSignedOoguri

/-!
# The intrinsic EPRL amplitude at `γ = 1` as an Ooguri sum with the sign of the link orientations

For a closed 4-complex `K` with an incidence bijection `e`, the intrinsic EPRL amplitude (the sum over the triangle
colourings of `Π_f (col f + 1)` times the tetrahedron-label sum of the products of the intrinsic vertex sums
`tetSumTerm`) equals the sum over the triangle colourings and the virtual spins `L` of the tetrahedra of the Ooguri
weight of the coloured complex `(col, L)`, times the triangle constraints and the sign `linkSign K col` of the
link orientations, which depends on the colouring only (`complex_tetSum_labels_ooguri_explicit`).
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- **The intrinsic EPRL amplitude at `γ = 1`** on a complex with an incidence bijection `e`: the sum over the
triangle colourings (colour `≤ cut f`) of `Π_f (col f + 1)` times the sum over the tetrahedron labels in their
boxes of `tetSumTerm`. -/
noncomputable def eprlIntrinsicAmp (K : Complex4 V) (cut : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) : ℝ :=
  ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
    (∏ f ∈ K.tris, ((Lightlike.PR.extS K.tris c f : ℝ) + 1)) *
      ∑ i ∈ Fintype.piFinset (fun t : K.tets =>
          range (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
            ((e (t, false)).2.succAbove 0) +
            complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 1) + 1)),
        tetSumTerm K (Lightlike.PR.extS K.tris c) i

/-- A triangle of the complex is not a tetrahedron, so `extL` keeps its colour. -/
lemma extL_of_mem_tris (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ) {f : Finset V} (hf : f ∈ K.tris) :
    extL K col L f = col f := by
  have h3 := Complex4.card_of_mem_faces hf
  have hn : f ∉ K.tets := fun h => by
    have h4 := Complex4.card_of_mem_faces h
    omega
  simp [extL, hn]

/-- **The intrinsic EPRL amplitude at `γ = 1` is an Ooguri sum with the sign of the link orientations**: the sum over
the triangle colourings `col` and the virtual spins `L` of the tetrahedra (in the boxes of the incidence) of the
triangle constraints times the sign `linkSign K col` times the Ooguri weight of the coloured complex `(col, L)`. -/
theorem eprlIntrinsicAmp_eq_signed_ooguri (K : Complex4 V) (cut : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    eprlIntrinsicAmp K cut e =
      ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
        ∑ L ∈ Fintype.piFinset (fun t : K.tets =>
            simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1) (e (t, false)).2 ∩
              simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, true)).1) (e (t, true)).2),
          (∏ t : K.tets, if
              Lightlike.Pentagon.Tri
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 0))
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 2))
                (L t) ∧
              Lightlike.Pentagon.Tri (L t)
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 1))
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 3))
            then (1 : ℝ) else 0) *
            (linkSign K (Lightlike.PR.extS K.tris c) *
              Lightlike.SpinFoam.weight K (extL K (Lightlike.PR.extS K.tris c) L)) := by
  unfold eprlIntrinsicAmp
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [complex_tetSum_labels_ooguri_explicit K (Lightlike.PR.extS K.tris c) e he, Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  have hw : Lightlike.SpinFoam.weight K (extL K (Lightlike.PR.extS K.tris c) L) =
      (∏ f ∈ K.tris, ((Lightlike.PR.extS K.tris c f : ℝ) + 1)) *
        ∏ s : K.simps, simpW (extL K (Lightlike.PR.extS K.tris c) L) s.1 := by
    unfold Lightlike.SpinFoam.weight
    rw [Finset.prod_coe_sort K.simps (fun s => simpW (extL K (Lightlike.PR.extS K.tris c) L) s)]
    congr 1
    exact Finset.prod_congr rfl fun f hf => by rw [extL_of_mem_tris K _ L hf]
  rw [hw]
  ring

end Lightlike.SpinFoam.EPRLStateSum

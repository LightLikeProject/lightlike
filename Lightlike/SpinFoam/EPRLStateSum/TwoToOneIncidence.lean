import Lightlike.SpinFoam.EPRLStateSum.GlobalGluing

/-!
# A two-to-one map is an incidence bijection

`exists_incidence_equiv`: if every fibre of `f : X → T` has two elements, there is a bijection
`e : T × Bool ≃ X` with `f (e (t, b)) = t`. For a closed 4-complex, `X` is the set of pairs
(4-simplex, omitted vertex position) and `f` sends it to the tetrahedron: this is the incidence
bijection `e` of `global_gluing_nodeI`.
-/

namespace Lightlike.SpinFoam.EPRLStateSum

/-- **Incidence bijection from a two-to-one map.** -/
theorem exists_incidence_equiv {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T] (f : X → T)
    (h : ∀ t, Fintype.card {x // f x = t} = 2) :
    ∃ e : T × Bool ≃ X, ∀ t b, f (e (t, b)) = t := by
  let g : ∀ t, {x // f x = t} ≃ Bool := fun t => Fintype.equivOfCardEq (by simp [h t])
  refine ⟨((Equiv.sigmaEquivProd T Bool).symm.trans
    (Equiv.sigmaCongrRight fun t => (g t).symm)).trans (Equiv.sigmaFiberEquiv f), fun t b => ?_⟩
  exact ((g t).symm b).2

end Lightlike.SpinFoam.EPRLStateSum

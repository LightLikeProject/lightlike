import Lightlike.OperatorAlgebras.MomentumInterval

/-!
# The momentum operator on `L²(0, 1)` with `C_c^∞` test functions

`momentumGraphSmooth` is the graph of `-i d/dx` on the `C_c^∞(0, 1)` functions, the domain used in the
textbook statement of the deficiency indices of the momentum operator on an interval. The library's
`momentumMin` uses the larger class of `C²` functions supported inside `(0, 1)` (`testFunctions`), on which
the derivative is proved to give a class of `L²(0, 1)`. Here the smooth class is a submodule of it, the
graph is the image of that submodule under the same pair map, and so `momentumGraphSmooth ≤ momentumGraph`.
Task T-OP1-P6 (`Tasks/OP/T_OP1_P6.lean`) says that the two graphs have the same closure.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Lightlike.OperatorAlgebras

/-- The pair map `f ↦ (ψ, -i ψ')` on the `C²` test functions, as a linear map. -/
noncomputable def momentumPairLin : testFunctions →ₗ[ℂ] L2I × L2I where
  toFun := momentumPair
  map_add' := momentumPair_add
  map_smul' := fun c f => by simpa using momentumPair_smul c f

/-- The graph `momentumGraph` is the image of all test functions under `momentumPairLin`. -/
theorem momentumGraph_eq_map : momentumGraph = Submodule.map momentumPairLin ⊤ := rfl

/-- The `C_c^∞` functions supported inside `(0, 1)`, as a subspace of the `C²` test functions. -/
def smoothTestFunctions : Submodule ℂ testFunctions where
  carrier := {f | ContDiff ℝ ∞ f.1}
  add_mem' := fun {f g} hf hg => by
    have hf' : ContDiff ℝ ∞ f.1 := hf
    have hg' : ContDiff ℝ ∞ g.1 := hg
    exact show ContDiff ℝ ∞ (f.1 + g.1) from hf'.add hg'
  zero_mem' := show ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)) from contDiff_const
  smul_mem' := fun c f hf => by
    have hf' : ContDiff ℝ ∞ f.1 := hf
    exact show ContDiff ℝ ∞ (c • f.1) from hf'.const_smul c

/-- **The graph of `-i d/dx` on `C_c^∞(0, 1)`**, as a subspace of `L²(0, 1) × L²(0, 1)`. -/
noncomputable def momentumGraphSmooth : Submodule ℂ (L2I × L2I) :=
  Submodule.map momentumPairLin smoothTestFunctions

/-- The smooth graph is contained in the `C²` graph. -/
theorem momentumGraphSmooth_le : momentumGraphSmooth ≤ momentumGraph :=
  Submodule.map_mono le_top

end Lightlike.OperatorAlgebras

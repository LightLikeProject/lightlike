import Lightlike.Regge.Conv3.FlatStarIdentity
import Lightlike.Regge.Conv3.KuhnCore

/-!
# The vector of a hinge

`hvec σ h` is the vector from the first to the second vertex of the hinge `h` of the Kuhn tetrahedron `σ`; its class
is the edge direction `dirs k`.

## Main results

* `hvec`: the hinge vector.

**Limits.** Definition only.
-/

open Real
namespace Lightlike.Regge.Linear3
open Lightlike.Regge.Conv3

/-- The vector of the hinge of the incidence `(σ, h)`. -/
noncomputable def hvec (σ h : Fin 6) : Fin 3 → ℝ := fun i => kv (hQ h) (perms σ i) - kv (hP h) (perms σ i)

end Lightlike.Regge.Linear3

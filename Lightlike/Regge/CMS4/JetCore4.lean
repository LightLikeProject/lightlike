import Lightlike.Regge.Conv3.JetCore
import Lightlike.Regge.CMS4.Dihedral4Curve
import Lightlike.Regge.CMS4.Kuhn4Core

/-!
# The star of a triangle at a single metric jet, in dimension four

The squared length of an edge of the Kuhn triangulation of the 4-cube, at scale `ε` around a base
point `m`, is the jet polynomial `edgePoly` of the metric and its first two derivatives at `m`. By
`Conv3.edgePoly_smul` (generic in the dimension) it splits into `ε² q + ε³ c + ε⁴ r`. This file
sets up, for the 240 incidences (simplex, hinge) of a 4-cube, the matrices `q`, `c`, `r` of squared
lengths of the five vertices of the simplex, and states the jet-level star identity as a named
hypothesis `JetStarCore4`. It does not mention the Regge sum or its limit.

The hinges of the Kuhn triangulation are triangles `pqr`; a triangle of the triangulation of `ℝ⁴`
is a translate of one of the 50 triangles `0, w₁, w₁ + w₂` with `w₁, w₂ ∈ {0,1}⁴` nonzero and
disjoint supports. A *class* is encoded by `c : Fin 4 → Fin 3` (coordinate `i` belongs to `w₁`
if `c i = 1`, to `w₂` if `c i = 2`).

## Main results

* `incMat4`, `incQ4`, `incC4`, `incR4`, `incLen4`: the squared-length matrices of a simplex.
* `incLen4_eq`: `incLen4 = ε² (q + ε c + ε² r)`.
* `JetStarCore4`: the dimension-4 jet-level star identity (hypothesis structure).
-/

open Lightlike Real
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The matrix of squared lengths of the five vertices of the simplex `σ`, measured from the
centroid of the hinge `h`, obtained by applying `f s Δ` to the midpoint offset `s` and the edge
vector `Δ` of each pair of vertices. -/
noncomputable def incMat4 (f : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) (σ : Fin 24) (h : Fin 10) :
    Fin 5 → Fin 5 → ℝ := fun a b =>
  f (fun i => (kpos4 σ h a i + kpos4 σ h b i) / 2) (fun i => kpos4 σ h b i - kpos4 σ h a i)

/-- The Gram squared lengths of the incidence `(σ, h)` for the metric at `m`. -/
noncomputable def incQ4 (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) : Fin 5 → Fin 5 → ℝ :=
  incMat4 (fun _ Δ => edgeQ g m Δ) σ h

/-- The `ε³` coefficient of the squared lengths of the incidence `(σ, h)`. -/
noncomputable def incC4 (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) : Fin 5 → Fin 5 → ℝ :=
  incMat4 (fun s Δ => edgeC g m s Δ) σ h

/-- The `ε⁴` coefficient of the squared lengths of the incidence `(σ, h)`. -/
noncomputable def incR4 (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) : Fin 5 → Fin 5 → ℝ :=
  incMat4 (fun s Δ => edgeR g m s Δ) σ h

/-- The squared lengths of the incidence `(σ, h)` at scale `ε`: the edge polynomial of the metric
jet at `m` on the vertices `ε • kpos4`. -/
noncomputable def incLen4 (m : Fin 4 → ℝ) (ε : ℝ) (σ : Fin 24) (h : Fin 10) :
    Fin 5 → Fin 5 → ℝ :=
  incMat4 (fun s Δ => edgePoly g m (ε • s) (ε • Δ)) σ h

/-- The squared lengths at scale `ε` are `ε² (q + ε c + ε² r)`. -/
theorem incLen4_eq (m : Fin 4 → ℝ) (ε : ℝ) (σ : Fin 24) (h : Fin 10) :
    incLen4 g m ε σ h = ε ^ 2 • (incQ4 g m σ h + ε • incC4 g m σ h + ε ^ 2 • incR4 g m σ h) := by
  funext a b
  simp only [incLen4, incQ4, incC4, incR4, incMat4, edgePoly_smul, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  ring

/-- The edge vectors `(w₁, w₂)` of the triangle class `c : Fin 4 → Fin 3`. -/
def clsW1 (c : Fin 4 → Fin 3) : Fin 4 → ℝ := fun i => if c i = 1 then 1 else 0

/-- The second edge vector of the triangle class `c`. -/
def clsW2 (c : Fin 4 → Fin 3) : Fin 4 → ℝ := fun i => if c i = 2 then 1 else 0

/-- A class is admissible if both edge vectors are nonzero. -/
def ClsOK (c : Fin 4 → Fin 3) : Prop := (∃ i, c i = 1) ∧ ∃ i, c i = 2

instance : DecidablePred ClsOK := fun c => by unfold ClsOK; infer_instance

/-- The hinge of the incidence `(σ, h)` lies in the triangle class `c`: its edge vectors `pq` and
`qr` are `w₁` and `w₂`. -/
def InClass4 (c : Fin 4 → Fin 3) (σ : Fin 24) (h : Fin 10) : Prop :=
  (∀ i, kv4 (hQ h) (perms4 σ i) - kv4 (hP h) (perms4 σ i) = clsW1 c i) ∧
    ∀ i, kv4 (hR h) (perms4 σ i) - kv4 (hQ h) (perms4 σ i) = clsW2 c i

open Classical in
/-- The sum of `f σ h` over the incidences whose hinge lies in the class `c`. -/
noncomputable def clsSum4 (c : Fin 4 → Fin 3) (f : Fin 24 → Fin 10 → ℝ) : ℝ :=
  ∑ σ, ∑ h, if InClass4 c σ h then f σ h else 0

/-- The area of the triangle with edge vectors `w₁, w₂` for the metric `g m`. -/
noncomputable def triArea (m : Fin 4 → ℝ) (c : Fin 4 → Fin 3) : ℝ :=
  √(edgeQ g m (clsW1 c) * edgeQ g m (clsW2 c) - (clsW1 c ⬝ᵥ (g m *ᵥ clsW2 c)) ^ 2) / 2

/-- The dihedral angle of the incidence `(σ, h)` as a function of the matrix of squared lengths. -/
noncomputable def incAng4 (h : Fin 10) : (Fin 5 → Fin 5 → ℝ) → ℝ :=
  dihF (hP h) (hQ h) (hR h) (hS h) (hU h)

/-- The first-order coefficient of the dihedral angle of the incidence `(σ, h)`. -/
noncomputable def angC14 (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) : ℝ :=
  fderiv ℝ (incAng4 h) (incQ4 g m σ h) (incC4 g m σ h)

/-- The second-order coefficient of the dihedral angle of the incidence `(σ, h)`. -/
noncomputable def angC24 (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) : ℝ :=
  fderiv ℝ (incAng4 h) (incQ4 g m σ h) (incR4 g m σ h)
    + (1 / 2) * fderiv ℝ (fderiv ℝ (incAng4 h)) (incQ4 g m σ h) (incC4 g m σ h) (incC4 g m σ h)

/-- **The jet-level star identity in dimension 4 (named hypothesis).** For the metric `g` at the
point `m` (its value, first and second derivatives), with the star of each of the 50 triangle
classes of the Kuhn triangulation taken at scale `ε`:

* `valid`: the Gram squared lengths of every incidence are admissible (`Valid4`);
* `angle_sum`: the dihedral angles of the Gram star add up to `2π` in every admissible class;
* `first_order`: the `ε`-coefficient of the class angle sum vanishes;
* `curvature`: the hinge-area weighted `ε²`-coefficients, added over the classes, equal minus half
  the scalar curvature times `√det g`.

This is a statement about one jet. It does not mention a triangulation of a manifold or the limit
of the Regge sum. -/
structure JetStarCore4 (m : Fin 4 → ℝ) : Prop where
  /-- The Gram squared lengths are admissible. -/
  valid : ∀ σ h, Valid4 (hP h) (hQ h) (hR h) (hS h) (hU h) (incQ4 g m σ h)
  /-- The Gram star is flat: the dihedral angles in each class add up to `2π`. -/
  angle_sum : ∀ c, ClsOK c →
    clsSum4 c (fun σ h => incAng4 h (incQ4 g m σ h)) = 2 * π
  /-- The first-order coefficient of each class angle sum vanishes. -/
  first_order : ∀ c, ClsOK c → clsSum4 c (angC14 g m) = 0
  /-- The weighted second-order coefficients sum to `-(R/2) √det g`. -/
  curvature : ∑ c : Fin 4 → Fin 3, (if ClsOK c then triArea g m c * clsSum4 c (angC24 g m) else 0)
    = -(scalarCurvature g m / 2) * √((g m).det)

end Lightlike.Regge4

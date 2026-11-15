import Lightlike.Regge.Lorentzian.ReggeEquations
import Lightlike.Regge.Lorentzian.Embedded
import Lightlike.Regge.D4.FlatSolution

/-!
# Flat Minkowski space solves the Lorentzian Regge equations

The Lorentzian counterpart of `Lightlike/Regge/D4/FlatSolution.lean`. A geometric triangulation of a region
of Minkowski space (`IsGeometric4`, with the signed squared lengths `lorLen φ x`) whose triangles
and tetrahedra are not null has zero Lorentzian deficit angles at its interior triangles
(`Lightlike/Regge/Lorentzian/Embedded.lean`). Here we show that its 4-simplices are Lorentzian
(`gram4L < 0`), so that the Lorentzian Regge equations of `Lightlike/Regge/Lorentzian/ReggeEquations.lean`
apply, and conclude that the complex Lorentzian Regge action is stationary under every variation of
the squared lengths that keeps the boundary fixed. This is the Lorentzian form of the statement
that flat space solves Regge's equations (Sorkin, Phys. Rev. D 12 (1975) 385).

The sign of the 4-volume comes from the signature of the Minkowski form: `gram4L` is the Gram
determinant of the four edge vectors at a vertex (`gram4L_eq_det`, a Laplace expansion along the
first row, `det_gram4`), and that determinant is negative for linearly independent vectors
(`det_gram_neg`). Non-null triangles and tetrahedra are a hypothesis (`IsNonNull4`), because
Minkowski space contains null triangles and tetrahedra that a geometric triangulation may use.

## Main results

* `det_gram4`: the `4 × 4` Gram determinant of a bilinear form, expanded along the first row.
* `gram4L_eq_det`, `gram4L_neg_of_linIndep`: for a placement in Minkowski space, `gram4L` is the
  Gram determinant of the edge vectors, negative when they are linearly independent.
* `IsGeometric4.lorLengthsNondeg4`: the signed squared lengths of a geometric triangulation without
  null triangles and tetrahedra satisfy `LorLengthsNondeg4`.
* `IsGeometric4.lorReggeAction_stationary`: **flat Minkowski space solves the Lorentzian Regge
  equations.**
-/

open Real Finset Module Matrix

namespace Lightlike.ReggeLor

open Lightlike.FourD (Complex4)
open Lightlike.Regge4 (IsGeometric4 IsTriManifold bdryEdges4 intTris4 linIndep_of_affIndep5 lineL
  distinct_of_card_five det3)

section Gram

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Gram determinant of four vectors for a bilinear form `g`, expanded along the first row
into `3 × 3` minors. -/
theorem det_gram4 (g : LinearMap.BilinForm ℝ E) (A B C D : E) :
    (Matrix.of fun i j => g (![A, B, C, D] i) (![A, B, C, D] j)).det =
      g A A * det3 (g B B) (g B C) (g B D) (g C B) (g C C) (g C D) (g D B) (g D C) (g D D)
      - g A B * det3 (g B A) (g B C) (g B D) (g C A) (g C C) (g C D) (g D A) (g D C) (g D D)
      + g A C * det3 (g B A) (g B B) (g B D) (g C A) (g C B) (g C D) (g D A) (g D B) (g D D)
      - g A D * det3 (g B A) (g B B) (g B C) (g C A) (g C B) (g C C) (g D A) (g D B) (g D C) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, det3]
  ring

variable (φ : E ≃ₗ[ℝ] (Fin 4 → ℝ)) {V : Type*} [DecidableEq V]

/-- For the signed squared lengths of a placement `x` in Minkowski space, `gram4L` is the Gram
determinant of the edge vectors at `p` for the Minkowski form. -/
theorem gram4L_eq_det (x : V → E) {L : Finset V → ℝ}
    (hL : ∀ a b, a ≠ b → L {a, b} = minkG φ (x b - x a) (x b - x a)) (p q r s u : V) :
    gram4L L p q r s u =
      (Matrix.of fun i j => minkG φ (![x q - x p, x r - x p, x s - x p, x u - x p] i)
        (![x q - x p, x r - x p, x s - x p, x u - x p] j)).det := by
  rw [det_gram4, gram4L]
  simp only [ipL_eq_g (minkG_comm φ) x hL]

/-- **Lorentzian 4-simplices.** If the edge vectors at `p` of a placement in Minkowski space are
linearly independent, then `gram4L < 0`. -/
theorem gram4L_neg_of_linIndep (x : V → E) {L : Finset V → ℝ}
    (hL : ∀ a b, a ≠ b → L {a, b} = minkG φ (x b - x a) (x b - x a)) {p q r s u : V}
    (h : LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p, x u - x p]) :
    gram4L L p q r s u < 0 := by
  rw [gram4L_eq_det φ x hL]
  exact det_gram_neg φ h

end Gram

section Flat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (φ : E ≃ₗ[ℝ] (Fin 4 → ℝ))
  {V : Type*} [DecidableEq V]

/-- **Geometric triangulations of Minkowski space have Lorentzian 4-simplices**: if no triangle or
tetrahedron is null, the signed squared lengths of a geometric triangulation satisfy
`LorLengthsNondeg4`, so the Lorentzian Regge equations apply. -/
theorem IsGeometric4.lorLengthsNondeg4 {K : Complex4 V} {x : V → E} (hK : IsGeometric4 K x)
    (hN : IsNonNull4 K (lorLen φ x)) : LorLengthsNondeg4 K (lorLen φ x) := by
  refine ⟨hN.tri, hN.tet, fun p q r s u hσ => ?_⟩
  obtain ⟨hpq, hpr, hps, hpu, hqr, hqs, hqu, hrs, hru, hsu⟩ :=
    distinct_of_card_five (K.card_eq _ hσ)
  exact gram4L_neg_of_linIndep φ x (lorLen_eq φ x)
    (linIndep_of_affIndep5 x hpq hpr hps hpu hqr hqs hqu hrs hru hsu (hK.nondeg _ hσ))

/-- **Flat Minkowski space solves the Lorentzian Regge equations.** Let `K` satisfy the manifold
condition at triangles and let `x` be a geometric triangulation of a region of Minkowski space,
with inertial coordinates `φ`, the induced signed squared lengths and no null triangles or
tetrahedra. Then the complex Lorentzian Regge action is stationary under every variation of the
squared lengths that keeps the boundary lengths fixed. -/
theorem IsGeometric4.lorReggeAction_stationary {K : Complex4 V} {x : V → E}
    (hK : IsGeometric4 K x) (hM : IsTriManifold K) (hN : IsNonNull4 K (lorLen φ x))
    (v : Finset V → ℝ) (hv : ∀ e ∈ bdryEdges4 K, v e = 0) :
    HasDerivAt (fun τ => lorReggeAction K (lineL (lorLen φ x) v τ)) 0 0 :=
  (lorReggeAction_stationary_iff (IsGeometric4.lorLengthsNondeg4 φ hK hN)).mpr
    (fun _ _ => sum_eq_zero fun t ht => by
      rw [IsGeometric4.lorDeficit_eq_zero φ hK hM hN (mem_filter.mp ht).1, mul_zero]) v hv

end Flat

end Lightlike.ReggeLor

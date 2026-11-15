import Lightlike.SpinFoam.TwistedCohomologySU2

/-!
# Trust checks for the twisted cochain complex

* A disc (one loop edge, one face): `d1` is onto, `H² = 0`, whatever the connection.
* The 2-sphere (one loop edge, two faces glued along it) with the trivial connection:
  `d1` is not onto, so `H² ≠ 0`. This is the wrong-model side of the existence criterion.
* A non-flat connection (holonomy `2` around a face, acting by multiplication on `ℝ`) breaks
  `d1 ∘ d0 = 0`: the flatness hypothesis of `d1_comp_d0` is needed.
-/

namespace Lightlike.SpinFoam

/-- A disc: one vertex, one loop edge, one face bounded by the edge. -/
def disc : Cell2 Unit Unit Unit where
  src _ := ()
  tgt _ := ()
  bdry _ := [((), true)]

/-- The 2-sphere: one vertex, one loop edge, two faces bounded by the edge in opposite
directions. -/
def sphere : Cell2 Unit Unit Bool where
  src _ := ()
  tgt _ := ()
  bdry b := [((), b)]

/-- Multiplication by a unit on `ℝ`. -/
noncomputable def mulRep : Representation ℝ ℝˣ ℝ :=
  (Algebra.lsmul ℝ ℝ ℝ : ℝ →ₐ[ℝ] ℝ →ₗ[ℝ] ℝ).toMonoidHom.comp (Units.coeHom ℝ)

theorem disc_wellFormed : disc.WellFormed := fun _ => ⟨(), by simp [disc, Cell2.IsWalk, Cell2.startV, Cell2.endV]⟩

theorem sphere_wellFormed : sphere.WellFormed := fun b =>
  ⟨(), by simp [sphere, Cell2.IsWalk, Cell2.startV, Cell2.endV]⟩

/-- On the disc, `d1` is onto for every connection, so `H² = 0`. -/
theorem disc_d1_surjective (g : Unit → ℝˣ) : Function.Surjective (d1 mulRep disc g) := by
  intro y
  refine ⟨fun _ => y (), ?_⟩
  funext f
  simp [d1, disc, dword, lc, lh]

/-- On the sphere with the trivial connection (holonomy `1`, trivial representation), `d1` is not
onto: `(Φ, -Φ)` is all it reaches, so `H² ≠ 0`. -/
theorem sphere_d1_not_surjective :
    ¬ Function.Surjective (d1 (Representation.trivial ℝ Unit ℝ) sphere (fun _ => (1 : Unit))) := by
  intro h
  obtain ⟨Φ, hΦ⟩ := h (fun b => if b then 1 else 0)
  have h1 := congrFun hΦ true
  have h2 := congrFun hΦ false
  simp [d1, sphere, dword, lc, lh] at h1 h2
  linarith

/-- The non-flat connection with holonomy `2` on the loop: `d1 ∘ d0 ≠ 0`. -/
theorem disc_nonflat_d1_comp_d0_ne :
    d1 mulRep disc (fun _ => (Units.mk0 2 two_ne_zero)) ∘ₗ
      d0 mulRep disc (fun _ => (Units.mk0 2 two_ne_zero)) ≠ 0 := by
  intro h
  have := congrArg (fun L => L (fun _ => (1 : ℝ)) ()) h
  simp [d1, d0, disc, dword, lc, lh, mulRep] at this
  norm_num at this

open Matrix in
/-- A nonzero element of `su(2)`: `diag(i, -i)`. -/
def sigmaZ : su2 :=
  ⟨Matrix.diagonal ![Complex.I, -Complex.I], by
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    · simp [Matrix.trace, Fin.sum_univ_two]⟩

theorem sigmaZ_ne_zero : sigmaZ ≠ 0 := by
  intro h
  have := congrArg (fun X : su2 => (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  simp [sigmaZ] at this

/-- **Wrong-model side of the criterion, `SU(2)` version.** On the 2-sphere (two faces glued along
one loop edge) with the trivial `SU(2)` connection, which is flat, `d1` for the adjoint
representation is not onto, so `H²(sphere, Ad) ≠ 0` and the holonomy map has no surjective
differential. -/
theorem sphere_su2_not_surjective :
    ¬ Function.Surjective (d1 adRep sphere (fun _ => (1 : SU2))) := by
  intro h
  obtain ⟨Φ, hΦ⟩ := h (fun b => if b then sigmaZ else 0)
  have h1 := congrFun hΦ true
  have h2 := congrFun hΦ false
  simp [d1, sphere, dword, lc, lh] at h1 h2
  exact sigmaZ_ne_zero (h1.symm.trans h2)

theorem sphere_su2_flat : Flat sphere (fun _ => (1 : SU2)) := by
  intro f; simp [sphere, hol, lh]

/-- For the sphere with the trivial `SU(2)` holonomy, `H²` of the adjoint representation is not trivial. -/
theorem sphere_su2_H2_nontrivial : ¬ Subsingleton (H2 adRep sphere (fun _ => (1 : SU2))) :=
  fun h => sphere_su2_not_surjective ((d1_surjective_iff _ _ _).2 h)

/-- The trivial `SU(2)` connection on the disc is flat. -/
theorem disc_su2_flat : Flat disc (fun _ => (1 : SU2)) := by
  intro f; simp [disc, hol, lh]

/-- **Surjective side of the criterion, `SU(2)` version.** On the disc, `d1` for the adjoint
representation is onto for every `SU(2)` connection, so `H²(disc, Ad) = 0` at the trivial
connection, which is flat (`disc_su2_flat`), and every first-order change of the face holonomy
is realised. Together with `sphere_su2_not_surjective` this instantiates both sides of
`h2_trivial_iff_face_variation`. -/
theorem disc_su2_d1_surjective (g : Unit → SU2) : Function.Surjective (d1 adRep disc g) := by
  intro y
  refine ⟨fun _ => y (), ?_⟩
  funext f
  simp [d1, disc, dword, lc, lh]

/-- On the disc at the trivial connection every first-order change of the face holonomy is
realised by varying the edge holonomy: the surjective side of
`h2_trivial_iff_face_variation`, with the hypotheses met. -/
theorem disc_su2_face_variation (X : Unit → su2) :
    ∃ Φ : Unit → su2, ∀ f,
      HasDerivAt (hcurve (expCurve (fun _ => (1 : SU2)) Φ) (disc.bdry f))
        (X f : Matrix (Fin 2) (Fin 2) ℂ) 0 :=
  (h2_trivial_iff_face_variation disc disc_su2_flat).2.1 (disc_su2_d1_surjective _) X

end Lightlike.SpinFoam

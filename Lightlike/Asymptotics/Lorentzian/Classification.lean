import Lightlike.Asymptotics.Lorentzian.Critical
import Lightlike.Asymptotics.EPRL.GluingSolutions

/-!
# The `SU(2)` critical points of the Lorentzian action and the Euclidean gluing

The edge relation of the Lorentzian critical points for `SU(2)` group elements
(`su2_relation_iff`) is equality of two spin vectors. Written with the first columns of the
frames `X_a g_ab ε` and `X_b g_ba` of the Euclidean theory, it is exactly their gluing condition,
equality of Bloch vectors. The bridge is that the spin vector of the first column of a matrix is
its Bloch vector (`spinVec_col_eq_bloch`), and that `J` reverses the spin vector
(`spinVec_jMap`).
-/

open Complex
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Spin4 (bloch)
open Lightlike.Asymptotics.EPRL

/-- The first column of a `2 × 2` matrix, as a spinor. -/
noncomputable def firstCol (M : Matrix (Fin 2) (Fin 2) ℂ) : Spinor := !₂[M 0 0, M 1 0]

/-- The spin vector of the first column of a matrix is its Bloch vector. -/
theorem spinVec_firstCol (M : Matrix (Fin 2) (Fin 2) ℂ) : spinVec (firstCol M) = bloch M := by
  funext i
  fin_cases i <;>
    simp [spinVec, bloch, firstCol, Complex.normSq_eq_norm_sq]

/-- The first column of an `SU(2)` matrix is a unit spinor. -/
lemma norm_firstCol (M : SU2) : ‖firstCol (M : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
  have h := Lightlike.Spin4.normSq_col M
  simp only [Complex.normSq_eq_norm_sq] at h
  rw [EuclideanSpace.norm_eq]
  simp [firstCol, Fin.sum_univ_two, h]

/-- **The edge relation of the Euclidean gluing, as the Lorentzian relation.** For `SU(2)`
boundary data the edge `e` is glued at `X` (equal Bloch vectors of the frames) exactly when the
first column of `X_a g_ab` is a phase times `J` of the first column of `X_b g_ba`, that is
`A⁻¹ξ = c B⁻¹Jξ'` with `ξ = g_ab e₀`, `ξ' = g_ba e₀` and `J` commuting with `SU(2)`. -/
theorem glued_iff_phase {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧
        firstCol ((X (edgeSrc e) * (⟨g e 0, hg e 0⟩ : SU2) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
          c • jMap (firstCol (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [bloch_frameSrc]
  have h1 := norm_firstCol (X (edgeSrc e) * (⟨g e 0, hg e 0⟩ : SU2))
  have h2 : ‖jMap (firstCol (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 := by
    rw [norm_jMap, norm_firstCol]
  rw [phase_iff_spinVec_eq h2 h1]
  simp only [spinVec_firstCol, spinVec_jMap]
  simp only [Submonoid.coe_mul]
  constructor
  · intro h i
    have := congrFun h i
    simp only [Pi.neg_apply] at this
    linarith
  · intro h
    funext i
    have := h i
    simp only [Pi.neg_apply]
    linarith

/-- The `SU(2)` critical condition on all ten edges: `A⁻¹ξ = c B⁻¹Jξ'` with a unit phase `c`,
written with the first columns of the frames of the Euclidean theory. -/
def IsSU2Critical {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) : Prop :=
  ∀ e : Fin 10, ∃ c : ℂ, ‖c‖ = 1 ∧
    firstCol ((X (edgeSrc e) * (⟨g e 0, hg e 0⟩ : SU2) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      c • jMap (firstCol (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ))

/-- The critical points with `SU(2)` group elements are the gluing points of the Euclidean
theory: the frames of every edge have equal Bloch vectors. -/
theorem isSU2Critical_iff_glued {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) :
    IsSU2Critical hg X ↔ ∀ e, bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) :=
  forall_congr' fun e => (glued_iff_phase hg X e).symm

/-- **The two classes of `SU(2)` critical points.** Let the data be glued at `X = 1` and at
`X = Q`, with `Q₄, Q_a, Q_b` real independent for distinct `a, b ≠ 4` (the hypotheses of
`glued_iff_two_classes`, which carry the nondegeneracy). Then `X` is critical exactly when
`X_a = ±X₄` for every `a`, or `X_a = ±X₄ Q₄† Q_a` for every `a`. -/
theorem isSU2Critical_iff_two_classes {g : BdryData} (hg : IsSU2Data g) (Q : Fin 5 → SU2)
    (h1 : ∀ e, bloch (frameSrc hg 1 e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg 1 e : Matrix (Fin 2) (Fin 2) ℂ))
    (hQ : ∀ e, bloch (frameSrc hg Q e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg Q e : Matrix (Fin 2) (Fin 2) ℂ))
    (hind : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 →
      LinearIndependent ℝ ![(Q 4 : Matrix (Fin 2) (Fin 2) ℂ), Q a, Q b])
    (X : Fin 5 → SU2) :
    IsSU2Critical hg X ↔
      (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) = -(X 4 : Matrix (Fin 2) (Fin 2) ℂ)) ∨
        (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            (X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (Q 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Q a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (Q 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Q a)) :=
  (isSU2Critical_iff_glued hg X).trans (glued_iff_two_classes hg Q h1 hQ hind X)

/-- Non-vacuity: the twisted data have the critical point `X = 1`. -/
example (h : Fin 10 → SU2) : IsSU2Critical (isSU2Data_twistData h) (fun _ => 1) :=
  (isSU2Critical_iff_glued _ _).2 (twistData_glued h)

/-- Wrong-model control: with parallel instead of antiparallel normals (`g_ba = g_ab = 1`), `X = 1`
is not critical. -/
example : ¬ IsSU2Critical (g := fun _ => ![1, 1])
    (fun _ i => by fin_cases i <;> exact one_mem _) (fun _ => 1) := by
  intro h
  have := (isSU2Critical_iff_glued _ _).1 h 0
  have h3 := bloch_frameSrc (g := fun _ => ![1, 1])
    (fun _ i => by fin_cases i <;> exact one_mem _) (fun _ => 1) 0
  have h2 := congrFun (h3.symm.trans this) 2
  simp [frameTgt, bloch_one] at h2
  norm_num at h2

end Lightlike.Asymptotics.Lorentzian

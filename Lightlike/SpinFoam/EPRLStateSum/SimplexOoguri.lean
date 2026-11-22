import Lightlike.SpinFoam.EPRLStateSum.SimplexAmpP
import Lightlike.SpinFoam.EPRLStateSum.BFPoint

/-!
# The EPRL vertex at `γ = 1` in terms of the Ooguri vertex amplitudes

`simpE_one_eq_sum_ampP`: for a 4-simplex `s` whose boundary data are an SU(2) boundary
(`IsVertexBoundary (triSpins ..) 0 (tetLabels ..)`), the EPRL vertex `simpE 1 col s` is the
signed combination `Σ_l Π_a fourRecoupling(i_a, l_a) · recoupSign J l · ampP J l` of the Ooguri vertex
amplitudes of `SpinFoam/Vertex.lean`, where `J p q = col (s∖{s_p, s_q})` and `i_a = col (s∖{s_a})`
are the data from which `vertexAmp` builds `ampP`. The two vertices thus differ by a change of basis
of the tetrahedron labels, not by a factor.
-/

open Finset Lightlike.Recoupling Lightlike.Spin4 Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The triangle spins `J p q = col (s∖{s_p, s_q})` of a 4-simplex `s`, as in `vertexAmp`. -/
def simplexJ (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) : Fin 5 → Fin 5 → ℕ :=
  fun p q => col ((s.erase (s.orderEmbOfFin hs p)).erase (s.orderEmbOfFin hs q))

/-- `vertexAmp` is `ampP` of `simplexJ` and the tetrahedron labels. -/
theorem vertexAmp_eq_ampP (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) :
    vertexAmp s hs col = ampP (simplexJ s hs col) (fun i => col (s.erase (s.orderEmbOfFin hs i))) :=
  rfl

/-- **The EPRL vertex at `γ = 1` as a signed combination of Ooguri vertex amplitudes.** -/
theorem simpE_one_eq_sum_ampP {s : Finset V} (hs : #s = 5) (col : Finset V → ℕ)
    (hb : IsVertexBoundary (EPRL.triSpins s hs col) 0 (EPRL.tetLabels s hs col)) :
    EPRL.simpE 1 col s =
      ((∑ l₀ ∈ range (simplexJ s hs col 0 1 + simplexJ s hs col 0 3 + 1),
        ∑ l₁ ∈ range (simplexJ s hs col 1 2 + simplexJ s hs col 1 4 + 1),
        ∑ l₂ ∈ range (simplexJ s hs col 2 3 + simplexJ s hs col 0 2 + 1),
        ∑ l₃ ∈ range (simplexJ s hs col 3 4 + simplexJ s hs col 1 3 + 1),
        ∑ l₄ ∈ range (simplexJ s hs col 0 4 + simplexJ s hs col 2 4 + 1),
        fourRecoupling (simplexJ s hs col 0 1) (simplexJ s hs col 0 2) (simplexJ s hs col 0 3)
            (simplexJ s hs col 0 4) (EPRL.tetLabels s hs col 0) l₀ *
          fourRecoupling (simplexJ s hs col 1 2) (simplexJ s hs col 1 3) (simplexJ s hs col 1 4)
            (simplexJ s hs col 0 1) (EPRL.tetLabels s hs col 1) l₁ *
          fourRecoupling (simplexJ s hs col 2 3) (simplexJ s hs col 2 4) (simplexJ s hs col 0 2)
            (simplexJ s hs col 1 2) (EPRL.tetLabels s hs col 2) l₂ *
          fourRecoupling (simplexJ s hs col 3 4) (simplexJ s hs col 0 3) (simplexJ s hs col 1 3)
            (simplexJ s hs col 2 3) (EPRL.tetLabels s hs col 3) l₃ *
          fourRecoupling (simplexJ s hs col 0 4) (simplexJ s hs col 1 4) (simplexJ s hs col 2 4)
            (simplexJ s hs col 3 4) (EPRL.tetLabels s hs col 4) l₄ *
          (recoupSign (simplexJ s hs col) ![l₀, l₁, l₂, l₃, l₄] *
            ampP (simplexJ s hs col) ![l₀, l₁, l₂, l₃, l₄]) : ℝ) : ℂ) := by
  rw [EPRL.simpE_one hs col hb]
  exact congrArg _ (fifteenJSimplex_eq_sum_ampP (simplexJ s hs col) _ _ _ _ _)

end Lightlike.SpinFoam.EPRLStateSum

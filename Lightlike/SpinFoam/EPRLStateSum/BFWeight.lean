import Lightlike.SpinFoam.EPRLStateSum.SimplexOoguri

/-!
# The EPRL weight at `γ = 1`: Ooguri face factors times Ooguri-vertex combinations

`weightE_one_eq_prod_vertexCombo`: when every 4-simplex of `K` has SU(2) boundary data, the EPRL
weight at `γ = 1` is `Π_f (col f + 1)` (the Ooguri face amplitude `dim = 2j + 1` in doubled spins)
times, for each 4-simplex, the signed combination `vertexCombo` of Ooguri vertex amplitudes
`ampP` of `simpE_one_eq_sum_ampP`.

This is a per-vertex relation. It is not an equality of the two state sums: the change of basis
at a tetrahedron shared by two 4-simplices is not the same for both, so the vertex-wise bases do
not cancel (see `SimplexAmpP.lean`, `fifteenJSimplex_eq_sum_ampP`).
-/

open Finset Lightlike.Recoupling Lightlike.Spin4 Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The signed combination of Ooguri vertex amplitudes `ampP` that equals the EPRL vertex at
`γ = 1` (the right-hand side of `simpE_one_eq_sum_ampP`), `0` if `s` is not a 4-simplex. -/
noncomputable def vertexCombo (s : Finset V) (col : Finset V → ℕ) : ℂ :=
  if hs : #s = 5 then
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
            ampP (simplexJ s hs col) ![l₀, l₁, l₂, l₃, l₄]) : ℝ) : ℂ)
  else 0

/-- On a 4-simplex with SU(2) boundary data, `vertexCombo` is the EPRL vertex at `γ = 1`. -/
theorem simpE_one_eq_vertexCombo {s : Finset V} (hs : #s = 5) (col : Finset V → ℕ)
    (hb : IsVertexBoundary (EPRL.triSpins s hs col) 0 (EPRL.tetLabels s hs col)) :
    EPRL.simpE 1 col s = vertexCombo s col := by
  unfold vertexCombo
  rw [dite_eq_left hs]
  exact simpE_one_eq_sum_ampP hs col hb

/-- **The EPRL weight at `γ = 1`.** If every 4-simplex of `K` has SU(2) boundary data, then
`weightE 1 K col = Π_f (col f + 1) · Π_s vertexCombo s col`. -/
theorem weightE_one_eq_prod_vertexCombo (K : Complex4 V) (col : Finset V → ℕ)
    (hb : ∀ s ∈ K.simps, ∀ hs : #s = 5,
      IsVertexBoundary (EPRL.triSpins s hs col) 0 (EPRL.tetLabels s hs col)) :
    EPRL.weightE 1 K col =
      (∏ f ∈ K.tris, ((col f : ℂ) + 1)) * ∏ s ∈ K.simps, vertexCombo s col := by
  rw [EPRL.weightE_one]
  congr 1
  refine Finset.prod_congr rfl fun s hsK => ?_
  have hs := K.card_eq s hsK
  exact simpE_one_eq_vertexCombo hs col (hb s hsK hs)

end Lightlike.SpinFoam.EPRLStateSum

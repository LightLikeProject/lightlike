import Lightlike.SpinFoam.EPRLStateSum.BFWeight

/-!
# The EPRL vertex at `γ = 1` in the intrinsic (sorted) basis of the tetrahedra

`simpE_one_eq_sum_ampP` expands the vertex of `Lightlike/SpinFoam/EPRL.lean` with, at the node `a`, the recoupling
matrix of the tetrahedron legs *rotated* by `a mod 4` (`NodeBasis.lean`). Here the node matrix is
the one of the legs in their sorted order, the same for every simplex containing the tetrahedron:

* `nodeI J a i l = fourRecoupling (J a a₀) (J a a₁) (J a a₂) (J a a₃) i l`, where `a₀ < … < a₃` are the
  other four positions (`Fin.succAbove`);
* `simpEIAux J i` is the sum of `simpE_one_eq_sum_ampP` with `nodeI` in place of the positional
  matrices, `simpEI` its value on a vertex set;
* `nodeI_zero`, `nodeI_four`: at the nodes `0` and `4` the two conventions agree (rotation `0`);
* `simplexJ_symm`: the triangle spins `J p q` are symmetric.
-/

open Finset Lightlike.Recoupling Lightlike.Spin4 Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The intrinsic node matrix: the recoupling matrix of the tetrahedron `s∖{s_a}` whose legs are
taken in the sorted order of the omitted vertices. -/
noncomputable def nodeI (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (i l : ℕ) : ℝ :=
  fourRecoupling (J a (a.succAbove 0)) (J a (a.succAbove 1)) (J a (a.succAbove 2))
    (J a (a.succAbove 3)) i l

/-- The triangle spins of a 4-simplex are symmetric. -/
theorem simplexJ_symm (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) (p q : Fin 5) :
    simplexJ s hs col p q = simplexJ s hs col q p := by
  unfold simplexJ
  rw [Finset.erase_right_comm]

theorem nodeI_zero (J : Fin 5 → Fin 5 → ℕ) (i l : ℕ) :
    nodeI J 0 i l = fourRecoupling (J 0 1) (J 0 2) (J 0 3) (J 0 4) i l := rfl

/-- At the node `4` the intrinsic matrix is the positional one, for symmetric `J`. -/
theorem nodeI_four (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (i l : ℕ) :
    nodeI J 4 i l = fourRecoupling (J 0 4) (J 1 4) (J 2 4) (J 3 4) i l := by
  unfold nodeI
  rw [hJ 4 (Fin.succAbove 4 0), hJ 4 (Fin.succAbove 4 1), hJ 4 (Fin.succAbove 4 2),
    hJ 4 (Fin.succAbove 4 3)]
  rfl

/-- **The sign defect.** `recoupSign J K * ampP J K` is the pentagram 15j symbol with the sign
`(-1)^(K₀+…+K₄+J₁₂+J₁₄+J₃₄)` only: the `ampSign` of `ampP` cancels. So the EPRL vertex carries
`(-1)^{J₁₂+J₁₄+J₃₄} Π_a (-1)^{l_a}` where the Ooguri vertex `ampP` carries `ampSign J l`. -/
theorem recoupSign_mul_ampP (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) :
    recoupSign J K * ampP J K =
      (-1) ^ (K 0 + K 1 + K 2 + K 3 + K 4 + J 1 2 + J 1 4 + J 3 4) *
        fifteenJSimplex (J 0 2) (J 0 4) (J 0 1) (J 0 3) (J 2 4) (J 1 2) (J 2 3) (J 1 4)
          (J 3 4) (J 1 3) (K 0) (K 2) (K 4) (K 1) (K 3) := by
  have h := ampSign_mul_self J K
  unfold recoupSign
  rw [ampP_eq]
  linear_combination ((-1) ^ (K 0 + K 1 + K 2 + K 3 + K 4 + J 1 2 + J 1 4 + J 3 4) *
    fifteenJSimplex (J 0 2) (J 0 4) (J 0 1) (J 0 3) (J 2 4) (J 1 2) (J 2 3) (J 1 4)
      (J 3 4) (J 1 3) (K 0) (K 2) (K 4) (K 1) (K 3)) * h

/-- The triangle part of the exponent of `recoupSign`: `J₁₂+J₁₄+J₃₄+J₀₂+J₀₄+J₂₄`. It depends on the triangle spins
only (`recoupSign_eq`) and is the orientation sign of the ten links of the 4-simplex. -/
def triPart (J : Fin 5 → Fin 5 → ℕ) : ℕ := J 1 2 + J 1 4 + J 3 4 + J 0 2 + J 0 4 + J 2 4

/-- **The intrinsic vertex sum**: the Ooguri vertex amplitudes `ampP J l` (virtual spins `l` in the channel `(0 2 | 1 3)` of the
sorted legs of each tetrahedron) with the sign `(-1)^(triPart J)` of the link orientations, in the sorted basis of each
tetrahedron (the intrinsic matrices `nodeI`). The sorted label of a tetrahedron then labels the same basis vector from both
adjacent 4-simplices, so that the sum over the labels is the basis-free contraction. -/
noncomputable def simpEIAux (J : Fin 5 → Fin 5 → ℕ) (i : Fin 5 → ℕ) : ℝ :=
  ∑ l₀ ∈ range (J 0 1 + J 0 3 + 1), ∑ l₁ ∈ range (J 1 2 + J 1 4 + 1),
  ∑ l₂ ∈ range (J 2 3 + J 0 2 + 1), ∑ l₃ ∈ range (J 3 4 + J 1 3 + 1),
  ∑ l₄ ∈ range (J 0 4 + J 2 4 + 1),
    nodeI J 0 (i 0) l₀ * nodeI J 1 (i 1) l₁ * nodeI J 2 (i 2) l₂ * nodeI J 3 (i 3) l₃ *
      nodeI J 4 (i 4) l₄ *
    ((-1) ^ triPart J * ampP J ![l₀, l₁, l₂, l₃, l₄])

/-- **The intrinsic EPRL vertex at `γ = 1`**: `simpEIAux` of the triangle spins and the tetrahedron
labels of a 4-simplex, `0` if `s` is not a 4-simplex. -/
noncomputable def simpEI (col : Finset V → ℕ) (s : Finset V) : ℂ :=
  if hs : #s = 5 then (simpEIAux (simplexJ s hs col) (EPRL.tetLabels s hs col) : ℂ) else 0

theorem simpEI_of_card {s : Finset V} (hs : #s = 5) (col : Finset V → ℕ) :
    simpEI col s = (simpEIAux (simplexJ s hs col) (EPRL.tetLabels s hs col) : ℂ) := by
  unfold simpEI
  simp only [hs, dite_true]

theorem simpEI_of_card_ne {s : Finset V} (hs : #s ≠ 5) (col : Finset V → ℕ) :
    simpEI col s = 0 := by
  unfold simpEI
  simp only [hs, dite_false]

/-- On a 4-simplex, `vertexCombo` is `simpEIAux` with the positional matrices at the nodes `0` and
`4` replaced: the two agree at those nodes (`nodeI_zero`, `nodeI_four`). -/
theorem vertexCombo_eq_sum_nodeI {s : Finset V} (hs : #s = 5) (col : Finset V → ℕ) :
    vertexCombo s col =
      ((∑ l₀ ∈ range (simplexJ s hs col 0 1 + simplexJ s hs col 0 3 + 1),
        ∑ l₁ ∈ range (simplexJ s hs col 1 2 + simplexJ s hs col 1 4 + 1),
        ∑ l₂ ∈ range (simplexJ s hs col 2 3 + simplexJ s hs col 0 2 + 1),
        ∑ l₃ ∈ range (simplexJ s hs col 3 4 + simplexJ s hs col 1 3 + 1),
        ∑ l₄ ∈ range (simplexJ s hs col 0 4 + simplexJ s hs col 2 4 + 1),
        nodeI (simplexJ s hs col) 0 (EPRL.tetLabels s hs col 0) l₀ *
          fourRecoupling (simplexJ s hs col 1 2) (simplexJ s hs col 1 3) (simplexJ s hs col 1 4)
            (simplexJ s hs col 0 1) (EPRL.tetLabels s hs col 1) l₁ *
          fourRecoupling (simplexJ s hs col 2 3) (simplexJ s hs col 2 4) (simplexJ s hs col 0 2)
            (simplexJ s hs col 1 2) (EPRL.tetLabels s hs col 2) l₂ *
          fourRecoupling (simplexJ s hs col 3 4) (simplexJ s hs col 0 3) (simplexJ s hs col 1 3)
            (simplexJ s hs col 2 3) (EPRL.tetLabels s hs col 3) l₃ *
          nodeI (simplexJ s hs col) 4 (EPRL.tetLabels s hs col 4) l₄ *
          (recoupSign (simplexJ s hs col) ![l₀, l₁, l₂, l₃, l₄] *
            ampP (simplexJ s hs col) ![l₀, l₁, l₂, l₃, l₄]) : ℝ) : ℂ) := by
  unfold vertexCombo
  simp only [hs, dite_true]
  refine congrArg Complex.ofReal ?_
  refine Finset.sum_congr rfl fun l₀ _ => Finset.sum_congr rfl fun l₁ _ =>
    Finset.sum_congr rfl fun l₂ _ => Finset.sum_congr rfl fun l₃ _ =>
    Finset.sum_congr rfl fun l₄ _ => ?_
  rw [nodeI_zero, nodeI_four _ (simplexJ_symm s hs col)]

end Lightlike.SpinFoam.EPRLStateSum

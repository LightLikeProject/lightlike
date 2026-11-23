import Lightlike.SpinFoam.EPRLStateSum.SimplexGen
import Lightlike.SpinFoam.Vertex

/-!
# The recoupled 4-simplex contraction is a pentagram-relabelled 15j symbol

`fifteenJSimplex_recouple` (`SimplexGen.lean`) writes the 4-simplex contraction with the virtual
spins `i_a` in the channel `(a+1, a+2)(a+3, a+4)` as a combination of contractions whose five
intertwiners are in the channel `(a+1, a+3)(a+2, a+4)`. The theorem `simplexGen_swapped_eq` of this
file identifies each of those contractions, up to the sign `(-1)^(l₀+…+l₄+j₁₂+j₁₄+j₃₄)`, with the
`fifteenJSimplex` whose vertices and edges are relabelled by the pentagram permutation
`(0, 2, 4, 1, 3)`, which is the symbol that occurs in the closed form `ampP` of the vertex
amplitude of the Ooguri model (`SpinFoam/Vertex.lean`).

The proof is a change of the ten summation variables (a permutation of the product box, with three
reversed projections) and `fourJ_swapPairs` at each of the five vertices.
-/

open Finset Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

open Lightlike.Recoupling Lightlike.SpinFoam

/-- The change of the ten edge projections from the real labelling to the pentagram labelling:
`(m₀₁, m₀₂, m₀₃, m₀₄, m₁₂, m₁₃, m₁₄, m₂₃, m₂₄, m₃₄) ↦ (m₀₂, m₀₄, m₀₁, m₀₃, m₂₄, -m₁₂, m₂₃, -m₁₄,
-m₃₄, m₁₃)`; the three edges `12`, `14`, `34` reverse their orientation. -/
def pentaFwd (x : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :
    ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  (x.2.1, x.2.2.2.1, x.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, -x.2.2.2.2.1,
    x.2.2.2.2.2.2.2.1, -x.2.2.2.2.2.2.1, -x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1)

/-- The inverse of `pentaFwd`. -/
def pentaBwd (y : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :
    ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  (y.2.2.1, y.1, y.2.2.2.1, y.2.1, -y.2.2.2.2.2.1, y.2.2.2.2.2.2.2.2.2,
    -y.2.2.2.2.2.2.2.1, y.2.2.2.2.2.2.1, y.2.2.2.2.1, -y.2.2.2.2.2.2.2.2.1)

theorem pentaBwd_pentaFwd (x : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :
    pentaBwd (pentaFwd x) = x := by
  obtain ⟨a, b, c, d, e, f, g, h, i, k⟩ := x
  simp [pentaBwd, pentaFwd]

theorem pentaFwd_pentaBwd (y : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :
    pentaFwd (pentaBwd y) = y := by
  obtain ⟨a, b, c, d, e, f, g, h, i, k⟩ := y
  simp [pentaBwd, pentaFwd]

theorem pentaFwd_mem {j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ}
    {x : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ}
    (hx : x ∈ simplexBox j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄) :
    pentaFwd x ∈ simplexBox j₀₂ j₀₄ j₀₁ j₀₃ j₂₄ j₁₂ j₂₃ j₁₄ j₃₄ j₁₃ := by
  obtain ⟨a, b, c, d, e, f, g, h, i, k⟩ := x
  simp only [simplexBox, pentaFwd, mem_product, mem_Icc] at hx ⊢
  omega

theorem pentaBwd_mem {j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ}
    {y : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ}
    (hy : y ∈ simplexBox j₀₂ j₀₄ j₀₁ j₀₃ j₂₄ j₁₂ j₂₃ j₁₄ j₃₄ j₁₃) :
    pentaBwd y ∈ simplexBox j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  obtain ⟨a, b, c, d, e, f, g, h, i, k⟩ := y
  simp only [simplexBox, pentaBwd, mem_product, mem_Icc] at hy ⊢
  omega

/-- The recoupled contraction (intertwiners in the channel with the second and third legs
exchanged at every vertex) is, up to the sign `(-1)^(l₀+…+l₄+j₁₂+j₁₄+j₃₄)`, the `fifteenJSimplex`
with the pentagram labelling `(0, 2, 4, 1, 3)` of the vertices, as used in `ampP`. -/
theorem simplexGen_swapped_eq
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ l₀ l₁ l₂ l₃ l₄ : ℕ) :
    simplexGen (fun a b c d => fourJ j₀₁ j₀₃ j₀₂ j₀₄ l₀ a c b d)
          (fun a b c d => fourJ j₁₂ j₁₄ j₁₃ j₀₁ l₁ a c b d)
          (fun a b c d => fourJ j₂₃ j₀₂ j₂₄ j₁₂ l₂ a c b d)
          (fun a b c d => fourJ j₃₄ j₁₃ j₀₃ j₂₃ l₃ a c b d)
          (fun a b c d => fourJ j₀₄ j₂₄ j₁₄ j₃₄ l₄ a c b d)
          j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ =
      (-1) ^ (l₀ + l₁ + l₂ + l₃ + l₄ + j₁₂ + j₁₄ + j₃₄) *
        fifteenJSimplex j₀₂ j₀₄ j₀₁ j₀₃ j₂₄ j₁₂ j₂₃ j₁₄ j₃₄ j₁₃ l₀ l₂ l₄ l₁ l₃ := by
  rw [fifteenJSimplex_eq_simplexGen]
  unfold simplexGen
  have key : ∑ x ∈ simplexBox j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄,
      simplexTerm (fourJ j₀₂ j₀₄ j₀₁ j₀₃ l₀) (fourJ j₂₄ j₁₂ j₂₃ j₀₂ l₂) (fourJ j₁₄ j₃₄ j₀₄ j₂₄ l₄)
        (fourJ j₁₃ j₀₁ j₁₂ j₁₄ l₁) (fourJ j₀₃ j₂₃ j₃₄ j₁₃ l₃)
        j₀₂ j₀₄ j₀₁ j₀₃ j₂₄ j₁₂ j₂₃ j₁₄ j₃₄ j₁₃ (pentaFwd x) =
      ∑ y ∈ simplexBox j₀₂ j₀₄ j₀₁ j₀₃ j₂₄ j₁₂ j₂₃ j₁₄ j₃₄ j₁₃,
      simplexTerm (fourJ j₀₂ j₀₄ j₀₁ j₀₃ l₀) (fourJ j₂₄ j₁₂ j₂₃ j₀₂ l₂) (fourJ j₁₄ j₃₄ j₀₄ j₂₄ l₄)
        (fourJ j₁₃ j₀₁ j₁₂ j₁₄ l₁) (fourJ j₀₃ j₂₃ j₃₄ j₁₃ l₃)
        j₀₂ j₀₄ j₀₁ j₀₃ j₂₄ j₁₂ j₂₃ j₁₄ j₃₄ j₁₃ y :=
    Finset.sum_nbij' pentaFwd pentaBwd (fun x hx => pentaFwd_mem hx) (fun y hy => pentaBwd_mem hy)
      (fun x _ => pentaBwd_pentaFwd x) (fun y _ => pentaFwd_pentaBwd y) (fun _ _ => rfl)
  rw [← key, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  obtain ⟨a, b, c, d, e, f, g, h, i, k⟩ := x
  simp only [simplexTerm, pentaFwd, neg_neg]
  by_cases h12 : ((j₁₂ : ℤ) - e) % 2 = 0
  swap
  · have h' : ((j₁₂ : ℤ) - -e) % 2 ≠ 0 := by omega
    simp [fourJ_par₁ h12, fourJ_par₂ h']
  by_cases h14 : ((j₁₄ : ℤ) - g) % 2 = 0
  swap
  · have h' : ((j₁₄ : ℤ) - -g) % 2 ≠ 0 := by omega
    simp [fourJ_par₂ h14, fourJ_par₁ h']
  by_cases h34 : ((j₃₄ : ℤ) - k) % 2 = 0
  swap
  · have h' : ((j₃₄ : ℤ) - -k) % 2 ≠ 0 := by omega
    simp [fourJ_par₁ h34, fourJ_par₂ h']
  rw [edgeSign_neg h12, edgeSign_neg h14, edgeSign_neg h34,
    fourJ_swapPairs j₀₁ j₀₃ j₀₂ j₀₄ l₀ a c b d, fourJ_swapPairs j₁₂ j₁₄ j₁₃ j₀₁ l₁ e g f (-a),
    fourJ_swapPairs j₂₃ j₀₂ j₂₄ j₁₂ l₂ h (-b) i (-e),
    fourJ_swapPairs j₃₄ j₁₃ j₀₃ j₂₃ l₃ k (-f) (-c) (-h),
    fourJ_swapPairs j₀₄ j₂₄ j₁₄ j₃₄ l₄ (-d) (-i) (-g) (-k)]
  have hsq : ∀ n : ℕ, ((-1 : ℝ)) ^ (n * 2) = 1 := fun n => by
    rw [mul_comm, pow_mul]; norm_num
  simp only [pow_add]
  ring_nf
  simp only [hsq, mul_one]

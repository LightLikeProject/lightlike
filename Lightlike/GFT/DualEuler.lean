import Lightlike.GFT.Dual

/-!
# The Euler characteristic of the dual of a colored graph

The number `f_p` of `p`-simplices of the dual `Δ_G` of a colored graph is the number of pairs of a set of
`p + 1` colors and a bubble of the other colors (`dual_f`). In dimension `2` this gives `f₀ = B₀₁ + B₀₂ + B₁₂`,
`f₁ = 3 #V / 2` (each line has two ends, `two_mul_nBubbles_singleton`) and `f₂ = #V`, and so the Euler
characteristic `f₀ - f₁ + f₂` of the pseudo-complex `Δ_G` satisfies `2 χ = twoChi2 G` (`eulerChar_dual`;
Gurau 2010, Section 2, eq. (6) for the definition). The count `twoChi2` is thus twice the Euler characteristic
of the dual complex, not only a count of faces.

## Not proved here

That the geometric realization of the dual is a closed surface and that `χ` is even for a connected graph, so
that the genus `1 - χ / 2` is an integer.

## References

* R. Gurau, *Lost in translation: topological singularities in group field theory*, Class. Quantum
  Grav. 27 (2010) 235023, arXiv:1006.0714, Section 2, eq. (6).
-/

open Finset

namespace Lightlike.GFT

variable {D : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

variable {G : ColoredGraph D V}

/-- **The number of `p`-simplices of the dual**: the simplices of rank `p + 1` are the pairs of a set `S` of
`p + 1` colors and a bubble of the other colors, so `f_p = Σ_{#S = p + 1} #(bubbles of the colors outside S)`. -/
theorem dual_f (G : ColoredGraph D V) (p : ℕ) :
    (dual G).f p = ∑ S ∈ powersetCard (p + 1) (univ : Finset (Fin (D + 1))), G.nBubbles (univ \ S) := by
  let T : Finset (Σ _ : Finset (Fin (D + 1)), Finset V) :=
    (powersetCard (p + 1) (univ : Finset (Fin (D + 1)))).sigma
      (fun S => univ.image (G.bubble (univ \ S)))
  have hT : T.card = ∑ S ∈ powersetCard (p + 1) (univ : Finset (Fin (D + 1))),
      G.nBubbles (univ \ S) := by
    rw [card_sigma]
    rfl
  rw [← hT, GradedPoset.f]
  have e : {σ : DualSimplex G // (dual G).rk σ = p + 1} ≃ {x // x ∈ T} :=
    { toFun := fun σ => ⟨⟨σ.1.colors, σ.1.bub⟩, by
        obtain ⟨v, hv⟩ := σ.1.bub_eq
        have h := σ.2
        simp only [T, mem_sigma, mem_powersetCard, subset_univ, true_and, mem_image, mem_univ]
        exact ⟨h, v, hv.symm⟩⟩
      invFun := fun x => ⟨⟨(x.1.1, x.1.2), by
        have h := x.2
        simp only [T, mem_sigma, mem_powersetCard, subset_univ, true_and, mem_image, mem_univ] at h
        obtain ⟨-, v, hv⟩ := h
        exact ⟨v, hv.symm⟩⟩, by
          have h := x.2
          simp only [T, mem_sigma, mem_powersetCard, subset_univ, true_and, mem_image,
            mem_univ] at h
          exact h.1⟩
      left_inv := fun σ => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e]
  simp

/-- **Two vertices per line**: the lines of one color pair up the vertices, so there are `#V / 2` of them. -/
theorem two_mul_nBubbles_singleton (G : ColoredGraph D V) (c : Fin (D + 1)) :
    2 * G.nBubbles {c} = Fintype.card V := by
  unfold nBubbles
  have h : ∀ B ∈ univ.image (G.bubble {c}), #(univ.filter fun w => G.bubble {c} w = B) = 2 := by
    intro B hB
    obtain ⟨v, -, rfl⟩ := mem_image.1 hB
    have : (univ.filter fun w => G.bubble {c} w = G.bubble {c} v) = G.bubble {c} v := by
      ext w
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro h
        rw [← h]; exact mem_bubble_self G _ w
      · intro h
        exact bubble_eq_of_mem G _ h
    rw [this, card_bubble_singleton]
  rw [← card_univ (α := V), card_eq_sum_card_image (G.bubble {c}) univ, Finset.sum_const_nat h,
    mul_comm]

/-- The number of simplices of top dimension of the dual is the number of vertices. -/
theorem dual_f_top (G : ColoredGraph D V) : (dual G).f D = Fintype.card V := by
  have h : powersetCard (D + 1) (univ : Finset (Fin (D + 1))) = {univ} := by
    ext S
    simp only [mem_powersetCard, subset_univ, true_and, mem_singleton]
    constructor
    · intro hS
      exact eq_univ_of_card _ (by simpa using hS)
    · rintro rfl
      simp
  rw [dual_f, h, sum_singleton, sdiff_self]
  exact nBubbles_empty G

/-- **The Euler characteristic of the dual in dimension 2** (Gurau 2010, Section 2, eq. (6)): twice the Euler
characteristic `f₀ - f₁ + f₂` of the pseudo-complex `Δ_G` of a colored graph of dimension `2` is `twoChi2 G`,
the count `2 (B₀₁ + B₀₂ + B₁₂) - #V` from the faces: `f₀ = B₀₁ + B₀₂ + B₁₂`, `f₁ = 3 #V / 2` (two vertices per
line) and `f₂ = #V`. -/
theorem eulerChar_dual (G : ColoredGraph 2 V) : 2 * (dual G).eulerChar 3 = G.twoChi2 := by
  have h0 : (dual G).f 0 = G.nBubbles {1, 2} + G.nBubbles {0, 2} + G.nBubbles {0, 1} := by
    rw [dual_f]
    have : powersetCard (0 + 1) (univ : Finset (Fin (2 + 1))) = {{0}, {1}, {2}} := by decide
    rw [this, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have e0 : (univ : Finset (Fin 3)) \ {0} = {1, 2} := by decide
    have e1 : (univ : Finset (Fin 3)) \ {1} = {0, 2} := by decide
    have e2 : (univ : Finset (Fin 3)) \ {2} = {0, 1} := by decide
    rw [e0, e1, e2]
    omega
  have h1 : (dual G).f 1 = G.nBubbles {2} + G.nBubbles {1} + G.nBubbles {0} := by
    rw [dual_f]
    have : powersetCard (1 + 1) (univ : Finset (Fin (2 + 1))) = {{0, 1}, {0, 2}, {1, 2}} := by decide
    rw [this, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have e0 : (univ : Finset (Fin 3)) \ {0, 1} = {2} := by decide
    have e1 : (univ : Finset (Fin 3)) \ {0, 2} = {1} := by decide
    have e2 : (univ : Finset (Fin 3)) \ {1, 2} = {0} := by decide
    rw [e0, e1, e2]
    omega
  have h2 : (dual G).f 2 = Fintype.card V := dual_f_top G
  have t0 := G.two_mul_nBubbles_singleton 0
  have t1 := G.two_mul_nBubbles_singleton 1
  have t2 := G.two_mul_nBubbles_singleton 2
  unfold twoChi2
  unfold GradedPoset.eulerChar
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2]
  push_cast
  omega

end ColoredGraph

end Lightlike.GFT

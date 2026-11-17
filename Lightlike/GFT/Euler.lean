import Lightlike.GFT.Bubble

/-!
# The Euler characteristic of the dual of a colored graph in dimension 2 is an integer

For a colored graph of dimension `2` the dual has `twoChi2 G = 2 (B₀₁ + B₀₂ + B₁₂) - #V` as twice its
Euler characteristic (`ColoredGraph.twoChi2`). Since `2 (B₀₁ + B₀₂ + B₁₂)` is even and a colored graph has
an even number of vertices (`ColoredGraph.even_card`), `twoChi2` is even for every colored graph
(`even_twoChi2`), so the Euler characteristic `χ = twoChi2 / 2` is an integer (`euler`, `two_mul_euler`).
The sphere (two vertices) gives `χ = 2` and the torus (six vertices) gives `χ = 0`.

## Not proved here

That `χ` is even for a connected graph, so that the genus `1 - χ / 2` is an integer; that `χ ≤ 2` for a
connected graph; and that `χ` is the Euler characteristic of a closed surface built from the dual. These
are the genus statements of the ribbon-graph and crystallization theory, not of Gurau 2010, and need the
surface, not only the face count.
-/

open Finset

namespace Lightlike.GFT

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

/-- **Twice the Euler characteristic of the dual in dimension 2 is even**, for every colored graph:
`2 (B₀₁ + B₀₂ + B₁₂)` is even and `#V` is even (`even_card`), so the Euler characteristic
`twoChi2 / 2` of the dual is an integer. -/
theorem even_twoChi2 (G : ColoredGraph 2 V) : Even G.twoChi2 := by
  unfold twoChi2
  obtain ⟨r, hr⟩ := G.even_card
  refine ⟨(G.nBubbles {0, 1} : ℤ) + G.nBubbles {0, 2} + G.nBubbles {1, 2} - r, ?_⟩
  have : (Fintype.card V : ℤ) = r + r := by exact_mod_cast hr
  omega

/-- The Euler characteristic `χ = twoChi2 / 2` of the dual of a graph of dimension `2`: an integer
by `even_twoChi2`. -/
def euler (G : ColoredGraph 2 V) : ℤ := G.twoChi2 / 2

/-- `2 χ = twoChi2`, exact because `twoChi2` is even. -/
theorem two_mul_euler (G : ColoredGraph 2 V) : 2 * G.euler = G.twoChi2 := by
  obtain ⟨k, hk⟩ := G.even_twoChi2
  unfold euler
  rw [hk]
  omega

end ColoredGraph

/-- **Trust check**: the graph with two vertices has `χ = 2` (the sphere) and the graph with six
vertices has `χ = 0` (the torus); the sphere value is not the torus value. -/
example : theta.euler = 2 ∧ torus.euler = 0 ∧ theta.euler ≠ torus.euler := by decide +kernel

end Lightlike.GFT

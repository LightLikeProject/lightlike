import Lightlike.Spacetime.EHManifold.GHYDomain
import Lightlike.Spacetime.EHManifold.GraphAtlas

/-!
# The Einstein–Hilbert action with the Gibbons–Hawking–York term on a domain with regular boundary

`eh_ghy_variation_regular`: let `D ⊆ ℝⁿ⁺¹` be measurable and such that every point of its closure has a
neighbourhood `U` in which `D` is the region above or below the graph of a `C²` function, or all of `U`; in
the first two cases let the graph be nowhere null for `g` in `U` and let the perturbation `h` vanish on the
graph in `U` (that is: the boundary of `D` is nowhere null and `h` vanishes on it). Let `h` have support in
the compact set `T`. Then there is a finite atlas of such graph charts with a smooth partition of unity
`ρ_a` such that

`d/dt|₀ [∫_{D ∩ T} √|g_t| (R(g_t) - 2Λ) - ∑_a σ_a ∫ ρ_a 2 √|h_t| K_t dy] = -∫_{D ∩ T} √|g| h_{ab} E^{ab}`.

The sum over the charts is the Gibbons–Hawking–York term `∫_{∂D} 2 √|h| K` of the boundary of `D`, in graph
charts with the partition of unity. With `exists_graphRegion_of_defining_function` the local graph
descriptions come from defining functions of the boundary.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1) to (4.4), p. 20.
-/

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

variable (g h : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)

include hg hh hgs hhs hdet in
/-- **The Einstein–Hilbert action with the Gibbons–Hawking–York term on a domain with regular, nowhere null
boundary**: for a perturbation with compact support that vanishes on the boundary, only the bulk variation
remains. -/
theorem eh_ghy_variation_regular (D : Set (Fin (n + 1) → ℝ)) (hD : MeasurableSet D) (Λ : ℝ)
    {T : Set (Fin (n + 1) → ℝ)} (hT : IsCompact T) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T)
    (hloc : ∀ x ∈ closure D, ∃ U ∈ 𝓝 x, ∃ (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)),
      ContDiff ℝ 2 γ ∧ (∀ y ∈ U, (y ∈ D ↔ y ∈ graphRegion σ γ i)) ∧
      (σ ≠ 0 → ∀ y, graphPt γ i y ∈ U →
        (∑ c, graphConormal γ i y c * ∑ b, (g (graphPt γ i y))⁻¹ c b * graphConormal γ i y b) ≠ 0 ∧
          h (graphPt γ i y) = 0)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ x ∈ closure D, ∀ᶠ y in 𝓝 x, y ∈ T → ∑ a, ρ a y = 1) ∧
      HasDerivAt (fun t : ℝ =>
          (∫ x in T, lagDensity g h Λ t x ∂(volume.restrict D)) -
            ∑ a, (σ a : ℝ) * ∫ y in (fun x : Fin (n + 1) → ℝ => (i a).removeNth x) '' T,
              ρ a (graphPt (γ a) (i a) y) * ghyGraph (fun z => g z + t • h z) (γ a) (i a) y)
        (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β
          ∂(volume.restrict D)) 0 := by
  obtain ⟨ι, hι, ρ, σ, γ, i, U, hρ, hρ0, hγ, hUo, hρU, hUD, hQ, hsum⟩ :=
    exists_graph_atlas D T hT
      (fun U σ γ i => σ ≠ 0 → ∀ y, graphPt γ i y ∈ U →
        (∑ c, graphConormal γ i y c * ∑ b, (g (graphPt γ i y))⁻¹ c b * graphConormal γ i y b) ≠ 0 ∧
          h (graphPt γ i y) = 0)
      (fun U U' σ γ i hUU hq hσ y hy => hq hσ y (hUU hy)) hloc
  refine ⟨ι, hι, ρ, σ, γ, i, hρ, hρ0, hγ, fun a x hx => hUD a x (hρU a hx), hsum, ?_⟩
  refine eh_ghy_variation_cover g h hg hh hgs hhs hdet D hD Λ hT hsupp ρ
    (fun a => (hρ a).of_le (by simp)) σ γ hγ i (fun a x hx => hUD a x (hρU a hx)) ?_ ?_ ?_
    (fun a => (fun x : Fin (n + 1) → ℝ => (i a).removeNth x) '' T) ?_ ?_
  · intro x hx
    filter_upwards [hsum x (subset_closure hx)] with y hy
    by_cases hyT : y ∈ T
    · exact Or.inl (hy hyT)
    · exact Or.inr hyT
  · intro a hσ y hy
    have hopen : (fun y => graphPt (γ a) (i a) y) ⁻¹' U a ∈ 𝓝 y :=
      ((hUo a).preimage (continuous_graphPt (γ a) (hγ a).continuous (i a))).mem_nhds (hρU a hy)
    filter_upwards [hopen] with y' hy'
    exact (hQ a hσ y' hy').2
  · intro a hσ y hy
    exact (hQ a hσ y (hρU a hy)).1
  · intro a
    exact hT.image (removeNthL (i a)).continuous
  · intro a y hy
    refine ⟨graphPt (γ a) (i a) y, hy, ?_⟩
    show (i a).removeNth (Fin.insertNth (α := fun _ => ℝ) (i a) (γ a y) y) = y
    simp

end Lightlike

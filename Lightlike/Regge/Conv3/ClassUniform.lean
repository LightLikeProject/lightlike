import Lightlike.Regge.Conv3.JetCore

/-!
# The class angle expansion, uniformly in a compact set of parameters

`class_sum_expansion` (`JetCore.lean`) expands the dihedral angle sum of one edge class of the Kuhn star
at scale `ε` around `2π`, with constants that depend on the base jet. The parametric version
`class_sum_expansion_uniform` takes the lengths `q`, `c`, `ρ` of the star as functions of a parameter in
a nonempty compact space `P` (for example the base point in a compact subset of the chart) and gives
constants `M` and `r` that do not depend on the parameter. This is what the sum over all hinges of a
fine grid needs.

## Main results

* `class_sum_expansion_uniform`: the `O(ε³)` expansion of the class angle sum with constants
  independent of `p ∈ P`.

**Limits.** The lengths must depend continuously on the parameter, be admissible for every
parameter, and satisfy the two class conditions (angle sum `2π`, vanishing first-order coefficient)
for every parameter; nothing is said about how to obtain them from a metric.
-/

open Real Matrix Lightlike Filter Topology
namespace Lightlike.Regge.Conv3

/-- **The class angle sum at scale `ε`, uniformly in a compact set of parameters.** Let `P` be a
nonempty compact space and `q c ρ : P → Fin 6 → Fin 6 → Fin 6 → ℝ` continuous in `p`, with admissible
base lengths `q p σ h` for all `p`, class angle sum `2π` and vanishing first-order coefficient for
every `p`. Then there are `M` and `r > 0`, independent of `p`, such that the class angle sum of the
star `ε² (q + ε c + ε² ρ)` is `2π + ε² c₂` up to `M ε³` for all `0 < ε ≤ r` and all `p`. -/
theorem class_sum_expansion_uniform {P : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
    (w : Fin 3 → ℝ) (q c ρ : P → Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hqc : ∀ σ h, Continuous fun p => q p σ h) (hcc : ∀ σ h, Continuous fun p => c p σ h)
    (hρc : ∀ σ h, Continuous fun p => ρ p σ h)
    (hv : ∀ p σ h, Valid (q p σ h))
    (hsum : ∀ p, clsSum w (fun σ h => Dsq (q p σ h)) = 2 * π)
    (hfirst : ∀ p, clsSum w (fun σ h => Dh (q p σ h, c p σ h)) = 0) :
    ∃ M r : ℝ, 0 < r ∧ ∀ p : P, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |clsSum w (fun σ h => Dsq (ε ^ 2 • (q p σ h + ε • c p σ h + ε ^ 2 • ρ p σ h))) - 2 * π
        - ε ^ 2 * clsSum w (fun σ h => Dh (q p σ h, ρ p σ h)
          + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) (q p σ h) (c p σ h) (c p σ h))| ≤ M * ε ^ 3 := by
  classical
  -- continuity on `P × (Fin 6 × Fin 6)`
  have hQ : Continuous fun x : P × (Fin 6 × Fin 6) => q x.1 x.2.1 x.2.2 :=
    continuous_prod_of_discrete_right.2 fun b => hqc b.1 b.2
  have hQ0 : Continuous fun x : P × (Fin 6 × Fin 6) => q x.1 x.2.1 x.2.2 0 :=
    (continuous_apply 0).comp hQ
  have hC : Continuous fun x : P × (Fin 6 × Fin 6) => ‖c x.1 x.2.1 x.2.2‖ + ‖ρ x.1 x.2.1 x.2.2‖ := by
    refine Continuous.add ?_ ?_
    · exact (continuous_prod_of_discrete_right.2 fun b => hcc b.1 b.2).norm
    · exact (continuous_prod_of_discrete_right.2 fun b => hρc b.1 b.2).norm
  set K : Set (Fin 6 → ℝ) := Set.range (fun x : P × (Fin 6 × Fin 6) => q x.1 x.2.1 x.2.2) with hKdef
  have hK : IsCompact K := isCompact_range hQ
  have hKV : ∀ L ∈ K, Valid L := by
    rintro _ ⟨x, rfl⟩; exact hv x.1 x.2.1 x.2.2
  obtain ⟨x0, -, hx0'⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := P × (Fin 6 × Fin 6)))
    hQ0.continuousOn
  have hx0 : ∀ x : P × (Fin 6 × Fin 6), q x0.1 x0.2.1 x0.2.2 0 ≤ q x.1 x.2.1 x.2.2 0 := fun x => hx0' (Set.mem_univ x)
  have ha : 0 < q x0.1 x0.2.1 x0.2.2 0 := (hv x0.1 x0.2.1 x0.2.2).1
  have hKa : ∀ L ∈ K, q x0.1 x0.2.1 x0.2.2 0 ≤ L 0 := by
    rintro _ ⟨x, rfl⟩; exact hx0 x
  obtain ⟨y0, -, hy0'⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := P × (Fin 6 × Fin 6)))
    hC.continuousOn
  have hy0 : ∀ x : P × (Fin 6 × Fin 6), ‖c x.1 x.2.1 x.2.2‖ + ‖ρ x.1 x.2.1 x.2.2‖ ≤
      ‖c y0.1 y0.2.1 y0.2.2‖ + ‖ρ y0.1 y0.2.1 y0.2.2‖ := fun x => hy0' (Set.mem_univ x)
  set B : ℝ := ‖c y0.1 y0.2.1 y0.2.2‖ + ‖ρ y0.1 y0.2.1 y0.2.2‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hBc : ∀ p σ h, ‖c p σ h‖ ≤ B := fun p σ h =>
    le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hy0 (p, (σ, h)))
  have hBρ : ∀ p σ h, ‖ρ p σ h‖ ≤ B := fun p σ h =>
    le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hy0 (p, (σ, h)))
  obtain ⟨M, r, hr, hexp⟩ := dihSq_scaled_expansion hK hKV ha hKa hB0
  refine ⟨36 * |M|, r, hr, fun p ε hε hεr => ?_⟩
  set A1 : Fin 6 → Fin 6 → ℝ := fun σ h => Dh (q p σ h, c p σ h) with hA1
  set A2 : Fin 6 → Fin 6 → ℝ := fun σ h => Dh (q p σ h, ρ p σ h)
    + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) (q p σ h) (c p σ h) (c p σ h) with hA2
  have hinc : ∀ σ h : Fin 6, |Dsq (ε ^ 2 • (q p σ h + ε • c p σ h + ε ^ 2 • ρ p σ h)) - Dsq (q p σ h)
      - ε * A1 σ h - ε ^ 2 * A2 σ h| ≤ |M| * ε ^ 3 := fun σ h =>
    (hexp (q p σ h) ⟨(p, (σ, h)), rfl⟩ (c p σ h) (ρ p σ h) (hBc p σ h) (hBρ p σ h) ε hε hεr).trans
      (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
  have h1 := hsum p
  have h2 : clsSum w A1 = 0 := hfirst p
  set err : Fin 6 → Fin 6 → ℝ := fun σ h =>
    Dsq (ε ^ 2 • (q p σ h + ε • c p σ h + ε ^ 2 • ρ p σ h)) - Dsq (q p σ h)
      - ε * A1 σ h - ε ^ 2 * A2 σ h with herr
  have hsplit : clsSum w (fun σ h => Dsq (ε ^ 2 • (q p σ h + ε • c p σ h + ε ^ 2 • ρ p σ h))) =
      clsSum w (fun σ h => Dsq (q p σ h)) + ε * clsSum w (A1)
        + ε ^ 2 * clsSum w (A2) + clsSum w err := by
    simp only [clsSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
    split_ifs
    · simp only [herr]; ring
    · simp
  have herrb : |clsSum w err| ≤ 36 * |M| * ε ^ 3 := by
    unfold clsSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ σ : Fin 6, |∑ h : Fin 6, (if InClass w σ h then err σ h else 0)|
        ≤ ∑ σ : Fin 6, ∑ h : Fin 6, |M| * ε ^ 3 :=
          Finset.sum_le_sum fun σ _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun h _ => by
              split_ifs
              · exact hinc σ h
              · simp; positivity)
      _ = 36 * |M| * ε ^ 3 := by simp; ring
  have : clsSum w (fun σ h => Dsq (ε ^ 2 • (q p σ h + ε • c p σ h + ε ^ 2 • ρ p σ h))) - 2 * π
      - ε ^ 2 * clsSum w (A2) = clsSum w err := by
    rw [hsplit, h1, h2]; ring
  rw [this]
  exact herrb

end Lightlike.Regge.Conv3

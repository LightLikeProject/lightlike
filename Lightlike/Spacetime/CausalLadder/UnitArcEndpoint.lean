import Lightlike.Spacetime.CausalLadder.BoundarylessChart

/-!
# A curve made of unit arcs of chart displacement bounded below has no future endpoint

Step of the proof of the limit-curve theorem (task `T-GE2-P20`, Hawking–Ellis Lemma 6.2.1): the curve glued from unit
arcs `[n, n + 1]`, each of chart displacement at least `ρ j` in the chart of the centre `c j` of the least `N j`
containing `σ n`, for a countable family of open sets `N j` covering the manifold, with `closure (N j)` in the chart
domain of `c j`, does not converge as the parameter tends to infinity. Only finitely many indices occur near a
putative endpoint, so the displacement is bounded below there, against the continuity of one chart at the endpoint.

Supporting lemma for the limit-curve theorem; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **A curve made of unit arcs of chart displacement bounded below has no future endpoint.** Let `(c j, ρ j, N j)`
be a countable family of open sets covering `M`, each with its closure in the chart domain of its centre, and `σ` a
curve on `[0, ∞)` such that the unit arc `[n, n + 1]` lies in the chart domain of `c j`, `j` the least index with
`σ n ∈ N j`, and has chart displacement at least `ρ j` there. If `σ t → q`, then `σ n` lies in the set `N j₀` that
contains `q` from some `n` on, so the index `j` is at most `j₀`: finitely many indices; one of them, `j*`, occurs for
infinitely many `n`, and for those `σ n` and `σ (n + 1)` converge to `q ∈ closure (N j*)`, in the chart domain of
`c j*`, so their chart images converge to the same point, against the displacement `≥ ρ j*`. -/
theorem not_tendsto_of_unit_arcs
    (c : ℕ → M) (ρ : ℕ → ℝ) (N : ℕ → Set M) (σ : ℝ → M) (hρ : ∀ j, 0 < ρ j)
    (hopen : ∀ j, IsOpen (N j)) (hcl : ∀ j, closure (N j) ⊆ (extChartAt I (c j)).source)
    (hcov : (⋃ j, N j) = univ)
    (harc : ∀ n : ℕ, ∃ j, σ n ∈ N j ∧ (∀ j', σ n ∈ N j' → j ≤ j') ∧
      (∀ u ∈ Icc (n : ℝ) (n + 1), σ u ∈ (extChartAt I (c j)).source) ∧
      ρ j ≤ ‖extChartAt I (c j) (σ (n + 1)) - extChartAt I (c j) (σ n)‖) (q : M) :
    ¬ Tendsto (fun t : Ici (0 : ℝ) => σ t) atTop (𝓝 q) := by
  intro hq
  -- the sequence of integer parameters
  have hn : Tendsto (fun n : ℕ => (⟨(n : ℝ), Set.mem_Ici.2 (Nat.cast_nonneg n)⟩ : Ici (0 : ℝ))) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    obtain ⟨m, hm⟩ := exists_nat_ge (b : ℝ)
    filter_upwards [eventually_ge_atTop m] with n hn
    show (b : ℝ) ≤ (n : ℝ)
    exact le_trans hm (by exact_mod_cast hn)
  have hσn : Tendsto (fun n : ℕ => σ (n : ℝ)) atTop (𝓝 q) := hq.comp hn
  have hσn1 : Tendsto (fun n : ℕ => σ ((n : ℝ) + 1)) atTop (𝓝 q) := by
    have := hσn.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp
  -- the index of the arc `n`
  choose j hj1 hj2 hj3 hj4 using harc
  -- `q` lies in some `N j₀`
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, q ∈ N j₀ := by
    have : q ∈ ⋃ j, N j := by rw [hcov]; exact mem_univ q
    simpa using this
  have hev : ∀ᶠ n : ℕ in atTop, σ (n : ℝ) ∈ N j₀ := hσn.eventually ((hopen j₀).mem_nhds hj₀)
  -- so the indices are at most `j₀` from some `n` on
  have hle : ∀ᶠ n : ℕ in atTop, j n ≤ j₀ := hev.mono fun n hn => hj2 n j₀ hn
  -- one index occurs infinitely often
  obtain ⟨jstar, hjstar⟩ : ∃ jstar, ∃ᶠ n : ℕ in atTop, j n = jstar := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ jj : Fin (j₀ + 1), ∀ᶠ n : ℕ in atTop, j n ≠ (jj : ℕ) := fun jj => hcon jj
    obtain ⟨n, hn1, hn2⟩ := ((Filter.eventually_all.2 hall).and hle).exists
    exact hn1 ⟨j n, Nat.lt_succ_of_le hn2⟩ rfl
  -- `q` is in the closure of `N jstar`, hence in the chart domain of its centre
  have hfreq : ∃ᶠ n : ℕ in atTop, σ (n : ℝ) ∈ N jstar := hjstar.mono fun n hn => hn ▸ hj1 n
  have hqcl : q ∈ closure (N jstar) := mem_closure_iff_nhds.2 fun U hU => by
    obtain ⟨n, h1, h2⟩ := ((hσn.eventually hU).and_frequently hfreq).exists
    exact ⟨σ n, h1, h2⟩
  have hqsrc : q ∈ (extChartAt I (c jstar)).source := hcl jstar hqcl
  -- the chart images converge to the same point along the subsequence where the index is `jstar`
  have hc : ContinuousAt (extChartAt I (c jstar)) q := continuousAt_extChartAt' hqsrc
  have h1 : Tendsto (fun n : ℕ => extChartAt I (c jstar) (σ (n : ℝ))) atTop (𝓝 (extChartAt I (c jstar) q)) :=
    hc.tendsto.comp hσn
  have h2 : Tendsto (fun n : ℕ => extChartAt I (c jstar) (σ ((n : ℝ) + 1))) atTop
      (𝓝 (extChartAt I (c jstar) q)) := hc.tendsto.comp hσn1
  have h3 : Tendsto (fun n : ℕ => ‖extChartAt I (c jstar) (σ ((n : ℝ) + 1)) - extChartAt I (c jstar) (σ (n : ℝ))‖)
      atTop (𝓝 0) := by
    have := (h2.sub h1)
    rw [sub_self] at this
    simpa using this.norm
  have h4 : ∀ᶠ n : ℕ in atTop, ‖extChartAt I (c jstar) (σ ((n : ℝ) + 1)) - extChartAt I (c jstar) (σ (n : ℝ))‖ < ρ jstar :=
    h3.eventually (gt_mem_nhds (hρ jstar))
  obtain ⟨n, hn1, hn2⟩ := (hjstar.and_eventually h4).exists
  have := hj4 n
  rw [hn1] at this
  linarith

end Lightlike.Causal

import Lightlike.GR.KruskalRegions

/-!
# The event horizon of the Kruskal spacetime

Gap row G1-020. In the Kruskal chart `(T, X, θ, φ)` with the time orientation `∂_T`, a point **reaches the
infinity of region I** if a future-directed causal curve starts at it along which `r → ∞` with `X > 0` in the
end (`ReachesKruskalInfinity`). This is the coordinate form of "the point is in the causal past of future null
infinity `𝓘⁺` of region I": the conformal boundary itself is not formalized, so `J⁻(𝓘⁺)` is rendered as the set
of points from which a future causal curve escapes to `r = ∞` in the exterior `X > 0`.

* `reachesKruskalInfinity_iff`: a point reaches infinity iff `T < X`.
* `frontier_kruskal_past_of_infinity`: the boundary of that set is `T = X`, the **event horizon**
  (S. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, (7.83): "the event horizon `r = 2GM`
  ... is `v = ±u`"; the branch `T = X` is the future horizon of region I together with its past extension).
-/

open Matrix Real Set Filter Topology

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- A point of the Kruskal chart **reaches the infinity of region I**: a future-directed causal curve starts at
it along which `r → ∞`, with `X > 0` in the end. -/
def ReachesKruskalInfinity (y₀ : Fin 4 → ℝ) : Prop :=
  ∃ γ : ℝ → Fin 4 → ℝ, Differentiable ℝ γ ∧ (∀ t, γ t ∈ kruskalU) ∧
    (∀ t, IsKruskalFutureCausal M (γ t) (deriv γ t)) ∧ γ 0 = y₀ ∧
    Tendsto (fun t => kr M (γ t)) atTop atTop ∧ ∀ᶠ t in atTop, 0 < γ t 1

variable {M}

/-- If `kF R < s` then `R < kG s`. -/
lemma lt_kG_of_kF_lt (hM : 0 < M) {R s : ℝ} (hR : 0 ≤ R) (hs : -1 < s) (h : kF M R < s) : R < kG M s := by
  have h1 := (kF_strictMonoOn M hM).lt_iff_lt (mem_Ici.2 hR) (mem_Ici.2 (kG_pos M hM hs).le)
  rw [kF_kG M hM hs] at h1
  exact h1.1 h

/-- No point with `X ≤ T` reaches the infinity of region I. -/
theorem not_reachesKruskalInfinity (hM : 0 < M) {y₀ : Fin 4 → ℝ} (h : y₀ 1 ≤ y₀ 0) :
    ¬ ReachesKruskalInfinity M y₀ := by
  rintro ⟨γ, hγ, hU, hc, h0, hr, hX⟩
  have hmono := (monotone_add_sub_of_futureCausal hM hγ hU hc).2
  obtain ⟨t, ht0, htX, htr⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hX.and (hr.eventually (eventually_gt_atTop (2 * M))))).exists
  have h1 : γ 0 0 - γ 0 1 ≤ γ t 0 - γ t 1 := hmono ht0
  rw [h0] at h1
  have h2 := (two_mul_lt_kr_iff M hM (hU t)).1 htr
  nlinarith

/-- Every point with `T < X` reaches the infinity of region I, along an outgoing radial null curve. -/
theorem reachesKruskalInfinity_of_lt (hM : 0 < M) {y₀ : Fin 4 → ℝ} (hy : y₀ ∈ kruskalU)
    (h : y₀ 0 < y₀ 1) : ReachesKruskalInfinity M y₀ := by
  set a := y₀ 1 - y₀ 0 with ha
  have ha0 : 0 < a := by linarith
  have hs0 : -1 < a * (y₀ 0 + y₀ 1) := by
    have := hy.1
    nlinarith
  set δ := (a * (y₀ 0 + y₀ 1) + 1) / (4 * a) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
  have hδa : a * (2 * δ) = (a * (y₀ 0 + y₀ 1) + 1) / 2 := by
    rw [hδ]; field_simp; ring
  set γ : ℝ → Fin 4 → ℝ := fun t =>
    ![y₀ 0 + δ * (exp t - 1), y₀ 1 + δ * (exp t - 1), y₀ 2, y₀ 3] with hγdef
  have hsq : ∀ t, γ t 1 ^ 2 - γ t 0 ^ 2 = a * (y₀ 0 + y₀ 1 + 2 * δ * (exp t - 1)) := fun t => by
    simp only [hγdef, Matrix.cons_val_zero, Matrix.cons_val_one, ha]
    ring
  have hlow : ∀ t, -1 < γ t 1 ^ 2 - γ t 0 ^ 2 := fun t => by
    rw [hsq]
    have he : 0 < exp t := exp_pos t
    have : a * (y₀ 0 + y₀ 1 + 2 * δ * (exp t - 1)) =
        a * (y₀ 0 + y₀ 1) - a * (2 * δ) + a * (2 * δ) * exp t := by ring
    rw [this, hδa]
    have h3 : 0 < (a * (y₀ 0 + y₀ 1) + 1) / 2 * exp t := mul_pos (by linarith) he
    linarith
  have hd : ∀ t, HasDerivAt γ ![δ * exp t, δ * exp t, 0, 0] t := fun t => by
    rw [hasDerivAt_pi]
    intro i
    have he : HasDerivAt (fun t : ℝ => δ * (exp t - 1)) (δ * exp t) t :=
      ((Real.hasDerivAt_exp t).sub_const 1).const_mul δ
    fin_cases i
    · exact he.const_add (y₀ 0)
    · exact he.const_add (y₀ 1)
    · exact hasDerivAt_const t (y₀ 2)
    · exact hasDerivAt_const t (y₀ 3)
  have hU : ∀ t, γ t ∈ kruskalU := fun t => ⟨hlow t, hy.2.1, hy.2.2⟩
  have hexp : Tendsto (fun t : ℝ => δ * (exp t - 1)) atTop atTop :=
    Tendsto.const_mul_atTop hδ0 (tendsto_atTop_add_const_right _ _ tendsto_exp_atTop)
  refine ⟨γ, fun t => (hd t).differentiableAt, hU, fun t => ?_, ?_, ?_, ?_⟩
  · rw [(hd t).deriv]
    refine ⟨?_, by simpa using mul_pos hδ0 (exp_pos t)⟩
    rw [kruskalQuad_eq]
    simp
  · ext i
    fin_cases i <;> simp [hγdef]
  · rw [tendsto_atTop]
    intro R
    have hsT : Tendsto (fun t => γ t 1 ^ 2 - γ t 0 ^ 2) atTop atTop := by
      have h1 : Tendsto (fun t : ℝ => a * (y₀ 0 + y₀ 1 + 2 * (δ * (exp t - 1)))) atTop atTop :=
        Tendsto.const_mul_atTop ha0
          (tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop (by norm_num) hexp))
      refine h1.congr fun t => ?_
      rw [hsq]; ring
    filter_upwards [hsT.eventually (eventually_gt_atTop (kF M (max R 0)))] with t ht
    exact (le_max_left R 0).trans (lt_kG_of_kF_lt hM (le_max_right R 0) (hlow t) ht).le
  · have h1 : Tendsto (fun t => γ t 1) atTop atTop := by
      have : Tendsto (fun t : ℝ => y₀ 1 + δ * (exp t - 1)) atTop atTop :=
        tendsto_atTop_add_const_left _ _ hexp
      exact this
    exact h1.eventually (eventually_gt_atTop 0)

/-- **The causal past of the infinity of region I is `T < X`.** -/
theorem reachesKruskalInfinity_iff (hM : 0 < M) {y₀ : Fin 4 → ℝ} (hy : y₀ ∈ kruskalU) :
    ReachesKruskalInfinity M y₀ ↔ y₀ 0 < y₀ 1 :=
  ⟨fun h => by
    by_contra hcon
    exact not_reachesKruskalInfinity hM (not_lt.1 hcon) h,
   reachesKruskalInfinity_of_lt hM hy⟩

/-- **The event horizon**: the boundary of the half-space `T < X` (the causal past of the infinity of region I,
`reachesKruskalInfinity_iff`) is the hypersurface `T = X`. -/
theorem frontier_kruskal_past_of_infinity :
    frontier {y : Fin 4 → ℝ | y 0 < y 1} = {y | y 0 = y 1} := by
  have hopen : IsOpen {y : Fin 4 → ℝ | y 0 < y 1} :=
    isOpen_lt (continuous_apply 0) (continuous_apply 1)
  apply Subset.antisymm
  · exact frontier_lt_subset_eq (continuous_apply 0) (continuous_apply 1)
  · intro y hy
    rw [frontier, hopen.interior_eq]
    refine ⟨?_, fun h => absurd hy (ne_of_lt h)⟩
    have hy' : y 0 = y 1 := hy
    have hlim : Tendsto (fun k : ℕ => y + (1 / ((k : ℝ) + 1)) • (Pi.single 1 1 : Fin 4 → ℝ)) atTop
        (𝓝 y) := by
      have h1 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • (Pi.single 1 1 : Fin 4 → ℝ)) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
          (Pi.single 1 1 : Fin 4 → ℝ)
      simpa using tendsto_const_nhds.add h1
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    show (y + (1 / ((k : ℝ) + 1)) • (Pi.single 1 1 : Fin 4 → ℝ)) 0 <
      (y + (1 / ((k : ℝ) + 1)) • (Pi.single 1 1 : Fin 4 → ℝ)) 1
    simp [hy']
    positivity

end Lightlike

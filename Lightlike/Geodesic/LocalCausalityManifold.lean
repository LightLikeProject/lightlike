import Lightlike.Geodesic.LocalCausality
import Lightlike.Spacetime.CausalLadder.PerturbTimelike
import Lightlike.Spacetime.CausalLadder.ChartLipschitz
import Lightlike.Spacetime.OpenCoordMetric

/-!
# Local causality for causal curves of the manifold

The bridge from `IsTimeBall.causal_cone` (normal coordinates) to the causal curves of the manifold
`↥U`, an open set of `ℝⁿ` with the Lorentzian metric `openMetric U g hL` and a time orientation `T`:
a future causal curve of `↥U` from `p` which stays in a time ball, whose field `N` is future
directed for `T`, ends in `σ_p ≤ 0`, `x⁰ ≥ 0` (`IsTimeBall.causal_cone_of_isFutureCausalCurve`).
This is the `J⁺(p; O)` line of Chruściel's (2.4.7), "⇒", for the relation `J⁺(p; O)` of curves
inside `O`.

## Main results

* `exists_lipschitzOnWith_comp_of_contDiffOn`: a `C¹` map of a Lipschitz curve is Lipschitz on a
  compact interval.
* `IsTimeBall.mono`, `IsTimeBall.exists_future`: shrinking a time ball makes `N` future directed
  for `T` when `e` is.
* `IsTimeBall.causal_cone_of_isFutureCausalCurve`: the bridge.

## References

* P. T. Chruściel, *Elements of causality theory*, arXiv:1110.6706v1, Proposition 2.4.5 and
  (2.4.7), p. 20 (read). See `docs/notes/local-causality-plan.md`.
-/

open Set Metric Filter Topology Matrix MeasureTheory Manifold Bundle
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ}

/-- **A `C¹` map of a Lipschitz curve is Lipschitz** on a compact interval, if the curve stays in
the open set where the map is `C¹`. -/
theorem exists_lipschitzOnWith_comp_of_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) {c : ℝ → E} {a b : ℝ} {K : NNReal}
    (hc : LipschitzOnWith K c (Icc a b)) (hmem : ∀ t ∈ Icc a b, c t ∈ s) :
    ∃ K', LipschitzOnWith K' (f ∘ c) (Icc a b) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
  intro t ht
  obtain ⟨K₁, T, hT, hlip⟩ := (hf.contDiffAt (hs.mem_nhds (hmem t ht))).exists_lipschitzOnWith
  refine ⟨K₁ * K, Icc a b ∩ c ⁻¹' T, ?_, ?_⟩
  · exact inter_mem self_mem_nhdsWithin ((hc.continuousOn t ht).preimage_mem_nhdsWithin hT)
  · exact hlip.comp (hc.mono inter_subset_left) fun u hu => hu.2

namespace IsTimeBall

variable {U : TopologicalSpace.Opens (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {p e : Fin n → ℝ} {ρ r : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}
  {N : (Fin n → ℝ) → Fin n → ℝ}

/-- A time ball of a smaller radius. -/
lemma mono (h : IsTimeBall g U p ρ φ e r N) {r' : ℝ} (hr' : 0 < r') (hle : r' ≤ r) :
    IsTimeBall g U p ρ φ e r' N where
  chart := h.chart
  pos := hr'
  le := hle.trans h.le
  timelike_zero := h.timelike_zero
  dual v hv := h.dual v (ball_subset_ball hle hv)
  timelike v hv := h.timelike v (ball_subset_ball hle hv)
  continuousOn := h.continuousOn.mono (ball_subset_ball hle)

set_option backward.isDefEq.respectTransparency false in
/-- The field of a time orientation of `↥U`, read in coordinates, is continuous. -/
theorem continuous_timeOrientation_coord (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) :
    Continuous fun x : U => (T.X x : Fin n → ℝ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hX := (contMDiffAt_section (s := T.X) x₀).1 (T.contMDiff x₀)
  have heq : (fun x : U => ((trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) x₀)
      ⟨x, T.X x⟩).2) = fun x => (T.X x : Fin n → ℝ) := by
    funext x
    have hb : x ∈ (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) x₀).baseSet := by
      simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
        OpenPartialHomeomorph.subtypeRestr_source]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb,
      opens_continuousLinearMapAt]
    rfl
  rw [heq] at hX
  exact hX.continuousAt

/-- **The field `N` of a small time ball is future directed**: if `e` is future directed at `p`
for the time orientation `T`, then on a smaller ball `g(N, X) < 0`. -/
theorem exists_future (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N) (x₀ : U)
    (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) :
    ∃ r', 0 < r' ∧ r' ≤ r ∧ ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r', x.1 = φ v →
      matForm (g x.1) (N v) (T.X x) < 0 := by
  set S : Set (Fin n → ℝ) := ball 0 r with hS
  set X' : U → Fin n → ℝ := fun x => T.X x with hX'
  have hφS : ContinuousOn φ S :=
    (h.chart.contDiffOn.continuousOn).mono fun v hv => h.mem_source hv
  set F : S → U := fun v => ⟨φ v, h.map_mem v.2⟩ with hF
  have hFc : Continuous F := (hφS.domRestrict).subtype_mk _
  have hXc : Continuous fun v : S => X' (F v) := (continuous_timeOrientation_coord hL T).comp hFc
  have hNc : Continuous fun v : S => N v := h.continuousOn.domRestrict
  have hGc : ∀ i j, Continuous fun v : S => g (φ v) i j := fun i j =>
    ((hL.1.smooth i j).continuousOn.comp hφS fun v hv => h.map_mem hv).domRestrict
  set G : S → ℝ := fun v => ∑ i, ∑ j, N v i * g (φ v) i j * X' (F v) j with hG
  have hGeq : ∀ v : S, G v = matForm (g (φ v)) (N v) (X' (F v)) := fun v => by
    rw [matForm_apply]
  have hGcont : Continuous G := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((continuous_apply i).comp hNc).mul (hGc i j)).mul ((continuous_apply j).comp hXc)
  have h0S : (0 : Fin n → ℝ) ∈ S := mem_ball_self h.pos
  have hG0 : G ⟨0, h0S⟩ < 0 := by
    have hF0 : F ⟨0, h0S⟩ = x₀ := Subtype.ext (by simp [hF, h.chart.map_zero, hx₀])
    have hd := h.dual 0 h0S (X' x₀)
    rw [h.chart.hasFDerivAt_zero.fderiv, ContinuousLinearMap.id_apply, h.chart.map_zero,
      pairing_eq_matForm, pairing_eq_matForm] at hd
    rw [hGeq]
    simp only [hF0, h.chart.map_zero]
    rw [hd]; exact he
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (hGcont.continuousAt.eventually (gt_mem_nhds hG0))
  refine ⟨min ε r, lt_min hε h.pos, min_le_right _ _, fun x v hv hxv => ?_⟩
  have hvS : v ∈ S := ball_subset_ball (min_le_right _ _) hv
  have hdist : Dist.dist (⟨v, hvS⟩ : S) ⟨0, h0S⟩ < ε := by
    rw [Subtype.dist_eq]; exact lt_of_lt_of_le (Metric.mem_ball.1 hv) (min_le_left _ _)
  have hFx : F ⟨v, hvS⟩ = x := Subtype.ext hxv.symm
  have := hball hdist
  rw [hGeq, hFx] at this
  rw [hxv]
  exact this

set_option backward.isDefEq.respectTransparency false in
/-- **Local causality for the causal curves of `↥U`** (Chruściel, Proposition 2.4.5, the `J⁺(p; O)`
line of (2.4.7), "⇒"). Let `T` be a time orientation of `openMetric U g hL`, and let the field `N`
of a time ball at `p` be future directed for `T`. A future causal curve `γ` of `↥U` on `[a, b]`
from `p` which stays in the time ball ends at a point `q` with `σ_p(q) = g_p(v, v) ≤ 0` and
`x⁰(q) = -g_p(e, v) ≥ 0`, `v = φ⁻¹ q`. -/
theorem causal_cone_of_isFutureCausalCurve (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    (hTN : ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r, x.1 = φ v → matForm (g x.1) (N v) (T.X x) < 0)
    {γ : ℝ → U} {a b : ℝ} (hab : a ≤ b) (hγ : Causal.IsFutureCausalCurve T γ (Icc a b))
    (ha : (γ a).1 = p) (hin : ∀ t ∈ Icc a b, (γ t).1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    pairing g p (φ.symm (γ b).1) (φ.symm (γ b).1) ≤ 0 ∧ 0 ≤ -pairing g p e (φ.symm (γ b).1) := by
  -- the curve in coordinates
  set c : ℝ → Fin n → ℝ := fun t => (γ t).1 with hcdef
  set v : ℝ → Fin n → ℝ := fun t => φ.symm (c t) with hvdef
  have hsrc0 : ∀ q : U, q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a)).source := fun q => by
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
  have hchart : (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a)) ∘ γ = c := by
    funext t; exact opens_extChartAt_apply U (γ a) (γ t)
  have hvmem : ∀ t ∈ Icc a b, v t ∈ ball (0 : Fin n → ℝ) r ∧ φ (v t) = c t := by
    intro t ht
    obtain ⟨w, hw, hφw⟩ := hin t ht
    have hws : w ∈ φ.source := h.mem_source hw
    have hvw : v t = w := by
      show φ.symm (γ t).1 = w
      rw [← hφw]; exact φ.left_inv hws
    exact ⟨hvw ▸ hw, by rw [hvw, hφw]⟩
  have hctgt : ∀ t ∈ Icc a b, c t ∈ φ.target := fun t ht => by
    rw [← (hvmem t ht).2]; exact φ.map_source (h.mem_source (hvmem t ht).1)
  have hv0 : v a = 0 := by
    have h0 : (0 : Fin n → ℝ) ∈ φ.source := h.mem_source (mem_ball_self h.pos)
    simp only [hvdef, hcdef, ha, ← h.chart.map_zero]
    exact φ.left_inv h0
  -- Lipschitz in coordinates
  obtain ⟨K, hcK⟩ := Causal.exists_lipschitzOnWith_chart_comp hγ.lipschitz (γ a) fun t _ => hsrc0 (γ t)
  rw [hchart] at hcK
  obtain ⟨K', hvK⟩ := exists_lipschitzOnWith_comp_of_contDiffOn φ.open_target
    (h.chart.contDiffOn_symm.of_le (by simp)) hcK hctgt
  have hvK' : LipschitzOnWith K' v (Icc a b) := hvK
  -- the velocity in coordinates
  have hvel := Causal.ae_hasDerivAt_chart (γ a) hγ fun t _ => hsrc0 (γ t)
  rw [hchart] at hvel
  refine h.causal_cone hL hab hvK' (fun t ht => (hvmem t ht).1) hv0 ?_
  filter_upwards [hvel] with t ht hmt
  obtain ⟨u₀, hu, hcu⟩ := ht hmt
  obtain ⟨u, rfl⟩ : ∃ u : Fin n → ℝ, u = u₀ := ⟨u₀, rfl⟩
  have htI := Ioo_subset_Icc_self hmt
  have hbase : γ t ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) U (γ a)).baseSet := by
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  have htriv : ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) U (γ a)) ⟨γ t, u⟩).2 = u := by
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hbase,
      opens_continuousLinearMapAt]
    rfl
  rw [htriv] at hcu
  -- the chain rule through `φ⁻¹`
  have hvt := hvmem t htI
  obtain ⟨D, hD, hDφ, -⟩ := h.exists_fderiv_symm hvt.1
  rw [hvt.2] at hD
  have hderiv : HasDerivAt v (D u) t := hD.comp_hasDerivAt t hcu
  have hX : fderiv ℝ φ (v t) (D u) = u := hDφ u
  refine ⟨D u, hderiv, ?_, ?_⟩
  · rw [hX, hvt.2, pairing_eq_matForm]; exact hu.2.1
  · rw [hX, hvt.2, pairing_eq_matForm]
    have hy : c t ∈ (U : Set (Fin n → ℝ)) := (γ t).2
    have hLf := isLorentzianForm_matForm hL hy
    have hNN : matForm (g (c t)) (N (v t)) (N (v t)) < 0 := by
      rw [← pairing_eq_matForm, ← hvt.2]; exact h.timelike _ hvt.1
    have hXX : matForm (g (c t)) (T.X (γ t)) (T.X (γ t)) < 0 := T.timelike (γ t)
    have hNX : matForm (g (c t)) (N (v t)) (T.X (γ t)) < 0 := hTN (γ t) (v t) hvt.1 hvt.2.symm
    have key := hLf.neg_of_causal_timelike hXX hu.2.1 hNN hu.2.2 hNX
    rw [← pairing_eq_matForm, pairing_comm hL.1 hy, pairing_eq_matForm]
    exact key

end IsTimeBall

end Lightlike.Geodesic

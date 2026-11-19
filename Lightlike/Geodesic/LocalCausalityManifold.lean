import Lightlike.Geodesic.LocalCausality
import Lightlike.Spacetime.CausalLadder.PerturbTimelike
import Lightlike.Spacetime.CausalLadder.ChartLipschitz
import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.Causal.CurveMargin
import Lightlike.Spacetime.Causal.TimeReversal

/-!
# Local causality: Chruściel's Proposition 2.4.5 for a time ball

On the manifold `↥U`, an open set of `ℝⁿ` with the Lorentzian metric `openMetric U g hL` and a
time orientation `T`, let `O = φ (ball 0 r)` be a time ball at `p` (`IsTimeBall`: normal
coordinates `v = φ⁻¹ q`, the time function `x⁰ = -g_p(e, v)` with timelike gradient) whose field
`e` is future directed for `T` at `p` (then `N` is on all of `O`, `IsTimeBall.future_of_center`). With `σ_p(q) = g_p(v, v)`, for `q ∈ O`:
`q ∈ I⁺(p; O)` iff `σ_p < 0 < x⁰`, `q ∈ J⁺(p; O)` iff `σ_p ≤ 0 ≤ x⁰`, `q` is on the boundary of
`J⁺(p; O)` iff `σ_p = 0 ≤ x⁰`, and the same for pasts with `x⁰ ≤ 0`. Here `J⁺(p; O)` and
`I⁺(p; O)` are reached by curves inside `O` (`Causal.causalFutureIn`, `Causal.chronFutureIn`).
"⇒" comes from `IsTimeBall.causal_cone` and `IsTimeBall.chron_cone` (normal coordinates), "⇐"
from the radial curves `t ↦ φ (t v)`.

Differences from the source (Chruściel, Proposition 2.4.5): the spacetime is an open set of
`ℝⁿ` with a smooth Lorentzian coordinate metric, not a general `C²` spacetime; `σ_p` and `x⁰` are
written in normal coordinates of an arbitrary basis, `σ_p(v) = g_p(v, v)` and `x⁰ = -g_p(e, ·)`
for a timelike `e` at `p`, which is Chruściel's `η_μν x^μ x^ν` and `x⁰` in orthonormal normal
coordinates with `e = ∂₀`; "`∇x⁰` timelike on `O`" is `IsTimeBall.timelike`, and "`e` future
directed at `p`" is the time orientation of Chruściel's normal coordinates ((2.2.10), p. 8). The proof does not use Chruściel's perturbed metrics (pp. 22–23): it uses the
Gauss lemma and the cone inequality (`docs/notes/local-causality-plan.md`).

## Main results

* `exists_lipschitzOnWith_comp_of_contDiffOn`: a `C¹` map of a Lipschitz curve is Lipschitz on a
  compact interval.
* `IsTimeBall.mono`: a time ball of smaller radius; `IsTimeBall.future_of_center`: `N` is future
  directed on the whole ball when `e` is at `p`.
* `Causal.causalFutureIn`, `Causal.chronFutureIn`, `Causal.causalPastIn`, `Causal.chronPastIn`:
  `J±(x; O)`, `I±(x; O)`, curves inside `O`; `Causal.causalFutureIn_reverse`,
  `Causal.chronFutureIn_reverse`: reversing the time orientation exchanges futures and pasts.
* `IsTimeBall.mem_causalPastIn_iff`, `IsTimeBall.mem_chronPastIn_iff`,
  `IsTimeBall.mem_frontier_causalPastIn_iff`: the analogues for pasts.
* `IsTimeBall.mem_causalFutureIn_iff`, `IsTimeBall.mem_chronFutureIn_iff`,
  `IsTimeBall.mem_horismosIn_iff`, `IsTimeBall.mem_frontier_causalFutureIn_iff`: Chruściel's
  (2.4.7) for the time ball; the third line both for `J⁺(p; O) \ I⁺(p; O)` and for the boundary
  `J̇⁺(p; O)`.
* `IsTimeBall.coord_of_curve`: a curve of `↥U` in the time ball, in normal coordinates.
* `IsTimeBall.causal_cone_of_isFutureCausalCurve`, `IsTimeBall.chron_cone_of_isFutureTimelikeCurve`:
  the `J⁺` and `I⁺` lines of (2.4.7), "⇒", for the curves of `↥U`.

## References

* P. T. Chruściel, *Elements of causality theory*, arXiv:1110.6706v1, Proposition 2.4.5 and
  (2.4.7), p. 20 (read). See `docs/notes/local-causality-plan.md`.
-/

open Set Metric Filter Topology Matrix MeasureTheory Manifold Bundle
open scoped ContDiff

noncomputable section

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ} {g' : LorentzianMetric I M k} (T : TimeOrientation g')

/-- The **causal future of `x` relative to `O`**, `J⁺(x; O)` (Chruściel, Section 2.4): the points
reached from `x` by a future causal curve that stays in `O`. -/
def causalFutureIn (x : M) (O : Set M) : Set M :=
  {y | ∃ (γ : ℝ → M) (a b : ℝ), a ≤ b ∧ IsFutureCausalCurve T γ (Icc a b) ∧ γ a = x ∧ γ b = y ∧
    ∀ t ∈ Icc a b, γ t ∈ O}

/-- The **chronological future of `x` relative to `O`**, `I⁺(x; O)`: the points reached from `x` by
a future timelike curve of positive parameter length that stays in `O`. -/
def chronFutureIn (x : M) (O : Set M) : Set M :=
  {y | ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = x ∧ γ b = y ∧
    ∀ t ∈ Icc a b, γ t ∈ O}

/-- The **causal past of `x` relative to `O`**, `J⁻(x; O)`: the points `y` with `x ∈ J⁺(y; O)`. -/
def causalPastIn (x : M) (O : Set M) : Set M := {y | x ∈ causalFutureIn T y O}

/-- The **chronological past of `x` relative to `O`**, `I⁻(x; O)`. -/
def chronPastIn (x : M) (O : Set M) : Set M := {y | x ∈ chronFutureIn T y O}

/-- A future causal curve inside `O` for the reversed orientation, run backwards, is one for `T`. -/
theorem causalFutureIn_reverse_subset {x y : M} {O : Set M}
    (h : y ∈ causalFutureIn T.reverse x O) : x ∈ causalFutureIn T y O := by
  obtain ⟨γ, a, b, hab, hγ, ha, hb, hin⟩ := h
  rcases hab.lt_or_eq with hlt | heq
  · have hr := (IsCurveWith.reflectNeg hγ hlt).mono_velocity fun x v hv =>
      (T.isFutureCausal_reverse_neg v).1 hv
    exact ⟨fun t => γ (-t), -b, -a, by linarith, hr, by simp [hb], by simp [ha],
      fun t ht => hin (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  · have hxO : x ∈ O := by rw [← ha]; exact hin a ⟨le_rfl, hab⟩
    have hxy : x = y := by rw [← ha, ← hb, heq]
    rw [← hxy]
    exact ⟨fun _ => x, 0, 0, le_rfl, isCurveWith_const _ x 0, rfl, rfl, fun _ _ => hxO⟩

/-- **`J⁺(x; O)` for the reversed orientation is `J⁻(x; O)`.** -/
theorem causalFutureIn_reverse (x : M) (O : Set M) :
    causalFutureIn T.reverse x O = causalPastIn T x O := by
  ext y
  constructor
  · exact fun h => causalFutureIn_reverse_subset T h
  · intro h
    have := causalFutureIn_reverse_subset T.reverse (x := y) (y := x) (O := O)
    rw [TimeOrientation.reverse_reverse] at this
    exact this h

/-- A future timelike curve inside `O` for the reversed orientation, run backwards, is one for
`T`. -/
theorem chronFutureIn_reverse_subset {x y : M} {O : Set M}
    (h : y ∈ chronFutureIn T.reverse x O) : x ∈ chronFutureIn T y O := by
  obtain ⟨γ, a, b, hab, hγ, ha, hb, hin⟩ := h
  obtain ⟨ε, hε, hm⟩ := hγ.2 a b hab subset_rfl
  have hr := (IsCurveWith.reflectNeg hm hab).mono_velocity fun x v hv =>
    (T.isFutureTimelikeWith_reverse_neg v).1 hv
  exact ⟨fun t => γ (-t), -b, -a, by linarith, isFutureTimelikeCurve_of_margin T hε hr,
    by simp [hb], by simp [ha], fun t ht => hin (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

/-- **`I⁺(x; O)` for the reversed orientation is `I⁻(x; O)`.** -/
theorem chronFutureIn_reverse (x : M) (O : Set M) :
    chronFutureIn T.reverse x O = chronPastIn T x O := by
  ext y
  constructor
  · exact fun h => chronFutureIn_reverse_subset T h
  · intro h
    have := chronFutureIn_reverse_subset T.reverse (x := y) (y := x) (O := O)
    rw [TimeOrientation.reverse_reverse] at this
    exact this h

end Lightlike.Causal

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

/-- **The field `N` of a time ball is future directed** on the whole ball if `e` is future directed
at `p`: `g(N, X)` is continuous on the connected ball and never zero (two timelike vectors are not
orthogonal), and negative at the centre, where `N 0` pairs like `e`. In Chruściel's normal
coordinates (Proposition 2.2.3, (2.2.10), p. 8) `∂₀` is future directed at `p`, so `e = ∂₀` is. -/
theorem future_of_center (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N) (x₀ : U)
    (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) :
    ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r, x.1 = φ v → matForm (g x.1) (N v) (T.X x) < 0 := by
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
  have : PreconnectedSpace S :=
    isPreconnected_iff_preconnectedSpace.1 (convex_ball (0 : Fin n → ℝ) r).isPreconnected
  have hne : ∀ v : S, G v ≠ 0 := by
    intro v h0
    rw [hGeq] at h0
    have hyU : φ v ∈ (U : Set (Fin n → ℝ)) := h.map_mem v.2
    have hLf := isLorentzianForm_matForm hL hyU
    have hXX : matForm (g (φ v)) (X' (F v)) (X' (F v)) < 0 := T.timelike (F v)
    have hNN : matForm (g (φ v)) (N v) (N v) < 0 := by
      rw [← pairing_eq_matForm]; exact h.timelike v v.2
    have hXN : matForm (g (φ v)) (X' (F v)) (N v) = 0 := by
      rw [← pairing_eq_matForm, pairing_comm hL.1 hyU, pairing_eq_matForm]; exact h0
    have hX0 := hLf.eq_zero_of_orthogonal_timelike hNN hXN hXX.le
    rw [hX0] at hXX
    simp at hXX
  intro x v hv hxv
  have hvS : v ∈ S := hv
  have hFx : F ⟨v, hvS⟩ = x := Subtype.ext hxv.symm
  have hlt : G ⟨v, hvS⟩ < 0 := by
    by_contra hge
    have hsub := isPreconnected_univ.intermediate_value (mem_univ (⟨0, h0S⟩ : S))
      (mem_univ (⟨v, hvS⟩ : S)) hGcont.continuousOn
    obtain ⟨w, -, hw⟩ := hsub ⟨hG0.le, not_lt.1 hge⟩
    exact hne w hw
  rw [hGeq, hFx] at hlt
  rw [hxv]
  exact hlt

set_option backward.isDefEq.respectTransparency false in
/-- **A curve of `↥U` in normal coordinates.** A curve of `↥U` on `[a, b]` with velocity in `P`,
from `p` and inside a time ball, is in normal coordinates `v = φ⁻¹ ∘ γ` a Lipschitz curve in the
ball from `0`, with `φ (v t) = γ t`, whose velocity `v'` satisfies `P (γ t) (Dφ(v t) v')` almost
everywhere. -/
theorem coord_of_curve (h : IsTimeBall g U p ρ φ e r N) {P : ∀ x : U, TangentSpace 𝓘(ℝ, Fin n → ℝ) x → Prop}
    {γ : ℝ → U} {a b : ℝ} (hγ : Causal.IsCurveWith P γ (Icc a b)) (ha : (γ a).1 = p)
    (hin : ∀ t ∈ Icc a b, (γ t).1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    (∃ K, LipschitzOnWith K (fun t => φ.symm (γ t).1) (Icc a b)) ∧
      (∀ t ∈ Icc a b, φ.symm (γ t).1 ∈ ball (0 : Fin n → ℝ) r ∧ φ (φ.symm (γ t).1) = (γ t).1) ∧
      φ.symm (γ a).1 = 0 ∧
      ∀ᵐ t, t ∈ Ioo a b → ∃ v' : Fin n → ℝ, HasDerivAt (fun t => φ.symm (γ t).1) v' t ∧
        P (γ t) (fderiv ℝ φ (φ.symm (γ t).1) v') := by
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
  obtain ⟨K, hcK⟩ := Causal.exists_lipschitzOnWith_chart_comp hγ.lipschitz (γ a)
    fun t _ => hsrc0 (γ t)
  rw [hchart] at hcK
  obtain ⟨K', hvK⟩ := exists_lipschitzOnWith_comp_of_contDiffOn φ.open_target
    (h.chart.contDiffOn_symm.of_le (by simp)) hcK hctgt
  refine ⟨⟨K', hvK⟩, hvmem, hv0, ?_⟩
  have hvel := Causal.ae_hasDerivAt_chart (γ a) hγ fun t _ => hsrc0 (γ t)
  rw [hchart] at hvel
  filter_upwards [hvel] with t ht hmt
  obtain ⟨u₀, hu, hcu⟩ := ht hmt
  obtain ⟨u, rfl⟩ : ∃ u : Fin n → ℝ, u = u₀ := ⟨u₀, rfl⟩
  have hbase : γ t ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) U (γ a)).baseSet := by
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
  have htriv : ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) U (γ a)) ⟨γ t, u⟩).2 = u := by
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hbase,
      opens_continuousLinearMapAt]
    rfl
  rw [htriv] at hcu
  have hvt := hvmem t (Ioo_subset_Icc_self hmt)
  obtain ⟨D, hD, hDφ, -⟩ := h.exists_fderiv_symm hvt.1
  rw [hvt.2] at hD
  refine ⟨D u, hD.comp_hasDerivAt t hcu, ?_⟩
  show P (γ t) (fderiv ℝ φ (v t) (D u))
  rw [hDφ u]
  exact hu

/-- A future directed vector for `T` pairs negatively with the field `N` of the time ball. -/
lemma pairing_N_neg (hL : IsLorentzianCoordMetric g U) (T : Causal.TimeOrientation (openMetric U g hL))
    (h : IsTimeBall g U p ρ φ e r N)
    (hTN : ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r, x.1 = φ v → matForm (g x.1) (N v) (T.X x) < 0)
    {x : U} {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) r) (hxv : φ v = x.1) {u : Fin n → ℝ}
    (hu : matForm (g x.1) u u ≤ 0) (hux : matForm (g x.1) u (T.X x) < 0) :
    pairing g (φ v) (N v) u < 0 := by
  have hy : x.1 ∈ (U : Set (Fin n → ℝ)) := x.2
  have hLf := isLorentzianForm_matForm hL hy
  have hNN : matForm (g x.1) (N v) (N v) < 0 := by
    rw [← pairing_eq_matForm, ← hxv]; exact h.timelike _ hv
  have hNX := hTN x v hv hxv.symm
  have key := hLf.neg_of_causal_timelike (T.timelike x) hu hNN hux hNX
  rw [hxv, pairing_comm hL.1 hy, pairing_eq_matForm]
  exact key

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
  obtain ⟨⟨K, hK⟩, hmem, h0, hd⟩ := h.coord_of_curve hγ ha hin
  refine h.causal_cone hL hab hK (fun t ht => (hmem t ht).1) h0 ?_
  filter_upwards [hd] with t ht hmt
  obtain ⟨v', hv', hu⟩ := ht hmt
  have hvt := hmem t (Ioo_subset_Icc_self hmt)
  refine ⟨v', hv', ?_, h.pairing_N_neg hL T hTN hvt.1 hvt.2 hu.2.1 hu.2.2⟩
  rw [hvt.2, pairing_eq_matForm]; exact hu.2.1

/-- **Local causality for the timelike curves of `↥U`** (Chruściel, Proposition 2.4.5, the
`I⁺(p; O)` line of (2.4.7), "⇒"): with the hypotheses of `causal_cone_of_isFutureCausalCurve`, a
future timelike curve on `[a, b]`, `a < b`, ends at a point with `σ_p < 0` and `x⁰ > 0`. -/
theorem chron_cone_of_isFutureTimelikeCurve (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    (hTN : ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r, x.1 = φ v → matForm (g x.1) (N v) (T.X x) < 0)
    {γ : ℝ → U} {a b : ℝ} (hab : a < b) (hγ : Causal.IsFutureTimelikeCurve T γ (Icc a b))
    (ha : (γ a).1 = p) (hin : ∀ t ∈ Icc a b, (γ t).1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    pairing g p (φ.symm (γ b).1) (φ.symm (γ b).1) < 0 ∧ 0 < -pairing g p e (φ.symm (γ b).1) := by
  obtain ⟨⟨K, hK⟩, hmem, h0, hd⟩ := h.coord_of_curve hγ.1 ha hin
  refine h.chron_cone hL hab hK (fun t ht => (hmem t ht).1) h0 ?_
  filter_upwards [hd] with t ht hmt
  obtain ⟨v', hv', hu⟩ := ht hmt
  have hvt := hmem t (Ioo_subset_Icc_self hmt)
  refine ⟨v', hv', ?_, h.pairing_N_neg hL T hTN hvt.1 hvt.2 hu.1.le hu.2⟩
  rw [hvt.2, pairing_eq_matForm]; exact hu.1

/-! ### The converse: radial curves -/

lemma smul_mem_ball' {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ ball (0 : Fin n → ℝ) r := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc t * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ = ‖v‖ := one_mul _
    _ < r := mem_ball_zero_iff.1 hv

/-- The radial curve `t ↦ φ (t v)` of the time ball, with `t` clamped to `[0, 1]`, as a curve of
`↥U`. -/
def radial (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) r) :
    ℝ → U := fun t =>
  ⟨φ ((projIcc (0 : ℝ) 1 zero_le_one t : ℝ) • v),
    h.map_mem (smul_mem_ball' hv (projIcc (0 : ℝ) 1 zero_le_one t).2)⟩

lemma radial_apply (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (h.radial hv t).1 = φ (t • v) := by
  simp only [radial, projIcc_of_mem _ ht]

set_option backward.isDefEq.respectTransparency false in
lemma radial_contMDiffOn (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (h.radial hv) (Icc 0 1) := by
  intro t ht
  rw [← ContMDiffWithinAt.subtypeVal_comp_iff, contMDiffWithinAt_iff_contDiffWithinAt]
  have hsrc : t • v ∈ φ.source := h.mem_source (smul_mem_ball' hv ht)
  have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => φ (s • v)) t :=
    (h.chart.contDiffOn.contDiffAt (φ.open_source.mem_nhds hsrc)).comp t
      (contDiffAt_id.smul contDiffAt_const)
  exact h1.contDiffWithinAt.congr (fun y hy => h.radial_apply hv hy) (h.radial_apply hv ht)

set_option backward.isDefEq.respectTransparency false in
lemma velocity_radial (h : IsTimeBall g U p ρ φ e r N) {v : Fin n → ℝ}
    (hv : v ∈ ball (0 : Fin n → ℝ) r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Causal.velocity 𝓘(ℝ, Fin n → ℝ) (h.radial hv) (Icc 0 1) t = fderiv ℝ φ (t • v) v := by
  have hmd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (h.radial hv) (Icc 0 1) t :=
    ((h.radial_contMDiffOn hv) t ht).mdifferentiableWithinAt (by simp)
  have hsrc : h.radial hv t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (h.radial hv t)).source := by
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
  have h1 := Causal.hasDerivWithinAt_chart_comp (h.radial hv t) hmd hsrc
  have hchart : (extChartAt 𝓘(ℝ, Fin n → ℝ) (h.radial hv t)) ∘ h.radial hv =
      fun s => (h.radial hv s).1 := funext fun s => opens_extChartAt_apply U _ _
  rw [hchart] at h1
  have hbase : h.radial hv t ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) U (h.radial hv t)).baseSet := by
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
  have htriv : ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) U (h.radial hv t))
      ⟨h.radial hv t, Causal.velocity 𝓘(ℝ, Fin n → ℝ) (h.radial hv) (Icc 0 1) t⟩).2 =
      Causal.velocity 𝓘(ℝ, Fin n → ℝ) (h.radial hv) (Icc 0 1) t := by
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hbase,
      opens_continuousLinearMapAt]
    rfl
  rw [htriv] at h1
  have hφd := h.hasFDerivAt (smul_mem_ball' hv ht)
  have hs : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have h2 : HasDerivWithinAt (fun s => (h.radial hv s).1) (fderiv ℝ φ (t • v) v) (Icc 0 1) t :=
    ((hφd.comp_hasDerivAt t hs).hasDerivWithinAt).congr (fun y hy => h.radial_apply hv hy)
      (h.radial_apply hv ht)
  exact (uniqueDiffOn_Icc zero_lt_one t ht).eq_deriv _ h1 h2

/-- **The Gauss lemma along a radial curve**: `g(φ(t v))(Dφ(t v) v, Dφ(t v) v) = g_p(v, v)`. -/
lemma pairing_radial (hL : IsLorentzianCoordMetric g U) (h : IsTimeBall g U p ρ φ e r N)
    {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pairing g (φ (t • v)) (fderiv ℝ φ (t • v) v) (fderiv ℝ φ (t • v) v) = pairing g p v v := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0, zero_smul, h.chart.hasFDerivAt_zero.fderiv, h.chart.map_zero]
    rfl
  · have hg := IsNormalChart.gauss hL.1 h.chart (h.mem_ball (smul_mem_ball' hv ht)) v
    rw [map_smul, pairing_smul_left, pairing_smul_left] at hg
    exact mul_left_cancel₀ hpos.ne' hg

/-- The velocity of the radial curve: `g(γ̇, γ̇) = σ_p(v)`, and `γ̇` is future directed for `T`
when `σ_p(v) ≤ 0 < x⁰(v)`. -/
lemma radial_velocity_props (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    (hTN : ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r, x.1 = φ v → matForm (g x.1) (N v) (T.X x) < 0)
    {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) r) (hσ : pairing g p v v ≤ 0)
    (hx : 0 < -pairing g p e v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    matForm (g (h.radial hv t).1) (fderiv ℝ φ (t • v) v) (fderiv ℝ φ (t • v) v) = pairing g p v v ∧
      fderiv ℝ φ (t • v) v ≠ 0 ∧
      matForm (g (h.radial hv t).1) (fderiv ℝ φ (t • v) v) (T.X (h.radial hv t)) < 0 := by
  have hball := smul_mem_ball' hv ht
  have hy := h.radial_apply hv ht
  have hyU : φ (t • v) ∈ (U : Set (Fin n → ℝ)) := hy ▸ (h.radial hv t).2
  have hσt := h.pairing_radial hL hv ht
  have hNt : pairing g (φ (t • v)) (N (t • v)) (fderiv ℝ φ (t • v) v) < 0 := by
    rw [h.dual _ hball v]; linarith
  have hLf := isLorentzianForm_matForm hL hyU
  refine ⟨by rw [hy, ← pairing_eq_matForm]; exact hσt, fun h0 => ?_, ?_⟩
  · rw [h0, pairing_zero_right] at hNt
    exact lt_irrefl _ hNt
  · set X0 : Fin n → ℝ := T.X (h.radial hv t) with hX0
    have hXX : matForm (g (h.radial hv t).1) X0 X0 < 0 := T.timelike (h.radial hv t)
    have hNX : matForm (g (h.radial hv t).1) (N (t • v)) X0 < 0 := hTN (h.radial hv t) (t • v) hball hy
    rw [hy] at hXX hNX ⊢
    have hNN : matForm (g (φ (t • v))) (N (t • v)) (N (t • v)) < 0 := by
      rw [← pairing_eq_matForm]; exact h.timelike _ hball
    have huu : matForm (g (φ (t • v))) (fderiv ℝ φ (t • v) v) (fderiv ℝ φ (t • v) v) ≤ 0 := by
      rw [← pairing_eq_matForm, hσt]; exact hσ
    have huN : matForm (g (φ (t • v))) (fderiv ℝ φ (t • v) v) (N (t • v)) < 0 := by
      rw [← pairing_eq_matForm, pairing_comm hL.1 hyU]; exact hNt
    have hXN : matForm (g (φ (t • v))) X0 (N (t • v)) < 0 := by
      rw [← pairing_eq_matForm, pairing_comm hL.1 hyU, pairing_eq_matForm]; exact hNX
    exact hLf.neg_of_causal_timelike hNN huu hXX huN hXN

/-- **The converse for `J⁺`** (Chruściel, (2.4.7), "⇐"): if `σ_p(v) ≤ 0` and `x⁰(v) ≥ 0`, the point
`φ v` is reached from `p` by a future causal curve inside the time ball (the radial curve, or the
constant curve for `v = 0`). -/
theorem exists_causal_of_cone (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    (hTN : ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r, x.1 = φ v → matForm (g x.1) (N v) (T.X x) < 0)
    {x₀ : U} (hx₀ : x₀.1 = p) {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) r)
    (hσ : pairing g p v v ≤ 0) (hx : 0 ≤ -pairing g p e v) :
    ∃ (γ : ℝ → U) (a b : ℝ), a ≤ b ∧ Causal.IsFutureCausalCurve T γ (Icc a b) ∧ γ a = x₀ ∧
      (γ b).1 = φ v ∧ ∀ t ∈ Icc a b, (γ t).1 ∈ φ '' ball (0 : Fin n → ℝ) r := by
  by_cases hv0 : v = 0
  · refine ⟨fun _ => x₀, 0, 0, le_rfl, Causal.isCurveWith_const _ x₀ 0, rfl, ?_, ?_⟩
    · rw [hx₀, hv0, h.chart.map_zero]
    · intro t _; exact ⟨0, mem_ball_self h.pos, by rw [h.chart.map_zero, hx₀]⟩
  have hp : p ∈ (U : Set (Fin n → ℝ)) := hx₀ ▸ x₀.2
  have hxpos : 0 < -pairing g p e v := by
    refine lt_of_le_of_ne hx fun h0 => hv0 ?_
    refine (isLorentzianForm_matForm hL hp).eq_zero_of_orthogonal_timelike (X := e) ?_ ?_ ?_
    · rw [← pairing_eq_matForm]; exact h.timelike_zero
    · rw [← pairing_eq_matForm, pairing_comm hL.1 hp]; linarith
    · rw [← pairing_eq_matForm]; exact hσ
  have hsm := h.radial_contMDiffOn hv
  refine ⟨h.radial hv, 0, 1, zero_le_one, ⟨ordConnected_Icc,
    Causal.isLocallyLipschitzOn_of_contMDiffOn zero_lt_one (hsm.of_le (by simp)), ?_⟩, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    refine ⟨(hsm t ht).mdifferentiableWithinAt (by simp), ?_⟩
    obtain ⟨h1, h2, h3⟩ := h.radial_velocity_props hL T hTN hv hσ hxpos ht
    rw [h.velocity_radial hv ht]
    exact ⟨h2, h1.trans_le hσ, h3⟩
  · refine Subtype.ext ?_
    rw [h.radial_apply hv ⟨le_rfl, zero_le_one⟩, zero_smul, h.chart.map_zero]
    exact hx₀.symm
  · rw [h.radial_apply hv ⟨zero_le_one, le_rfl⟩, one_smul]
  · intro t ht; exact ⟨t • v, smul_mem_ball' hv ht, (h.radial_apply hv ht).symm⟩

/-- **The converse for `I⁺`** (Chruściel, (2.4.7), "⇐"): if `σ_p(v) < 0` and `x⁰(v) > 0`, the point
`φ v` is reached from `p` by a future timelike curve inside the time ball (the radial curve). -/
theorem exists_timelike_of_cone (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    (hTN : ∀ x : U, ∀ v ∈ ball (0 : Fin n → ℝ) r, x.1 = φ v → matForm (g x.1) (N v) (T.X x) < 0)
    {x₀ : U} (hx₀ : x₀.1 = p) {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) r)
    (hσ : pairing g p v v < 0) (hx : 0 < -pairing g p e v) :
    ∃ (γ : ℝ → U) (a b : ℝ), a < b ∧ Causal.IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = x₀ ∧
      (γ b).1 = φ v ∧ ∀ t ∈ Icc a b, (γ t).1 ∈ φ '' ball (0 : Fin n → ℝ) r := by
  have hsm := h.radial_contMDiffOn hv
  refine ⟨h.radial hv, 0, 1, zero_lt_one, Causal.isFutureTimelikeCurve_of_contMDiffOn T zero_lt_one
    (hsm.of_le (by simp)) fun t ht => ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, -, h3⟩ := h.radial_velocity_props hL T hTN hv hσ.le hx ht
    rw [h.velocity_radial hv ht]
    exact ⟨h1.trans_lt hσ, h3⟩
  · refine Subtype.ext ?_
    rw [h.radial_apply hv ⟨le_rfl, zero_le_one⟩, zero_smul, h.chart.map_zero]
    exact hx₀.symm
  · rw [h.radial_apply hv ⟨zero_le_one, le_rfl⟩, one_smul]
  · intro t ht; exact ⟨t • v, smul_mem_ball' hv ht, (h.radial_apply hv ht).symm⟩

/-- `σ_p(v) ≤ 0` and `x⁰(v) = 0` only at `v = 0`. -/
lemma eq_zero_of_cone (hL : IsLorentzianCoordMetric g U) (h : IsTimeBall g U p ρ φ e r N)
    (hp : p ∈ (U : Set (Fin n → ℝ))) {v : Fin n → ℝ} (hσ : pairing g p v v ≤ 0)
    (hx : pairing g p e v = 0) : v = 0 :=
  (isLorentzianForm_matForm hL hp).eq_zero_of_orthogonal_timelike (X := e)
    (by rw [← pairing_eq_matForm]; exact h.timelike_zero)
    (by rw [← pairing_eq_matForm, pairing_comm hL.1 hp]; exact hx)
    (by rw [← pairing_eq_matForm]; exact hσ)

/-- **Chruściel, Proposition 2.4.5, the `J⁺` line of (2.4.7)**: for `q = φ v` in the time ball
`O = φ (ball 0 r)`, `q ∈ J⁺(p; O)` iff `σ_p(q) ≤ 0` and `x⁰(q) ≥ 0`. -/
theorem mem_causalFutureIn_iff (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    {x₀ : U} (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) {q : U}
    (hq : q.1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    q ∈ Causal.causalFutureIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r} ↔
      pairing g p (φ.symm q.1) (φ.symm q.1) ≤ 0 ∧ 0 ≤ -pairing g p e (φ.symm q.1) := by
  have hTN := h.future_of_center hL T x₀ hx₀ he
  constructor
  · rintro ⟨γ, a, b, hab, hγ, ha, hb, hin⟩
    have := h.causal_cone_of_isFutureCausalCurve hL T hTN hab hγ (by rw [ha, hx₀]) hin
    rwa [hb] at this
  · rintro ⟨hσ, hx⟩
    obtain ⟨w, hw, hφw⟩ := hq
    have hsw : φ.symm q.1 = w := by rw [← hφw]; exact φ.left_inv (h.mem_source hw)
    rw [hsw] at hσ hx
    obtain ⟨γ, a, b, hab, hγ, ha, hb, hin⟩ := h.exists_causal_of_cone hL T hTN hx₀ hw hσ hx
    exact ⟨γ, a, b, hab, hγ, ha, Subtype.ext (hb.trans hφw), hin⟩

/-- **Chruściel, Proposition 2.4.5, the `I⁺` line of (2.4.7)**: for `q = φ v` in the time ball,
`q ∈ I⁺(p; O)` iff `σ_p(q) < 0` and `x⁰(q) > 0`. -/
theorem mem_chronFutureIn_iff (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    {x₀ : U} (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) {q : U}
    (hq : q.1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    q ∈ Causal.chronFutureIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r} ↔
      pairing g p (φ.symm q.1) (φ.symm q.1) < 0 ∧ 0 < -pairing g p e (φ.symm q.1) := by
  have hTN := h.future_of_center hL T x₀ hx₀ he
  constructor
  · rintro ⟨γ, a, b, hab, hγ, ha, hb, hin⟩
    have := h.chron_cone_of_isFutureTimelikeCurve hL T hTN hab hγ (by rw [ha, hx₀]) hin
    rwa [hb] at this
  · rintro ⟨hσ, hx⟩
    obtain ⟨w, hw, hφw⟩ := hq
    have hsw : φ.symm q.1 = w := by rw [← hφw]; exact φ.left_inv (h.mem_source hw)
    rw [hsw] at hσ hx
    obtain ⟨γ, a, b, hab, hγ, ha, hb, hin⟩ := h.exists_timelike_of_cone hL T hTN hx₀ hw hσ hx
    exact ⟨γ, a, b, hab, hγ, ha, Subtype.ext (hb.trans hφw), hin⟩

/-- **The horismos of a time ball**: for `q` in the time ball, `q ∈ J⁺(p; O) \ I⁺(p; O)` iff
`σ_p(q) = 0` and `x⁰(q) ≥ 0`: the null cone of `p`. -/
theorem mem_horismosIn_iff (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    {x₀ : U} (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) {q : U}
    (hq : q.1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    q ∈ Causal.causalFutureIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r} \
        Causal.chronFutureIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r} ↔
      pairing g p (φ.symm q.1) (φ.symm q.1) = 0 ∧ 0 ≤ -pairing g p e (φ.symm q.1) := by
  have hp : p ∈ (U : Set (Fin n → ℝ)) := hx₀ ▸ x₀.2
  rw [Set.mem_sdiff, h.mem_causalFutureIn_iff hL T hx₀ he hq, h.mem_chronFutureIn_iff hL T hx₀ he hq]
  constructor
  · rintro ⟨⟨hσ, hx⟩, hnot⟩
    refine ⟨le_antisymm hσ (not_lt.1 fun hlt => hnot ⟨hlt, lt_of_le_of_ne hx fun h0 => ?_⟩), hx⟩
    have h0' := h.eq_zero_of_cone hL hp hσ (by linarith)
    rw [h0', pairing_zero_right] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨hσ, hx⟩
    exact ⟨⟨hσ.le, hx⟩, fun ⟨hlt, _⟩ => (lt_irrefl _ (hσ ▸ hlt))⟩

/-- **Chruściel, Proposition 2.4.5, the `J̇⁺` line of (2.4.7)**: for `q` in the time ball
`O = φ (ball 0 r)`, `q` lies on the boundary of `J⁺(p; O)` iff `σ_p(q) = 0` and `x⁰(q) ≥ 0`. The
interior of `J⁺(p; O)` is the open cone `σ_p < 0 < x⁰`: at a point with `σ_p = 0` the points
`φ (v - s e)`, `s > 0` small, leave the closed cone. -/
theorem mem_frontier_causalFutureIn_iff (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    {x₀ : U} (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) {q : U}
    (hq : q.1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    q ∈ frontier (Causal.causalFutureIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r}) ↔
      pairing g p (φ.symm q.1) (φ.symm q.1) = 0 ∧ 0 ≤ -pairing g p e (φ.symm q.1) := by
  set O' : Set U := {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r} with hO'
  set S := Causal.causalFutureIn T x₀ O' with hSdef
  have hg := hL.1
  have hp : p ∈ (U : Set (Fin n → ℝ)) := hx₀ ▸ x₀.2
  have himg : IsOpen (φ '' ball (0 : Fin n → ℝ) r) :=
    φ.isOpen_image_of_subset_source isOpen_ball fun w hw => h.mem_source hw
  have hO'open : IsOpen O' := himg.preimage continuous_subtype_val
  have htgt : ∀ y ∈ O', y.1 ∈ φ.target := by
    rintro y ⟨w, hw, hφw⟩; rw [← hφw]; exact φ.map_source (h.mem_source hw)
  have hψ : ContinuousOn (fun y : U => φ.symm y.1) O' :=
    φ.continuousOn_symm.comp continuous_subtype_val.continuousOn fun y hy => htgt y hy
  have hpc : Continuous fun w : Fin n → ℝ => pairing g p w w := by
    have : (fun w : Fin n → ℝ => pairing g p w w) = fun w => matForm (g p) w w :=
      funext fun w => pairing_eq_matForm g p w w
    rw [this]; exact (matForm (g p)).continuous.clm_apply continuous_id
  have hec : Continuous fun w : Fin n → ℝ => -pairing g p e w := by
    have : (fun w : Fin n → ℝ => -pairing g p e w) = fun w => -(matForm (g p) e w) :=
      funext fun w => by rw [pairing_eq_matForm]
    rw [this]; exact (matForm (g p) e).continuous.neg
  set fσ : U → ℝ := fun y => pairing g p (φ.symm y.1) (φ.symm y.1) with hfσ
  set fx : U → ℝ := fun y => -pairing g p e (φ.symm y.1) with hfx
  have hfσc : ContinuousOn fσ O' := hpc.comp_continuousOn hψ
  have hfxc : ContinuousOn fx O' := hec.comp_continuousOn hψ
  have hSO : S ⊆ O' := by
    rintro y ⟨γ, a, b, hab, -, -, hb, hin⟩; rw [← hb]; exact hin b ⟨hab, le_rfl⟩
  have hS : ∀ y ∈ S, fσ y ≤ 0 ∧ 0 ≤ fx y := fun y hy =>
    (h.mem_causalFutureIn_iff hL T hx₀ he (hSO hy)).1 hy
  have hqO : q ∈ O' := hq
  -- the closure lies in the closed cone
  have hcl : q ∈ closure S → fσ q ≤ 0 ∧ 0 ≤ fx q := by
    intro hqc
    have h1 := ((hfσc q hqO).mono hSO).mem_closure_image hqc
    have h2 := ((hfxc q hqO).mono hSO).mem_closure_image hqc
    exact ⟨closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact (hS y hy).1) isClosed_Iic h1,
      closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact (hS y hy).2) isClosed_Ici h2⟩
  -- the interior is the open cone
  have hint : q ∈ interior S ↔ fσ q < 0 ∧ 0 < fx q := by
    constructor
    · intro hqi
      by_contra hcon
      obtain ⟨w, hw, hφw⟩ := hq
      have hsw : φ.symm q.1 = w := by rw [← hφw]; exact φ.left_inv (h.mem_source hw)
      obtain ⟨hσ0, hx0⟩ := hS q (interior_subset hqi)
      simp only [hfσ, hfx, hsw] at hσ0 hx0 hcon
      have hnhds : Subtype.val '' S ∈ 𝓝 q.1 := by
        rw [← (U.isOpen.isOpenEmbedding_subtypeVal).map_nhds_eq]
        exact image_mem_map (mem_interior_iff_mem_nhds.1 hqi)
      have hB : φ ⁻¹' (Subtype.val '' S) ∈ 𝓝 w := by
        have hcont : ContinuousAt φ w :=
          h.chart.contDiffOn.continuousOn.continuousAt (φ.open_source.mem_nhds (h.mem_source hw))
        exact hcont.preimage_mem_nhds (by rw [hφw]; exact hnhds)
      have hballw : ball (0 : Fin n → ℝ) r ∈ 𝓝 w := isOpen_ball.mem_nhds hw
      have htend : Filter.Tendsto (fun s : ℝ => w - s • e) (𝓝[>] 0) (𝓝 w) := by
        have : Filter.Tendsto (fun s : ℝ => w - s • e) (𝓝 0) (𝓝 (w - (0 : ℝ) • e)) :=
          (continuous_const.sub (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have he := h.timelike_zero
      have hsymB : matForm (g p) w e = matForm (g p) e w := by
        rw [← pairing_eq_matForm, ← pairing_eq_matForm, pairing_comm hg hp]
      have hexp : ∀ s : ℝ, pairing g p (w - s • e) (w - s • e) =
          pairing g p w w - 2 * s * pairing g p e w + s ^ 2 * pairing g p e e := fun s => by
        simp only [pairing_eq_matForm, map_sub, map_smul, _root_.sub_apply, _root_.smul_apply,
          smul_eq_mul]
        linear_combination (-s) * hsymB
      have hxexp : ∀ s : ℝ, -pairing g p e (w - s • e) = -pairing g p e w + s * pairing g p e e :=
        fun s => by
          simp only [pairing_eq_matForm, map_sub, map_smul, smul_eq_mul]
          ring
      have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ,
          ¬ (pairing g p (w - s • e) (w - s • e) ≤ 0 ∧ 0 ≤ -pairing g p e (w - s • e)) := by
        by_cases hx0' : -pairing g p e w = 0
        · refine ⟨1, one_pos, fun s hs ⟨_, h2⟩ => ?_⟩
          rw [hxexp, hx0'] at h2
          nlinarith [mul_neg_of_pos_of_neg hs.1 he]
        · have hxpos : 0 < -pairing g p e w := lt_of_le_of_ne hx0 (Ne.symm hx0')
          have hσw : pairing g p w w = 0 :=
            le_antisymm hσ0 (not_lt.1 fun hlt => hcon ⟨hlt, hxpos⟩)
          have hY : 0 < -pairing g p e e := by linarith
          refine ⟨(-pairing g p e w) / (-pairing g p e e), div_pos hxpos hY,
            fun s hs ⟨h1, _⟩ => ?_⟩
          rw [hexp, hσw] at h1
          have hsY : s * (-pairing g p e e) < -pairing g p e w := by
            have := hs.2; rwa [lt_div_iff₀ hY] at this
          nlinarith [mul_lt_mul_of_pos_left hsY hs.1, mul_pos hs.1 hxpos]
      obtain ⟨δ, hδpos, hδ⟩ := hδ
      have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), w - s • e ∈ φ ⁻¹' (Subtype.val '' S) ∧
          w - s • e ∈ ball (0 : Fin n → ℝ) r ∧ s ∈ Ioo 0 δ :=
        (htend.eventually hB).and ((htend.eventually hballw).and (Ioo_mem_nhdsGT hδpos))
      obtain ⟨s, ⟨y, hyS, hyv⟩, hsb, hsI⟩ := hev.exists
      have hy := hS y hyS
      have hsy : φ.symm y.1 = w - s • e := by rw [hyv]; exact φ.left_inv (h.mem_source hsb)
      simp only [hfσ, hfx, hsy] at hy
      exact hδ s hsI hy
    · rintro ⟨h1, h2⟩
      have hW : IsOpen ((O' ∩ fσ ⁻¹' Iio 0) ∩ (O' ∩ fx ⁻¹' Ioi 0)) :=
        (hfσc.isOpen_inter_preimage hO'open isOpen_Iio).inter
          (hfxc.isOpen_inter_preimage hO'open isOpen_Ioi)
      refine mem_interior.2 ⟨_, ?_, hW, ⟨hqO, h1⟩, ⟨hqO, h2⟩⟩
      rintro y ⟨⟨hyO, hy1⟩, ⟨-, hy2⟩⟩
      exact (h.mem_causalFutureIn_iff hL T hx₀ he hyO).2 ⟨le_of_lt hy1, le_of_lt hy2⟩
  show q ∈ closure S \ interior S ↔ _
  rw [Set.mem_sdiff, hint]
  constructor
  · rintro ⟨hc, hni⟩
    obtain ⟨h1, h2⟩ := hcl hc
    refine ⟨le_antisymm h1 (not_lt.1 fun hlt => hni ⟨hlt, lt_of_le_of_ne h2 fun h0 => ?_⟩), h2⟩
    have h0' := h.eq_zero_of_cone hL hp h1 (by simp only [hfx] at h0; linarith)
    simp only [h0', pairing_zero_right] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨h1, h2⟩
    exact ⟨subset_closure ((h.mem_causalFutureIn_iff hL T hx₀ he hq).2 ⟨h1.le, h2⟩),
      fun ⟨hlt, _⟩ => lt_irrefl _ (h1 ▸ hlt)⟩

/-! ### The pasts -/

/-- The time ball of `-e`: the field is `-N`. -/
lemma neg (h : IsTimeBall g U p ρ φ e r N) : IsTimeBall g U p ρ φ (-e) r (fun v => -N v) where
  chart := h.chart
  pos := h.pos
  le := h.le
  timelike_zero := by simpa [pairing] using h.timelike_zero
  dual v hv w := by
    have := h.dual v hv w
    simp only [pairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this ⊢
    rw [this]
  timelike v hv := by simpa [pairing] using h.timelike v hv
  continuousOn := h.continuousOn.neg

/-- `-e` is future directed for the reversed orientation if `e` is for `T`. -/
lemma he_reverse (hL : IsLorentzianCoordMetric g U) (T : Causal.TimeOrientation (openMetric U g hL))
    {x₀ : U} (he : matForm (g p) e (T.X x₀) < 0) : matForm (g p) (-e) (T.reverse.X x₀) < 0 := by
  have hX : ∀ j, (T.reverse.X x₀ : Fin n → ℝ) j = -(T.X x₀ : Fin n → ℝ) j := fun j => rfl
  erw [matForm_apply] at he ⊢
  simp only [hX, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  exact he

lemma neg_pairing_neg (w : Fin n → ℝ) : -pairing g p (-e) w = -(-pairing g p e w) := by
  simp [pairing]

/-- **The `J⁻` line** ("the obvious analogue for pasts"): `q ∈ J⁻(p; O)` iff `σ_p(q) ≤ 0` and
`x⁰(q) ≤ 0`. -/
theorem mem_causalPastIn_iff (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    {x₀ : U} (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) {q : U}
    (hq : q.1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    q ∈ Causal.causalPastIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r} ↔
      pairing g p (φ.symm q.1) (φ.symm q.1) ≤ 0 ∧ -pairing g p e (φ.symm q.1) ≤ 0 := by
  rw [← Causal.causalFutureIn_reverse,
    h.neg.mem_causalFutureIn_iff hL T.reverse hx₀ (he_reverse hL T he) hq, neg_pairing_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- **The `I⁻` line**: `q ∈ I⁻(p; O)` iff `σ_p(q) < 0` and `x⁰(q) < 0`. -/
theorem mem_chronPastIn_iff (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    {x₀ : U} (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) {q : U}
    (hq : q.1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    q ∈ Causal.chronPastIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r} ↔
      pairing g p (φ.symm q.1) (φ.symm q.1) < 0 ∧ -pairing g p e (φ.symm q.1) < 0 := by
  rw [← Causal.chronFutureIn_reverse,
    h.neg.mem_chronFutureIn_iff hL T.reverse hx₀ (he_reverse hL T he) hq, neg_pairing_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- **The `J̇⁻` line**: `q` lies on the boundary of `J⁻(p; O)` iff `σ_p(q) = 0` and `x⁰(q) ≤ 0`. -/
theorem mem_frontier_causalPastIn_iff (hL : IsLorentzianCoordMetric g U)
    (T : Causal.TimeOrientation (openMetric U g hL)) (h : IsTimeBall g U p ρ φ e r N)
    {x₀ : U} (hx₀ : x₀.1 = p) (he : matForm (g p) e (T.X x₀) < 0) {q : U}
    (hq : q.1 ∈ φ '' ball (0 : Fin n → ℝ) r) :
    q ∈ frontier (Causal.causalPastIn T x₀ {y : U | y.1 ∈ φ '' ball (0 : Fin n → ℝ) r}) ↔
      pairing g p (φ.symm q.1) (φ.symm q.1) = 0 ∧ -pairing g p e (φ.symm q.1) ≤ 0 := by
  rw [← Causal.causalFutureIn_reverse,
    h.neg.mem_frontier_causalFutureIn_iff hL T.reverse hx₀ (he_reverse hL T he) hq,
    neg_pairing_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

end IsTimeBall

end Lightlike.Geodesic

import Lightlike.Spacetime.CausalLadder.LimitBound
import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.CausalLadder.LimitFunctional
import Lightlike.Spacetime.CausalLadder.Ascoli
import Lightlike.Spacetime.CausalLadder.Reparam
import Lightlike.Spacetime.CausalLadder.ChartCurve

/-!
# The limit-curve theorem in one chart (endpoint form)

Around every point `p` there is a neighbourhood `W` with the following property. Let `K ⊆ W` be
compact, and let `γₖ` be future-directed causal curves with values in `K` whose initial points
converge to `x ∈ K` and whose final points converge to `y ∈ K` (in the chart at `p`). Then there is a
future-directed causal curve in `K` from `x` to `y`; in particular `y ∈ J⁺(x)`.

This is the local, endpoint form of the limit-curve theorem (Hawking–Ellis, Lemma 6.2.1;
Beem–Ehrlich–Easley, Theorem 3.31; Minguzzi, *Lorentzian causality theory*, Section 2.4), which the
causal ladder uses to show that causal futures are closed in a chart box. The comparison with those
locations is pending: they were not read. The differences from the textbook form are the endpoint
form (curves with converging endpoints rather than a point of accumulation), the localisation to one
chart and a compact subset, and the regularity class of causal curves (locally Lipschitz with
almost-everywhere velocity in the closed cone, as in `Lightlike.Causal.IsCurveWith`).

The proof reparametrises the chart images by the time functional `ℓ` of the cone estimate, extracts
a uniformly convergent subsequence by Arzelà–Ascoli, and shows that the derivative of the limit lies
in the future causal cone using the frozen functional estimate and the self-duality of the cone.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Limit-curve theorem from a chart cone estimate.** The statement of `exists_limit_curve` for
any neighbourhood `W` of `p`, functional `ℓ` and constant `C` satisfying the cone estimate of
`exists_cone_estimate_curve`; the same `W`, `ℓ` and `C` can then be used to control the curves. -/
theorem limit_curve_of_cone_estimate (p : M) {W : Set M} (hWb : W ⊆ (tTriv I M p).baseSet)
    {ℓ : E →L[ℝ] ℝ} {C : ℝ} (hC : 0 < C)
    (hcone : ∀ q ∈ W, ∀ v : TangentSpace I q, T.IsFutureCausal v →
      ‖(tTriv I M p ⟨q, v⟩).2‖ ≤ C * ℓ (tTriv I M p ⟨q, v⟩).2)
    (hest : ∀ (γ : ℝ → M) (a b : ℝ), IsFutureCausalCurve T γ (Icc a b) → (∀ t ∈ Icc a b, γ t ∈ W) →
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
          ℓ (extChartAt I p (γ s)) ≤ ℓ (extChartAt I p (γ t)) ∧
          ‖extChartAt I p (γ t) - extChartAt I p (γ s)‖ ≤
            C * (ℓ (extChartAt I p (γ t)) - ℓ (extChartAt I p (γ s)))) :
    ∀ K : Set M, IsCompact K → K ⊆ interior W →
      ∀ (γ : ℕ → ℝ → M) (a b : ℕ → ℝ) (x y : M), x ∈ K → y ∈ K → (∀ k, a k ≤ b k) →
        (∀ k, IsFutureCausalCurve T (γ k) (Icc (a k) (b k))) →
        (∀ k, ∀ t ∈ Icc (a k) (b k), γ k t ∈ K) →
        Tendsto (fun k => extChartAt I p (γ k (a k))) atTop (𝓝 (extChartAt I p x)) →
        Tendsto (fun k => extChartAt I p (γ k (b k))) atTop (𝓝 (extChartAt I p y)) →
        ∃ (σ : ℝ → M) (α β : ℝ), α ≤ β ∧ IsFutureCausalCurve T σ (Icc α β) ∧ σ α = x ∧
          σ β = y := by
  intro K hK hKW γ a b x y hxK hyK hab hγ hKmem hxlim hylim
  set φ := extChartAt I p with hφ
  have hKsrc : ∀ q ∈ K, q ∈ φ.source := fun q hq => by
    rw [hφ, extChartAt_source]; exact hWb (interior_subset (hKW hq))
  -- finite dimensionality of the model space, from the Lorentzian frame at `p`
  have hfin : FiniteDimensional ℝ E := by
    obtain ⟨e, -⟩ := g.lorentzian p
    exact Module.Finite.of_basis (e.map ((tTriv I M p).linearEquivAt ℝ p
      (mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p)))
  -- chart images of the curves
  have hsrc : ∀ k, ∀ t ∈ Icc (a k) (b k), γ k t ∈ φ.source := fun k t ht => hKsrc _ (hKmem k t ht)
  have hLip : ∀ k, ∃ L, LipschitzOnWith L (φ ∘ γ k) (Icc (a k) (b k)) := fun k =>
    exists_lipschitzOnWith_chart_comp (hγ k).lipschitz p (hsrc k)
  have hcontc : ∀ k, ContinuousOn (fun t => φ (γ k t)) (Icc (a k) (b k)) := fun k =>
    (hLip k).choose_spec.continuousOn
  have hmono : ∀ k, ∀ s ∈ Icc (a k) (b k), ∀ t ∈ Icc (a k) (b k), s ≤ t →
      ℓ (φ (γ k s)) ≤ ℓ (φ (γ k t)) ∧ ‖φ (γ k t) - φ (γ k s)‖ ≤ C * (ℓ (φ (γ k t)) - ℓ (φ (γ k s))) :=
    fun k => hest (γ k) (a k) (b k) (hγ k) (fun t ht => interior_subset (hKW (hKmem k t ht)))
  -- reparametrisation through `ℓ`
  have hfac : ∀ k, ∃ f : ℝ → E, (∀ x y, ‖f x - f y‖ ≤ C * |x - y|) ∧
      (∀ t ∈ Icc (a k) (b k), f (ℓ (φ (γ k t))) = φ (γ k t)) ∧
      (∀ s, ∃ t ∈ Icc (a k) (b k), f s = φ (γ k t)) := fun k =>
    exists_lipschitz_factor hC (hab k) (hcontc k) (hmono k)
  choose f hflip hff hfr using hfac
  -- a bound for the values
  have hKc : IsCompact (φ '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt p).mono hKsrc)
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  have hfK : ∀ k σ, f k σ ∈ φ '' K := fun k σ => by
    obtain ⟨t, ht, e⟩ := hfr k σ
    exact ⟨γ k t, hKmem k t ht, e.symm⟩
  have hfR : ∀ k σ, ‖f k σ‖ ≤ R := fun k σ => hR _ (hfK k σ)
  -- endpoint values of `ℓ ∘ c`
  set α : ℝ := ℓ (φ x) with hα
  set β : ℝ := ℓ (φ y) with hβ
  have hαk : Tendsto (fun k => ℓ (φ (γ k (a k)))) atTop (𝓝 α) :=
    (ℓ.continuous.tendsto _).comp hxlim
  have hβk : Tendsto (fun k => ℓ (φ (γ k (b k)))) atTop (𝓝 β) :=
    (ℓ.continuous.tendsto _).comp hylim
  have hαβ : α ≤ β := le_of_tendsto_of_tendsto' hαk hβk fun k =>
    (hmono k (a k) ⟨le_rfl, hab k⟩ (b k) ⟨hab k, le_rfl⟩ (hab k)).1
  -- Arzelà–Ascoli
  obtain ⟨ψ, hψ, u, hulip, hconv⟩ :=
    exists_subseq_tendstoUniformlyOn hC α β f (fun k x y => hflip k x y) hfR
  have hpt : ∀ σ ∈ Icc α β, Tendsto (fun k => f (ψ k) σ) atTop (𝓝 (u σ)) := fun σ hσ =>
    hconv.tendsto_at hσ
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hu_in : ∀ σ ∈ Icc α β, u σ ∈ φ '' K := fun σ hσ =>
    hKc.isClosed.mem_of_tendsto (hpt σ hσ) (Eventually.of_forall fun k => hfK (ψ k) σ)
  -- the endpoints of the limit
  have hend : ∀ (σ₀ : ℝ) (e : ℕ → ℝ) (z : E), σ₀ ∈ Icc α β → Tendsto e atTop (𝓝 σ₀) →
      Tendsto (fun k => f (ψ k) (e (ψ k))) atTop (𝓝 z) → u σ₀ = z := by
    intro σ₀ e z hσ₀ he hz
    have h1 : Tendsto (fun k => f (ψ k) σ₀ - f (ψ k) (e (ψ k))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => hflip (ψ k) _ _) ?_
      have : Tendsto (fun k => |σ₀ - e (ψ k)|) atTop (𝓝 0) := by
        have := (he.comp hψtop).const_sub σ₀
        simpa using this.abs
      simpa using this.const_mul C
    have h2 : Tendsto (fun k => f (ψ k) σ₀) atTop (𝓝 z) := by
      simpa using h1.add hz |>.congr fun k => by simp
    exact tendsto_nhds_unique (hpt σ₀ hσ₀) h2
  have hxα : u α = φ x := by
    refine hend α (fun k => ℓ (φ (γ k (a k)))) (φ x) ⟨le_rfl, hαβ⟩ hαk ?_
    refine (hxlim.comp hψtop).congr fun k => ?_
    simp only [Function.comp_apply]
    exact (hff (ψ k) (a (ψ k)) ⟨le_rfl, hab _⟩).symm
  have hyβ : u β = φ y := by
    refine hend β (fun k => ℓ (φ (γ k (b k)))) (φ y) ⟨hαβ, le_rfl⟩ hβk ?_
    refine (hylim.comp hψtop).congr fun k => ?_
    simp only [Function.comp_apply]
    exact (hff (ψ k) (b (ψ k)) ⟨hab _, le_rfl⟩).symm
  -- the limit is parametrised by `ℓ`
  have hlu : ∀ σ ∈ Icc α β, ℓ (u σ) = σ := by
    intro σ hσ
    rcases hσ.1.eq_or_lt with h1 | h1
    · rw [← h1, hxα]
    rcases hσ.2.eq_or_lt with h2 | h2
    · rw [h2, hyβ]
    have hev : ∀ᶠ k in atTop, ℓ (f (ψ k) σ) = σ := by
      filter_upwards [(hαk.comp hψtop).eventually (Iio_mem_nhds h1),
        (hβk.comp hψtop).eventually (Ioi_mem_nhds h2)] with k hk1 hk2
      have hcl : ContinuousOn (fun t => ℓ (φ (γ (ψ k) t))) (Icc (a (ψ k)) (b (ψ k))) :=
        ℓ.continuous.comp_continuousOn (hcontc (ψ k))
      obtain ⟨t, ht, e⟩ := intermediate_value_Icc (hab (ψ k)) hcl ⟨hk1.le, hk2.le⟩
      rw [← e, hff (ψ k) t ht]
    have h3 : Tendsto (fun k => ℓ (f (ψ k) σ)) atTop (𝓝 (ℓ (u σ))) :=
      (ℓ.continuous.tendsto _).comp (hpt σ hσ)
    exact tendsto_nhds_unique h3 (tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm))
  have hulipw : LipschitzWith ⟨C, hC.le⟩ u := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, Real.dist_eq]; exact hulip x y
  -- the derivative of the limit lies in the future causal cone
  have hcausal : ∀ σ₀ ∈ Ioo α β, DifferentiableAt ℝ u σ₀ →
      T.IsFutureCausal ((tTriv I M p).symm (φ.symm (u σ₀)) (deriv u σ₀)) := by
    intro σ₀ hσ₀ hdiff
    obtain ⟨x₀, hx₀K, hx₀⟩ := hu_in σ₀ ⟨hσ₀.1.le, hσ₀.2.le⟩
    have hx₀' : φ.symm (u σ₀) = x₀ := by rw [← hx₀]; exact φ.left_inv (hKsrc x₀ hx₀K)
    rw [hx₀']
    have hDd : HasDerivAt u (deriv u σ₀) σ₀ := hdiff.hasDerivAt
    set D := deriv u σ₀ with hD
    have hx₀W : x₀ ∈ interior W := hKW hx₀K
    have hx₀b : x₀ ∈ (tTriv I M p).baseSet := hWb (interior_subset hx₀W)
    have hWnhds : W ∈ 𝓝 x₀ := mem_of_superset (isOpen_interior.mem_nhds hx₀W) interior_subset
    -- `ℓ D = 1`
    have hℓD : ℓ D = 1 := by
      have h1 : HasDerivAt (fun σ => ℓ (u σ)) (ℓ D) σ₀ := ℓ.hasFDerivAt.comp_hasDerivAt σ₀ hDd
      have h2 : HasDerivAt (fun σ => ℓ (u σ)) 1 σ₀ := by
        refine (hasDerivAt_id σ₀).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hσ₀.1 hσ₀.2] with σ hσ using hlu σ ⟨hσ.1.le, hσ.2.le⟩
      exact h1.unique h2
    have hD0 : D ≠ 0 := by
      intro h; rw [h] at hℓD; simp at hℓD
    refine isFutureCausal_of_forall_nonpos T p x₀ hx₀b hD0 ?_
    intro uu huu1 huu2
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set V : E := (tTriv I M p ⟨x₀, uu⟩).2 with hV
    have hUV : localField (I := I) p V x₀ = uu :=
      (tTriv I M p).symm_apply_apply_mk hx₀b uu
    obtain ⟨Φ, hΦ, r, hr, hmain⟩ := exists_reparam_bound T p x₀ hx₀b V
      (by rw [hUV]; exact huu1) (by rw [hUV]; exact huu2) hε hWb hC hcone hWnhds
    set h₀ : ℝ := (β - σ₀) / 2 with hh₀
    have hh₀pos : 0 < h₀ := by rw [hh₀]; linarith [hσ₀.2]
    have hconv' : TendstoUniformlyOn (fun k => f (ψ k)) u atTop (Icc σ₀ (σ₀ + h₀)) :=
      hconv.mono (Icc_subset_Icc hσ₀.1.le (by rw [hh₀]; linarith [hσ₀.2]))
    have hbound : ∀ᶠ k in atTop, ∀ σ₁ σ₂, σ₀ ≤ σ₁ → σ₁ ≤ σ₂ → σ₂ ≤ σ₀ + h₀ →
        (∀ σ ∈ Icc σ₁ σ₂, ‖f (ψ k) σ - u σ₀‖ < r) →
          Φ (f (ψ k) σ₂ - f (ψ k) σ₁) ≤ ε * (σ₂ - σ₁) := by
      have hlt : σ₀ + h₀ < β := by rw [hh₀]; linarith [hσ₀.2]
      filter_upwards [(hαk.comp hψtop).eventually (Iio_mem_nhds hσ₀.1),
        (hβk.comp hψtop).eventually (Ioi_mem_nhds hlt)] with k hk1 hk2
      intro σ₁ σ₂ h1 h12 h2 hball
      have hcl : ContinuousOn (fun t => ℓ (φ (γ (ψ k) t))) (Icc (a (ψ k)) (b (ψ k))) :=
        ℓ.continuous.comp_continuousOn (hcontc (ψ k))
      have hmem' : ∀ σ, σ₀ ≤ σ → σ ≤ σ₀ + h₀ →
          ∃ t ∈ Icc (a (ψ k)) (b (ψ k)), ℓ (φ (γ (ψ k) t)) = σ := fun σ hs1 hs2 =>
        intermediate_value_Icc (hab (ψ k)) hcl ⟨(show ℓ (φ (γ (ψ k) (a (ψ k)))) ≤ σ by
          simp only [Function.comp_apply] at hk1; linarith), (show σ ≤ ℓ (φ (γ (ψ k) (b (ψ k)))) by
          simp only [Function.comp_apply] at hk2; linarith)⟩
      have := hmain (hγ (ψ k)) (fun t ht => interior_subset (hKW (hKmem (ψ k) t ht)))
        (fun s hs t ht hst => (hmono (ψ k) s hs t ht hst).1) (hff (ψ k)) h12
        (hmem' σ₁ h1 (h12.trans h2)) (hmem' σ₂ (h1.trans h12) h2)
        (fun t ht hl1 hl2 => by
          have := hball (ℓ (φ (γ (ψ k) t))) ⟨hl1, hl2⟩
          rw [hff (ψ k) t ht, ← hx₀] at this
          exact this)
      rw [map_sub]; exact this
    have hΦD : Φ D ≤ ε :=
      functional_le_of_tendstoUniformlyOn hr hC hh₀pos (fun k => f (ψ k)) hulip hDd hconv' hbound
    have hd := hΦ ((tTriv I M p).symm x₀ D)
    rw [(tTriv I M p).apply_mk_symm hx₀b D, hUV] at hd
    simp only at hd
    linarith
  -- the limit curve in the manifold
  have htarget : ∀ σ ∈ Icc α β, u σ ∈ φ.target := fun σ hσ => by
    obtain ⟨q, hq, e⟩ := hu_in σ hσ
    rw [← e]; exact φ.map_source (hKsrc q hq)
  refine ⟨φ.symm ∘ u, α, β, hαβ, ⟨ordConnected_Icc, ?_, ?_⟩, ?_, ?_⟩
  · exact isLocallyLipschitzOn_chart_symm (hulipw.lipschitzOnWith) p htarget
  · rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hulipw.ae_differentiableAt_real, Measure.ae_ne volume α,
      Measure.ae_ne volume β] with σ hdiff hnα hnβ hσ
    have hσ' : σ ∈ Ioo α β := ⟨lt_of_le_of_ne hσ.1 (Ne.symm hnα), lt_of_le_of_ne hσ.2 hnβ⟩
    have hsd : UniqueDiffWithinAt ℝ (Icc α β) σ :=
      (uniqueDiffOn_Icc (hσ'.1.trans hσ'.2)) σ hσ
    obtain ⟨hmd, hcoord⟩ := mdifferentiableWithinAt_chart_symm p hsd hσ
      hdiff.hasDerivAt.hasDerivWithinAt htarget
    refine ⟨hmd, ?_⟩
    have hγb : (φ.symm ∘ u) σ ∈ (tTriv I M p).baseSet := by
      have : (φ.symm ∘ u) σ ∈ φ.source := φ.map_target (htarget σ hσ)
      simpa [hφ, extChartAt_source] using this
    have := (tTriv I M p).symm_apply_apply_mk hγb (velocity I (φ.symm ∘ u) (Icc α β) σ)
    rw [hcoord] at this
    show T.IsFutureCausal (velocity I (φ.symm ∘ u) (Icc α β) σ)
    rw [← this]
    exact hcausal σ hσ' hdiff
  · exact (φ.left_inv (hKsrc x hxK)) ▸ (by simp [hxα])
  · exact (φ.left_inv (hKsrc y hyK)) ▸ (by simp [hyβ])

/-- **Limit-curve theorem, endpoint form, in one chart** (Hawking–Ellis, Lemma 6.2.1, comparison
pending). Around `p` there is a neighbourhood `W` such that, for every compact `K ⊆ interior W`, if
future-directed causal curves `γ k` on `[a k, b k]` with values in `K` have initial points
`γ k (a k)` converging to `x ∈ K` and final points converging to `y ∈ K` in the chart at `p`, then
there is a future-directed causal curve `σ` on some `[α, β]` from `x` to `y`.

Differences from the textbook form: (a) endpoint form, with converging endpoints, not a limit curve
through a point of accumulation of an inextendible curve; (b) localised to one chart and a compact
subset of its domain; (c) the regularity class is the library's (`IsFutureCausalCurve`: locally
Lipschitz, velocity in the future causal cone almost everywhere), for which the closedness of the
cone condition is proved here; (d) no Hausdorff or second countability assumption is used. -/
theorem exists_limit_curve (p : M) :
    ∃ W ∈ 𝓝 p, W ⊆ (tTriv I M p).baseSet ∧ ∀ K : Set M, IsCompact K → K ⊆ interior W →
      ∀ (γ : ℕ → ℝ → M) (a b : ℕ → ℝ) (x y : M), x ∈ K → y ∈ K → (∀ k, a k ≤ b k) →
        (∀ k, IsFutureCausalCurve T (γ k) (Icc (a k) (b k))) →
        (∀ k, ∀ t ∈ Icc (a k) (b k), γ k t ∈ K) →
        Tendsto (fun k => extChartAt I p (γ k (a k))) atTop (𝓝 (extChartAt I p x)) →
        Tendsto (fun k => extChartAt I p (γ k (b k))) atTop (𝓝 (extChartAt I p y)) →
        ∃ (σ : ℝ → M) (α β : ℝ), α ≤ β ∧ IsFutureCausalCurve T σ (Icc α β) ∧ σ α = x ∧
          σ β = y := by
  obtain ⟨W, hW, hWb, ℓ, C, hC, hcone, hest⟩ := exists_cone_estimate_curve T p
  exact ⟨W, hW, hWb, limit_curve_of_cone_estimate T p hWb hC hcone hest⟩

/-- **A limit of causal futures stays in the causal future, in one chart.** The conclusion of
`exists_limit_curve` as membership `y ∈ J⁺(x)`. -/
theorem exists_limit_mem_causalFuture (p : M) :
    ∃ W ∈ 𝓝 p, W ⊆ (tTriv I M p).baseSet ∧ ∀ K : Set M, IsCompact K → K ⊆ interior W →
      ∀ (γ : ℕ → ℝ → M) (a b : ℕ → ℝ) (x y : M), x ∈ K → y ∈ K → (∀ k, a k ≤ b k) →
        (∀ k, IsFutureCausalCurve T (γ k) (Icc (a k) (b k))) →
        (∀ k, ∀ t ∈ Icc (a k) (b k), γ k t ∈ K) →
        Tendsto (fun k => extChartAt I p (γ k (a k))) atTop (𝓝 (extChartAt I p x)) →
        Tendsto (fun k => extChartAt I p (γ k (b k))) atTop (𝓝 (extChartAt I p y)) →
          y ∈ causalFuture T x := by
  obtain ⟨W, hW, hWb, h⟩ := exists_limit_curve T p
  refine ⟨W, hW, hWb, fun K hK hKW γ a b x y hx hy hab hγ hmem hxl hyl => ?_⟩
  obtain ⟨σ, α, β, hαβ, hσ, h1, h2⟩ := h K hK hKW γ a b x y hx hy hab hγ hmem hxl hyl
  exact ⟨σ, α, β, hαβ, hσ, h1, h2⟩

/-- **Non-vacuity.** The hypotheses of `exists_limit_curve` hold for the constant sequence of
constant curves at `p`, with `K = {p}`: the limit curve is then a constant curve at `p`. -/
theorem exists_limit_curve_const (p : M) : p ∈ causalFuture T p := by
  obtain ⟨W, hW, hWb, h⟩ := exists_limit_mem_causalFuture T p
  have hK : ({p} : Set M) ⊆ interior W := by
    intro q hq; rw [mem_singleton_iff.1 hq]; exact mem_interior_iff_mem_nhds.2 hW
  exact h {p} isCompact_singleton hK (fun _ _ => p) (fun _ => 0) (fun _ => 0) p p rfl rfl
    (fun _ => le_rfl) (fun _ => isCurveWith_const _ p 0) (fun _ t _ => rfl)
    tendsto_const_nhds tendsto_const_nhds

end Lightlike.Causal

import Lightlike.Spacetime.EHManifold.Locality
import Lightlike.Spacetime.EHManifold.PieceAction
import Lightlike.Spacetime.EHManifold.IntrinsicVariation
import Lightlike.Spacetime.EHManifold.ManifoldDivergence
import Lightlike.Spacetime.EHManifold.PerturbationCovDeriv
import Lightlike.Spacetime.EHManifold.CompactVariation

/-!
# The first variation of the Einstein–Hilbert action on a region of a manifold (M16, step 2)

Over a measurable piece `A` of a compact set in a small coordinate ball, `hasDerivAt_ehAction_piece` gives the
derivative of the Einstein–Hilbert action as the chart integral `pieceVar` of `-√|g| ⟨E, h⟩ + ∂ⱼ(√|g| Wʲ)`, for the
metric retracted to the ball. `pieceVar_intrinsic`: this is
`∫_A (-⟨G + Λ g, h⟩_g + div_g V(h)) d vol_g`, with `V(h)` the boundary vector field of the variation
(`palatiniField`). The proof: on the inner ball the retracted metric and perturbation agree with the chart components
near every point, and the integrand depends only on their germs (`ehFluxDiv_congr`, `ricciUp_congr`).

`eh_variation_region_manifold`: for a measurable region `D` of the manifold and `h` vanishing outside a compact set `K`,
`d/dt ∫_{D ∩ K} (R(g + t h) - 2Λ) d vol_{g + t h} = ∫_{D ∩ K} (-⟨G + Λ g, h⟩_g + div_g V(h)) d vol_g` at `t = 0`. The
proof cuts `D ∩ K` into disjoint measurable pieces inside small chart balls (the cover of `eh_first_variation_manifold_compact`,
intersected with `D`) and sums `pieceVar_intrinsic`; no integration by parts is needed, since the pieces are disjoint and
`V(h)` is one vector field.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric Bundle
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

section Germ

variable {n : ℕ} {g g' h h' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}

/-- The variation of the Christoffel symbols depends only on the germs of `g` and `h`. -/
theorem dChristoffel_eventuallyEq (hg : g =ᶠ[𝓝 x] g') (hh : h =ᶠ[𝓝 x] h') (i j k : Fin n) :
    dChristoffel g h i j k =ᶠ[𝓝 x] dChristoffel g' h' i j k := by
  have hpg : ∀ a b c : Fin n, pd a (fun y => g y b c) =ᶠ[𝓝 x] pd a (fun y => g' y b c) := fun a b c =>
    pd_eventuallyEq (eventuallyEq_entry hg b c) a
  have hph : ∀ a b c : Fin n, pd a (fun y => h y b c) =ᶠ[𝓝 x] pd a (fun y => h' y b c) := fun a b c =>
    pd_eventuallyEq (eventuallyEq_entry hh b c) a
  have hall : ∀ᶠ y in 𝓝 x, g y = g' y ∧ h y = h' y ∧
      (∀ a b c : Fin n, pd a (fun z => g z b c) y = pd a (fun z => g' z b c) y) ∧
      (∀ a b c : Fin n, pd a (fun z => h z b c) y = pd a (fun z => h' z b c) y) :=
    hg.and (hh.and ((eventually_all.2 fun a => eventually_all.2 fun b => eventually_all.2 fun c => hpg a b c).and
      (eventually_all.2 fun a => eventually_all.2 fun b => eventually_all.2 fun c => hph a b c)))
  exact hall.mono fun y hy => by
    show dChristoffel g h i j k y = dChristoffel g' h' i j k y
    unfold dChristoffel
    simp only [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

/-- The boundary vector `W` depends only on the germs of `g` and `h`. -/
theorem Wvec_eventuallyEq (hg : g =ᶠ[𝓝 x] g') (hh : h =ᶠ[𝓝 x] h') (ρ : Fin n) :
    Wvec g h ρ =ᶠ[𝓝 x] Wvec g' h' ρ := by
  have hall : ∀ᶠ y in 𝓝 x, g y = g' y ∧ ∀ i j k : Fin n, dChristoffel g h i j k y = dChristoffel g' h' i j k y :=
    hg.and (eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
      dChristoffel_eventuallyEq hg hh i j k)
  exact hall.mono fun y hy => by
    show Wvec g h ρ y = Wvec g' h' ρ y
    unfold Wvec
    simp only [hy.1, hy.2]

/-- The divergence term `∂ᵨ(√|g| Wᵖ)` at `x` depends only on the germs of `g` and `h` at `x`. -/
theorem ehFluxDiv_congr (hg : g =ᶠ[𝓝 x] g') (hh : h =ᶠ[𝓝 x] h') : ehFluxDiv g h x = ehFluxDiv g' h' x := by
  unfold ehFluxDiv
  refine Finset.sum_congr rfl fun ρ _ => (pd_eventuallyEq ?_ ρ).eq_of_nhds
  exact (hg.and (Wvec_eventuallyEq hg hh ρ)).mono fun y hy => by
    show √|(g y).det| * Wvec g h ρ y = √|(g' y).det| * Wvec g' h' ρ y
    rw [hy.1, hy.2]

/-- The raised Ricci tensor at `x` depends only on the germ of `g` at `x`. -/
theorem ricciUp_congr (hg : g =ᶠ[𝓝 x] g') (α β : Fin n) : ricciUp g x α β = ricciUp g' x α β := by
  unfold ricciUp
  simp only [ricci_congr hg, hg.eq_of_nhds]

/-- The coordinate expansion at `x` depends only on the germ of the field at `x`. -/
theorem expansion_congr {v w : (Fin n → ℝ) → Fin n → ℝ} (hvw : v =ᶠ[𝓝 x] w) :
    expansion g v x = expansion g w x := by
  unfold expansion covD
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(pd_eventuallyEq (hvw.mono fun y hy => by rw [hy]) a).eq_of_nhds, hvw.eq_of_nhds]

end Germ

section Piece

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
  {c : Fin n → ℝ} (φ : ContDiffBump c)

/-- `pieceVar` with the chart components themselves in place of the retracted ones. -/
theorem pieceVar_eq_chart (Λ : ℝ) {T A : Set M} (hT : IsCompact T) (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hTball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ ball c φ.rIn) (hA : MeasurableSet A) (hAT : A ⊆ T) :
    pieceVar g h x₀ φ Λ T A =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A,
        (-√|(g.coordMetric x₀ y).det| * ∑ α, ∑ β, h.coordComp x₀ y α β *
            (ricciUp (g.coordMetric x₀) y α β -
              (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
              Λ * (g.coordMetric x₀ y)⁻¹ α β) +
          ehFluxDiv (g.coordMetric x₀) (h.coordComp x₀) y) := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A ⊆ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T := image_mono hAT
  unfold pieceVar
  rw [Measure.restrict_restrict hTc.measurableSet, inter_eq_right.2 hsub]
  refine setIntegral_congr_fun (measurableSet_image_extChartAt x₀ hA (hAT.trans hT0)) fun y hy => ?_
  have hyb := hTball (hsub hy)
  have hG : g.coordMetricR x₀ φ =ᶠ[𝓝 y] g.coordMetric x₀ := eventuallyEq_comp_ballRetract φ _ hyb
  have hH : h.coordCompR x₀ φ =ᶠ[𝓝 y] h.coordComp x₀ := eventuallyEq_comp_ballRetract φ _ hyb
  simp only [hG.eq_of_nhds, hH.eq_of_nhds, ricciUp_congr hG, scalarCurvature_congr hG, ehFluxDiv_congr hG hH]

/-- **The derivative over a piece, in intrinsic form**: `pieceVar = ∫_A (-⟨G + Λ g, h⟩_g + div_g V(h)) d vol_g`. -/
theorem pieceVar_intrinsic (Λ : ℝ) {T A : Set M} (hT : IsCompact T)
    (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hTball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ ball c φ.rIn) (hA : MeasurableSet A) (hAT : A ⊆ T) :
    pieceVar g h x₀ φ Λ T A =
      ∫ p in A, (-ehIntegrand g h Λ p + expansionM (leviCivita g) (palatiniField g h) p)
        ∂(NondegMetric.volumeMeasure g) := by
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hV := contMDiff_palatiniField g h
  have hA0 : A ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := hAT.trans hT0
  have hcont : ContinuousOn (fun p => -ehIntegrand g h Λ p + expansionM (leviCivita g) (palatiniField g h) p)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (continuousOn_ehIntegrand g h Λ x₀).neg.add (continuousOn_expansionM (leviCivita g) g hLC hV x₀)
  rw [pieceVar_eq_chart g h x₀ φ Λ hT hT0 hTball hA hAT,
    NondegMetric.setIntegral_volumeMeasure_chart g x₀ hA hA0 _ ((hcont.mono hA0).aestronglyMeasurable hA)]
  refine setIntegral_congr_fun (measurableSet_image_extChartAt x₀ hA hA0) fun y hy => ?_
  have hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    obtain ⟨p, hp, rfl⟩ := hy
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hA0 hp)
  have hgc := g.isCoordMetric_coordMetric x₀
  have hcomp : chartComp x₀ (palatiniField g h) =ᶠ[𝓝 y] pvec g h x₀ := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds hyt] with z hz
    have hzs := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_target hz
    show hv x₀ _ (palatiniField g h _) = _
    rw [hv_palatiniField g h hzs, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hz]
  have hexp : expansionM (leviCivita g) (palatiniField g h) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      expansion (g.coordMetric x₀) (pvec g h x₀) y := by
    rw [expansionM_eq (leviCivita g) g hLC hV x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_target hyt),
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hyt]
    exact expansion_congr hcomp
  have hdiv : √|(g.coordMetric x₀ y).det| * expansion (g.coordMetric x₀) (pvec g h x₀) y =
      ehFluxDiv (g.coordMetric x₀) (h.coordComp x₀) y := by
    rw [sqrt_det_mul_expansion hgc (fun a => (contDiffOn_pi.1 (contDiffOn_pvec g h x₀)) a) hyt]
    rfl
  rw [ehIntegrand_chart g h Λ x₀ hyt, hexp, NondegMetric.volDensity, mul_add, hdiv]
  ring

end Piece

section Region

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)

/-- **The first variation of the Einstein–Hilbert action on a region of a manifold**: for a measurable `D` and a
perturbation `h` vanishing outside a compact set `K`,
`d/dt ∫_{D ∩ K} (R(g + t h) - 2Λ) d vol_{g + t h} = ∫_{D ∩ K} (-⟨G + Λ g, h⟩_g + div_g V(h)) d vol_g` at `t = 0`,
with `V(h)` the boundary vector field of the variation. -/
theorem eh_variation_region_manifold {K : Set M} (hK : IsCompact K) (hsupp : ∀ p, p ∉ K → h.h p = 0)
    {D : Set M} (hD : MeasurableSet D) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ (D ∩ K))
      (∫ p in D ∩ K, (-ehIntegrand g h Λ p + expansionM (leviCivita g) (palatiniField g h) p)
        ∂(NondegMetric.volumeMeasure g)) 0 := by
  classical
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hV := contMDiff_palatiniField g h
  rcases isEmpty_or_nonempty M with hM | hM
  · have hKe : D ∩ K = ∅ := Set.eq_empty_of_isEmpty _
    simp only [hKe, ehAction, Measure.restrict_empty, integral_zero_measure]
    exact hasDerivAt_const 0 0
  obtain ⟨p₀⟩ := hM
  obtain ⟨ε, hε, hnd⟩ := g.exists_addSmul_nondegenerate h hK hsupp
  have hrex : ∀ p : M, ∃ r > 0, ball (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) r ⊆
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target := fun p =>
    Metric.isOpen_iff.1 (isOpen_extChartAt_target p) _ (mem_extChartAt_target p)
  choose r hr0 hrball using hrex
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun p => coverU n p (r p)) (fun p _ => coverU_mem_nhds (n := n) p (hr0 p))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = t.toList.length := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → M, x = fun k => t.toList.getD k p₀ := ⟨_, rfl⟩
  have hcov : ∀ q ∈ K, ∃ k, k < N ∧ q ∈ coverU n (x k) (r (x k)) := by
    intro q hq
    obtain ⟨p, hp, hqU⟩ := mem_iUnion₂.1 (htK hq)
    obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem (Finset.mem_toList.2 hp)
    refine ⟨k, by rw [hN]; exact hk, ?_⟩
    have hxk : x k = p := by
      rw [hx]
      show t.toList.getD k p₀ = p
      rw [List.getD_eq_getElem _ _ hk, hkp]
    rw [hxk]
    exact hqU
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → Set M, T = fun k => coverC n (x k) (r (x k)) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Set M, F = fun k => if k < N then D ∩ K ∩ T k else ∅ := ⟨_, rfl⟩
  have hTc : ∀ k, IsCompact (T k) := fun k => by
    rw [hTdef]; exact isCompact_coverC (n := n) (x k) (hr0 _) (hrball _)
  have hT0 : ∀ k, T k ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k)).source := fun k => by
    rw [hTdef]; exact coverC_subset_source (n := n) (x k) (hr0 _) (hrball _)
  have hTb : ∀ k, extChartAt 𝓘(ℝ, Fin n → ℝ) (x k) '' T k ⊆
      ball (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k) (x k)) (coverBump (n := n) (x k) (r (x k)) (hr0 _)).rIn := fun k => by
    rw [hTdef]; exact image_coverC_subset (n := n) (x k) (hr0 _) (hrball _)
  have hFsub : ∀ k, F k ⊆ D ∩ K ∩ T k := fun k => by
    rw [hF]
    by_cases hk : k < N
    · simp only [hk, ite_true]; exact subset_rfl
    · simp only [hk, ite_false]; exact empty_subset _
  have hFm : ∀ k, MeasurableSet (F k) := fun k => by
    rw [hF]
    by_cases hk : k < N
    · simp only [hk, ite_true]; exact (hD.inter hK.measurableSet).inter (hTc k).measurableSet
    · simp only [hk, ite_false]; exact MeasurableSet.empty
  have hFN : ∀ k, ¬ k < N → F k = ∅ := fun k hk => by
    rw [hF]; simp only [hk, ite_false]
  have hAm : ∀ k, MeasurableSet (disjointed F k) := fun k => MeasurableSet.disjointed hFm k
  have hAT : ∀ k, disjointed F k ⊆ T k := fun k => ((disjointed_le F k).trans (hFsub k)).trans inter_subset_right
  have hAd : Set.Pairwise (↑(Finset.range N)) (Function.onFun Disjoint (disjointed F)) :=
    fun i _ j _ hij => disjoint_disjointed F hij
  have hDK : D ∩ K = ⋃ k ∈ Finset.range N, disjointed F k := by
    ext q
    constructor
    · intro hq
      obtain ⟨k, hk, hqU⟩ := hcov q hq.2
      have hqF : q ∈ ⋃ k, F k := by
        refine mem_iUnion.2 ⟨k, ?_⟩
        rw [hF]
        simp only [hk, ite_true]
        refine ⟨hq, ?_⟩
        rw [hTdef]
        exact coverU_subset_coverC (n := n) _ hqU
      rw [← iUnion_disjointed] at hqF
      obtain ⟨j, hj⟩ := mem_iUnion.1 hqF
      have hjN : j < N := by
        by_contra hjN
        have := disjointed_le F j hj
        rw [hFN j hjN] at this
        exact this
      exact mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hjN, hj⟩
    · intro hq
      obtain ⟨k, -, hqk⟩ := mem_iUnion₂.1 hq
      exact ((disjointed_le F k).trans (hFsub k) hqk).1
  -- the action over `D ∩ K` is the sum over the pieces
  have hfun : (fun t : ℝ => ehAction (g.perturb h t) Λ (D ∩ K)) =
      fun t => ∑ k ∈ Finset.range N, ehAction (g.perturb h t) Λ (disjointed F k) := by
    funext s
    rw [hDK]
    exact ehAction_biUnion (g.perturb h s) Λ (Finset.range N) (disjointed F) T x (fun k _ => hAm k) hAd
      (fun k _ => hTc k) (fun k _ => hT0 k) (fun k _ => hAT k)
  -- the integrand is integrable on every piece
  have hcont : ∀ k, ContinuousOn (fun p => -ehIntegrand g h Λ p + expansionM (leviCivita g) (palatiniField g h) p)
      (T k) := fun k =>
    ((continuousOn_ehIntegrand g h Λ (x k)).neg.add (continuousOn_expansionM (leviCivita g) g hLC hV (x k))).mono
      (hT0 k)
  have hint : ∫ p in D ∩ K, (-ehIntegrand g h Λ p + expansionM (leviCivita g) (palatiniField g h) p)
      ∂(NondegMetric.volumeMeasure g) = ∑ k ∈ Finset.range N,
        ∫ p in disjointed F k, (-ehIntegrand g h Λ p + expansionM (leviCivita g) (palatiniField g h) p)
          ∂(NondegMetric.volumeMeasure g) := by
    rw [hDK]
    exact integral_biUnion_finset (Finset.range N) (fun k _ => hAm k) hAd fun k _ =>
      g.integrableOn_of_continuousOn (x k) (hTc k) (hT0 k) (hcont k) (hAT k)
  rw [hfun, hint]
  refine HasDerivAt.fun_sum fun k _ => ?_
  rw [← pieceVar_intrinsic g h (x k) (coverBump (n := n) (x k) (r (x k)) (hr0 _)) Λ (hTc k) (hT0 k) (hTb k) (hAm k) (hAT k)]
  exact hasDerivAt_ehAction_piece g h (x k) (coverBump (n := n) (x k) (r (x k)) (hr0 _)) (hrball (x k)) (hTc k) (hT0 k)
    (hTb k) (hAm k) (hAT k) Λ hε hnd

end Region

end Lightlike

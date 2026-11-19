import Lightlike.GR.KruskalExtension
import Lightlike.GR.KruskalGeodesicBound
import Lightlike.Spacetime.GeodesicChartChange

/-!
# No geodesic of an extension leaves the Kruskal manifold

Gap row G1-020, toward maximality. Let `ι` be an extension of the Kruskal manifold into a Hausdorff Lorentzian
manifold `(M', g')` and `p ∈ M'`. A geodesic `σ` of `g'` in the chart at `p`, defined on `(-1, 2)` and staying
in the chart on `[0, 1]`, that starts in the image of `ι` cannot leave it
(`IsLorentzianExtension.false_of_geodesic_kruskal`).

Proof. Let `b` be the first time at which `σ` is outside the image. On `[0, b)` the curve lifts to a geodesic `c`
of the Kruskal manifold (`IsGeodesicOn.lift_chartChange`). If the radius is bounded below along `c`, then `c` has
a limit in the Kruskal manifold at `b` (`exists_tendsto_kruskalC_geodesic`), whose image is `σ b`: a
contradiction. Otherwise a sequence of points of `c` approaches the singularity while its image converges in
`M'`, which `IsLorentzianExtension.not_tendsto_kruskal` excludes.
-/

open Matrix Real Set Filter Topology Manifold TopologicalSpace
open scoped ContDiff

noncomputable section

namespace Lightlike

open Lightlike.Geodesic

variable {M : ℝ} {M' : Type*} [TopologicalSpace M'] [ChartedSpace (Fin 4 → ℝ) M']
  [IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ M']

open Classical in
/-- **A geodesic of an extension that starts in the Kruskal manifold does not leave it.** -/
theorem IsLorentzianExtension.false_of_geodesic_kruskal [T2Space M'] (hM : 0 < M)
    {g' : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M' 4} {ι : kruskalCOpen → M'}
    (hext : IsLorentzianExtension (kruskalManifoldMetric M hM) g' ι) (p : M')
    {σ wσ : ℝ → Fin 4 → ℝ} (hσ : IsGeodesicOn (g'.coordMetric p) σ wσ (Ioo (-1) 2))
    (hσU : ∀ s ∈ Icc (0 : ℝ) 1, σ s ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p).target)
    (h0 : (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p).symm (σ 0) ∈ range ι)
    (h1 : (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p).symm (σ 1) ∉ range ι) : False := by
  set e := extChartAt 𝓘(ℝ, Fin 4 → ℝ) p with he
  set ψ := extChartMap kruskalCOpen ι p with hψdef
  set Dom := extChartDom kruskalCOpen ι p with hDom
  have hL := kruskalC_isLorentzian M hM
  have hK0 := isCoordMetric_kruskalC M hM
  have hch : IsChartChange ψ Dom e.target :=
    isChartChange_extChartMap kruskalCOpen ι p (kruskalCMetric M) hL g' hext.contMDiff hext.isometric
  have hG := g'.isCoordMetric_coordMetric p
  have hpull : ∀ y ∈ Dom, pullback (g'.coordMetric p) ψ y = kruskalCMetric M y := fun y hy =>
    pullback_coordMetric_extChartMap kruskalCOpen ι p (kruskalCMetric M) hL g' hext.contMDiff
      hext.isometric hy
  have hDomsub : Dom ⊆ kruskalC := fun y hy => hy.1
  have hK : IsCoordMetric (kruskalCMetric M) Dom :=
    ⟨hch.isOpen, fun x hx => hK0.symm x (hDomsub hx), fun x hx => hK0.isUnit_det x (hDomsub hx),
      fun i j => (hK0.smooth i j).mono hDomsub⟩
  have hψ : ∀ (y : Fin 4 → ℝ) (h : y ∈ kruskalC), ψ y = e (ι ⟨y, h⟩) := fun y h =>
    extChartMap_apply kruskalCOpen ι p ⟨y, h⟩
  have hinj : InjOn ψ Dom := by
    rintro y1 ⟨h1', hs1⟩ y2 ⟨h2', hs2⟩ heq
    rw [hψ y1 h1', hψ y2 h2'] at heq
    have h3 := hext.isOpenEmbedding.injective (e.injOn hs1 hs2 heq)
    exact congrArg Subtype.val h3
  -- the image of `ι` in the chart
  set A : Set (Fin 4 → ℝ) := e.target ∩ e.symm ⁻¹' range ι with hA
  have hAopen : IsOpen A :=
    (continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p)
      hext.isOpenEmbedding.isOpen_range
  have hlift : ∀ y ∈ A, ∃ z ∈ Dom, ψ z = y := by
    rintro y ⟨hy, ⟨x, hx⟩⟩
    have hsrc : ι x ∈ e.source := by rw [hx]; exact e.map_target hy
    refine ⟨x.1, ⟨x.2, hsrc⟩, ?_⟩
    rw [hψ x.1 x.2]
    show e (ι x) = y
    rw [hx]
    exact e.right_inv hy
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-1) 2 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hσc : ContinuousOn σ (Ioo (-1) 2) := fun s hs =>
    (hσ.pos s hs).continuousAt.continuousWithinAt
  have hcomp : ContinuousOn (fun s => e.symm (σ s)) (Icc 0 1) :=
    (continuousOn_extChartAt_symm p).comp (hσc.mono hIcc) fun s hs => hσU s hs
  -- the first exit time
  set N : Set ℝ := Icc 0 1 ∩ σ ⁻¹' Aᶜ with hN
  have hNclosed : IsClosed N :=
    (hσc.mono hIcc).preimage_isClosed_of_isClosed isClosed_Icc hAopen.isClosed_compl
  have h1N : (1 : ℝ) ∈ N := ⟨⟨zero_le_one, le_rfl⟩, fun hA' => h1 hA'.2⟩
  have hbdd : BddBelow N := ⟨0, fun s hs => hs.1.1⟩
  set b := sInf N with hb
  have hbN : b ∈ N := hNclosed.csInf_mem ⟨1, h1N⟩ hbdd
  have h0A : σ 0 ∈ A := ⟨hσU 0 ⟨le_rfl, zero_le_one⟩, h0⟩
  have hb0 : 0 < b := by
    refine lt_of_le_of_ne hbN.1.1 fun h => hbN.2 ?_
    rw [← h]
    exact h0A
  have hIco : ∀ s ∈ Ico 0 b, σ s ∈ A := fun s hs => by
    by_contra hA'
    have : s ∈ N := ⟨⟨hs.1, hs.2.le.trans hbN.1.2⟩, hA'⟩
    exact absurd (csInf_le hbdd this) (not_le.2 hs.2)
  set O : Set ℝ := Ioo (-1) 2 ∩ σ ⁻¹' A with hOdef
  have hO : IsOpen O := hσc.isOpen_inter_preimage isOpen_Ioo hAopen
  have hIcoO : Ico 0 b ⊆ O := fun s hs => ⟨hIcc ⟨hs.1, hs.2.le.trans hbN.1.2⟩, hIco s hs⟩
  -- the lift
  set c : ℝ → Fin 4 → ℝ := fun s => if h : σ s ∈ A then (hlift (σ s) h).choose else 0 with hc
  have hcspec : ∀ s ∈ O, c s ∈ Dom ∧ ψ (c s) = σ s := fun s hs => by
    have : c s = (hlift (σ s) hs.2).choose := dif_pos hs.2
    rw [this]
    exact (hlift (σ s) hs.2).choose_spec
  have hσO : IsGeodesicOn (g'.coordMetric p) σ wσ O :=
    ⟨fun t ht => hσ.pos t ht.1, fun t ht => hσ.vel t ht.1⟩
  have hgeoO := IsGeodesicOn.lift_chartChange hG hK hch hpull hinj hO hσO
    (fun s hs => (hcspec s hs).1) (fun s hs => (hcspec s hs).2)
  set u : ℝ → Fin 4 → ℝ := fun s => (jac ψ (c s))⁻¹ *ᵥ wσ s with hu
  have hgeo : IsGeodesicOn (kruskalCMetric M) c u (Ico 0 b) :=
    ⟨fun t ht => hgeoO.pos t (hIcoO ht), fun t ht => hgeoO.vel t (hIcoO ht)⟩
  have hcK : ∀ s ∈ Ico 0 b, c s ∈ kruskalC := fun s hs => hDomsub (hcspec s (hIcoO hs)).1
  have hιc : ∀ s ∈ Ico 0 b, ∀ h : c s ∈ kruskalC, ι ⟨c s, h⟩ = e.symm (σ s) := fun s hs h => by
    obtain ⟨hd, hψs⟩ := hcspec s (hIcoO hs)
    obtain ⟨h', hsrc⟩ := hd
    rw [← hψs, hψ (c s) h]
    exact (e.left_inv hsrc).symm
  by_cases hbd : ∃ r0 > 0, ∀ s ∈ Ico 0 b, r0 ≤ krC M (c s)
  · -- the radius is bounded below: the lift has a limit, whose image is `σ b`
    obtain ⟨r0, hr0, hr⟩ := hbd
    obtain ⟨z, hz, hzlim⟩ := exists_tendsto_kruskalC_geodesic hM hb0 hgeo hcK hr0 hr
    have hI : Ico 0 b ∈ 𝓝[<] b := Ico_mem_nhdsLT hb0
    set cS : ℝ → kruskalCOpen := fun s => if h : c s ∈ kruskalC then ⟨c s, h⟩ else ⟨z, hz⟩ with hcS
    have hcSlim : Tendsto cS (𝓝[<] b) (𝓝 ⟨z, hz⟩) := by
      rw [tendsto_subtype_rng]
      refine hzlim.congr' ?_
      filter_upwards [hI] with s hs
      simp only [hcS, dif_pos (hcK s hs)]
    have e1 : Tendsto (fun s => ι (cS s)) (𝓝[<] b) (𝓝 (ι ⟨z, hz⟩)) :=
      (hext.isOpenEmbedding.continuous.tendsto _).comp hcSlim
    have e2 : Tendsto (fun s => ι (cS s)) (𝓝[<] b) (𝓝 (e.symm (σ b))) := by
      have hcw := hcomp b hbN.1
      have ht : Tendsto (fun s : ℝ => s) (𝓝[<] b) (𝓝[Icc 0 1] b) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_id.mono_left nhdsWithin_le_nhds, by
          filter_upwards [hI] with s hs
          exact ⟨hs.1, hs.2.le.trans hbN.1.2⟩⟩
      refine (hcw.tendsto.comp ht).congr' ?_
      filter_upwards [hI] with s hs
      simp only [Function.comp, hcS, dif_pos (hcK s hs)]
      exact (hιc s hs (hcK s hs)).symm
    have h3 := tendsto_nhds_unique e1 e2
    exact hbN.2 ⟨hσU b hbN.1, ⟨_, h3⟩⟩
  · -- the radius is not bounded below: a sequence approaches the singularity
    push_neg at hbd
    choose s hsI hsr using fun k : ℕ => hbd (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨sstar, hsstar, φ, hφ, hφlim⟩ := isCompact_Icc.tendsto_subseq
      (fun k => (⟨(hsI k).1, (hsI k).2.le.trans hbN.1.2⟩ : s k ∈ Icc (0 : ℝ) 1))
    set zs : ℕ → kruskalCOpen := fun k => ⟨c (s (φ k)), hcK _ (hsI (φ k))⟩ with hzs
    have hlim : Tendsto (fun k => sC (zs k).1) atTop (𝓝 (-1)) := by
      have hr0 : Tendsto (fun k => krC M (c (s (φ k)))) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => (krC_pos M hM (hcK _ (hsI (φ k)))).le)
          (fun k => (hsr (φ k)).le) ?_
        exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      have hkF : Tendsto (fun k => kF M (krC M (c (s (φ k))))) atTop (𝓝 (kF M 0)) :=
        ((contDiff_kF M hM.ne').continuous.tendsto 0).comp hr0
      rw [kF_zero M hM.ne'] at hkF
      refine hkF.congr fun k => ?_
      exact kF_kG M hM (hcK _ (hsI (φ k))).2
    refine IsLorentzianExtension.not_tendsto_kruskal M hM hext hlim (e.symm (σ sstar)) ?_
    have hcw := hcomp sstar hsstar
    have ht : Tendsto (fun k => s (φ k)) atTop (𝓝[Icc 0 1] sstar) :=
      tendsto_nhdsWithin_iff.2 ⟨hφlim, Eventually.of_forall fun k =>
        ⟨(hsI (φ k)).1, (hsI (φ k)).2.le.trans hbN.1.2⟩⟩
    refine (hcw.tendsto.comp ht).congr fun k => ?_
    exact (hιc _ (hsI (φ k)) _).symm

end Lightlike

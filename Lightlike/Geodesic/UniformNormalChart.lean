import Lightlike.Geodesic.GlobalTwoPoint
import Lightlike.Geodesic.Gauss

/-!
# Normal charts of uniform radius over a compact set

For a coordinate metric `g` on `U` and a compact `K ⊆ U` there is one radius `ρ > 0` such that for
every `p ∈ K` the exponential map `v ↦ exp_p v` is a normal chart at `p` on the ball of radius `ρ`
(`Lightlike.Geodesic.exists_uniform_normalChart`). This is the step of Chruściel's local causality
(*Elements of causality theory*, section 2.4) that makes the radius of a normal neighbourhood
uniform on compact sets; it is the first ingredient of a uniform time ball.

Proof: a finite cover of `K` by the balls of `exists_twoPoint_diffeo` gives a uniform radius for the
geodesics on `(-1, 2)`; the tube lemma applied to the neighbourhood `W` of the zero section of
`exists_twoPoint_diffeo_global` gives a uniform radius on which `exp_p` is injective with smooth
inverse and open image.
-/

open Set Metric Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- A finite family of positive numbers has a positive common lower bound. -/
lemma exists_pos_le_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, hδs⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    refine ⟨min δ (f a), lt_min hδ (hf a (Finset.mem_insert_self a s)), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδs i hi)

/-- **Uniform geodesics.** For compact `K ⊆ U` there is `ρ > 0` such that for `p ∈ K` and `v` in the
ball of radius `ρ`, there is a geodesic on `(-1, 2)` from `p` with velocity `v`, equal to
`t ↦ exp_p (t v)` on `[-1, 1]`, and `exp_p (t v) ∈ U` there. -/
theorem exists_uniform_geodesic (hg : Lightlike.IsCoordMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ,
      γ 0 = p ∧ w 0 = v ∧ IsGeodesicOn g γ w (Ioo (-1) 2) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, γ t = expMap g U (p, t • v) ∧ γ t ∈ U := by
  classical
  have hloc : ∀ x : Fin n → ℝ, ∃ ρ : ℝ, 0 < ρ ∧ (x ∈ U → ∀ p ∈ ball x ρ,
      ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ,
      γ 0 = p ∧ w 0 = v ∧ IsGeodesicOn g γ w (Ioo (-1) 2) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, γ t = expMap g U (p, t • v) ∧ γ t ∈ U) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨ρ, E, Θ, hρ, -, -, hEU, hEg, -⟩ := exists_twoPoint_diffeo hg hx
      refine ⟨ρ, hρ, fun _ p hp v hv => ?_⟩
      have hsm : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ u ∈ ball (0 : Fin n → ℝ) ρ,
          t • u ∈ ball (0 : Fin n → ℝ) ρ := by
        intro t ht u hu
        rw [mem_ball_zero_iff] at hu ⊢
        rw [norm_smul, Real.norm_eq_abs]
        have : |t| ≤ 1 := abs_le.2 ht
        nlinarith [norm_nonneg u, abs_nonneg t]
      obtain ⟨γ, w, h0, hw0, hgeo, hγE⟩ := hEg p hp v hv
      refine ⟨γ, w, h0, hw0, hgeo, fun t ht => ?_⟩
      have hE : ∀ u ∈ ball (0 : Fin n → ℝ) ρ, expMap g U (p, u) = E (p, u) := by
        intro u hu
        obtain ⟨γ', w', h0', hw0', hgeo', hγE'⟩ := hEg p hp u hu
        have h01 : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun t ht =>
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hUγ : ∀ s ∈ Icc (0 : ℝ) 1, γ' s ∈ U := fun s hs => by
          rw [hγE' s ⟨by linarith [hs.1], hs.2⟩]
          exact hEU p hp _ (hsm s ⟨by linarith [hs.1], hs.2⟩ u hu)
        have h2 := expMap_eq hg isOpen_Ioo h01 hgeo' hUγ
        rw [h0', hw0'] at h2
        rw [h2, hγE' 1 ⟨by norm_num, le_rfl⟩, one_smul]
      have htv := hsm t ht v hv
      rw [hγE t ht, hE _ htv]
      exact ⟨rfl, hEU p hp _ htv⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose ρ hρ hQ using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => ball x (ρ x))
    (fun x _ => ball_mem_nhds x (hρ x))
  obtain ⟨δ, hδ, hδt⟩ := exists_pos_le_finset t ρ fun i _ => hρ i
  refine ⟨δ, hδ, fun p hp v hv => ?_⟩
  obtain ⟨x, hxt, hpx⟩ := mem_iUnion₂.1 (hcov hp)
  exact hQ x (hKU (htK x hxt)) p hpx v (ball_subset_ball (hδt x hxt) hv)


/-- The image of an open set `V ⊆ B(0, ρ)` under `exp_p` is open, when `{p} × B(0, ρ) ⊆ W` for the
neighbourhood `W` of the zero section of `exists_twoPoint_diffeo_global`. -/
lemma isOpen_image_expMap {W : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {G : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (hW : IsOpen W)
    (himg : IsOpen (twoPointMap g U '' W)) (hG : ∀ q ∈ W, G (twoPointMap g U q) = q)
    (hGs : ContDiffOn ℝ ∞ G (twoPointMap g U '' W)) {p : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hV : IsOpen V) (hpV : ∀ v ∈ V, ((p, v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ W) :
    IsOpen ((fun v => expMap g U (p, v)) '' V) := by
  set W' : Set ((Fin n → ℝ) × (Fin n → ℝ)) := W ∩ (univ ×ˢ V) with hW'
  have hW'o : IsOpen W' := hW.inter (isOpen_univ.prod hV)
  have h1 : IsOpen (twoPointMap g U '' W') := by
    have : twoPointMap g U '' W' = twoPointMap g U '' W ∩ G ⁻¹' W' := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq.1, rfl⟩, by rw [Set.mem_preimage, hG q hq.1]; exact hq⟩
      · rintro ⟨⟨q, hq, rfl⟩, hy⟩
        rw [Set.mem_preimage, hG q hq] at hy
        exact ⟨q, hy, rfl⟩
    rw [this]
    exact hGs.continuousOn.isOpen_inter_preimage himg hW'o
  have h2 : IsOpen ((fun y : Fin n → ℝ => ((p, y) : (Fin n → ℝ) × (Fin n → ℝ))) ⁻¹'
      (twoPointMap g U '' W')) :=
    h1.preimage (by fun_prop)
  convert h2 using 1
  ext y
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(p, v), ⟨hpV v hv, trivial, hv⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨-, -, hb⟩, hq⟩
    simp only [twoPointMap, Prod.mk.injEq] at hq
    obtain ⟨rfl, hy⟩ := hq
    exact ⟨b, hb, hy⟩


/-- **Normal charts of uniform radius over a compact set.** For compact `K ⊆ U` there is `ρ > 0`
such that for every `p ∈ K` there is a normal chart `φ` at `p` on the ball of radius `ρ`, and
`φ v = exp_p v` there. -/
theorem exists_uniform_normalChart (hg : Lightlike.IsCoordMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ (∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ,
        ((p, v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ expDomain g U) ∧
      ∀ p ∈ K, ∃ φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
      IsNormalChart g U p ρ φ ∧ ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ v = expMap g U (p, v) := by
  obtain ⟨ρ₁, hρ₁, hgeo⟩ := exists_uniform_geodesic hg hK hKU
  obtain ⟨W, G, hW, hW0, hWd, hinj, hWs, himg, -, hG, hGs⟩ := exists_twoPoint_diffeo_global hg
  obtain ⟨u, v, hu, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hW
    (t := ({(0 : Fin n → ℝ)} : Set (Fin n → ℝ)))
    (fun q hq => by
      have h2 := Set.mem_singleton_iff.1 hq.2
      have h3 := hW0 q.1 (hKU hq.1)
      rw [← h2] at h3
      exact h3)
  obtain ⟨ρ₂, hρ₂, hbv⟩ := Metric.isOpen_iff.1 hv 0 (h0v rfl)
  set ρ := min ρ₁ ρ₂ with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ hρ₂
  refine ⟨ρ, hρpos, fun p hp w hw => ?_, fun p hp => ?_⟩
  · exact hWd (huv ⟨hKu hp, hbv (ball_subset_ball (min_le_right _ _) hw)⟩)
  have hball : ∀ w ∈ ball (0 : Fin n → ℝ) ρ, ((p, w) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ W :=
    fun w hw => huv ⟨hKu hp, hbv (ball_subset_ball (min_le_right _ _) hw)⟩
  set f : (Fin n → ℝ) → (Fin n → ℝ) := fun w => expMap g U (p, w) with hf
  have hfinj : InjOn f (ball 0 ρ) := by
    intro a ha b hb hab
    have := hinj (hball a ha) (hball b hb) (Prod.ext rfl hab)
    exact (Prod.ext_iff.1 this).2
  have hfopen : ∀ V, IsOpen V → V ⊆ ball 0 ρ → IsOpen (f '' V) := fun V hV hVs =>
    isOpen_image_expMap hW himg hG hGs hV fun w hw => hball w (hVs hw)
  have hfcd : ContDiffOn ℝ ∞ f (ball 0 ρ) := by
    refine (contDiffOn_expMap hg).comp (contDiff_const.prodMk contDiff_id).contDiffOn ?_
    exact fun w hw => hWd (hball w hw)
  set e : PartialEquiv (Fin n → ℝ) (Fin n → ℝ) := hfinj.toPartialEquiv f (ball 0 ρ) with he
  have hesrc : e.source = ball 0 ρ := rfl
  have hecoe : ⇑e = f := rfl
  let φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict e (by rw [hesrc, hecoe]; exact hfcd.continuousOn)
      (by
        intro O hO
        have h1 : IsOpen (Subtype.val '' O) :=
          (show IsOpen e.source by rw [hesrc]; exact isOpen_ball).isOpenMap_subtype_val O hO
        have h2 : (e.source.domRestrict e) '' O = f '' (Subtype.val '' O) := by
          rw [Set.image_image]; rfl
        rw [h2]
        exact hfopen _ h1 (by
          rintro _ ⟨x, -, rfl⟩
          show (x : Fin n → ℝ) ∈ ball (0 : Fin n → ℝ) ρ
          rw [← hesrc]
          exact x.2))
      (by rw [hesrc]; exact isOpen_ball)
  have hφsrc : φ.source = ball 0 ρ := hesrc
  have hφcoe : ⇑φ = f := rfl
  have hφt : φ.target = f '' ball 0 ρ := rfl
  have hφU : ∀ w ∈ ball (0 : Fin n → ℝ) ρ, f w ∈ U := fun w hw => by
    obtain ⟨γ, w', h0, hw0, -, hγ⟩ := hgeo p hp w (ball_subset_ball (min_le_left _ _) hw)
    have := (hγ 1 ⟨by norm_num, le_rfl⟩).2
    rwa [(hγ 1 ⟨by norm_num, le_rfl⟩).1, one_smul] at this
  have hρ1 : ∀ w ∈ ball (0 : Fin n → ℝ) ρ, w ∈ ball (0 : Fin n → ℝ) ρ₁ := fun w hw =>
    ball_subset_ball (min_le_left _ _) hw
  have hf0 : f 0 = p := expMap_zero hg (hKU hp)
  -- the derivative at `0`
  have hfat : DifferentiableAt ℝ f 0 :=
    (hfcd.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρpos))).differentiableAt (by simp)
  have hDu : ∀ w ∈ ball (0 : Fin n → ℝ) ρ, fderiv ℝ f 0 w = w := by
    intro w hw
    obtain ⟨γ, w', h0, hw0, hgeo', hγ⟩ := hgeo p hp w (hρ1 w hw)
    have h1 : HasDerivAt γ (w' 0) 0 := hgeo'.pos 0 ⟨by norm_num, by norm_num⟩
    have h2 : HasDerivAt (fun t : ℝ => f (t • w)) (fderiv ℝ f 0 w) 0 := by
      have hin : HasDerivAt (fun t : ℝ => t • w) w 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
      have hfd : HasFDerivAt f (fderiv ℝ f 0) ((fun t : ℝ => t • w) 0) := by
        simpa using hfat.hasFDerivAt
      exact hfd.comp_hasDerivAt 0 hin
    have h3 : γ =ᶠ[𝓝 (0 : ℝ)] fun t => f (t • w) := by
      filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
        with t ht using (hγ t ht).1
    exact (h1.unique (h2.congr_of_eventuallyEq h3)).symm.trans hw0
  have hD : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    ext1 w
    obtain ⟨c, hc, hcw⟩ : ∃ c : ℝ, 0 < c ∧ c • w ∈ ball (0 : Fin n → ℝ) ρ := by
      refine ⟨ρ / (2 * (‖w‖ + 1)), by positivity, ?_⟩
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h1 : 0 < ‖w‖ + 1 := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg w]
    have := hDu _ hcw
    rw [map_smul] at this
    simpa [hc.ne'] using this
  refine ⟨φ, ⟨hρpos, hφsrc, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun w _ => rfl⟩
  · show f 0 = p
    exact hf0
  · rw [hφsrc]; exact hfcd
  · have hmaps : MapsTo (fun y : Fin n → ℝ => ((p, y) : (Fin n → ℝ) × (Fin n → ℝ))) φ.target
        (twoPointMap g U '' W) := by
      rintro y ⟨w', hw', rfl⟩
      exact ⟨(p, w'), hball w' hw', rfl⟩
    have h1 : ContDiffOn ℝ ∞ (fun y => (G (p, y)).2) φ.target :=
      contDiff_snd.comp_contDiffOn (hGs.comp (contDiff_const.prodMk contDiff_id).contDiffOn hmaps)
    refine h1.congr fun y hy => ?_
    obtain ⟨w', hw', rfl⟩ := hy
    have hl : φ.symm (f w') = w' := φ.left_inv (by rw [hφsrc]; exact hw')
    rw [hl, show ((p, f w') : (Fin n → ℝ) × (Fin n → ℝ)) = twoPointMap g U (p, w') from rfl,
      hG (p, w') (hball w' hw')]
  · rw [show ⇑φ = f from rfl]
    have := hD ▸ hfat.hasFDerivAt
    exact this
  · rintro y ⟨w, hw, rfl⟩
    exact hφU w hw
  · intro w hw
    obtain ⟨γ, w', h0, hw0, hgeo', hγ⟩ := hgeo p hp w (hρ1 w hw)
    refine ⟨γ, w', h0.symm ▸ rfl, hw0, ?_, hgeo', fun t ht => ?_⟩
    · rw [(hγ 1 ⟨by norm_num, le_rfl⟩).1, one_smul]; rfl
    · exact (hγ t ht).1
      
end Lightlike.Geodesic

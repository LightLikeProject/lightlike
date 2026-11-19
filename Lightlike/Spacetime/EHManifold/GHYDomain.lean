import Lightlike.Spacetime.EHManifold.GHYGraph

/-!
# The Einstein–Hilbert action with the Gibbons–Hawking–York term on a domain with regular boundary

`eh_ghy_variation_cover`: let `D ⊆ ℝⁿ⁺¹` be a measurable set with a finite atlas of graph charts and cut-off
functions `ρ_a` as in `integral_divergence_of_graph_cover` (on the support of `ρ_a` the set `D` is the
region above or below the graph of `γ_a`, or everything), with `∑_a ρ_a = 1` near the points of `D` in the
support `T` of the perturbation `h`, and let `h` vanish on the boundary: on each graph near the support of
`ρ_a`. Then

`d/dt|₀ [∫_{D ∩ T} √|g_t| (R(g_t) - 2Λ) - ∑_a σ_a ∫ ρ_a 2 √|h_t| K_t dy] = -∫_{D ∩ T} √|g| h_{ab} E^{ab}`.

The sum over the charts is the Gibbons–Hawking–York boundary term `∫_{∂D} 2 √|h| K` in the graph charts with
the partition of unity, with the sign of the outward orientation.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1) to (4.4), p. 20.
-/

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- A partial derivative along a hyperplane vanishes if the function vanishes on the hyperplane near the
point. -/
lemma pd_eq_zero_of_eventually_vanishing_on_hyperplane {m : ℕ} {f : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ}
    (hf : DifferentiableAt ℝ f x) (i σ : Fin m) (hσ : σ ≠ i)
    (hz : ∀ᶠ y in 𝓝 x, y i = x i → f y = 0) : pd σ f x = 0 := by
  have hc : HasDerivAt (fun s : ℝ => x + s • (Pi.single σ (1 : ℝ) : Fin m → ℝ))
      (Pi.single σ (1 : ℝ) : Fin m → ℝ) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single σ (1 : ℝ) : Fin m → ℝ)).const_add x
    simpa using h1
  have hcomp : HasDerivAt (fun s : ℝ => f (x + s • (Pi.single σ (1 : ℝ) : Fin m → ℝ)))
      (fderiv ℝ f x (Pi.single σ 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf.hasFDerivAt hc (by simp)
  have ht : Tendsto (fun s : ℝ => x + s • (Pi.single σ (1 : ℝ) : Fin m → ℝ)) (𝓝 0) (𝓝 x) := by
    have h1 := hc.continuousAt.tendsto
    simpa using h1
  have hev : (fun s : ℝ => f (x + s • (Pi.single σ (1 : ℝ) : Fin m → ℝ))) =ᶠ[𝓝 0]
      fun _ => (0 : ℝ) :=
    (ht.eventually hz).mono fun s hs => hs (by simp [hσ.symm])
  unfold pd
  exact hcomp.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)

/-- **A function vanishing on the graph near a point has only a normal derivative there.** -/
theorem pd_of_eventually_vanishing_on_graph (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 1 γ)
    (i : Fin (n + 1)) (H : (Fin (n + 1) → ℝ) → ℝ) (hH : Differentiable ℝ H) (y : Fin n → ℝ)
    (hz : ∀ᶠ y' in 𝓝 y, H (graphPt γ i y') = 0) (τ : Fin (n + 1)) :
    pd τ H (graphPt γ i y) = graphConormal γ i y τ * pd i H (graphPt γ i y) := by
  rcases Fin.eq_self_or_eq_succAbove i τ with h | ⟨k, h⟩
  · rw [h]
    simp only [graphConormal, Fin.insertNth_apply_same, one_mul]
  · rw [h]
    obtain ⟨z, hzdef⟩ : ∃ z : Fin (n + 1) → ℝ, z = Fin.insertNth (α := fun _ => ℝ) i 0 y := ⟨_, rfl⟩
    have hrem : i.removeNth z = y := by
      rw [hzdef]
      simp
    have hzi : z i = 0 := by
      rw [hzdef]
      simp
    have hz0 : shearFwd γ i z = graphPt γ i y := by
      unfold shearFwd graphPt
      rw [hrem, hzi, zero_add]
    have hΨ : Differentiable ℝ (shearFwd γ i) := (contDiff_shearFwd γ hγ i).differentiable (by simp)
    have hc := pd_comp_shearFwd_succAbove γ i k H z
      ((hγ.differentiable (by simp)).differentiableAt) (hH _)
    have htend : Tendsto (fun w : Fin (n + 1) → ℝ => i.removeNth w) (𝓝 z) (𝓝 y) := by
      have h1 := (removeNthL i).continuous.tendsto z
      rw [removeNthL_apply, hrem] at h1
      exact h1
    have h0 : pd (i.succAbove k) (fun w => H (shearFwd γ i w)) z = 0 :=
      pd_eq_zero_of_eventually_vanishing_on_hyperplane ((hH _).comp z (hΨ z)) i (i.succAbove k)
        (Fin.succAbove_ne i k) ((htend.eventually hz).mono fun w hw hwi => by
          have e : shearFwd γ i w = graphPt γ i (i.removeNth w) := by
            unfold shearFwd graphPt
            rw [hwi, hzi, zero_add]
          show H (shearFwd γ i w) = 0
          rw [e]
          exact hw)
    rw [h0, hrem, hz0] at hc
    simp only [graphConormal, Fin.insertNth_apply_succAbove]
    linarith

variable (g h : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)

include hg hh hgs hhs in
/-- At a point of the graph near which the perturbation vanishes on the graph, the Gibbons–Hawking–York
density of `g + t h` is affine in `t` with slope minus the Palatini flux through the graph. -/
theorem ghyGraph_add_smul (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 1 γ) (i : Fin (n + 1))
    (y : Fin n → ℝ) (hbd : ∀ᶠ y' in 𝓝 y, h (graphPt γ i y') = 0)
    (hN : (∑ a, graphConormal γ i y a *
      ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0) (t : ℝ) :
    ghyGraph (fun z => g z + t • h z) γ i y =
      ghyGraph g γ i y + t * (-∑ ρ, ehFlux g h ρ (graphPt γ i y) * graphConormal γ i y ρ) := by
  have hx0 : h (graphPt γ i y) = 0 := hbd.self_of_nhds
  have hgd : ∀ l k, DifferentiableAt ℝ (fun z => g z l k) (graphPt γ i y) := fun l k =>
    ((hg l k).differentiable (by simp)).differentiableAt
  have hhd : ∀ l k, DifferentiableAt ℝ (fun z => h z l k) (graphPt γ i y) := fun l k =>
    ((hh l k).differentiable (by simp)).differentiableAt
  have hinv : ∀ a b, (g (graphPt γ i y))⁻¹ a b = (g (graphPt γ i y))⁻¹ b a := by
    intro a b
    have hT' : ((g (graphPt γ i y))⁻¹)ᵀ = (g (graphPt γ i y))⁻¹ := by
      have : (g (graphPt γ i y))ᵀ = g (graphPt γ i y) := by ext k l; exact hgs _ l k
      rw [Matrix.transpose_nonsing_inv, this]
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hT' a) b).symm
  have hpd : ∀ τ a b, pd τ (fun z => h z a b) (graphPt γ i y) =
      graphConormal γ i y τ * pd i (fun z => h z a b) (graphPt γ i y) := fun τ a b =>
    pd_of_eventually_vanishing_on_graph γ hγ i (fun z => h z a b)
      ((hh a b).differentiable (by simp)) y (hbd.mono fun y' hy' => by
        show h (graphPt γ i y') a b = 0
        rw [hy']
        rfl) τ
  have hk : ∀ a b, pd i (fun z => h z a b) (graphPt γ i y) =
      pd i (fun z => h z b a) (graphPt γ i y) := fun a b => by
    have e : (fun z => h z a b) = fun z => h z b a := funext fun z => hhs z a b
    rw [e]
  unfold ghyGraph
  rw [ghyDensityOf_add_smul_of_zero g h _ _ _ hgd hhd hx0 t,
    ghySlopeOf_eq_neg_flux g h _ _ (fun a b => pd i (fun z => h z a b) (graphPt γ i y)) hx0
      hpd hinv hk hN]

include hg hh hgs hhs hdet in
/-- **The variation of the Einstein–Hilbert action over a measurable region**, with the divergence of the
Palatini flux integrated over the region. -/
theorem eh_variation_region (Λ : ℝ) {T : Set (Fin (n + 1) → ℝ)} (hT : IsCompact T)
    (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) (A : Set (Fin (n + 1) → ℝ))
    (hA : MeasurableSet A) :
    HasDerivAt (fun t : ℝ => ∫ x in T, lagDensity g h Λ t x ∂(volume.restrict A))
      ((-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β ∂(volume.restrict A)) +
        ∫ x in A, ∑ ρ, pd ρ (ehFlux g h ρ) x) 0 := by
  have hmain := eh_variation_piece g h hg hh hgs hhs hdet hT A Λ
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  have hFs : ∀ ρ, ContDiff ℝ ∞ (ehFlux g h ρ) := fun ρ => contDiff_flux g h hg hh hdet ρ
  have hzero : ∀ x, x ∉ T → ∀ a b, (fun z => h z a b) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun x hx a b =>
    notMem_tsupport_iff_eventuallyEq.1 fun hmem => hx (hsupp a b hmem)
  have hGc : Continuous g := continuous_matrix fun a b => (hg a b).continuous
  have hbulk : Continuous (fun x => -√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) :=
    ((Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)).neg).mul
      (continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
        (hh α β).continuous.mul (contDiff_einsteinUp g hg hdet hgs Λ α β).continuous)
  have hdivc : Continuous (ehFluxDiv g h) := by
    unfold ehFluxDiv
    exact continuous_finsetSum _ fun ρ _ => (contDiff_pd (hFs ρ) ρ).continuous
  have hle : ((volume : Measure (Fin (n + 1) → ℝ)).restrict A).restrict T ≤
      (volume : Measure (Fin (n + 1) → ℝ)).restrict T :=
    Measure.restrict_mono subset_rfl Measure.restrict_le_self
  have hsplit : ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
        (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
        ehFluxDiv g h x) ∂(volume.restrict A) =
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β ∂(volume.restrict A)) +
        ∫ x in T, ehFluxDiv g h x ∂(volume.restrict A) := by
    have i1 : IntegrableOn (fun x => -√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β)
        T (volume.restrict A) :=
      Integrable.mono_measure (hbulk.continuousOn.integrableOn_compact hT) hle
    have i2 : IntegrableOn (ehFluxDiv g h) T (volume.restrict A) :=
      Integrable.mono_measure (hdivc.continuousOn.integrableOn_compact hT) hle
    have e1 : ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
          ehFluxDiv g h x) ∂(volume.restrict A) =
        ∫ x in T, ((-√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) +
          ehFluxDiv g h x) ∂(volume.restrict A) := rfl
    have e2 : ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β)
          ∂(volume.restrict A) =
        -∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β ∂(volume.restrict A) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show -√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β =
        -(√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β)
      ring
    rw [e1, integral_add i1 i2, e2]
  have hdiv : ∫ x in T, ehFluxDiv g h x ∂(volume.restrict A) = ∫ x in A, ehFluxDiv g h x := by
    rw [Measure.restrict_restrict hTm, ← integral_indicator (hTm.inter hA), ← integral_indicator hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hxT : x ∈ T
    · by_cases hxE : x ∈ A
      · rw [indicator_of_mem (Set.mem_inter hxT hxE), indicator_of_mem hxE]
      · rw [indicator_of_notMem (fun h' : x ∈ T ∩ A => hxE h'.2), indicator_of_notMem hxE]
    · have h0 : ehFluxDiv g h x = 0 :=
        ehFluxDiv_eq_zero_of_eventuallyEq g h hg hh x (hzero x hxT)
      simp only [indicator, h0, ite_self]
  rw [hsplit, hdiv] at hmain
  exact hmain

include hg hh hgs hhs hdet in
/-- **The Einstein–Hilbert action with the Gibbons–Hawking–York term on a domain covered by graph charts**:
for a perturbation with compact support that vanishes on the boundary, only the bulk variation remains. -/
theorem eh_ghy_variation_cover {ι : Type*} [Fintype ι] (D : Set (Fin (n + 1) → ℝ))
    (hD : MeasurableSet D) (Λ : ℝ) {T : Set (Fin (n + 1) → ℝ)} (hT : IsCompact T)
    (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T)
    (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (hρ : ∀ a, ContDiff ℝ 1 (ρ a)) (σ : ι → SignType)
    (γ : ι → (Fin n → ℝ) → ℝ) (hγ : ∀ a, ContDiff ℝ 2 (γ a)) (i : ι → Fin (n + 1))
    (hDE : ∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a)))
    (hsum : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, ∑ a, ρ a y = 1 ∨ y ∉ T)
    (hbd : ∀ a, σ a ≠ 0 → ∀ y, graphPt (γ a) (i a) y ∈ tsupport (ρ a) →
      ∀ᶠ y' in 𝓝 y, h (graphPt (γ a) (i a) y') = 0)
    (hN : ∀ a, σ a ≠ 0 → ∀ y, graphPt (γ a) (i a) y ∈ tsupport (ρ a) →
      (∑ c, graphConormal (γ a) (i a) y c *
        ∑ b, (g (graphPt (γ a) (i a) y))⁻¹ c b * graphConormal (γ a) (i a) y b) ≠ 0)
    (S : ι → Set (Fin n → ℝ)) (hS : ∀ a, IsCompact (S a))
    (hST : ∀ a y, graphPt (γ a) (i a) y ∈ T → y ∈ S a) :
    HasDerivAt (fun t : ℝ =>
        (∫ x in T, lagDensity g h Λ t x ∂(volume.restrict D)) -
          ∑ a, (σ a : ℝ) * ∫ y in S a, ρ a (graphPt (γ a) (i a) y) *
            ghyGraph (fun z => g z + t • h z) (γ a) (i a) y)
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β
        ∂(volume.restrict D)) 0 := by
  have hmain := eh_variation_region g h hg hh hgs hhs hdet Λ hT hsupp D hD
  have hFs : ∀ ρ, ContDiff ℝ ∞ (ehFlux g h ρ) := fun ρ => contDiff_flux g h hg hh hdet ρ
  have hzero : ∀ x, x ∉ T → ∀ a b, (fun z => h z a b) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun x hx a b =>
    notMem_tsupport_iff_eventuallyEq.1 fun hmem => hx (hsupp a b hmem)
  have hflux0 : ∀ x, x ∉ T → ∀ ρ, ehFlux g h ρ x = 0 := by
    intro x hx ρ
    have hW : Wvec g h ρ x = 0 := by
      unfold Wvec
      simp [dChristoffel_eq_zero g h hg hh x (hzero x hx)]
    show √|(g x).det| * Wvec g h ρ x = 0
    rw [hW, mul_zero]
  have hFc : ∀ ρ, HasCompactSupport (ehFlux g h ρ) := fun ρ =>
    HasCompactSupport.intro hT fun x hx => hflux0 x hx ρ
  -- the divergence theorem on `D`
  have hdiv := integral_divergence_of_graph_cover D hD (ehFlux g h)
    (fun ρ => (hFs ρ).of_le (by simp)) hFc ρ hρ σ γ hγ i hDE (fun x hx => by
      filter_upwards [hsum x hx] with y hy j
      rcases hy with h1 | h2
      · rw [← Finset.sum_mul, h1, one_mul]
      · simp [hflux0 y h2 j])
  rw [hdiv] at hmain
  -- each chart's boundary term is affine in `t`
  have hXc : ∀ a, Continuous fun y => graphPt (γ a) (i a) y := fun a =>
    continuous_graphPt (γ a) (hγ a).continuous (i a)
  have hνc : ∀ a, Continuous fun y => graphConormal (γ a) (i a) y := fun a =>
    continuous_graphConormal (γ a) ((hγ a).of_le (by norm_num)) (i a)
  have hpt : ∀ (a : ι), σ a ≠ 0 → ∀ (t : ℝ) (y : Fin n → ℝ),
      ρ a (graphPt (γ a) (i a) y) * ghyGraph (fun z => g z + t • h z) (γ a) (i a) y =
        ρ a (graphPt (γ a) (i a) y) * ghyGraph g (γ a) (i a) y +
          t * (-∑ j, (ρ a (graphPt (γ a) (i a) y) * ehFlux g h j (graphPt (γ a) (i a) y)) *
            graphConormal (γ a) (i a) y j) := by
    intro a hσ t y
    by_cases hy : ρ a (graphPt (γ a) (i a) y) = 0
    · simp [hy]
    · have hmem : graphPt (γ a) (i a) y ∈ tsupport (ρ a) := subset_tsupport _ hy
      rw [ghyGraph_add_smul g h hg hh hgs hhs (γ a) ((hγ a).of_le (by norm_num)) (i a) y
        (hbd a hσ y hmem) (hN a hσ y hmem) t, mul_add]
      congr 1
      have e : ∑ j, (ρ a (graphPt (γ a) (i a) y) * ehFlux g h j (graphPt (γ a) (i a) y)) *
          graphConormal (γ a) (i a) y j =
          ρ a (graphPt (γ a) (i a) y) *
            ∑ j, ehFlux g h j (graphPt (γ a) (i a) y) * graphConormal (γ a) (i a) y j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      ring
  have hc0 : ∀ a, σ a ≠ 0 →
      Continuous fun y => ρ a (graphPt (γ a) (i a) y) * ghyGraph g (γ a) (i a) y := by
    intro a hσ
    refine continuous_iff_continuousAt.2 fun y => ?_
    by_cases hy : graphPt (γ a) (i a) y ∈ tsupport (ρ a)
    · exact (((hρ a).continuous.comp (hXc a)).continuousAt).mul
        (continuousAt_ghyGraph g hg hdet (γ a) (hγ a) (i a) y (hN a hσ y hy))
    · have hev : (fun y => ρ a (graphPt (γ a) (i a) y) * ghyGraph g (γ a) (i a) y) =ᶠ[𝓝 y]
          fun _ => (0 : ℝ) := by
        have hopen : (fun y => graphPt (γ a) (i a) y) ⁻¹' (tsupport (ρ a))ᶜ ∈ 𝓝 y :=
          ((isClosed_tsupport (ρ a)).isOpen_compl.preimage (hXc a)).mem_nhds hy
        filter_upwards [hopen] with z hz
        have hz0 : ρ a (graphPt (γ a) (i a) z) = 0 := by
          by_contra hne
          exact hz (subset_tsupport _ hne)
        rw [hz0, zero_mul]
      exact continuousAt_const.congr hev.symm
  have hsl : ∀ a, Continuous fun y =>
      -∑ j, (ρ a (graphPt (γ a) (i a) y) * ehFlux g h j (graphPt (γ a) (i a) y)) *
        graphConormal (γ a) (i a) y j := fun a =>
    (continuous_finsetSum _ fun j _ =>
      ((((hρ a).continuous.comp (hXc a)).mul ((hFs j).continuous.comp (hXc a)))).mul
        ((continuous_apply j).comp (hνc a))).neg
  have hslI : ∀ a, ∫ y in S a,
      -∑ j, (ρ a (graphPt (γ a) (i a) y) * ehFlux g h j (graphPt (γ a) (i a) y)) *
        graphConormal (γ a) (i a) y j =
      -graphFlux (γ a) (i a) (fun j y => ρ a y * ehFlux g h j y) := by
    intro a
    rw [integral_neg, graphFlux_eq]
    congr 1
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      Finset.sum_eq_zero fun j _ => by
        rw [hflux0 _ (fun hT' => hy (hST a y hT')) j, mul_zero, zero_mul]
  have hB : ∀ (a : ι), σ a ≠ 0 → ∀ (t : ℝ), ∫ y in S a, ρ a (graphPt (γ a) (i a) y) *
        ghyGraph (fun z => g z + t • h z) (γ a) (i a) y =
      (∫ y in S a, ρ a (graphPt (γ a) (i a) y) * ghyGraph g (γ a) (i a) y) +
        t * (-graphFlux (γ a) (i a) (fun j y => ρ a y * ehFlux g h j y)) := by
    intro a hσ t
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y => hpt a hσ t y)).trans ?_
    rw [integral_add ((hc0 a hσ).continuousOn.integrableOn_compact (hS a))
      (((hsl a).continuousOn.integrableOn_compact (hS a)).const_mul t), integral_const_mul, hslI a]
  have hlin : ∀ a ∈ (Finset.univ : Finset ι), HasDerivAt (fun t : ℝ => (σ a : ℝ) *
      ∫ y in S a, ρ a (graphPt (γ a) (i a) y) * ghyGraph (fun z => g z + t • h z) (γ a) (i a) y)
      ((σ a : ℝ) * (-graphFlux (γ a) (i a) (fun j y => ρ a y * ehFlux g h j y))) 0 := by
    intro a _
    by_cases hσ : σ a = 0
    · simp only [hσ, SignType.coe_zero, zero_mul]
      exact hasDerivAt_const 0 0
    · have h3 := ((hasDerivAt_id' (0 : ℝ)).mul_const
        (-graphFlux (γ a) (i a) (fun j y => ρ a y * ehFlux g h j y))).const_add
        (∫ y in S a, ρ a (graphPt (γ a) (i a) y) * ghyGraph g (γ a) (i a) y)
      rw [one_mul] at h3
      have hfa : (fun t : ℝ => (σ a : ℝ) * ∫ y in S a, ρ a (graphPt (γ a) (i a) y) *
            ghyGraph (fun z => g z + t • h z) (γ a) (i a) y) =
          fun t : ℝ => (σ a : ℝ) *
            ((∫ y in S a, ρ a (graphPt (γ a) (i a) y) * ghyGraph g (γ a) (i a) y) +
              t * (-graphFlux (γ a) (i a) (fun j y => ρ a y * ehFlux g h j y))) :=
        funext fun t => by rw [hB a hσ t]
      rw [hfa]
      exact h3.const_mul (σ a : ℝ)
  refine (hmain.fun_sub (HasDerivAt.fun_sum hlin)).congr_deriv ?_
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

end Lightlike

import Lightlike.Spacetime.EHManifold.ConormalGHY
import Lightlike.Spacetime.EHManifold.DomainDivergence
import Lightlike.Spacetime.EHManifold.FluxLocal

/-!
# The Einstein–Hilbert action with the Gibbons–Hawking–York term on the region bounded by a graph

For `γ : ℝⁿ → ℝ` of class `C²`, the boundary `{x_i = γ(x')}` has the defining function `u = x_i - γ(x')`,
with conormal `ν = du = e_i - ∇γ` (`graphConormal`) and `∂ν = -∂∂γ` (`graphConormalD`).

* `pd_of_vanishing_on_graph`: a differentiable function vanishing on the graph has derivative
  `∂_τ H = ν_τ ∂_i H` at the points of the graph;
* `ghyGraph g γ i y`: the Gibbons–Hawking–York density `2 √|h| K` of the graph at the point `(y, γ(y))`,
  with respect to `dy` (`ghyDensityOf` with the conormal of the graph);
* `eh_ghy_variation_graph`: for a perturbation `h` with support in a compact set `T` that vanishes on the
  graph, on the region `E` above (`σ = 1`) or below (`σ = -1`) the graph,

  `d/dt|₀ [∫_{E ∩ T} √|g_t| (R(g_t) - 2Λ) - σ ∫_S 2 √|h_t| K_t dy] = -∫_{E ∩ T} √|g| h_{ab} E^{ab}`:

  with the Gibbons–Hawking–York term only the bulk variation remains. No condition on the normal derivative
  of `h` at the boundary is needed. The sign `-σ` is the orientation: `du` is the inward conormal of the
  region above the graph.

This removes the coordinate-box and coordinate-hyperplane restrictions of `eh_ghy_variation_box`.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1) to (4.4), p. 20.
-/

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The point `(y, γ(y))` of the graph, with `γ(y)` at the `i`-th place. -/
def graphPt (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) i (γ y) y

/-- The conormal `du = e_i - ∇γ` of the graph, for the defining function `u = x_i - γ(x')`. -/
def graphConormal (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) i 1 (fun k => -pd k γ y)

/-- The second derivatives `∂_α ∂_β u = -∂∂γ` of the defining function `u = x_i - γ(x')` of the graph. -/
def graphConormalD (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (y : Fin n → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  Fin.insertNth (α := fun _ => Fin (n + 1) → ℝ) i 0
    (fun k => Fin.insertNth (α := fun _ => ℝ) i 0 (fun l => -pd k (fun w => pd l γ w) y))

/-- **The Gibbons–Hawking–York density of the graph** at the point `(y, γ(y))`, with respect to `dy`. -/
def ghyGraph (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : (Fin n → ℝ) → ℝ)
    (i : Fin (n + 1)) (y : Fin n → ℝ) : ℝ :=
  ghyDensityOf g (graphConormal γ i y) (graphConormalD γ i y) (graphPt γ i y)

lemma continuous_graphPt (γ : (Fin n → ℝ) → ℝ) (hγ : Continuous γ) (i : Fin (n + 1)) :
    Continuous (fun y => graphPt γ i y) := by
  show Continuous fun y => Fin.insertNth (α := fun _ => ℝ) i (γ y) y
  exact Continuous.finInsertNth i hγ continuous_id

lemma continuous_graphConormal (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 1 γ) (i : Fin (n + 1)) :
    Continuous (fun y => graphConormal γ i y) := by
  show Continuous fun y => Fin.insertNth (α := fun _ => ℝ) i 1 (fun k => -pd k γ y)
  exact Continuous.finInsertNth i continuous_const
    (continuous_pi fun k => (continuous_pd_of_contDiff_one hγ k).neg)

lemma continuous_graphConormalD (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 2 γ) (i : Fin (n + 1)) :
    Continuous (fun y => graphConormalD γ i y) := by
  have h1 : ∀ l, ContDiff ℝ 1 (fun w => pd l γ w) := fun l => by
    unfold pd
    exact (hγ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  show Continuous fun y => Fin.insertNth (α := fun _ => Fin (n + 1) → ℝ) i 0
    (fun k => Fin.insertNth (α := fun _ => ℝ) i 0 (fun l => -pd k (fun w => pd l γ w) y))
  exact Continuous.finInsertNth i continuous_const (continuous_pi fun k =>
    Continuous.finInsertNth i continuous_const
      (continuous_pi fun l => (continuous_pd_of_contDiff_one (h1 l) k).neg))

/-- The flux through the graph is the integral of the contraction with the conormal. -/
lemma graphFlux_eq (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1))
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) :
    graphFlux γ i F = ∫ y : Fin n → ℝ, ∑ ρ, F ρ (graphPt γ i y) * graphConormal γ i y ρ := by
  unfold graphFlux
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show F i (graphPt γ i y) - ∑ k, pd k γ y * F (i.succAbove k) (graphPt γ i y) =
    ∑ ρ, F ρ (graphPt γ i y) * graphConormal γ i y ρ
  have hi : graphConormal γ i y i = 1 := by
    simp only [graphConormal, Fin.insertNth_apply_same]
  have hk : ∀ k, F (i.succAbove k) (graphPt γ i y) * graphConormal γ i y (i.succAbove k) =
      -(pd k γ y * F (i.succAbove k) (graphPt γ i y)) := by
    intro k
    simp only [graphConormal, Fin.insertNth_apply_succAbove]
    ring
  rw [Fin.sum_univ_succAbove _ i, hi, mul_one, Finset.sum_congr rfl fun k _ => hk k,
    Finset.sum_neg_distrib, sub_eq_add_neg]

/-- **A function vanishing on the graph has only a normal derivative there**: `∂_τ H = ν_τ ∂_i H`. -/
theorem pd_of_vanishing_on_graph (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 1 γ) (i : Fin (n + 1))
    (H : (Fin (n + 1) → ℝ) → ℝ) (hH : Differentiable ℝ H) (hz : ∀ y, H (graphPt γ i y) = 0)
    (y : Fin n → ℝ) (τ : Fin (n + 1)) :
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
    have h0 : pd (i.succAbove k) (fun w => H (shearFwd γ i w)) z = 0 :=
      pd_eq_zero_of_vanishing_on_hyperplane ((hH _).comp z (hΨ z)) i (i.succAbove k)
        (Fin.succAbove_ne i k) (fun w hw => by
          have e : shearFwd γ i w = graphPt γ i (i.removeNth w) := by
            unfold shearFwd graphPt
            rw [hw, hzi, zero_add]
          show H (shearFwd γ i w) = 0
          rw [e]
          exact hz _)
    rw [h0, hrem, hz0] at hc
    simp only [graphConormal, Fin.insertNth_apply_succAbove]
    linarith

variable (g h : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)

include hg hdet in
/-- The Gibbons–Hawking–York density of the graph is continuous along the graph at a parameter where the
graph is not null. -/
lemma continuousAt_ghyGraph (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 2 γ) (i : Fin (n + 1))
    (y₀ : Fin n → ℝ) (hN : (∑ a, graphConormal γ i y₀ a *
      ∑ b, (g (graphPt γ i y₀))⁻¹ a b * graphConormal γ i y₀ b) ≠ 0) :
    ContinuousAt (fun y => ghyGraph g γ i y) y₀ := by
  have hX := continuous_graphPt γ hγ.continuous i
  have hν := continuous_graphConormal γ (hγ.of_le (by norm_num)) i
  have hdν := continuous_graphConormalD γ hγ i
  have hνa : ∀ a, Continuous fun y => graphConormal γ i y a := fun a => (continuous_apply a).comp hν
  have hdνab : ∀ a b, Continuous fun y => graphConormalD γ i y a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp hdν)
  have hG : ∀ a b, Continuous fun y => (g (graphPt γ i y))⁻¹ a b := fun a b =>
    (contDiff_inv_entry g hg hdet a b).continuous.comp hX
  have hΓ : ∀ μ a b, Continuous fun y => christoffel g μ a b (graphPt γ i y) := fun μ a b =>
    (contDiff_christoffel g hg hdet μ a b).continuous.comp hX
  have hGc : Continuous g := continuous_matrix fun a b => (hg a b).continuous
  have hsq : Continuous fun y => √|(g (graphPt γ i y)).det| :=
    (Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)).comp hX
  have hNup : ∀ a, Continuous fun y => ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b :=
    fun a => continuous_finsetSum _ fun b _ => (hG a b).mul (hνa b)
  have hS : Continuous fun y => ∑ a, graphConormal γ i y a *
      ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b :=
    continuous_finsetSum _ fun a _ => (hνa a).mul (hNup a)
  have hopen : IsOpen {y : Fin n → ℝ | (∑ a, graphConormal γ i y a *
      ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0} :=
    isOpen_ne_fun hS continuous_const
  have hon : ContinuousOn (fun y => 2 * √|(g (graphPt γ i y)).det| * ∑ α, ∑ β,
      ((g (graphPt γ i y))⁻¹ α β -
        (∑ b, (g (graphPt γ i y))⁻¹ α b * graphConormal γ i y b) *
          (∑ b, (g (graphPt γ i y))⁻¹ β b * graphConormal γ i y b) /
        (∑ a, graphConormal γ i y a * ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b)) *
      (graphConormalD γ i y α β - ∑ μ, christoffel g μ α β (graphPt γ i y) * graphConormal γ i y μ))
      {y : Fin n → ℝ | (∑ a, graphConormal γ i y a *
        ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0} :=
    (continuous_const.mul hsq).continuousOn.mul (continuousOn_finsetSum _ fun α _ =>
      continuousOn_finsetSum _ fun β _ =>
        ((hG α β).continuousOn.sub
          (((hNup α).mul (hNup β)).continuousOn.div hS.continuousOn fun y hy => hy)).mul
          ((hdνab α β).sub (continuous_finsetSum _ fun μ _ => (hΓ μ α β).mul (hνa μ))).continuousOn)
  exact hon.continuousAt (hopen.mem_nhds hN)

include hg hdet in
/-- The Gibbons–Hawking–York density of the graph is continuous along the graph, if the graph is nowhere
null. -/
lemma continuous_ghyGraph (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 2 γ) (i : Fin (n + 1))
    (hN : ∀ y, (∑ a, graphConormal γ i y a *
      ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0) :
    Continuous (fun y => ghyGraph g γ i y) :=
  continuous_iff_continuousAt.2 fun y => continuousAt_ghyGraph g hg hdet γ hγ i y (hN y)

include hg hh hgs hhs hdet in
/-- **The Einstein–Hilbert action with the Gibbons–Hawking–York term on the region bounded by a graph**:
for a perturbation with compact support that vanishes on the graph, only the bulk variation remains. -/
theorem eh_ghy_variation_graph (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 2 γ)
    (i : Fin (n + 1)) (Λ : ℝ) {T : Set (Fin (n + 1) → ℝ)} (hT : IsCompact T)
    (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) (hbd : ∀ y, h (graphPt γ i y) = 0)
    (hN : ∀ y, (∑ a, graphConormal γ i y a *
      ∑ b, (g (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0)
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hST : ∀ y, graphPt γ i y ∈ T → y ∈ S) :
    HasDerivAt (fun t : ℝ =>
        (∫ x in T, lagDensity g h Λ t x ∂(volume.restrict (graphRegion σ γ i))) -
          (σ : ℝ) * ∫ y in S, ghyGraph (fun z => g z + t • h z) γ i y)
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β
        ∂(volume.restrict (graphRegion σ γ i))) 0 := by
  have hmain := eh_variation_piece g h hg hh hgs hhs hdet hT (graphRegion σ γ i) Λ
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  have hEm := measurableSet_graphRegion σ γ hγ.continuous.measurable i
  have hFs : ∀ ρ, ContDiff ℝ ∞ (ehFlux g h ρ) := fun ρ => contDiff_flux g h hg hh hdet ρ
  -- the perturbation and the flux vanish outside `T`
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
  -- the two parts of the bulk variation
  have hGc : Continuous g := continuous_matrix fun a b => (hg a b).continuous
  have hbulk : Continuous (fun x => -√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) :=
    ((Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)).neg).mul
      (continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
        (hh α β).continuous.mul (contDiff_einsteinUp g hg hdet hgs Λ α β).continuous)
  have hdivc : Continuous (ehFluxDiv g h) := by
    unfold ehFluxDiv
    exact continuous_finsetSum _ fun ρ _ => (contDiff_pd (hFs ρ) ρ).continuous
  have hle : ((volume : Measure (Fin (n + 1) → ℝ)).restrict (graphRegion σ γ i)).restrict T ≤
      (volume : Measure (Fin (n + 1) → ℝ)).restrict T :=
    Measure.restrict_mono subset_rfl Measure.restrict_le_self
  have hsplit : ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
        (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
        ehFluxDiv g h x) ∂(volume.restrict (graphRegion σ γ i)) =
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β
          ∂(volume.restrict (graphRegion σ γ i))) +
        ∫ x in T, ehFluxDiv g h x ∂(volume.restrict (graphRegion σ γ i)) := by
    have i1 : IntegrableOn (fun x => -√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β)
        T (volume.restrict (graphRegion σ γ i)) :=
      Integrable.mono_measure (hbulk.continuousOn.integrableOn_compact hT) hle
    have i2 : IntegrableOn (ehFluxDiv g h) T (volume.restrict (graphRegion σ γ i)) :=
      Integrable.mono_measure (hdivc.continuousOn.integrableOn_compact hT) hle
    have e1 : ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
          ehFluxDiv g h x) ∂(volume.restrict (graphRegion σ γ i)) =
        ∫ x in T, ((-√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) +
          ehFluxDiv g h x) ∂(volume.restrict (graphRegion σ γ i)) := rfl
    have e2 : ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β)
          ∂(volume.restrict (graphRegion σ γ i)) =
        -∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β
          ∂(volume.restrict (graphRegion σ γ i)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show -√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β =
        -(√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β)
      ring
    rw [e1, integral_add i1 i2, e2]
  -- the divergence theorem on the graph region
  have hdiv : ∫ x in T, ehFluxDiv g h x ∂(volume.restrict (graphRegion σ γ i)) =
      -((σ : ℝ) * graphFlux γ i (ehFlux g h)) := by
    rw [Measure.restrict_restrict hTm]
    have h1 : ∫ x in T ∩ graphRegion σ γ i, ehFluxDiv g h x =
        ∫ x in graphRegion σ γ i, ehFluxDiv g h x := by
      rw [← integral_indicator (hTm.inter hEm), ← integral_indicator hEm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hxT : x ∈ T
      · by_cases hxE : x ∈ graphRegion σ γ i
        · rw [indicator_of_mem (Set.mem_inter hxT hxE), indicator_of_mem hxE]
        · rw [indicator_of_notMem (fun h' : x ∈ T ∩ graphRegion σ γ i => hxE h'.2),
            indicator_of_notMem hxE]
      · have h0 : ehFluxDiv g h x = 0 :=
          ehFluxDiv_eq_zero_of_eventuallyEq g h hg hh x (hzero x hxT)
        simp only [indicator, h0, ite_self]
    rw [h1]
    exact integral_divergence_graphRegion σ γ hγ i (ehFlux g h) (fun ρ => (hFs ρ).of_le (by simp)) hFc
  rw [hsplit, hdiv] at hmain
  -- the boundary term is affine in `t`
  have hX := continuous_graphPt γ hγ.continuous i
  have hν := continuous_graphConormal γ (hγ.of_le (by norm_num)) i
  have hpt : ∀ (t : ℝ) (y : Fin n → ℝ), ghyGraph (fun z => g z + t • h z) γ i y =
      ghyGraph g γ i y + t * (-∑ ρ, ehFlux g h ρ (graphPt γ i y) * graphConormal γ i y ρ) := by
    intro t y
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
      pd_of_vanishing_on_graph γ (hγ.of_le (by norm_num)) i (fun z => h z a b)
        ((hh a b).differentiable (by simp)) (fun y' => by
          show h (graphPt γ i y') a b = 0
          rw [hbd y']
          rfl) y τ
    have hk : ∀ a b, pd i (fun z => h z a b) (graphPt γ i y) =
        pd i (fun z => h z b a) (graphPt γ i y) := fun a b => by
      have e : (fun z => h z a b) = fun z => h z b a := funext fun z => hhs z a b
      rw [e]
    unfold ghyGraph
    rw [ghyDensityOf_add_smul_of_zero g h _ _ _ hgd hhd (hbd y) t,
      ghySlopeOf_eq_neg_flux g h _ _ (fun a b => pd i (fun z => h z a b) (graphPt γ i y)) (hbd y)
        hpd hinv hk (hN y)]
  have hc0 : Continuous fun y => ghyGraph g γ i y := continuous_ghyGraph g hg hdet γ hγ i hN
  have hsl : Continuous fun y => -∑ ρ, ehFlux g h ρ (graphPt γ i y) * graphConormal γ i y ρ :=
    (continuous_finsetSum _ fun ρ _ =>
      ((hFs ρ).continuous.comp hX).mul ((continuous_apply ρ).comp hν)).neg
  have hslI : ∫ y in S, -∑ ρ, ehFlux g h ρ (graphPt γ i y) * graphConormal γ i y ρ =
      -graphFlux γ i (ehFlux g h) := by
    rw [integral_neg, graphFlux_eq]
    congr 1
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      Finset.sum_eq_zero fun ρ _ => by
        rw [hflux0 _ (fun hT' => hy (hST y hT')) ρ, zero_mul]
  have hB : ∀ t : ℝ, ∫ y in S, ghyGraph (fun z => g z + t • h z) γ i y =
      (∫ y in S, ghyGraph g γ i y) + t * (-graphFlux γ i (ehFlux g h)) := by
    intro t
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y => hpt t y)).trans ?_
    rw [integral_add (hc0.continuousOn.integrableOn_compact hS)
      ((hsl.continuousOn.integrableOn_compact hS).const_mul t), integral_const_mul, hslI]
  have hlin : HasDerivAt (fun t : ℝ => (∫ y in S, ghyGraph g γ i y) +
      t * (-graphFlux γ i (ehFlux g h))) (-graphFlux γ i (ehFlux g h)) 0 := by
    have h3 := ((hasDerivAt_id' (0 : ℝ)).mul_const (-graphFlux γ i (ehFlux g h))).const_add
      (∫ y in S, ghyGraph g γ i y)
    rw [one_mul] at h3
    exact h3
  have hfun : (fun t : ℝ =>
        (∫ x in T, lagDensity g h Λ t x ∂(volume.restrict (graphRegion σ γ i))) -
          (σ : ℝ) * ∫ y in S, ghyGraph (fun z => g z + t • h z) γ i y) =
      fun t : ℝ => (∫ x in T, lagDensity g h Λ t x ∂(volume.restrict (graphRegion σ γ i))) -
        (σ : ℝ) * ((∫ y in S, ghyGraph g γ i y) + t * (-graphFlux γ i (ehFlux g h))) :=
    funext fun t => by rw [hB t]
  rw [hfun]
  exact (hmain.fun_sub (hlin.const_mul (σ : ℝ))).congr_deriv (by ring)

end Lightlike

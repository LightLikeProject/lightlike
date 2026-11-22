import Lightlike.Spacetime.RaychaudhuriManifold
import Lightlike.Spacetime.Raychaudhuri.RicciBound

/-!
# Focusing under a uniform positive Ricci bound, on a manifold (GE3, Tier 1)

`raychaudhuri_focusing_manifold_at` (`RaychaudhuriManifold.lean`) discards the Ricci term once `Ric(V, V) ≥ 0`. Here the
sharper inequality `V(Θ) ≤ -Θ²/(n-1) - Ric(V, V)` is proved in coordinates (`raychaudhuri_ricci_ineq_at`) and on a
manifold (`raychaudhuri_ricci_ineq_manifold_at`), and joined with `focusing_ricci_pi` (`RicciBound.lean`): a unit geodesic
rotation-free congruence with `Ric(V, V) ≥ c > 0` along an integral curve cannot be defined on a parameter interval longer
than `π (n-1)/√((n-1) c)`, whatever the initial expansion is (`raychaudhuri_focusing_ricci_manifold`).
-/

open Filter Topology Set Matrix Bundle Manifold Real
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike

section Coord

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {v : (Fin n → ℝ) → Fin n → ℝ}

/-- **The sharp focusing inequality in coordinates** (Kar–SenGupta, after (12)): for a unit geodesic field of a Lorentzian
coordinate metric with `ω = 0` at `x`, `v(Θ) ≤ -Θ²/(n-1) - R(v, v)`. -/
theorem raychaudhuri_ricci_ineq_at (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
    (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0) (hnorm : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = -1)
    (hgL : IsLorentzianCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (hn : 1 < n)
    (hω : rotation g v x = 0) :
    ∑ c, v x c * pd c (expansion g v) x ≤
      -(expansion g v x) ^ 2 / (n - 1) - ∑ s, ∑ t, ricci g s t x * v x s * v x t := by
  rw [raychaudhuri_equation hgL.1 hv hgeo hx (hnorm x hx) hn, hω]
  have hσ := shear_normSq_nonneg hv hgeo hnorm hgL hx
  have h0 : Raychaudhuri.normSqG (g x) 0 = 0 := by simp [Raychaudhuri.normSqG]
  rw [h0]
  linarith

end Coord

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)

/-- **The sharp focusing inequality on a manifold**: for a Lorentzian metric with its Levi-Civita connection and a smooth
unit geodesic vector field, rotation-free at `x`: `V(Θ) ≤ -Θ²/(n-1) - Ric(V, V)` at `x`. -/
theorem raychaudhuri_ricci_ineq_manifold_at (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    {x : M} (hgeo : ∀ᶠ q in 𝓝 x, cov V q (V q) = 0) (hnorm : ∀ᶠ q in 𝓝 x, gL.g q (V q) (V q) = -1) (hn : 1 < n)
    (hrot : ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, gL.g x (cov V x u) w = gL.g x (cov V x w) u) :
    expansionDeriv cov V x ≤
      -(expansionM cov V x) ^ 2 / (n - 1) - cov.ricciAt x (V x) (V x) := by
  set g := gL.toNondegMetric
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hx0 : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) = x :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hxs
  have hy0 : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hxs
  have hmd : ∀ q, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q :=
    fun q => (hV q).mdifferentiableAt (by simp)
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1
    ((hgeo.and hnorm).and ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hxs))
  set U := (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm ⁻¹' W with hU
  have hUo : IsOpen U :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hWo
  have hy0U : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ U := ⟨hy0, by simp only [mem_preimage, hx0]; exact hxW⟩
  have hgL : IsLorentzianCoordMetric (g.coordMetric x) U :=
    (gL.isLorentzianCoordMetric_coordMetric x).of_subset hUo inter_subset_left
  have hvU : ∀ a, ContDiffOn ℝ ∞ (fun y => chartComp x V y a) U := fun a =>
    (contDiffOn_chartComp hV x a).mono inter_subset_left
  have hgeoU : ∀ y ∈ U, ∀ d, ∑ c, chartComp x V y c * covD (g.coordMetric x) (chartComp x V) d c y = 0 := by
    intro y hy d
    have hq := hWsub hy.2
    have e := hv_cov_eq x cov g h hy.1 (hmd _) (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y))
    have hvV : hv x _ (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) = chartComp x V y := rfl
    rw [hq.1.1, hvV] at e
    have e2 := congrFun e d
    have h0 : hv x ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y) (0 : TangentSpace 𝓘(ℝ, Fin n → ℝ) _) = 0 :=
      ((tTriv (E := Fin n → ℝ) x).linear ℝ (symm_mem_chartTriv_baseSet x hy.1)).map_zero
    rw [h0] at e2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, covDMat, Matrix.of_apply] at e2
    rw [e2]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have hnormU : ∀ y ∈ U, chartComp x V y ⬝ᵥ (g.coordMetric x y *ᵥ chartComp x V y) = -1 := by
    intro y hy
    have hq := hWsub hy.2
    have e := g_hv x g hy.1 (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y))
    have hc : chartComp x V y = hv x _ (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) := rfl
    rw [hc, ← e]
    exact hq.1.2
  have hvx : hv x x (V x) = chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    simp only [chartComp, hx0]; rfl
  have hω := rotation_chart_eq_zero cov g h (hmd x) hrot
  have key := raychaudhuri_ricci_ineq_at hvU hgeoU hnormU hgL hy0U hn hω
  unfold expansionDeriv
  rw [mfderiv_expansionM cov g h hV x, expansionM_eq cov g h hV x hxs, ricciAt_hv' x cov g h hxs (V x), hvx]
  exact key

set_option backward.isDefEq.respectTransparency false in
/-- **Focusing under a uniform positive Ricci bound on a manifold** (timelike Bonnet–Myers type): for a Lorentzian metric
with its Levi-Civita connection and a smooth vector field `V`, along an integral curve `γ` of `V` on `[0, L)` near which
`V` is unit, geodesic and rotation-free, with `Ric(V, V) ≥ c > 0` along `γ`: `L ≤ π (n-1)/√((n-1) c)`, whatever the initial
expansion. -/
theorem raychaudhuri_focusing_ricci_manifold (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (hn : 1 < n) {γ : ℝ → M} {L c : ℝ}
    (hc : 0 < c)
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u)
    (hR : ∀ s ∈ Ico 0 L, c ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s))) :
    L ≤ π * (((n : ℝ) - 1) / √(((n : ℝ) - 1) * c)) := by
  have hm : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  refine focusing_ricci_pi (Θ := fun s => expansionM cov V (γ s))
    (Θ' := fun s => expansionDeriv cov V (γ s)) hm hc ?_ ?_
  · intro s hs
    have h1 := (mdifferentiableAt_expansionM cov gL.toNondegMetric h hV (γ s)).hasMFDerivAt
    show HasDerivAt (expansionM cov V ∘ γ) (expansionDeriv cov V (γ s)) s
    rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
    apply (h1.comp s (hγ s hs)).congr_mfderiv
    rw [ContinuousLinearMap.ext_iff]
    intro a
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul]
    rfl
  · intro s hs
    have := raychaudhuri_ricci_ineq_manifold_at cov gL h hV (hgeo s hs) (hnorm s hs) hn (hrot s hs)
    linarith [hR s hs]

end Manifold

end Lightlike

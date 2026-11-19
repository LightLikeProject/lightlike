import Lightlike.Spacetime.RaychaudhuriManifold
import Lightlike.Spacetime.RaychaudhuriNull

/-!
# Null geodesic focusing on a manifold (G1-009)

Kar and SenGupta (gr-qc/0611123), Section D, (17) and the sentence after it: the focusing theorem for null geodesic
congruences follows as for timelike ones under the null convergence condition `R_ab kᵃ kᵇ ≥ 0`. Here, for a Lorentzian metric
on a manifold modelled on `ℝⁿ` (`n ≥ 3`) with its Levi-Civita connection and a smooth null geodesic vector field `V`
(rotation-free, `Ric(V, V) ≥ 0`, an auxiliary null vector `N` with `g(V, N) = -1`): `V(Θ) ≤ -Θ²/(n-2)`
(`raychaudhuri_null_focusing_manifold_at`), and along an integral curve with `Θ(γ(0)) < 0`, `L ≤ (n-2)/|Θ(γ(0))|`
(`raychaudhuri_null_focusing_manifold`), read in the chart from the coordinate statements (`RaychaudhuriNull.lean`).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Matrix Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)


/-- The projection onto the screen of `V` and an auxiliary null `N`: `π u = u + g(N, u) V + g(V, u) N`. -/
def screenProj (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) {x : M}
    (N u : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) : TangentSpace 𝓘(ℝ, Fin n → ℝ) x :=
  u + g.g x N u • V x + g.g x (V x) u • N

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The entries of a matrix as pairings with the coordinate vectors. -/
theorem matrix_apply_eq_dot (A : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    A a b = Pi.single a (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single b 1) := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **Zero screen rotation in the chart**: if `g(∇_{π u} V, π w) = g(∇_{π w} V, π u)` for all `u, w` at `x`, the coordinate
null rotation `ω̂` vanishes at `φ(x)` (for the components of `N`). -/
theorem nullRotation_chart_eq_zero (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
    {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {x : M}
    (hV : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x)
    {N : TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
    (hscr : ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, g.g x (cov V x (screenProj g V N u)) (screenProj g V N w) =
      g.g x (cov V x (screenProj g V N w)) (screenProj g V N u)) :
    nullRotation (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) (hv x x N) = 0 := by
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hx0 : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) = x :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hxs
  have hb := mem_baseSet_of_mem_source x hxs
  set G := g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) with hGdef
  have hG : Gᵀ = G := g.coordMetric_transpose x _
  have hGu : IsUnit G.det := g.coordMetric_isUnit_det x ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hxs)
  set k := chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) with hk
  set Nc := hv x x N with hNc
  have hvx : hv x x (V x) = k := by simp only [hk, chartComp, hx0]; rfl
  set P := nullProj (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) Nc with hPdef
  set M := covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) with hMdef
  have hPe : P = 1 + Matrix.vecMulVec k (G *ᵥ Nc) + Matrix.vecMulVec Nc (G *ᵥ k) := by
    simp only [hPdef, nullProj]; exact Raychaudhuri.inv_mul_nullScreen hGu
  -- the components of `π u`
  have hπ : ∀ u, hv x x (screenProj g V N u) = P *ᵥ hv x x u := by
    intro u
    unfold screenProj
    rw [hv_add x hb, hv_add x hb, hv_smul' x hb, hv_smul' x hb, hvx, g_hv' x g hxs N u, g_hv' x g hxs (V x) u, hvx,
      ← hGdef, hPe, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
      Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, dotProduct_comm (G *ᵥ Nc),
      dotProduct_comm (G *ᵥ k), Raychaudhuri.dot_G_comm hG (hv x x u) Nc, Raychaudhuri.dot_G_comm hG (hv x x u) k]
  have hcov : ∀ u, hv x x (cov V x u) = M *ᵥ hv x x u := fun u => hv_cov_eq' x cov g h hxs hV u
  -- `g P = Pᵀ g`
  have hGP : G * P = Pᵀ * G := by
    have hh : G * P = Raychaudhuri.nullScreen G k Nc := by
      simp only [hPdef, nullProj]
      rw [← hGdef, ← hk, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mul]
    rw [hh]
    have : (G * P)ᵀ = G * P := by rw [hh]; exact Raychaudhuri.nullScreen_transpose hG
    rw [Matrix.transpose_mul, hG, hh] at this
    exact this.symm
  have hent : ∀ a b, (G * nullB (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) Nc) a b =
      g.g x (cov V x (screenProj g V N ((tTriv (E := Fin n → ℝ) x).symmL ℝ x (Pi.single b 1))))
        (screenProj g V N ((tTriv (E := Fin n → ℝ) x).symmL ℝ x (Pi.single a 1))) := by
    intro a b
    rw [g_hv' x g hxs, ← hGdef, hcov, hπ, hπ, hv_symmL x hb, hv_symmL x hb,
      matrix_apply_eq_dot (G * nullB (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) Nc) a b]
    show Pi.single a 1 ⬝ᵥ ((G * (P * M * P)) *ᵥ Pi.single b 1) = _
    rw [show G * (P * M * P) = Pᵀ * G * (M * P) by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGP]; simp only [Matrix.mul_assoc],
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul, hG,
      Matrix.transpose_transpose, ← Matrix.mulVec_mulVec, Raychaudhuri.dot_G_comm hG]
    rw [← Matrix.mulVec_mulVec, dotProduct_comm, Raychaudhuri.dot_G_comm hG]
  unfold nullRotation
  have hsym : (G * nullB (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) Nc)ᵀ =
      G * nullB (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) Nc := by
    ext a b
    rw [Matrix.transpose_apply, hent, hent, hscr]
  rw [hsym, sub_self, smul_zero]

/-- **The null focusing inequality on a manifold** (Kar–SenGupta, after (17)): for a Lorentzian metric, its Levi-Civita
connection and a smooth null (`g(V, V) = 0` near `x`) geodesic vector field that is rotation-free at `x`, with
`Ric(V, V) ≥ 0` at `x` and an auxiliary null `N ∈ T_x M` with `g(V, N) = -1`: `V(Θ) ≤ -Θ²/(n-2)` at `x`. -/
theorem raychaudhuri_null_focusing_manifold_at (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    {x : M} (hgeo : ∀ᶠ q in 𝓝 x, cov V q (V q) = 0) (hnorm : ∀ᶠ q in 𝓝 x, gL.g q (V q) (V q) = 0) (hn : 2 < n)
    (hN : ∃ N : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, gL.g x N N = 0 ∧ gL.g x (V x) N = -1 ∧
      ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, gL.g x (cov V x (screenProj gL.toNondegMetric V N u))
        (screenProj gL.toNondegMetric V N w) =
        gL.g x (cov V x (screenProj gL.toNondegMetric V N w)) (screenProj gL.toNondegMetric V N u))
    (hR : 0 ≤ cov.ricciAt x (V x) (V x)) :
    expansionDeriv cov V x ≤ -(expansionM cov V x) ^ 2 / (n - 2) := by
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
  have hnormU : ∀ y ∈ U, chartComp x V y ⬝ᵥ (g.coordMetric x y *ᵥ chartComp x V y) = 0 := by
    intro y hy
    have hq := hWsub hy.2
    have e := g_hv x g hy.1 (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y))
    have hc : chartComp x V y = hv x _ (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) := rfl
    rw [hc, ← e]
    exact hq.1.2
  have hvx : hv x x (V x) = chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    simp only [chartComp, hx0]; rfl
  have hRc : 0 ≤ ∑ s, ∑ t, ricci (g.coordMetric x) s t (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
      chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) s * chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) t := by
    rw [← hvx, ← ricciAt_hv' x cov g h hxs (V x)]; exact hR
  have hNc : ∃ N' : Fin n → ℝ, N' ⬝ᵥ (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *ᵥ N') = 0 ∧
      chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) ⬝ᵥ (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *ᵥ N') = -1 ∧
      nullRotation (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) N' = 0 := by
    obtain ⟨N, hNN, hkN, hscr⟩ := hN
    refine ⟨hv x x N, ?_, ?_, nullRotation_chart_eq_zero cov g h (hmd x) hscr⟩
    · rw [← g_hv' x g hxs]; exact hNN
    · rw [← hvx, ← g_hv' x g hxs]; exact hkN
  have key := raychaudhuri_null_focusing_at hgL hvU hgeoU hnormU hy0U hn hNc hRc
  unfold expansionDeriv
  rw [mfderiv_expansionM cov g h hV x, expansionM_eq cov g h hV x hxs]
  exact key

set_option backward.isDefEq.respectTransparency false in
/-- **Null geodesic focusing on a manifold** (Kar–SenGupta, after (17): the null convergence condition): for a Lorentzian
metric (`n ≥ 3`) with its Levi-Civita connection and a smooth vector field `V`, along an integral curve `γ` of `V` on
`[0, L)` near which `V` is null and geodesic, rotation-free with `Ric(V, V) ≥ 0` and an auxiliary null vector along `γ`,
that starts converging (`Θ(γ(0)) < 0`): `L ≤ (n-2)/|Θ(γ(0))|`. -/
theorem raychaudhuri_null_focusing_manifold (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (hn : 2 < n) {γ : ℝ → M} {L : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = 0)
    (hN : ∀ s ∈ Ico 0 L, ∃ N : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s), gL.g (γ s) N N = 0 ∧ gL.g (γ s) (V (γ s)) N = -1 ∧
      ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s), gL.g (γ s) (cov V (γ s) (screenProj gL.toNondegMetric V N u))
        (screenProj gL.toNondegMetric V N w) =
        gL.g (γ s) (cov V (γ s) (screenProj gL.toNondegMetric V N w)) (screenProj gL.toNondegMetric V N u))
    (hR : ∀ s ∈ Ico 0 L, 0 ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s)))
    (h0 : expansionM cov V (γ 0) < 0) : L ≤ (n - 2) / |expansionM cov V (γ 0)| := by
  have hm : (0 : ℝ) < n - 2 := by
    have : (2 : ℝ) < n := by exact_mod_cast hn
    linarith
  refine focusing (Θ := fun s => expansionM cov V (γ s)) (Θ' := fun s => expansionDeriv cov V (γ s)) hm ?_ ?_ h0
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
    exact raychaudhuri_null_focusing_manifold_at cov gL h hV (hgeo s hs) (hnorm s hs) hn (hN s hs) (hR s hs)

end Lightlike

import Lightlike.Spacetime.PenroseSingularity.JacobiCompat
import Lightlike.Spacetime.PenroseSingularity.JacobiLocal
import Lightlike.Spacetime.PenroseSingularity.JacobiGeom

/-!
# Orthogonality and symmetry for an `m`-parameter family of null geodesics, in a chart (G1-012, D3b)

For `H(t, σ)` a `C³` family of geodesics in `t` (for each `σ`) with null velocity `∂_t H`, the functions
`ω_j = g(∂_t H, ∂_{σ_j} H)` satisfy `∂_t ω_j = 0`; if `ω_j ≡ 0` then `g(P_i, J_j)` is symmetric in `i, j`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- Derivative of a directional derivative along a curve (chain rule), on a general base. -/
theorem hasDerivAt_fderiv_comp' {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} {q : ℝ → X} {q' : X} {r : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (q r)) (hq : HasDerivAt q q' r) (v : X) :
    HasDerivAt (fun r => fderiv ℝ f (q r) v) (fderiv ℝ (fderiv ℝ f) (q r) q' v) r := by
  have h := hf.hasFDerivAt.comp_hasDerivAt r hq
  simpa using h.clm_apply (hasDerivAt_const r v)

/-- The `t`-derivative of `ω_j = g(∂_t H, ∂_{σ_j} H)` vanishes for a family of null geodesics. -/
theorem omega_hasDerivAt_zero (hg : Lightlike.IsCoordMetric g U)
    {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))} (hW : IsOpen W)
    (hH : ContDiffOn ℝ 3 H W) (hU : ∀ p ∈ W, H p ∈ U)
    (hgeo : ∀ p ∈ W, Lightlike.Geodesic.IsGeodesicOn g (fun t => H (t, p.2))
      (fun t => fderiv ℝ H (t, p.2) (1, 0)) {t | (t, p.2) ∈ W})
    (hnull : ∀ p ∈ W, gpairAt g (H p) (fderiv ℝ H p (1, 0)) (fderiv ℝ H p (1, 0)) = 0)
    {p : ℝ × (Fin m → ℝ)} (hp : p ∈ W) (j : Fin m) :
    HasDerivAt (fun t => gpairAt g (H (t, p.2)) (fderiv ℝ H (t, p.2) (1, 0))
      (fderiv ℝ H (t, p.2) (0, Pi.single j 1))) 0 p.1 := by
  classical
  set σ := p.2 with hσ
  set t := p.1 with ht
  have hpe : p = (t, σ) := rfl
  -- smoothness at the points of `W`
  have hC : ∀ q ∈ W, ContDiffAt ℝ 3 H q := fun q hq => hH.contDiffAt (hW.mem_nhds hq)
  have hd0 : ∀ q ∈ W, DifferentiableAt ℝ H q := fun q hq => (hC q hq).differentiableAt (by norm_num)
  have hf2 : ∀ q ∈ W, ContDiffAt ℝ 2 (fderiv ℝ H) q := fun q hq => (hC q hq).fderiv_right (by norm_num)
  have hd1 : ∀ q ∈ W, DifferentiableAt ℝ (fderiv ℝ H) q := fun q hq =>
    (hf2 q hq).differentiableAt (by norm_num)
  have hsym : ∀ q ∈ W, ∀ u v, fderiv ℝ (fderiv ℝ H) q u v = fderiv ℝ (fderiv ℝ H) q v u := fun q hq u v =>
    (((hC q hq).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])) u v
  set ej : Fin m → ℝ := Pi.single j 1 with hej
  have hqt : HasDerivAt (fun t' : ℝ => ((t', σ) : ℝ × (Fin m → ℝ))) ((1, 0) : ℝ × (Fin m → ℝ)) t := by
    simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t σ)
  have hpW : (t, σ) ∈ W := hp
  have hγ : HasDerivAt (fun t' : ℝ => H (t', σ)) (fderiv ℝ H (t, σ) (1, 0)) t :=
    (hgeo p hp).pos t (by simpa using hp)
  have hw : HasDerivAt (fun t' : ℝ => fderiv ℝ H (t', σ) (1, 0))
      (Lightlike.Geodesic.accel g (H (t, σ)) (fderiv ℝ H (t, σ) (1, 0))) t :=
    (hgeo p hp).vel t (by simpa using hp)
  have hJ : HasDerivAt (fun t' : ℝ => fderiv ℝ H (t', σ) (0, ej))
      (fderiv ℝ (fderiv ℝ H) (t, σ) (1, 0) (0, ej)) t :=
    hasDerivAt_fderiv_comp' (hd1 _ hpW) hqt (0, ej)
  have hh := hasDerivAt_gpair hg hγ (hU _ hpW) hw hJ
  -- the first term vanishes: `D_t w = 0`
  have hcw : (fun a => covDAlong g (H (t, σ)) (fderiv ℝ H (t, σ) (1, 0)) (fderiv ℝ H (t, σ) (1, 0))
      (Lightlike.Geodesic.accel g (H (t, σ)) (fderiv ℝ H (t, σ) (1, 0))) a) = 0 := by
    funext a
    simp [covDAlong, Lightlike.Geodesic.accel]
  -- the second term: use the `σ_j`-derivative of `g(∂_t H, ∂_t H) = 0`
  set c : ℝ → ℝ × (Fin m → ℝ) := fun s => (t, σ + s • ej) with hc
  have hcd : HasDerivAt c ((0, ej) : ℝ × (Fin m → ℝ)) 0 := by
    have : HasDerivAt (fun s : ℝ => σ + s • ej) ej 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ej).const_add σ
    simpa [hc] using (hasDerivAt_const (0 : ℝ) t).prodMk this
  have hc0 : c 0 = (t, σ) := by simp [hc]
  have hγs : HasDerivAt (fun s : ℝ => H (c s)) (fderiv ℝ H (t, σ) (0, ej)) 0 := by
    have := (hd0 (c 0) (by rw [hc0]; exact hpW)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcd
    rw [hc0] at this
    exact this
  have hcW : ∀ᶠ s in 𝓝 (0 : ℝ), c s ∈ W := by
    have hcont : Continuous c := by fun_prop
    exact hcont.continuousAt.eventually (hW.mem_nhds (by rw [hc0]; exact hpW))
  have hWs : HasDerivAt (fun s : ℝ => fderiv ℝ H (c s) (1, 0))
      (fderiv ℝ (fderiv ℝ H) (c 0) (0, ej) (1, 0)) 0 :=
    hasDerivAt_fderiv_comp' (hd1 (c 0) (by rw [hc0]; exact hpW)) hcd (1, 0)
  have hgs := hasDerivAt_gpair hg hγs (by rw [hc0]; exact hU _ hpW) hWs hWs
  have hz : HasDerivAt (fun s : ℝ => gpairAt g (H (c s)) (fderiv ℝ H (c s) (1, 0))
      (fderiv ℝ H (c s) (1, 0))) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hcW] with s hs using hnull _ hs
  have hzero := hgs.unique hz
  rw [hc0] at hzero
  -- identify the two covariant derivatives
  have hsw : fderiv ℝ (fderiv ℝ H) (t, σ) (0, ej) (1, 0) = fderiv ℝ (fderiv ℝ H) (t, σ) (1, 0) (0, ej) :=
    hsym _ hpW _ _
  have hXeq : (fun a => covDAlong g (H (t, σ)) (fderiv ℝ H (t, σ) (0, ej))
      (fderiv ℝ H (t, σ) (1, 0)) (fderiv ℝ (fderiv ℝ H) (t, σ) (0, ej) (1, 0)) a) =
      (fun a => covDAlong g (H (t, σ)) (fderiv ℝ H (t, σ) (1, 0))
        (fderiv ℝ H (t, σ) (0, ej)) (fderiv ℝ (fderiv ℝ H) (t, σ) (1, 0) (0, ej)) a) := by
    have hcomm := Lightlike.Geodesic.gammaApply_comm hg (hU _ hpW) (fderiv ℝ H (t, σ) (0, ej))
      (fderiv ℝ H (t, σ) (1, 0))
    funext a
    have := congrFun hcomm a
    simp only [covDAlong, Lightlike.Geodesic.gammaApply] at this ⊢
    rw [hsw, this]
  have hsymm_g := gpairAt_symm hg (hU _ hpW)
  rw [hXeq] at hzero
  rw [hcw] at hh
  have h0 : gpairAt g (H (t, σ)) (0 : Fin n → ℝ) (fderiv ℝ H (t, σ) (0, ej)) = 0 := by
    simp [gpairAt]
  rw [h0, zero_add] at hh
  have h2 : gpairAt g (H (t, σ)) (fderiv ℝ H (t, σ) (1, 0)) (fun a => covDAlong g (H (t, σ))
      (fderiv ℝ H (t, σ) (1, 0)) (fderiv ℝ H (t, σ) (0, ej))
      (fderiv ℝ (fderiv ℝ H) (t, σ) (1, 0) (0, ej)) a) = 0 := by
    have hs2 := hsymm_g (fderiv ℝ H (t, σ) (1, 0)) (fun a => covDAlong g (H (t, σ))
      (fderiv ℝ H (t, σ) (1, 0)) (fderiv ℝ H (t, σ) (0, ej))
      (fderiv ℝ (fderiv ℝ H) (t, σ) (1, 0) (0, ej)) a)
    linarith
  rw [h2] at hh
  exact hh

end Lightlike.Penrose

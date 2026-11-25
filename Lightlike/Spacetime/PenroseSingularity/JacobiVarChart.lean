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

/-- Differentiating `g(∂_t H, ∂_{σ_j} H) ≡ 0` in the direction `e`. -/
theorem omega_dir_eq (hg : Lightlike.IsCoordMetric g U)
    {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))} (hW : IsOpen W)
    (hH : ContDiffOn ℝ 3 H W) (hU : ∀ p ∈ W, H p ∈ U)
    (hω : ∀ q ∈ W, ∀ j : Fin m, gpairAt g (H q) (fderiv ℝ H q (1, 0)) (fderiv ℝ H q (0, Pi.single j 1)) = 0)
    {p : ℝ × (Fin m → ℝ)} (hp : p ∈ W) (e : Fin m → ℝ) (j : Fin m) :
    gpairAt g (H p) (fun a => covDAlong g (H p) (fderiv ℝ H p (0, e)) (fderiv ℝ H p (1, 0))
        (fderiv ℝ (fderiv ℝ H) p (0, e) (1, 0)) a) (fderiv ℝ H p (0, Pi.single j 1)) +
      gpairAt g (H p) (fderiv ℝ H p (1, 0)) (fun a => covDAlong g (H p) (fderiv ℝ H p (0, e))
        (fderiv ℝ H p (0, Pi.single j 1)) (fderiv ℝ (fderiv ℝ H) p (0, e) (0, Pi.single j 1)) a) = 0 := by
  classical
  have hC : ∀ q ∈ W, ContDiffAt ℝ 3 H q := fun q hq => hH.contDiffAt (hW.mem_nhds hq)
  have hd0 : ∀ q ∈ W, DifferentiableAt ℝ H q := fun q hq => (hC q hq).differentiableAt (by norm_num)
  have hf2 : ∀ q ∈ W, ContDiffAt ℝ 2 (fderiv ℝ H) q := fun q hq => (hC q hq).fderiv_right (by norm_num)
  have hd1 : ∀ q ∈ W, DifferentiableAt ℝ (fderiv ℝ H) q := fun q hq =>
    (hf2 q hq).differentiableAt (by norm_num)
  set c : ℝ → ℝ × (Fin m → ℝ) := fun s => (p.1, p.2 + s • e) with hc
  have hcd : HasDerivAt c ((0, e) : ℝ × (Fin m → ℝ)) 0 := by
    have : HasDerivAt (fun s : ℝ => p.2 + s • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p.2
    simpa [hc] using (hasDerivAt_const (0 : ℝ) p.1).prodMk this
  have hc0 : c 0 = p := by simp [hc]
  have hcW : ∀ᶠ s in 𝓝 (0 : ℝ), c s ∈ W := by
    have hcont : Continuous c := by fun_prop
    exact hcont.continuousAt.eventually (hW.mem_nhds (by rw [hc0]; exact hp))
  have hγs : HasDerivAt (fun s : ℝ => H (c s)) (fderiv ℝ H p (0, e)) 0 := by
    have := (hd0 (c 0) (by rw [hc0]; exact hp)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcd
    rw [hc0] at this
    exact this
  have hW1 : HasDerivAt (fun s : ℝ => fderiv ℝ H (c s) (1, 0))
      (fderiv ℝ (fderiv ℝ H) (c 0) (0, e) (1, 0)) 0 :=
    hasDerivAt_fderiv_comp' (hd1 (c 0) (by rw [hc0]; exact hp)) hcd (1, 0)
  have hW2 : HasDerivAt (fun s : ℝ => fderiv ℝ H (c s) (0, Pi.single j 1))
      (fderiv ℝ (fderiv ℝ H) (c 0) (0, e) (0, Pi.single j 1)) 0 :=
    hasDerivAt_fderiv_comp' (hd1 (c 0) (by rw [hc0]; exact hp)) hcd (0, Pi.single j 1)
  have hgs := hasDerivAt_gpair hg hγs (by rw [hc0]; exact hU _ hp) hW1 hW2
  have hz : HasDerivAt (fun s : ℝ => gpairAt g (H (c s)) (fderiv ℝ H (c s) (1, 0))
      (fderiv ℝ H (c s) (0, Pi.single j 1))) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hcW] with s hs using hω _ hs j
  have := hgs.unique hz
  rw [hc0] at this
  exact this

/-- **`g(P_i, J_j)` is symmetric** when `g(∂_t H, ∂_{σ_j} H) ≡ 0`, `P_i = D_t J_i`. -/
theorem gramC_symm_of_omega (hg : Lightlike.IsCoordMetric g U)
    {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))} (hW : IsOpen W)
    (hH : ContDiffOn ℝ 3 H W) (hU : ∀ p ∈ W, H p ∈ U)
    (hω : ∀ q ∈ W, ∀ j : Fin m, gpairAt g (H q) (fderiv ℝ H q (1, 0)) (fderiv ℝ H q (0, Pi.single j 1)) = 0)
    {p : ℝ × (Fin m → ℝ)} (hp : p ∈ W) (i j : Fin m) :
    gpairAt g (H p) (fun a => covDAlong g (H p) (fderiv ℝ H p (1, 0)) (fderiv ℝ H p (0, Pi.single i 1))
        (fderiv ℝ (fderiv ℝ H) p (1, 0) (0, Pi.single i 1)) a) (fderiv ℝ H p (0, Pi.single j 1)) =
      gpairAt g (H p) (fun a => covDAlong g (H p) (fderiv ℝ H p (1, 0)) (fderiv ℝ H p (0, Pi.single j 1))
        (fderiv ℝ (fderiv ℝ H) p (1, 0) (0, Pi.single j 1)) a) (fderiv ℝ H p (0, Pi.single i 1)) := by
  classical
  have hC : ∀ q ∈ W, ContDiffAt ℝ 3 H q := fun q hq => hH.contDiffAt (hW.mem_nhds hq)
  have hsym : ∀ u v, fderiv ℝ (fderiv ℝ H) p u v = fderiv ℝ (fderiv ℝ H) p v u := fun u v =>
    (((hC p hp).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])) u v
  have hΓ := fun v u => Lightlike.Geodesic.gammaApply_comm hg (hU _ hp) v u
  have E1 := omega_dir_eq hg hW hH hU hω hp (Pi.single i 1) j
  have E2 := omega_dir_eq hg hW hH hU hω hp (Pi.single j 1) i
  -- identify the covariant `σ`-derivative of `∂_t H` with `P`
  have hPt : ∀ k : Fin m, (fun a => covDAlong g (H p) (fderiv ℝ H p (0, Pi.single k 1)) (fderiv ℝ H p (1, 0))
        (fderiv ℝ (fderiv ℝ H) p (0, Pi.single k 1) (1, 0)) a) =
      fun a => covDAlong g (H p) (fderiv ℝ H p (1, 0)) (fderiv ℝ H p (0, Pi.single k 1))
        (fderiv ℝ (fderiv ℝ H) p (1, 0) (0, Pi.single k 1)) a := by
    intro k
    funext a
    have := congrFun (hΓ (fderiv ℝ H p (0, Pi.single k 1)) (fderiv ℝ H p (1, 0))) a
    simp only [covDAlong, Lightlike.Geodesic.gammaApply] at this ⊢
    rw [hsym (0, Pi.single k 1) (1, 0), this]
  have hX : (fun a => covDAlong g (H p) (fderiv ℝ H p (0, Pi.single i 1)) (fderiv ℝ H p (0, Pi.single j 1))
        (fderiv ℝ (fderiv ℝ H) p (0, Pi.single i 1) (0, Pi.single j 1)) a) =
      fun a => covDAlong g (H p) (fderiv ℝ H p (0, Pi.single j 1)) (fderiv ℝ H p (0, Pi.single i 1))
        (fderiv ℝ (fderiv ℝ H) p (0, Pi.single j 1) (0, Pi.single i 1)) a := by
    funext a
    have := congrFun (hΓ (fderiv ℝ H p (0, Pi.single i 1)) (fderiv ℝ H p (0, Pi.single j 1))) a
    simp only [covDAlong, Lightlike.Geodesic.gammaApply] at this ⊢
    rw [hsym (0, Pi.single i 1) (0, Pi.single j 1), this]
  rw [hPt i] at E1
  rw [hPt j] at E2
  rw [hX] at E1
  linarith

/-- Along a geodesic in a chart, `g(w, w)` has zero `t`-derivative. -/
theorem null_hasDerivAt_zero (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ} {t : ℝ}
    (hγ : HasDerivAt γ (w t) t) (hw : HasDerivAt w (Lightlike.Geodesic.accel g (γ t) (w t)) t)
    (hU : γ t ∈ U) :
    HasDerivAt (fun s => gpairAt g (γ s) (w s) (w s)) 0 t := by
  have h := hasDerivAt_gpair hg hγ hU hw hw
  have hcw : (fun a => covDAlong g (γ t) (w t) (w t) (Lightlike.Geodesic.accel g (γ t) (w t)) a) = 0 := by
    funext a
    simp [covDAlong, Lightlike.Geodesic.accel]
  rw [hcw] at h
  have h0 : gpairAt g (γ t) (0 : Fin n → ℝ) (w t) = 0 := by simp [gpairAt]
  have h0' : gpairAt g (γ t) (w t) (0 : Fin n → ℝ) = 0 := by simp [gpairAt]
  rw [h0, h0', add_zero] at h
  exact h

end Lightlike.Penrose

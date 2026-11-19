import Lightlike.Geodesic.GaussAux
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Gauss lemma

The exponential map is a radial isometry: for `v` in the ball on which `exp_x` is the normal
chart `φ`, and every `w`,

`g (φ v) (Dφ(v) v, Dφ(v) w) = g x (v, w)`

(`Lightlike.Geodesic.IsNormalChart.gauss`, and `Lightlike.Geodesic.exists_normal_chart_gauss`
for the existence of a chart with this property). The metric may have any signature.

The proof is the classical one. For `u` in the ball and a direction `w` put
`F t s = φ (t • (u + s • w))`. Each `t ↦ F t s` is a geodesic of constant speed
`g x (u + s w, u + s w)`; the lowered geodesic equation gives
`d/dt g (∂_t F, ∂_s F) = ½ ∂_s g (∂_t F, ∂_t F) = g x (u, w)` at `s = 0`, and `∂_s F = 0` at
`t = 0`.

## Main definitions

* `Lightlike.Geodesic.IsNormalChart g U x ρ φ`: `φ` is the exponential map at `x` on the ball of
  radius `ρ`, a diffeomorphism onto an open subset of `U`
  (the conclusions of `exists_expMap_diffeo`, bundled).
* `Lightlike.Geodesic.pairing g y a b`: the metric pairing `∑ i j, a i * (g y i j * b j)`.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Theorem 2.1.21 (Gauss lemma),
  page 43, equation (2.1.24). Differences: a coordinate metric on an open subset of `ℝⁿ`; the
  point `x` of the source ranges over the maximal domain `D_p` of `exp_p`, here over the ball on
  which `exp` is the normal chart.
-/

open Set Metric Filter Topology Matrix
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The metric pairing `g_y (a, b) = ∑ i j, a i * (g y i j * b j)`. -/
def pairing (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a b : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * (g y i j * b j)

/-- The pairing is the matrix expression `a ⬝ᵥ (g y *ᵥ b)`. -/
lemma pairing_eq_dotProduct (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a b : Fin n → ℝ) :
    pairing g y a b = a ⬝ᵥ (g y *ᵥ b) := by
  simp only [pairing, dotProduct, Matrix.mulVec, Finset.mul_sum]

lemma pairing_self (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a : Fin n → ℝ) :
    pairing g y a a = normSq g y a := by
  simp only [pairing, normSq, dotProduct, Matrix.mulVec, Finset.mul_sum]

lemma pairing_comm (hg : Lightlike.IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (a b : Fin n → ℝ) : pairing g y a b = pairing g y b a := by
  simp only [pairing]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun (hg.symm y hy) i) j
  simp only [Matrix.transpose_apply] at this
  rw [this]; ring

lemma pairing_zero_right (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a : Fin n → ℝ) :
    pairing g y a 0 = 0 := by
  simp [pairing]

lemma pairing_smul_left (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a b : Fin n → ℝ)
    (c : ℝ) : pairing g y (c • a) b = c * pairing g y a b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma pairing_smul_right (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a b : Fin n → ℝ)
    (c : ℝ) : pairing g y a (c • b) = c * pairing g y a b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `φ` is a **normal chart** at `x`: the exponential map at `x` on the ball of radius `ρ` about
`0`, a diffeomorphism onto an open subset of `U`. For `v` in the ball, `t ↦ φ (t • v)` is the
geodesic from `x` with initial velocity `v`. -/
structure IsNormalChart (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)) : Prop where
  /-- The radius is positive. -/
  pos : 0 < ρ
  /-- The source is the ball of radius `ρ`. -/
  source_eq : φ.source = ball 0 ρ
  /-- The chart is centred at `x`. -/
  map_zero : φ 0 = x
  /-- The chart is smooth. -/
  contDiffOn : ContDiffOn ℝ ∞ φ φ.source
  /-- The inverse of the chart is smooth. -/
  contDiffOn_symm : ContDiffOn ℝ ∞ φ.symm φ.target
  /-- The derivative at the origin is the identity. -/
  hasFDerivAt_zero : HasFDerivAt φ (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0
  /-- The chart takes values in `U`. -/
  target_subset : φ.target ⊆ U
  /-- Radial lines are mapped to geodesics. -/
  geodesic : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ, γ 0 = x ∧ w 0 = v ∧
    γ 1 = φ v ∧ IsGeodesicOn g γ w (Ioo (-1) 2) ∧ ∀ t ∈ Icc (-1 : ℝ) 1, γ t = φ (t • v)

/-- **Normal charts exist** (Kunzinger–Steinbauer, Theorem 2.1.14). -/
theorem exists_isNormalChart (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)), IsNormalChart g U x ρ φ := by
  obtain ⟨ρ, φ, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_expMap_diffeo hg hx
  exact ⟨ρ, φ, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- A real function with zero derivative on an open interval is constant there. -/
lemma eq_of_hasDerivAt_zero_Ioo {f : ℝ → ℝ} {a b : ℝ} (h : ∀ t ∈ Ioo a b, HasDerivAt f 0 t)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : f x = f y :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (h t ht).differentiableAt.differentiableWithinAt) (fun t ht => (h t ht).deriv)
    hx hy

namespace IsNormalChart

variable {x : Fin n → ℝ} {ρ : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}

set_option maxHeartbeats 400000 in
/-- **The Gauss lemma along a radial geodesic.** In a normal chart `φ` at `x`, for `u` in the
ball, any `w` and `t ∈ (-1, 1)`:
`g (φ (t u)) (Dφ(t u) u, Dφ(t u) (t w)) = t g x (u, w)`. -/
theorem pairing_fderiv_radial (hg : Lightlike.IsCoordMetric g U) (h : IsNormalChart g U x ρ φ)
    {u : Fin n → ℝ} (hu : u ∈ ball (0 : Fin n → ℝ) ρ) (w : Fin n → ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    pairing g (φ (t • u)) (fderiv ℝ φ (t • u) u) (fderiv ℝ φ (t • u) (t • w)) =
      t * pairing g x u w := by
  have hball : ∀ z ∈ ball (0 : Fin n → ℝ) ρ, ContDiffAt ℝ ∞ φ z := fun z hz =>
    h.contDiffOn.contDiffAt (by rw [h.source_eq]; exact isOpen_ball.mem_nhds hz)
  have hφd : ∀ z ∈ ball (0 : Fin n → ℝ) ρ, HasFDerivAt φ (fderiv ℝ φ z) z := fun z hz =>
    ((hball z hz).differentiableAt (by simp)).hasFDerivAt
  have hφ2 : ∀ z ∈ ball (0 : Fin n → ℝ) ρ,
      HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) z := fun z hz =>
    (((hball z hz).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hφU : ∀ z ∈ ball (0 : Fin n → ℝ) ρ, φ z ∈ U := fun z hz =>
    h.target_subset (φ.map_source (by rw [h.source_eq]; exact hz))
  have hsm : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z ∈ ball (0 : Fin n → ℝ) ρ,
      τ • z ∈ ball (0 : Fin n → ℝ) ρ := by
    intro τ hτ z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs]
    have : |τ| ≤ 1 := abs_le.2 hτ
    nlinarith [norm_nonneg z, abs_nonneg τ]
  have hIoc : ∀ τ ∈ Ioo (-1 : ℝ) 1, τ ∈ Icc (-1 : ℝ) 1 := fun τ hτ => ⟨hτ.1.le, hτ.2.le⟩
  have hIoo2 : ∀ τ ∈ Ioo (-1 : ℝ) 1, τ ∈ Ioo (-1 : ℝ) 2 := fun τ hτ =>
    ⟨hτ.1, by linarith [hτ.2]⟩
  have h0I : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  -- nearby directions `u + s • w` stay in the ball
  obtain ⟨δ, hδ, hδb⟩ : ∃ δ > 0, ∀ s ∈ ball (0 : ℝ) δ, u + s • w ∈ ball (0 : Fin n → ℝ) ρ := by
    have hc : Continuous fun s : ℝ => u + s • w := by fun_prop
    have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), u + s • w ∈ ball (0 : Fin n → ℝ) ρ :=
      (hc.tendsto 0).eventually (isOpen_ball.mem_nhds (by simpa using hu))
    exact Metric.eventually_nhds_iff_ball.1 h1
  have h0δ : (0 : ℝ) ∈ ball (0 : ℝ) δ := mem_ball_self hδ
  choose Γ W hΓ0 hW0 _hΓ1 hgeo hΓφ using fun s : ball (0 : ℝ) δ =>
    h.geodesic (u + (s : ℝ) • w) (hδb s s.2)
  set F : ℝ → ℝ → Fin n → ℝ := fun τ s => φ (τ • (u + s • w)) with hF
  set a : ℝ → ℝ → Fin n → ℝ := fun τ s => fderiv ℝ φ (τ • (u + s • w)) (u + s • w) with ha
  have hz : ∀ s ∈ ball (0 : ℝ) δ, ∀ τ ∈ Ioo (-1 : ℝ) 1,
      τ • (u + s • w) ∈ ball (0 : Fin n → ℝ) ρ := fun s hs τ hτ =>
    hsm τ (hIoc τ hτ) _ (hδb s hs)
  -- the `t`-derivative of `F` is `a`
  have hFt : ∀ s ∈ ball (0 : ℝ) δ, ∀ τ ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun τ => F τ s) (a τ s) τ := by
    intro s hs τ hτ
    have h1 : HasDerivAt (fun τ : ℝ => τ • (u + s • w)) (u + s • w) τ := by
      have h0 := (hasDerivAt_id τ).smul_const (u + s • w)
      rw [one_smul] at h0
      exact h0
    exact (hφd _ (hz s hs τ hτ)).comp_hasDerivAt τ h1
  -- the velocity of the geodesic is `a`
  have hWa : ∀ s (hs : s ∈ ball (0 : ℝ) δ), ∀ τ ∈ Ioo (-1 : ℝ) 1, W ⟨s, hs⟩ τ = a τ s := by
    intro s hs τ hτ
    have hev : (fun τ => F τ s) =ᶠ[𝓝 τ] Γ ⟨s, hs⟩ := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ using (hΓφ ⟨s, hs⟩ σ (hIoc σ hσ)).symm
    have h2 := ((hgeo ⟨s, hs⟩).pos τ (hIoo2 τ hτ)).congr_of_eventuallyEq hev
    exact h2.unique (hFt s hs τ hτ)
  -- `a` solves the geodesic equation in `t`
  have hat : ∀ s ∈ ball (0 : ℝ) δ, ∀ τ ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun τ => a τ s) (accel g (F τ s) (a τ s)) τ := by
    intro s hs τ hτ
    have hevW : (fun τ => a τ s) =ᶠ[𝓝 τ] W ⟨s, hs⟩ := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ using (hWa s hs σ hσ).symm
    have h1 := ((hgeo ⟨s, hs⟩).vel τ (hIoo2 τ hτ)).congr_of_eventuallyEq hevW
    rw [hΓφ ⟨s, hs⟩ τ (hIoc τ hτ), hWa s hs τ hτ] at h1
    exact h1
  -- constant speed
  have hN : ∀ s ∈ ball (0 : ℝ) δ, ∀ τ ∈ Ioo (-1 : ℝ) 1,
      normSq g (F τ s) (a τ s) = normSq g x (u + s • w) := by
    intro s hs τ hτ
    have hsp : ∀ σ ∈ Ioo (-1 : ℝ) 1,
        HasDerivAt (fun σ => normSq g (Γ ⟨s, hs⟩ σ) (W ⟨s, hs⟩ σ)) 0 σ := fun σ hσ =>
      (hgeo ⟨s, hs⟩).hasDerivAt_speed hg (hIoo2 σ hσ)
        (by rw [hΓφ ⟨s, hs⟩ σ (hIoc σ hσ)]; exact hφU _ (hz s hs σ hσ))
    have h1 := eq_of_hasDerivAt_zero_Ioo hsp hτ h0I
    simp only [hΓ0, hW0] at h1
    rw [hΓφ ⟨s, hs⟩ τ (hIoc τ hτ), hWa s hs τ hτ] at h1
    exact h1
  have e0 : u + (0 : ℝ) • w = u := by simp
  -- the function whose derivative is computed
  set ψ : ℝ → ℝ := fun τ =>
    ∑ i, ∑ j, a τ 0 i * (g (F τ 0) i j * (fderiv ℝ φ (τ • u) (τ • w)) j) with hψ
  have key : ∀ τ ∈ Ioo (-1 : ℝ) 1, HasDerivAt ψ (pairing g x u w) τ := by
    intro τ hτ
    have hzu : τ • u ∈ ball (0 : Fin n → ℝ) ρ := hsm τ (hIoc τ hτ) u hu
    have hz0 : τ • (u + (0 : ℝ) • w) ∈ ball (0 : Fin n → ℝ) ρ := hz 0 h0δ τ hτ
    have hyU : F τ 0 ∈ U := hφU _ hz0
    have hdiff : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) (F τ 0) := fun i j =>
      ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hyU)).differentiableAt (by simp)
    have hdiffx : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x := fun i j => by
      have hxU : x ∈ U := by
        have := hφU 0 (mem_ball_self h.pos)
        rwa [h.map_zero] at this
      exact ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hxU)).differentiableAt (by simp)
    -- derivatives in `s` at `0`
    have h3 : HasDerivAt (fun s : ℝ => u + s • w) w 0 := by
      have h0 := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
      rw [one_smul] at h0
      exact h0
    have h1 : HasDerivAt (fun s : ℝ => τ • (u + s • w)) (τ • w) 0 := h3.const_smul τ
    have hFs : HasDerivAt (fun s => F τ s) (fderiv ℝ φ (τ • (u + (0 : ℝ) • w)) (τ • w)) 0 :=
      (hφd _ hz0).comp_hasDerivAt 0 h1
    have has : HasDerivAt (fun s => a τ s)
        (fderiv ℝ (fderiv ℝ φ) (τ • (u + (0 : ℝ) • w)) (τ • w) (u + (0 : ℝ) • w) +
          fderiv ℝ φ (τ • (u + (0 : ℝ) • w)) w) 0 :=
      ((hφ2 _ hz0).comp_hasDerivAt 0 h1).clm_apply h3
    -- derivative in `t` of the variation field
    have h4' : HasDerivAt (fun σ : ℝ => σ • u) u τ := by
      have h0 := (hasDerivAt_id τ).smul_const u
      rw [one_smul] at h0
      exact h0
    have h4 : HasDerivAt (fun σ : ℝ => fderiv ℝ φ (σ • u)) (fderiv ℝ (fderiv ℝ φ) (τ • u) u) τ :=
      (hφ2 _ hzu).comp_hasDerivAt τ h4'
    have h5 : HasDerivAt (fun σ : ℝ => σ • w) w τ := by
      have h0 := (hasDerivAt_id τ).smul_const w
      rw [one_smul] at h0
      exact h0
    have hbt : HasDerivAt (fun σ => fderiv ℝ φ (σ • u) (σ • w))
        (fderiv ℝ (fderiv ℝ φ) (τ • u) u (τ • w) + fderiv ℝ φ (τ • u) w) τ :=
      h4.clm_apply h5
    have hsymm : fderiv ℝ (fderiv ℝ φ) (τ • u) (τ • w) u =
        fderiv ℝ (fderiv ℝ φ) (τ • u) u (τ • w) :=
      ((hball _ hzu).isSymmSndFDerivAt (by simp)).eq (τ • w) u
    rw [e0] at hFs has
    rw [hsymm] at has
    set y : Fin n → ℝ := F τ 0 with hy
    set av : Fin n → ℝ := a τ 0 with hav
    set b : Fin n → ℝ := fderiv ℝ φ (τ • u) (τ • w) with hb
    set c : Fin n → ℝ := fderiv ℝ (fderiv ℝ φ) (τ • u) u (τ • w) + fderiv ℝ φ (τ • u) w with hc
    -- the derivative of `ψ`
    have hψd := hasDerivAt_pairing (g := g) (γ := fun σ => F σ 0) (a := fun σ => a σ 0)
      (b := fun σ => fderiv ℝ φ (σ • u) (σ • w)) hdiff (hFt 0 h0δ τ hτ) (hat 0 h0δ τ hτ) hbt
    -- the derivative of the speed in `s`
    have hNd := hasDerivAt_pairing (g := g) (γ := fun s => F τ s) (a := fun s => a τ s)
      (b := fun s => a τ s) (s := 0) hdiff hFs has has
    have hNx := hasDerivAt_pairing (g := g) (γ := fun _ : ℝ => x) (a := fun s : ℝ => u + s • w)
      (b := fun s : ℝ => u + s • w) (s := 0) hdiffx (hasDerivAt_const (0 : ℝ) x) h3 h3
    have hevN : (fun s => ∑ i, ∑ j, a τ s i * (g (F τ s) i j * a τ s j)) =ᶠ[𝓝 (0 : ℝ)]
        fun s => ∑ i, ∑ j, (u + s • w) i * (g x i j * (u + s • w) j) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
      have h6 := hN s hs τ hτ
      rw [← pairing_self, ← pairing_self] at h6
      exact h6
    have hNeq := (hNx.congr_of_eventuallyEq hevN).unique hNd
    -- the algebra
    have hGsym : ∀ i j, g y i j = g y j i := fun i j => by
      have := congrFun (congrFun (hg.symm y hyU) j) i
      simpa [Matrix.transpose_apply] using this
    have halg := gauss_algebra (fun i j => g y i j)
      (fun k i j => Lightlike.pd k (fun z => g z i j) y) (accel g y av) av b c hGsym
      (fun j => lowered_accel_add hg hyU av j)
    have hxval : ∑ i, ∑ j, (w i * (g x i j * (u + (0 : ℝ) • w) j) +
        (u + (0 : ℝ) • w) i * ((∑ k, (0 : Fin n → ℝ) k *
          Lightlike.pd k (fun y => g y i j) x) * (u + (0 : ℝ) • w) j + g x i j * w j)) =
        2 * pairing g x u w := by
      have hxU : x ∈ U := by
        have := hφU 0 (mem_ball_self h.pos)
        rwa [h.map_zero] at this
      have h7 : ∀ i j, w i * (g x i j * (u + (0 : ℝ) • w) j) +
          (u + (0 : ℝ) • w) i * ((∑ k, (0 : Fin n → ℝ) k *
            Lightlike.pd k (fun y => g y i j) x) * (u + (0 : ℝ) • w) j + g x i j * w j) =
          w i * (g x i j * u j) + u i * (g x i j * w j) := fun i j => by
        simp
      simp only [h7, Finset.sum_add_distrib]
      have h8 : ∑ i, ∑ j, w i * (g x i j * u j) = pairing g x w u := rfl
      have h9 : ∑ i, ∑ j, u i * (g x i j * w j) = pairing g x u w := rfl
      rw [h8, h9, pairing_comm hg hxU w u]
      ring
    refine hψd.congr_deriv ?_
    have h10 : (∑ i, ∑ j, (accel g y av i * (g y i j * b j) +
        av i * ((∑ k, av k * Lightlike.pd k (fun z => g z i j) y) * b j + g y i j * c j))) =
        (1 / 2) * (2 * pairing g x u w) := by
      rw [halg, ← hxval, hNeq]
    rw [h10]
    ring
  -- integrate from `0`
  have hconst : ∀ τ ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun τ => ψ τ - τ * pairing g x u w) 0 τ := fun τ hτ => by
    have h1 : HasDerivAt (fun τ => ψ τ - τ * pairing g x u w)
        (pairing g x u w - 1 * pairing g x u w) τ :=
      (key τ hτ).sub ((hasDerivAt_id τ).mul_const (pairing g x u w))
    have h2 : pairing g x u w - 1 * pairing g x u w = 0 := by ring
    rw [h2] at h1
    exact h1
  have h2 := eq_of_hasDerivAt_zero_Ioo hconst ht h0I
  have hψ0 : ψ 0 = 0 := by
    have hz0 : fderiv ℝ φ ((0 : ℝ) • u) ((0 : ℝ) • w) = 0 := by
      rw [zero_smul, zero_smul]
      exact (fderiv ℝ φ 0).map_zero
    simp only [hψ, hz0, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  simp only [hψ0, zero_mul, sub_zero] at h2
  have h3 : ψ t = pairing g (φ (t • u)) (fderiv ℝ φ (t • u) u) (fderiv ℝ φ (t • u) (t • w)) := by
    simp only [hψ, hF, ha, pairing, e0]
  rw [← h3]
  linarith

/-- **The Gauss lemma** (Kunzinger–Steinbauer, Theorem 2.1.21): in a normal chart `φ` at `x`,
for `v` in the ball and every `w`, `g (φ v) (Dφ(v) v, Dφ(v) w) = g x (v, w)`: the exponential
map is a radial isometry. -/
theorem gauss (hg : Lightlike.IsCoordMetric g U) (h : IsNormalChart g U x ρ φ)
    {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) ρ) (w : Fin n → ℝ) :
    pairing g (φ v) (fderiv ℝ φ v v) (fderiv ℝ φ v w) = pairing g x v w := by
  rw [mem_ball_zero_iff] at hv
  have hρ := h.pos
  set θ : ℝ := (‖v‖ / ρ + 1) / 2 with hθ
  have hq : ‖v‖ / ρ < 1 := (div_lt_one hρ).2 hv
  have hq0 : 0 ≤ ‖v‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hθv : ‖v‖ < θ * ρ := by
    have : ‖v‖ / ρ < θ := by rw [hθ]; linarith
    rwa [div_lt_iff₀ hρ] at this
  have hu : θ⁻¹ • v ∈ ball (0 : Fin n → ℝ) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hθ0),
      inv_mul_lt_iff₀ hθ0]
    exact hθv
  have h1 := h.pairing_fderiv_radial hg hu w (t := θ) ⟨by linarith, hθ1⟩
  rw [smul_smul, mul_inv_cancel₀ hθ0.ne', one_smul, map_smul, map_smul, pairing_smul_left,
    pairing_smul_right, pairing_smul_left] at h1
  have h2 : θ⁻¹ * (θ * pairing g (φ v) (fderiv ℝ φ v v) (fderiv ℝ φ v w)) =
      pairing g (φ v) (fderiv ℝ φ v v) (fderiv ℝ φ v w) := by
    rw [← mul_assoc, inv_mul_cancel₀ hθ0.ne', one_mul]
  have h3 : θ * (θ⁻¹ * pairing g x v w) = pairing g x v w := by
    rw [← mul_assoc, mul_inv_cancel₀ hθ0.ne', one_mul]
  rw [h2, h3] at h1
  exact h1

end IsNormalChart

/-- **The Gauss lemma, with the existence of the chart** (Kunzinger–Steinbauer, Theorems 2.1.14
and 2.1.21, for a coordinate metric of any signature): every point `x ∈ U` has a normal chart
`φ` on a ball of radius `ρ`, and for `v` in the ball and every `w`,
`g (φ v) (Dφ(v) v, Dφ(v) w) = g x (v, w)`. -/
theorem exists_normal_chart_gauss (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)), IsNormalChart g U x ρ φ ∧
      ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∀ w : Fin n → ℝ,
        pairing g (φ v) (fderiv ℝ φ v v) (fderiv ℝ φ v w) = pairing g x v w := by
  obtain ⟨ρ, φ, h⟩ := exists_isNormalChart hg hx
  exact ⟨ρ, φ, h, fun v hv w => h.gauss hg hv w⟩

end Lightlike.Geodesic

import Lightlike.Geodesic.Variation

/-!
# A timelike variation of a null geodesic with a moving initial point

Chart-level core of the orthogonality of the generators of `∂J⁺(S)` to `S`
(Hawking–Ellis, section 4.5): if `γ` is a null geodesic of a
coordinate metric `g` and `u` is a vector with `g(γ'(t₀), u) > 0`, then the curves
`t ↦ γ t + h t • d`, `h t₀ = 1`, `h (t₀ + δ) = 0`, with `d = ε v` and `v` near `u`, are timelike
for small `ε > 0`, with the same end point and the start point moved by `d`.
-/

open Set Metric Filter Topology Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The directional derivative `∂_u g (w, w)` of the metric along `u`, at the point `y`. -/
def dirDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y u w : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * ((∑ k, u k * Lightlike.pd k (fun z => g z i j) y) * w j)

/-- **The first variation of the pairing with a constant vector along a geodesic**:
`d/dt g(γ', u) = ½ ∂_u g(γ', γ')`. -/
theorem hasDerivAt_pairing_const (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {J : Set ℝ} (h : IsGeodesicOn g γ w J) {t : ℝ} (ht : t ∈ J) (hU : γ t ∈ U)
    (u : Fin n → ℝ) :
    HasDerivAt (fun τ => pairing g (γ τ) (w τ) u) (dirDeriv g (γ t) u (w t) / 2) t := by
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) (γ t) := fun i j =>
    ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hU)).differentiableAt (by simp)
  have hline : HasDerivAt (fun s : ℝ => γ t + s • u) u 0 := by
    have h0 := ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (γ t)
    rw [one_smul] at h0
    exact h0
  have hN := hasDerivAt_pairing (g := g) (γ := fun s : ℝ => γ t + s • u) (a := fun _ => w t)
    (b := fun _ => w t) (s := 0) (by simpa using hdiff) hline (hasDerivAt_const _ _)
    (hasDerivAt_const _ _)
  have hv := hasDerivAt_pairing_variation hg (F := fun τ s => γ τ + s • u) (a := fun τ _ => w τ)
    (b := fun _ => u) (c := 0) (N := fun s => ∑ i, ∑ j, w t i * (g (γ t + s • u) i j * w t j))
    (N' := dirDeriv g (γ t) u (w t)) (t := t) (by simpa using hU)
    (by simpa using h.pos t ht) (by simpa using h.vel t ht) hline (hasDerivAt_const _ _)
    (hasDerivAt_const _ _)
    (Eventually.of_forall fun s => by rw [← pairing_self]; rfl)
    (by
      refine hN.congr_deriv ?_
      simp [dirDeriv])
  simpa using hv


/-- The squared speed of the varied curve `t ↦ x + z • d` with velocity `y + z' • d`, as a function
of the displacement `d` and the parameters `p = (x, y, z, z')`. -/
def varPsi (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) : ℝ :=
  pairing g (p.1 + p.2.2.1 • d) (p.2.1 + p.2.2.2 • d) (p.2.1 + p.2.2.2 • d)

/-- `varPsi` is smooth jointly in `(d, p)` near a point where the base point lies in `U`. -/
theorem varPsi_contDiffAt (hg : Lightlike.IsCoordMetric g U) {x y : Fin n → ℝ} {z z' : ℝ}
    (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (fun q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) => varPsi g q.1 q.2)
      (0, (x, y, z, z')) := by
  have hgij : ∀ i j, ContDiffAt ℝ ∞ (fun q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) =>
      g (q.2.1 + q.2.2.2.1 • q.1) i j) (0, (x, y, z, z')) := by
    intro i j
    have h1 : ContDiffAt ℝ ∞ (fun y' : Fin n → ℝ => g y' i j)
        ((fun q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) =>
          q.2.1 + q.2.2.2.1 • q.1) (0, (x, y, z, z'))) := by
      simp only [smul_zero, add_zero]
      exact (hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hx)
    have hin : ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) =>
        q.2.1 + q.2.2.2.1 • q.1) := by fun_prop
    exact ContDiffAt.comp (0, (x, y, z, z')) h1 hin.contDiffAt
  unfold varPsi pairing
  refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_
  refine ContDiffAt.mul ?_ (ContDiffAt.mul (hgij i j) ?_)
  · exact (by fun_prop : ContDiff ℝ ∞ fun q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) =>
      (q.2.2.1 + q.2.2.2.2 • q.1) i).contDiffAt
  · exact (by fun_prop : ContDiff ℝ ∞ fun q : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) =>
      (q.2.2.1 + q.2.2.2.2 • q.1) j).contDiffAt

/-- The derivative of `s ↦ varPsi (s • u) p` at `0`: `2 z' g_x(y, u) + z ∂_u g (y, y)`. -/
theorem hasDerivAt_varPsi (hg : Lightlike.IsCoordMetric g U) {x y u : Fin n → ℝ} {z z' : ℝ}
    (hx : x ∈ U) :
    HasDerivAt (fun s : ℝ => varPsi g (s • u) (x, y, z, z'))
      (2 * z' * pairing g x y u + z * dirDeriv g x u y) 0 := by
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun y' => g y' i j) (x + z • (0 : ℝ) • u) := fun i j => by
    rw [zero_smul, smul_zero, add_zero]
    exact ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hγ : HasDerivAt (fun s : ℝ => x + z • s • u) (z • u) 0 := by
    have h0 := (((hasDerivAt_id (0 : ℝ)).smul_const u).const_smul z).const_add x
    simpa using h0
  have ha : HasDerivAt (fun s : ℝ => y + z' • s • u) (z' • u) 0 := by
    have h0 := (((hasDerivAt_id (0 : ℝ)).smul_const u).const_smul z').const_add y
    simpa using h0
  have h := hasDerivAt_pairing (g := g) hdiff hγ ha ha
  refine h.congr_deriv ?_
  simp only [zero_smul, smul_zero, add_zero, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ i j, z' * u i * (g x i j * y j) + y i * ((∑ k, z * u k *
      Lightlike.pd k (fun y => g y i j) x) * y j + g x i j * (z' * u j)) =
      z' * (u i * (g x i j * y j)) + z' * (y i * (g x i j * u j)) +
      z * (y i * ((∑ k, u k * Lightlike.pd k (fun y => g y i j) x) * y j)) := by
    intro i j
    have : ∑ k, z * u k * Lightlike.pd k (fun y => g y i j) x =
        z * ∑ k, u k * Lightlike.pd k (fun y => g y i j) x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]; ring
  have key : ∀ (f : Fin n → Fin n → ℝ) (c : ℝ), ∑ i, ∑ j, c * f i j = c * ∑ i, ∑ j, f i j := by
    intro f c; simp [Finset.mul_sum]
  simp only [hterm, Finset.sum_add_distrib, key]
  have h1 : ∑ i, ∑ j, u i * (g x i j * y j) = pairing g x y u := by
    rw [pairing_comm hg hx y u]; rfl
  have h2 : ∑ i, ∑ j, y i * (g x i j * u j) = pairing g x y u := rfl
  rw [h1, h2]
  simp only [dirDeriv]
  ring


/-- Continuity of `s ↦ g_{γ s} (a s, b s)` at a time where the curve is in `U`. -/
theorem continuousAt_pairing_curve {X : Type*} [TopologicalSpace X]
    (hg : Lightlike.IsCoordMetric g U) {γ a b : X → Fin n → ℝ}
    {t : X} (hγ : ContinuousAt γ t) (ha : ContinuousAt a t) (hb : ContinuousAt b t)
    (hU : γ t ∈ U) : ContinuousAt (fun s => pairing g (γ s) (a s) (b s)) t := by
  unfold pairing
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  have hgij : ContinuousAt (fun s => g (γ s) i j) t :=
    ((hg.smooth i j).continuousOn.continuousAt (hg.isOpen.mem_nhds hU)).comp hγ
  exact ((continuous_apply i).continuousAt.comp ha).mul
    (hgij.mul ((continuous_apply j).continuousAt.comp hb))

/-- Continuity of the directional derivative term `∂_u g (w, w)` along a curve. -/
theorem continuousAt_dirDeriv_curve (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {t : ℝ} (u : Fin n → ℝ) (hγ : ContinuousAt γ t) (hw : ContinuousAt w t) (hU : γ t ∈ U) :
    ContinuousAt (fun s => dirDeriv g (γ s) u (w s)) t := by
  unfold dirDeriv
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  have hpd : ∀ k, ContinuousAt (fun s => Lightlike.pd k (fun z => g z i j) (γ s)) t := by
    intro k
    have h1 : ContinuousOn (fderiv ℝ (fun z => g z i j)) U :=
      (hg.smooth i j).continuousOn_fderiv_of_isOpen hg.isOpen (by simp)
    have h2 : ContinuousAt (fun z => Lightlike.pd k (fun z => g z i j) z) (γ t) :=
      ((h1.clm_apply continuousOn_const).continuousAt (hg.isOpen.mem_nhds hU))
    exact h2.comp hγ
  exact ((continuous_apply i).continuousAt.comp hw).mul
    ((tendsto_finsetSum _ fun k _ => continuousAt_const.mul (hpd k)).mul
      ((continuous_apply j).continuousAt.comp hw))


/-- **A timelike variation of a null geodesic.** Let `γ` be a geodesic of the coordinate metric `g`
on a neighbourhood `J` of `t₀`, null at `t₀`, and `u` a vector with `g(γ'(t₀), u) > 0`; let `X` be a
continuous vector field with `g(γ'(t₀), X) < 0`. Then there are `δ > 0` and a function `h` with
`h t₀ = 1`, `h (t₀ + δ) = 0`, such that for small `ε > 0` and `v` near `u` the curves
`t ↦ γ t + h t • (ε v)` on `[t₀, t₀ + δ]` stay in `U`, have timelike velocity
`w t + h' t • (ε v)` and have `g(velocity, X) < 0`: they start at `γ t₀ + ε v`, end at `γ (t₀ + δ)`. -/
theorem exists_null_variation (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {J : Set ℝ} {t₀ : ℝ} (hJ : J ∈ 𝓝 t₀) (hgeo : IsGeodesicOn g γ w J)
    (hUJ : ∀ t ∈ J, γ t ∈ U) (hnull : normSq g (γ t₀) (w t₀) = 0) {u : Fin n → ℝ}
    (hG : 0 < pairing g (γ t₀) (w t₀) u) {X : (Fin n → ℝ) → Fin n → ℝ} (hX : ContinuousOn X U)
    (hXneg : pairing g (γ t₀) (w t₀) (X (γ t₀)) < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ h h' : ℝ → ℝ, ∃ O : Set ℝ, IsOpen O ∧ Icc t₀ (t₀ + δ) ⊆ O ∧ O ⊆ J ∧
      (∀ t ∈ O, HasDerivAt h (h' t) t) ∧ (∀ t ∈ O, ContinuousAt h' t) ∧
      h t₀ = 1 ∧ h (t₀ + δ) = 0 ∧
      ∃ ε₀ ν : ℝ, 0 < ε₀ ∧ 0 < ν ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ v ∈ ball u ν, ∀ t ∈ Icc t₀ (t₀ + δ),
        γ t + h t • (ε • v) ∈ U ∧
        pairing g (γ t + h t • (ε • v)) (w t + h' t • (ε • v)) (w t + h' t • (ε • v)) < 0 ∧
        pairing g (γ t + h t • (ε • v)) (w t + h' t • (ε • v))
          (X (γ t + h t • (ε • v))) < 0 := by
  obtain ⟨r, hr, hrJ⟩ : ∃ r : ℝ, 0 < r ∧ Ioo (t₀ - r) (t₀ + r) ⊆ J := by
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 hJ
    exact ⟨r, hr, by simpa [Real.ball_eq_Ioo] using hsub⟩
  set I : Set ℝ := Ioo (t₀ - r) (t₀ + r) with hI
  have ht₀I : t₀ ∈ I := ⟨by linarith, by linarith⟩
  have hnullI : ∀ t ∈ I, normSq g (γ t) (w t) = 0 := fun t ht => by
    have := eq_of_hasDerivAt_zero_Ioo (f := fun s => normSq g (γ s) (w s)) (a := t₀ - r)
      (b := t₀ + r) (fun s hs => hgeo.hasDerivAt_speed hg (hrJ hs) (hUJ s (hrJ hs))) ht ht₀I
    rw [this]; exact hnull
  have hγc : ∀ t ∈ J, ContinuousAt γ t := fun t ht => (hgeo.pos t ht).continuousAt
  have hwc : ∀ t ∈ J, ContinuousAt w t := fun t ht => (hgeo.vel t ht).continuousAt
  set G : ℝ → ℝ := fun t => pairing g (γ t) (w t) u with hGdef
  set D : ℝ → ℝ := fun t => dirDeriv g (γ t) u (w t) with hDdef
  set F0 : ℝ → ℝ := fun t => pairing g (γ t) (w t) (X (γ t)) with hF0def
  have hXc : ∀ t ∈ J, ContinuousAt (fun s => X (γ s)) t := fun t ht =>
    (hX.continuousAt (hg.isOpen.mem_nhds (hUJ t ht))).comp (hγc t ht)
  have hGc : ∀ t ∈ J, ContinuousAt G t := fun t ht =>
    continuousAt_pairing_curve hg (hγc t ht) (hwc t ht) continuousAt_const (hUJ t ht)
  have hDc : ∀ t ∈ J, ContinuousAt D t := fun t ht =>
    continuousAt_dirDeriv_curve hg u (hγc t ht) (hwc t ht) (hUJ t ht)
  have hF0c : ∀ t ∈ J, ContinuousAt F0 t := fun t ht =>
    continuousAt_pairing_curve hg (hγc t ht) (hwc t ht) (hXc t ht) (hUJ t ht)
  have hGd : ∀ t ∈ J, HasDerivAt G (D t / 2) t := fun t ht =>
    hasDerivAt_pairing_const hg hgeo ht (hUJ t ht) u
  have hJ0 : t₀ ∈ J := hrJ ht₀I
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ I ∧ G t₀ / 2 < G t ∧ F0 t < 0 :=
    ((show ∀ᶠ t in 𝓝 t₀, t ∈ I from Ioo_mem_nhds (by linarith : t₀ - r < t₀) (by linarith : t₀ < t₀ + r)).and
      (((hGc t₀ hJ0).eventually (lt_mem_nhds (half_lt_self hG))).and
        ((hF0c t₀ hJ0).eventually (gt_mem_nhds hXneg)))).mono fun t ht => ⟨ht.1, ht.2.1, ht.2.2⟩
  obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hbI : ∀ t ∈ ball t₀ η, t ∈ I ∧ G t₀ / 2 < G t ∧ F0 t < 0 := fun t ht => hηsub t ht
  have hbJ : ∀ t ∈ ball t₀ η, t ∈ J := fun t ht => hrJ (hbI t ht).1
  set δ : ℝ := η / 2 with hδdef
  have hδ : 0 < δ := half_pos hη
  have hIcc : Icc t₀ (t₀ + δ) ⊆ ball t₀ η := fun t ht => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  set G₀ : ℝ := G t₀ with hG₀def
  have hG₀ : 0 < G₀ := hG
  have hGpos : ∀ t ∈ ball t₀ η, 0 < G t := fun t ht => by
    have := (hbI t ht).2.1; linarith
  set h : ℝ → ℝ := fun t => (1 - (t - t₀) / δ) * G₀ / G t with hhdef
  set h' : ℝ → ℝ := fun t => (-(G₀ / δ) - h t * D t / 2) / G t with hh'def
  have hhd : ∀ t ∈ ball t₀ η, HasDerivAt h (h' t) t := by
    intro t ht
    have hnum : HasDerivAt (fun t => (1 - (t - t₀) / δ) * G₀) (-(1 / δ) * G₀) t := by
      have h1 : HasDerivAt (fun t : ℝ => 1 - (t - t₀) / δ) (-(1 / δ)) t := by
        have := (((hasDerivAt_id t).sub_const t₀).div_const δ).const_sub 1
        simpa using this
      exact h1.mul_const G₀
    have := hnum.div (hGd t (hbJ t ht)) (hGpos t ht).ne'
    refine this.congr_deriv ?_
    have hne : G t ≠ 0 := (hGpos t ht).ne'
    simp only [hh'def, hhdef]
    field_simp
  have hid : ∀ t ∈ ball t₀ η, h' t * G t + h t * D t / 2 = -(G₀ / δ) := by
    intro t ht
    have hne : G t ≠ 0 := (hGpos t ht).ne'
    simp only [hh'def]
    field_simp
    ring
  have hh₀ : h t₀ = 1 := by
    simp only [hhdef]
    rw [sub_self, zero_div, sub_zero, one_mul, div_self hG₀.ne']
  have hhδ : h (t₀ + δ) = 0 := by
    simp only [hhdef]
    rw [add_sub_cancel_left, div_self hδ.ne', sub_self, zero_mul, zero_div]
  have hh'c : ∀ t ∈ ball t₀ η, ContinuousAt h' t := by
    intro t ht
    have hne : G t ≠ 0 := (hGpos t ht).ne'
    have hhc : ContinuousAt h t := (hhd t ht).continuousAt
    have hDc' := hDc t (hbJ t ht)
    have hGc' := hGc t (hbJ t ht)
    exact (continuousAt_const.sub ((hhc.mul hDc').div_const 2)).div hGc' hne
  set π : ℝ → (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ := fun t => (γ t, w t, h t, h' t) with hπdef
  have hπc : ∀ t ∈ ball t₀ η, ContinuousAt π t := fun t ht =>
    (hγc t (hbJ t ht)).prodMk ((hwc t (hbJ t ht)).prodMk
      ((hhd t ht).continuousAt.prodMk (hh'c t ht)))
  have hΨ0 : ∀ t ∈ ball t₀ η, varPsi g 0 (π t) = 0 := by
    intro t ht
    simp only [varPsi, hπdef, smul_zero, add_zero]
    rw [pairing_self]; exact hnullI t (hbI t ht).1
  set κ : ℝ := G₀ / δ with hκdef
  have hκ : 0 < κ := div_pos hG₀ hδ
  have hΛd : ∀ t ∈ ball t₀ η,
      HasDerivAt (fun s : ℝ => varPsi g (s • u) (π t)) (-(2 * κ)) 0 := by
    intro t ht
    have := hasDerivAt_varPsi hg (x := γ t) (y := w t) (u := u) (z := h t) (z' := h' t)
      (hUJ t (hbJ t ht))
    refine this.congr_deriv ?_
    have := hid t ht
    show 2 * h' t * G t + h t * D t = -(2 * κ)
    linarith
  set Ψ' : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) → ℝ := fun q => varPsi g q.1 q.2
    with hΨ'
  have hstrict : ∀ t ∈ ball t₀ η, HasStrictFDerivAt Ψ' (fderiv ℝ Ψ' (0, π t)) (0, π t) :=
    fun t ht => (varPsi_contDiffAt hg (y := w t) (z := h t) (z' := h' t)
      (hUJ t (hbJ t ht))).hasStrictFDerivAt (by simp)
  have hΛu : ∀ t ∈ ball t₀ η, fderiv ℝ Ψ' (0, π t) (u, 0) = -(2 * κ) := by
    intro t ht
    have hline : HasDerivAt (fun s : ℝ => (s • u, π t)) (u, 0) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const u).prodMk (hasDerivAt_const (0 : ℝ) (π t))
      simpa using this
    have hl : HasFDerivAt Ψ' (fderiv ℝ Ψ' (0, π t)) ((fun s : ℝ => (s • u, π t)) 0) := by
      simpa using (hstrict t ht).hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0 : ℝ) hline
    exact h1.unique (hΛd t ht)
  refine ⟨δ, hδ, h, h', ball t₀ η, isOpen_ball, hIcc, fun t ht => hbJ t ht, hhd, hh'c, hh₀, hhδ,
    ?_⟩
  have hev2 : ∀ᶠ z in 𝓝 ((0 : ℝ), u), ∀ t ∈ Icc t₀ (t₀ + δ), 0 < z.1 →
      (γ t + h t • (z.1 • z.2) ∈ U ∧
      pairing g (γ t + h t • (z.1 • z.2)) (w t + h' t • (z.1 • z.2))
        (w t + h' t • (z.1 • z.2)) < 0 ∧
      pairing g (γ t + h t • (z.1 • z.2)) (w t + h' t • (z.1 • z.2))
        (X (γ t + h t • (z.1 • z.2))) < 0) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun (z : ℝ × (Fin n → ℝ)) (t : ℝ) => 0 < z.1 →
        (γ t + h t • (z.1 • z.2) ∈ U ∧
        pairing g (γ t + h t • (z.1 • z.2)) (w t + h' t • (z.1 • z.2))
          (w t + h' t • (z.1 • z.2)) < 0 ∧
        pairing g (γ t + h t • (z.1 • z.2)) (w t + h' t • (z.1 • z.2))
          (X (γ t + h t • (z.1 • z.2))) < 0)) fun t₁ ht₁ => ?_
    have htb : t₁ ∈ ball t₀ η := hIcc ht₁
    set z₁ : (ℝ × (Fin n → ℝ)) × ℝ := ((0, u), t₁) with hz₁
    have hfst : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ => z.1.1) z₁ :=
      continuousAt_fst.comp continuousAt_fst
    have hsnd : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ => z.1.2) z₁ :=
      continuousAt_snd.comp continuousAt_fst
    have hthd : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ => z.2) z₁ := continuousAt_snd
    have hcc : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ =>
        γ z.2 + h z.2 • (z.1.1 • z.1.2)) z₁ :=
      ((hγc t₁ (hbJ t₁ htb)).comp hthd).add
        (((hhd t₁ htb).continuousAt.comp hthd).smul (hfst.smul hsnd))
    have hcc' : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ =>
        w z.2 + h' z.2 • (z.1.1 • z.1.2)) z₁ :=
      ((hwc t₁ (hbJ t₁ htb)).comp hthd).add
        (((hh'c t₁ htb).comp hthd).smul (hfst.smul hsnd))
    have hval : γ t₁ + h t₁ • ((0 : ℝ) • u) = γ t₁ := by simp
    have hval' : w t₁ + h' t₁ • ((0 : ℝ) • u) = w t₁ := by simp
    have hcU : ∀ᶠ z in 𝓝 z₁, γ z.2 + h z.2 • (z.1.1 • z.1.2) ∈ U :=
      hcc.eventually (hg.isOpen.mem_nhds (by simpa [hz₁, hval] using hUJ t₁ (hbJ t₁ htb)))
    have hXcc : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ =>
        X (γ z.2 + h z.2 • (z.1.1 • z.1.2))) z₁ :=
      (hX.continuousAt (hg.isOpen.mem_nhds (by simpa [hz₁, hval] using hUJ t₁ (hbJ t₁ htb)))).comp
        (by simpa [hz₁] using hcc)
    have hfut : ∀ᶠ z in 𝓝 z₁, pairing g (γ z.2 + h z.2 • (z.1.1 • z.1.2))
        (w z.2 + h' z.2 • (z.1.1 • z.1.2)) (X (γ z.2 + h z.2 • (z.1.1 • z.1.2))) < 0 := by
      have hc := continuousAt_pairing_curve hg hcc hcc' hXcc
        (by simpa [hz₁, hval] using hUJ t₁ (hbJ t₁ htb))
      refine hc.eventually (gt_mem_nhds ?_)
      simp only [hz₁, hval, hval']
      exact (hbI t₁ htb).2.2
    -- the timelike part
    set Λ := fderiv ℝ Ψ' (0, π t₁) with hΛdef
    set c₀ : ℝ := κ / (2 * (‖u‖ + 1)) with hc₀
    have hc₀pos : 0 < c₀ := by positivity
    have hs := (hstrict t₁ htb).isLittleO.def hc₀pos
    have hmt : Tendsto (fun z : (ℝ × (Fin n → ℝ)) × ℝ =>
        (((z.1.1 • z.1.2, π z.2) : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ)),
          ((0 : Fin n → ℝ), π z.2))) (𝓝 z₁) (𝓝 ((0, π t₁), (0, π t₁))) := by
      have hπ : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ => π z.2) z₁ :=
        ContinuousAt.comp (f := fun z : (ℝ × (Fin n → ℝ)) × ℝ => z.2) (hπc t₁ htb) hthd
      have h1 : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ => z.1.1 • z.1.2) z₁ := hfst.smul hsnd
      have hc0 : ContinuousAt (fun _ : (ℝ × (Fin n → ℝ)) × ℝ => (0 : Fin n → ℝ)) z₁ :=
        continuousAt_const
      have h2 := (h1.prodMk hπ).prodMk (hc0.prodMk hπ)
      simpa [hz₁] using h2.tendsto
    have hev3 := hmt.eventually hs
    have hlam : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ => Λ (z.1.2, 0)) z₁ :=
      ContinuousAt.comp (g := Λ)
        (f := fun z : (ℝ × (Fin n → ℝ)) × ℝ =>
          (z.1.2, (0 : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ)))
        Λ.continuous.continuousAt (hsnd.prodMk continuousAt_const)
    have hev4 : ∀ᶠ z in 𝓝 z₁, Λ (z.1.2, 0) < -κ := by
      refine hlam.eventually (gt_mem_nhds ?_)
      simp only [hz₁]
      rw [hΛdef, hΛu t₁ htb]; linarith
    have hev5 : ∀ᶠ z in 𝓝 z₁, ‖z.1.2‖ < ‖u‖ + 1 := by
      have : ContinuousAt (fun z : (ℝ × (Fin n → ℝ)) × ℝ => ‖z.1.2‖) z₁ := hsnd.norm
      refine this.eventually (gt_mem_nhds ?_)
      simp [hz₁]
    have hev6 : ∀ᶠ z in 𝓝 z₁, z.2 ∈ ball t₀ η :=
      hthd.eventually (isOpen_ball.mem_nhds htb)
    filter_upwards [hcU, hfut, hev3, hev4, hev5, hev6] with z hU1 hF hs3 hl4 hn5 hb6 hpos
    refine ⟨hU1, ?_, hF⟩
    obtain ⟨⟨ε, v⟩, t⟩ := z
    simp only at hpos hs3 hl4 hn5 hb6 ⊢
    have hΨt := hΨ0 t hb6
    have e1 : (((ε • v, π t) : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ)) -
        ((0 : Fin n → ℝ), π t)) = ε • ((v, (0 : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ)) :
          (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ)) := by
      ext <;> simp
    rw [e1] at hs3
    have hnorm : ‖ε • ((v, (0 : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ)) :
        (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ))‖ = ε * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, Prod.norm_def]
      simp
    rw [hnorm, map_smul, smul_eq_mul] at hs3
    have hΨeq : Ψ' (ε • v, π t) = pairing g (γ t + h t • (ε • v)) (w t + h' t • (ε • v))
        (w t + h' t • (ε • v)) := rfl
    have hΨz : Ψ' (0, π t) = 0 := hΨt
    have h5 := (abs_le.1 (by simpa [Real.norm_eq_abs] using hs3)).2
    rw [hΨeq] at h5
    rw [hΨz] at h5
    have hκ2 : c₀ * (‖u‖ + 1) = κ / 2 := by
      simp only [hc₀]; field_simp
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    have hc1 : c₀ * ‖v‖ ≤ c₀ * (‖u‖ + 1) := mul_le_mul_of_nonneg_left hn5.le hc₀pos.le
    nlinarith [mul_pos hpos hκ, mul_le_mul_of_nonneg_left hc1 hpos.le,
      mul_lt_mul_of_pos_left hl4 hpos]
  obtain ⟨ε', hε', hball⟩ := Metric.eventually_nhds_iff.1 hev2
  refine ⟨ε', ε', hε', hε', fun ε hε v hv t ht => ?_⟩
  refine hball (y := (ε, v)) ?_ t ht hε.1
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨by rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]; exact hε.2, hv⟩

end Lightlike.Geodesic

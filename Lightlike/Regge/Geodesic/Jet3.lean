import Lightlike.Regge.Geodesic.DistExpansion

/-!
# Third derivatives of the metric and Taylor's theorem of order four

Part of step 4 of RC6a: the ingredients of the sixth-order expansion of the squared distance.
For a point `x` and vectors `u, v, s`:

* `dddmat g x u v s` is the matrix `Σ_{k,l,p} u_k v_l s_p ∂_p ∂_l ∂_k g_{ij}(x)`, linear in each
  vector argument;
* `taylorMetric3 g x u = g + ∂_u g + ½ ∂_u ∂_u g + ⅙ ∂_u ∂_u ∂_u g` (all at `x`) is the
  third-order Taylor polynomial of the metric at `x`, evaluated at `x + u`.

## Main results

* `IsCoordMetric.ddmat_comm`: `∂_u ∂_v g = ∂_v ∂_u g` on `U`, since mixed partial derivatives
  commute.
* `taylor_four`: Taylor's theorem with remainder of order `4` along a segment in `U`.
* `LocalJet3`: the bounds of `LocalJet`, together with a bound for the third derivatives of the
  metric at `x` and for the remainder of `taylorMetric3` on the ball; `IsRiemMetric.exists_localJet3`
  gives one set of constants on a compact set.

## References

* The third derivatives of the metric enter the term of order five of the expansion of the
  squared distance (Synge's world function) about one end point; see L. Brewin, *Riemann normal
  coordinate expansions using Cadabra*, arXiv:0903.2087 (2009), Section 9.
* Taylor's theorem in several variables: J. Dieudonné, *Foundations of Modern Analysis*
  (Academic Press, 1960), Chapter VIII, Section 14. The remainder bound proven here is cruder
  (no factor `1/24`), which is enough for the expansion.
-/

open Set Filter Topology Metric
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## The third derivative of the metric as a matrix -/

/-- The third derivative of the metric at `x` in the directions `u, v, s`: the matrix
`Σ_{k,l,p} u_k v_l s_p ∂_p ∂_l ∂_k g_{ij}(x)`. -/
noncomputable def dddmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u v s : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, ∑ p,
    u k * v l * s p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) x

theorem dddmat_add_left (x u u' v s : Fin n → ℝ) :
    dddmat g x (u + u') v s = dddmat g x u v s + dddmat g x u' v s := by
  ext i j; simp [dddmat, add_mul, Finset.sum_add_distrib]

theorem dddmat_add_mid (x u v v' s : Fin n → ℝ) :
    dddmat g x u (v + v') s = dddmat g x u v s + dddmat g x u v' s := by
  ext i j; simp [dddmat, mul_add, add_mul, Finset.sum_add_distrib]

theorem dddmat_add_right (x u v s s' : Fin n → ℝ) :
    dddmat g x u v (s + s') = dddmat g x u v s + dddmat g x u v s' := by
  ext i j; simp [dddmat, mul_add, add_mul, Finset.sum_add_distrib]

theorem dddmat_smul_left (x u v s : Fin n → ℝ) (c : ℝ) :
    dddmat g x (c • u) v s = c • dddmat g x u v s := by
  ext i j; simp only [dddmat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem dddmat_smul_mid (x u v s : Fin n → ℝ) (c : ℝ) :
    dddmat g x u (c • v) s = c • dddmat g x u v s := by
  ext i j; simp only [dddmat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem dddmat_smul_right (x u v s : Fin n → ℝ) (c : ℝ) :
    dddmat g x u v (c • s) = c • dddmat g x u v s := by
  ext i j; simp only [dddmat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem dddmat_zero_left (x v s : Fin n → ℝ) : dddmat g x 0 v s = 0 := by
  ext i j; simp [dddmat]

/-- **Mixed partial derivatives commute**: `∂_u ∂_v g = ∂_v ∂_u g` on `U`. -/
theorem _root_.Lightlike.IsCoordMetric.ddmat_comm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (u v : Fin n → ℝ) : ddmat g x u v = ddmat g x v u := by
  ext i j
  simp only [ddmat, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by
    rw [Lightlike.pd_pd_comm (hg.smooth i j) hg.isOpen hx l k]; ring

/-- Entries of `∂_u ∂_v ∂_s g` are bounded by `n³ m ‖u‖ ‖v‖ ‖s‖` if the third derivatives are
bounded by `m`. -/
theorem abs_dddmat_le {x u v s : Fin n → ℝ} {m : ℝ}
    (hd : ∀ i j k l p, |Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) x| ≤ m) (i j : Fin n) :
    |dddmat g x u v s i j| ≤ n ^ 3 * m * ‖u‖ * ‖v‖ * ‖s‖ := by
  have h : |∑ k, u k * ∑ l, v l * ∑ p, s p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) x| ≤
      n * ‖u‖ * (n * ‖v‖ * (n * ‖s‖ * m)) :=
    abs_sum_mul_le (norm_nonneg u) (abs_le_norm_apply u) fun k =>
      abs_sum_mul_le (norm_nonneg v) (abs_le_norm_apply v) fun l =>
        abs_sum_mul_le (norm_nonneg s) (abs_le_norm_apply s) (hd i j k l)
  have e : dddmat g x u v s i j =
      ∑ k, u k * ∑ l, v l * ∑ p, s p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) x := by
    simp only [dddmat, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  calc _ ≤ _ := h
    _ = n ^ 3 * m * ‖u‖ * ‖v‖ * ‖s‖ := by ring

/-- **Uniform bounds for the fourth derivatives of the metric** on a compact subset `K` of
`U`. -/
theorem _root_.Lightlike.IsCoordMetric.exists_jet_bound4 (hg : Lightlike.IsCoordMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ m, 0 ≤ m ∧ ∀ z ∈ K, ∀ i j k l p q : Fin n,
      |Lightlike.pd q (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j)))) z| ≤ m := by
  have d4 : ∀ k l p q i j,
      ContDiffOn ℝ ∞ (Lightlike.pd q (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))))) U :=
    fun k l p q i j => Lightlike.contDiffOn_pd (Lightlike.contDiffOn_pd (Lightlike.contDiffOn_pd
      (hg.contDiffOn_pdg k i j) hg.isOpen l) hg.isOpen p) hg.isOpen q
  obtain ⟨m, h0, hm⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n × Fin n × Fin n) =>
      Lightlike.pd t.2.2.2.1 (Lightlike.pd t.2.2.1 (Lightlike.pd t.2.1 (Lightlike.pd t.1
        (fun y => g y t.2.2.2.2.1 t.2.2.2.2.2)))))
    fun t => (d4 t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2).continuousOn.mono hKU
  exact ⟨m, h0, fun z hz i j k l p q => hm (k, l, p, q, i, j) z hz⟩

/-! ## Taylor's theorem of order four -/

/-- One-dimensional Taylor estimate of order `4`. -/
theorem taylor_aux_four {φ0 φ1 φ2 φ3 φ4 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ0 (φ1 s) s)
    (d1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (d2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ2 (φ3 s) s)
    (d3 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ3 (φ4 s) s) (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ4 s| ≤ K) :
    |φ0 1 - φ0 0 - φ1 0 - (1 / 2) * φ2 0 - (1 / 6) * φ3 0| ≤ K := by
  have h3 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ3 s - φ3 0) (ψ' := φ4) (K := K) (k := 0)
    (by simp) (fun s hs => (d3 s hs).sub_const _) (fun s hs => by simpa using hb s hs)
  have h2 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ2 s - φ2 0 - s * φ3 0)
    (ψ' := fun s => φ3 s - φ3 0) (K := K) (k := 1) (by simp)
    (fun s hs => (((d2 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ3 0))).congr_deriv
      (by ring))
    (fun s hs => by simpa using h3 s hs)
  have h1 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ1 s - φ1 0 - s * φ2 0 - s ^ 2 / 2 * φ3 0)
    (ψ' := fun s => φ2 s - φ2 0 - s * φ3 0) (K := K / 2) (k := 2) (by simp)
    (fun s hs => ((((d1 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ2 0))).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (φ3 0))).congr_deriv (by simp))
    (fun s hs => (h2 s hs).trans_eq (by push_cast; ring))
  have h0 := abs_le_of_hasDerivAt_le_pow
    (ψ := fun s => φ0 s - φ0 0 - s * φ1 0 - s ^ 2 / 2 * φ2 0 - s ^ 3 / 6 * φ3 0)
    (ψ' := fun s => φ1 s - φ1 0 - s * φ2 0 - s ^ 2 / 2 * φ3 0) (K := K / 6) (k := 3) (by simp)
    (fun s hs => (((((d0 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ1 0))).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (φ2 0))).sub
      (((hasDerivAt_pow 3 s).div_const 6).mul_const (φ3 0))).congr_deriv (by push_cast; ring))
    (fun s hs => (h1 s hs).trans_eq (by push_cast; ring))
    1 ⟨zero_le_one, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  norm_num at h0
  rw [show φ0 1 - φ0 0 - φ1 0 - 1 / 2 * φ2 0 - 1 / 6 * φ3 0
      = φ0 1 - φ0 0 - φ1 0 - 2⁻¹ * φ2 0 - 6⁻¹ * φ3 0 by ring]
  linarith [h0]

/-- **Taylor's theorem of order `4`** along a segment in `U`, with the fourth partial derivatives
bounded by `m` on the segment. -/
theorem taylor_four {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ U) {m : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k l p q,
      |Lightlike.pd q (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f))) (x + s • w)| ≤ m) :
    |f (x + w) - f x - ∑ k, w k * Lightlike.pd k f x
      - (1 / 2) * ∑ k, ∑ l, w k * w l * Lightlike.pd l (Lightlike.pd k f) x
      - (1 / 6) * ∑ k, ∑ l, ∑ p, w k * w l * w p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f)) x|
      ≤ n ^ 4 * m * ‖w‖ ^ 4 := by
  have f1 : ∀ k, ContDiffOn ℝ ∞ (Lightlike.pd k f) U := fun k => Lightlike.contDiffOn_pd hf hU k
  have f2 : ∀ k l, ContDiffOn ℝ ∞ (Lightlike.pd l (Lightlike.pd k f)) U :=
    fun k l => Lightlike.contDiffOn_pd (f1 k) hU l
  have f3 : ∀ k l p, ContDiffOn ℝ ∞ (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f))) U :=
    fun k l p => Lightlike.contDiffOn_pd (f2 k l) hU p
  have := taylor_aux_four (φ0 := fun s => f (x + s • w))
    (φ1 := fun s => ∑ k, w k * Lightlike.pd k f (x + s • w))
    (φ2 := fun s => ∑ k, w k * ∑ l, w l * Lightlike.pd l (Lightlike.pd k f) (x + s • w))
    (φ3 := fun s => ∑ k, w k * ∑ l, w l * ∑ p, w p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f)) (x + s • w))
    (φ4 := fun s => ∑ k, w k * ∑ l, w l * ∑ p, w p * ∑ q, w q *
      Lightlike.pd q (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f))) (x + s • w))
    (K := n * ‖w‖ * (n * ‖w‖ * (n * ‖w‖ * (n * ‖w‖ * m))))
    (fun s hs => hasDerivAt_line hf hU (hseg s hs))
    (fun s hs => HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_line (f1 k) hU (hseg s hs)).const_mul (w k))
    (fun s hs => HasDerivAt.fun_sum fun k _ => (HasDerivAt.fun_sum fun l _ =>
      (hasDerivAt_line (f2 k l) hU (hseg s hs)).const_mul (w l)).const_mul (w k))
    (fun s hs => HasDerivAt.fun_sum fun k _ => (HasDerivAt.fun_sum fun l _ =>
      (HasDerivAt.fun_sum fun p _ =>
        (hasDerivAt_line (f3 k l p) hU (hseg s hs)).const_mul (w p)).const_mul (w l)).const_mul
          (w k))
    (fun s hs => abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun k =>
      abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun l =>
        abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun p =>
          abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun q => hm s hs k l p q)
  simp only [one_smul, zero_smul, add_zero] at this
  have e2 : ∑ k, w k * ∑ l, w l * Lightlike.pd l (Lightlike.pd k f) x =
      ∑ k, ∑ l, w k * w l * Lightlike.pd l (Lightlike.pd k f) x := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ k, w k * ∑ l, w l * ∑ p, w p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f)) x =
      ∑ k, ∑ l, ∑ p, w k * w l * w p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f)) x := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  rw [← e2, ← e3]
  calc _ ≤ _ := this
    _ = n ^ 4 * m * ‖w‖ ^ 4 := by ring

/-! ## Uniform bounds of third order near a point -/

/-- The third-order Taylor polynomial of the metric at `x`, evaluated at `x + u`. -/
noncomputable def taylorMetric3 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  taylorMetric g x u + (1 / 6 : ℝ) • dddmat g x u u u

/-- A larger constant also works in `LocalJet`. -/
theorem LocalJet.mono {x : Fin n → ℝ} {B δ l : ℝ} (h : LocalJet g U x B δ l) {B' : ℝ}
    (hB : B ≤ B') : LocalJet g U x B' δ l where
  one_le := h.one_le.trans hB
  δ_pos := h.δ_pos
  δ_le_one := h.δ_le_one
  l_pos := h.l_pos
  mem := h.mem
  g_le p q := (h.g_le p q).trans (by gcongr)
  d_le u p q := (h.d_le u p q).trans (by gcongr)
  dd_le u u' p q := (h.dd_le u u' p q).trans (by gcongr)
  chr_le u v := (h.chr_le u v).trans (by gcongr)
  inv_le a := (h.inv_le a).trans (by gcongr)
  tay_le u hu p q := (h.tay_le u hu p q).trans (by gcongr)
  low := h.low

/-- **Uniform bounds of third order at `x`**: the bounds of `LocalJet`, a bound by `B` for the
third derivatives of the metric at `x`, and the fourth-order accuracy of the third-order Taylor
polynomial of the metric on the ball of radius `δ` about `x` (sup norms). -/
structure LocalJet3 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (B δ l : ℝ) : Prop extends LocalJet g U x B δ l where
  /-- The third derivatives at `x`. -/
  ddd_le : ∀ u v s p q : Fin n → ℝ,
    |p ⬝ᵥ (dddmat g x u v s *ᵥ q)| ≤ B * ‖u‖ * ‖v‖ * ‖s‖ * ‖p‖ * ‖q‖
  /-- Taylor's theorem of order four for the metric on the ball. -/
  tay3_le : ∀ u : Fin n → ℝ, ‖u‖ ≤ δ → ∀ p q : Fin n → ℝ,
    |p ⬝ᵥ ((g (x + u) - taylorMetric3 g x u) *ᵥ q)| ≤ B * ‖u‖ ^ 4 * ‖p‖ * ‖q‖

/-- **Uniform bounds of third order on a compact set**: for a compact `K ⊆ U` one triple
`B, δ, l` gives `LocalJet3 g U x B δ l` at every `x ∈ K`. -/
theorem IsRiemMetric.exists_localJet3 (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ B δ l : ℝ, ∀ x ∈ K, LocalJet3 g U x B δ l := by
  obtain ⟨B₁, δ, l, hJ⟩ := hg.exists_localJet hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨1, 1, 1, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have hδ := (hJ x₀ hx₀).δ_pos
  have hK' : IsCompact (cthickening δ K) := hK.cthickening
  have hK'U : cthickening δ K ⊆ U := by
    rw [hK.cthickening_eq_biUnion_closedBall hδ.le]
    refine iUnion₂_subset fun x hx y hy => ?_
    have := (hJ x hx).mem (y - x) (by rw [← dist_eq_norm]; exact hy)
    simpa using this
  have hball : ∀ x ∈ K, ∀ u : Fin n → ℝ, ‖u‖ ≤ δ → x + u ∈ cthickening δ K :=
    fun x hx u hu => closedBall_subset_cthickening hx _
      (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hu)
  obtain ⟨m, hm0, hm⟩ := hg.coord.exists_jet_bound hK' hK'U
  obtain ⟨m4, hm40, hm4⟩ := hg.coord.exists_jet_bound4 hK' hK'U
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have p5 := mul_nonneg (pow_nonneg hn 5) hm0
  have p6 := mul_nonneg (pow_nonneg hn 6) hm40
  set B₃ : ℝ := n ^ 6 * m4 + n ^ 5 * m + 1 with hB₃
  have t5 : (n : ℝ) ^ 5 * m ≤ max B₁ B₃ := (by linarith : (n : ℝ) ^ 5 * m ≤ B₃).trans
    (le_max_right _ _)
  have t6 : (n : ℝ) ^ 6 * m4 ≤ max B₁ B₃ := (by linarith : (n : ℝ) ^ 6 * m4 ≤ B₃).trans
    (le_max_right _ _)
  refine ⟨max B₁ B₃, δ, l, fun x hx => ?_⟩
  have h := (hJ x hx).mono (le_max_left B₁ B₃)
  have hx' : x ∈ cthickening δ K := self_subset_cthickening K hx
  have hseg : ∀ u : Fin n → ℝ, ‖u‖ ≤ δ → ∀ s ∈ Icc (0 : ℝ) 1,
      x + s • u ∈ cthickening δ K := fun u hu s hs => hball x hx _ (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg u])
  refine ⟨h, ?_, ?_⟩
  · intro u v s p q
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity)
          (fun i j => abs_dddmat_le (fun i j k l p => (hm x hx' i j k l p).2.2.2.2.1) i j) p q
      _ = n ^ 5 * m * ‖u‖ * ‖v‖ * ‖s‖ * ‖p‖ * ‖q‖ := by ring
      _ ≤ max B₁ B₃ * ‖u‖ * ‖v‖ * ‖s‖ * ‖p‖ * ‖q‖ := by gcongr
  · intro u hu p q
    have hE : ∀ i j, |(g (x + u) - taylorMetric3 g x u) i j| ≤ n ^ 4 * m4 * ‖u‖ ^ 4 := by
      intro i j
      have h4 := taylor_four (f := fun y => g y i j) (hg.coord.smooth i j) hg.coord.isOpen
        (fun s hs => hK'U (hseg u hu s hs))
        (fun s hs k l p q => hm4 _ (hseg u hu s hs) i j k l p q)
      have e : (g (x + u) - taylorMetric3 g x u) i j = g (x + u) i j - g x i j
          - ∑ k, u k * Lightlike.pd k (fun y => g y i j) x
          - (1 / 2) * ∑ k, ∑ l, u k * u l * Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) x
          - (1 / 6) * ∑ k, ∑ l, ∑ p,
              u k * u l * u p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) x := by
        simp only [taylorMetric3, taylorMetric, dmat, ddmat, dddmat, Matrix.sub_apply,
          Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
        ring
      rw [e]; exact h4
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity) hE p q
      _ = n ^ 6 * m4 * ‖u‖ ^ 4 * ‖p‖ * ‖q‖ := by ring
      _ ≤ max B₁ B₃ * ‖u‖ ^ 4 * ‖p‖ * ‖q‖ := by gcongr

end Lightlike.Geodesic

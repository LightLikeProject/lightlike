import Lightlike.Regge.Geodesic.Equation

/-!
# The conserved momentum of a cyclic coordinate

If the components of a coordinate metric `g` do not depend on the coordinate `yᵏ` at the points of a geodesic
(`∂_k g_{ij} = 0`), then the momentum `p_k = Σⱼ g_{kj} wʲ` is constant along the geodesic
(`Lightlike.Geodesic.IsGeodesicOn.hasDerivAt_momentum`). For the Schwarzschild and Eddington–Finkelstein metrics
this gives the energy (`k` the time coordinate) and the axial angular momentum (`k = φ`).

In general `(Σⱼ g_{kj} wʲ)' = ½ Σ_{ml} ∂_k g_{ml} wᵐ wˡ` (`IsGeodesicOn.hasDerivAt_momentum_general`).

Proof: `(g_{kj} wʲ)' = wᵐ ∂_m g_{kj} wʲ + g_{kj} (wʲ)'`, and the lowered geodesic equation gives
`g_{kj} (wʲ)' = -Γ_{k m l} wᵐ wˡ = -wᵐ wˡ ∂_m g_{kl} + ½ wᵐ wˡ ∂_k g_{ml}`.
-/

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The derivative of a momentum along a geodesic**: `(Σⱼ g_{kj} wʲ)' = ½ Σ_{ml} ∂_k g_{ml} wᵐ wˡ`. -/
theorem IsGeodesicOn.hasDerivAt_momentum_general (hg : Lightlike.IsCoordMetric g U)
    {γ w : ℝ → Fin n → ℝ} {I : Set ℝ} (h : IsGeodesicOn g γ w I) {t : ℝ} (ht : t ∈ I) (hγt : γ t ∈ U)
    (k : Fin n) :
    HasDerivAt (fun s => ∑ j, g (γ s) k j * w s j)
      (1 / 2 * ∑ m, ∑ l, Lightlike.pd k (fun y => g y m l) (γ t) * w t m * w t l) t := by
  have hdiff : ∀ j, DifferentiableAt ℝ (fun y => g y k j) (γ t) := fun j =>
    ((hg.smooth k j).contDiffAt (hg.isOpen.mem_nhds hγt)).differentiableAt (by simp)
  have hgkj : ∀ j, HasDerivAt (fun s => g (γ s) k j)
      (∑ m, w t m * Lightlike.pd m (fun y => g y k j) (γ t)) t :=
    fun j => hasDerivAt_comp_pd (hdiff j) (h.pos t ht)
  have hw : ∀ j, HasDerivAt (fun s => w s j) (accel g (γ t) (w t) j) t := fun j =>
    hasDerivAt_pi.mp (h.vel t ht) j
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hgkj j).mul (hw j)
  refine hd.congr_deriv ?_
  set v := w t
  set y₀ := γ t with hy₀
  set A : Fin n → Fin n → ℝ := fun m l => Lightlike.pd m (fun z => g z k l) y₀ with hA
  set B : Fin n → Fin n → ℝ := fun m l => Lightlike.pd k (fun z => g z m l) y₀ with hB
  have hΓ : ∀ m l, Lightlike.christoffelFirst g k m l y₀ = 1 / 2 * (A m l + A l m - B m l) := by
    intro m l
    simp only [Lightlike.christoffelFirst, hA, hB]
  have h1 : ∑ j, g y₀ k j * accel g y₀ v j =
      -∑ m, ∑ l, 1 / 2 * (A m l + A l m - B m l) * v m * v l := by
    simp only [accel, mul_neg, Finset.sum_neg_distrib, neg_inj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hΓ m l, ← hg.lower_christoffel hγt k m l, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ m, ∑ l, 1 / 2 * (A m l + A l m - B m l) * v m * v l =
      ∑ m, ∑ l, A m l * v m * v l - 1 / 2 * ∑ m, ∑ l, B m l * v m * v l := by
    have e1 : ∑ m, ∑ l, 1 / 2 * (A m l + A l m - B m l) * v m * v l =
        ∑ m, ∑ l, 1 / 2 * (A m l * v m * v l) + ∑ m, ∑ l, 1 / 2 * (A l m * v m * v l) -
          ∑ m, ∑ l, 1 / 2 * (B m l * v m * v l) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ m, ∑ l, 1 / 2 * (A l m * v m * v l) = ∑ m, ∑ l, 1 / 2 * (A m l * v m * v l) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    have e3 : ∑ m, ∑ l, 1 / 2 * (A m l * v m * v l) = 1 / 2 * ∑ m, ∑ l, A m l * v m * v l := by
      simp only [Finset.mul_sum]
    have e4 : ∑ m, ∑ l, 1 / 2 * (B m l * v m * v l) = 1 / 2 * ∑ m, ∑ l, B m l * v m * v l := by
      simp only [Finset.mul_sum]
    rw [e1, e2, e3, e4]
    ring
  have h3 : ∑ j, (∑ m, v m * A m j) * v j = ∑ m, ∑ l, A m l * v m * v l := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  show ∑ j, ((∑ m, v m * A m j) * v j + g y₀ k j * accel g y₀ v j) = _
  rw [Finset.sum_add_distrib, h1, h2, h3]
  ring

/-- **The momentum of a cyclic coordinate is conserved along geodesics.** -/
theorem IsGeodesicOn.hasDerivAt_momentum (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {I : Set ℝ} (h : IsGeodesicOn g γ w I) {t : ℝ} (ht : t ∈ I) (hγt : γ t ∈ U) (k : Fin n)
    (hcyc : ∀ i j, Lightlike.pd k (fun y => g y i j) (γ t) = 0) :
    HasDerivAt (fun s => ∑ j, g (γ s) k j * w s j) 0 t := by
  have h1 := h.hasDerivAt_momentum_general hg ht hγt k
  simpa [hcyc] using h1

/-- **Noether's formula along a geodesic**: for a field `K` along the curve,
`(Σ_k K^k p_k)' = Σ_k (K^k)' p_k + ½ Σ_k K^k ∂_k g(w, w)`, with `p_k = Σⱼ g_{kj} wʲ`. -/
theorem IsGeodesicOn.hasDerivAt_noether (hg : Lightlike.IsCoordMetric g U)
    {γ w : ℝ → Fin n → ℝ} {I : Set ℝ} (h : IsGeodesicOn g γ w I) {t : ℝ} (ht : t ∈ I) (hγt : γ t ∈ U)
    {K : ℝ → Fin n → ℝ} {K' : Fin n → ℝ} (hK : HasDerivAt K K' t) :
    HasDerivAt (fun s => ∑ k, K s k * ∑ j, g (γ s) k j * w s j)
      (∑ k, K' k * ∑ j, g (γ t) k j * w t j +
        1 / 2 * ∑ k, K t k * ∑ m, ∑ l, Lightlike.pd k (fun y => g y m l) (γ t) * w t m * w t l) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hasDerivAt_pi.1 hK k).mul (h.hasDerivAt_momentum_general hg ht hγt k)
  refine hd.congr_deriv ?_
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The derivative of the quadratic form `g(v, v)` along a line, in terms of the partial derivatives. -/
theorem hasDerivAt_quadratic_line (hg : Lightlike.IsCoordMetric g U) {z : Fin n → ℝ} (hz : z ∈ U)
    (K v : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => ∑ m, ∑ l, g (z + s • K) m l * v m * v l)
      (∑ k, K k * ∑ m, ∑ l, Lightlike.pd k (fun y => g y m l) z * v m * v l) 0 := by
  have hline : HasDerivAt (fun s : ℝ => z + s • K) K 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const K).const_add z
  have h0 : z + (0 : ℝ) • K = z := by simp
  have hml : ∀ m l, HasDerivAt (fun s : ℝ => g (z + s • K) m l)
      (∑ k, K k * Lightlike.pd k (fun y => g y m l) z) 0 := fun m l => by
    have hd : DifferentiableAt ℝ (fun y => g y m l) (z + (0 : ℝ) • K) := by
      rw [h0]
      exact ((hg.smooth m l).contDiffAt (hg.isOpen.mem_nhds hz)).differentiableAt (by simp)
    have := hasDerivAt_comp_pd (γ := fun s : ℝ => z + s • K) hd hline
    simpa only [h0] using this
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun m _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun l _ => ((hml m l).mul_const (v m)).mul_const (v l)
  refine hd.congr_deriv ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun m _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ =>
    Finset.sum_congr rfl fun l _ => by ring

end Lightlike.Geodesic

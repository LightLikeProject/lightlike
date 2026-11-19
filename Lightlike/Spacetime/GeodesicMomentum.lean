import Lightlike.Regge.Geodesic.Equation

/-!
# The conserved momentum of a cyclic coordinate

If the components of a coordinate metric `g` do not depend on the coordinate `yᵏ` at the points of a geodesic
(`∂_k g_{ij} = 0`), then the momentum `p_k = Σⱼ g_{kj} wʲ` is constant along the geodesic
(`Lightlike.Geodesic.IsGeodesicOn.hasDerivAt_momentum`). For the Schwarzschild and Eddington–Finkelstein metrics
this gives the energy (`k` the time coordinate) and the axial angular momentum (`k = φ`).

Proof: `(g_{kj} wʲ)' = wᵐ ∂_m g_{kj} wʲ + g_{kj} (wʲ)'`, and the lowered geodesic equation gives
`g_{kj} (wʲ)' = -Γ_{k m l} wᵐ wˡ = -wᵐ wˡ ∂_m g_{kl} + ½ wᵐ wˡ ∂_k g_{ml}`.
-/

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The momentum of a cyclic coordinate is conserved along geodesics.** -/
theorem IsGeodesicOn.hasDerivAt_momentum (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {I : Set ℝ} (h : IsGeodesicOn g γ w I) {t : ℝ} (ht : t ∈ I) (hγt : γ t ∈ U) (k : Fin n)
    (hcyc : ∀ i j, Lightlike.pd k (fun y => g y i j) (γ t) = 0) :
    HasDerivAt (fun s => ∑ j, g (γ s) k j * w s j) 0 t := by
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
  -- the lowered geodesic equation with the cyclic coordinate
  have hΓ : ∀ m l, Lightlike.christoffelFirst g k m l y₀ = 1 / 2 * (A m l + A l m) := by
    intro m l
    simp only [Lightlike.christoffelFirst, hA, hcyc m l]
    ring
  have h1 : ∑ j, g y₀ k j * accel g y₀ v j = -∑ m, ∑ l, 1 / 2 * (A m l + A l m) * v m * v l := by
    simp only [accel, mul_neg, Finset.sum_neg_distrib, neg_inj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hΓ m l, ← hg.lower_christoffel hγt k m l, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ m, ∑ l, 1 / 2 * (A m l + A l m) * v m * v l = ∑ m, ∑ l, A m l * v m * v l := by
    have e1 : ∑ m, ∑ l, 1 / 2 * (A m l + A l m) * v m * v l =
        ∑ m, ∑ l, 1 / 2 * (A m l * v m * v l) + ∑ m, ∑ l, 1 / 2 * (A l m * v m * v l) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ m, ∑ l, 1 / 2 * (A l m * v m * v l) = ∑ m, ∑ l, 1 / 2 * (A m l * v m * v l) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h3 : ∑ j, (∑ m, v m * A m j) * v j = ∑ m, ∑ l, A m l * v m * v l := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  show ∑ j, ((∑ m, v m * A m j) * v j + g y₀ k j * accel g y₀ v j) = 0
  rw [Finset.sum_add_distrib, h1, h2, h3]
  ring

end Lightlike.Geodesic

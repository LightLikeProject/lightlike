import Mathlib
import Lightlike.Geometry.HeatKernel.HeatCoeffs
import Lightlike.Geometry.HeatKernel.WorldFunctionDiag

/-!
# The first heat-kernel coefficient on the diagonal

For the data of `exists_heatCoeffs` (a world function `σ` in the pairing form `g_p(V, V)`, coefficients `u_k` solving the
transport equations), the transport equation of order one at the diagonal reduces to `u₁(p, p) = −Δu₀(p, p)`
(`IsCoordMetric.heatCoeff_one_diag_eq_neg_laplacian`): the gradient of `σ(p, ·)` vanishes at `p` and the transport
coefficient `Δσ/4 + n/2` vanishes there (`IsCoordMetric.transportCoeff_diag`).

## References

* `basile-2024`: I. Basile, L. Buoninfante, F. Di Filippo, B. Knorr, A. Platania, A. Tokareva, *Lectures in Quantum
  Gravity*, arXiv:2412.08690v3, §4.2.5, eq. (4.80) (the recursion (4.79) at coincidence for `n = 1`). The library's `σ`
  is twice the source's and its Laplacian is the negative of the source's `∇²`.
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- A partial derivative depends only on the germ of the function. -/
lemma pd_congr_of_eventuallyEq {F F' : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] F') (i : Fin n) :
    pd i F y = pd i F' y := by
  unfold pd
  rw [h.fderiv_eq]

/-- The coordinate Laplacian depends only on the germ of the function. -/
lemma coordLaplacian_congr_of_eventuallyEq {F F' : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] F') :
    coordLaplacian g F y = coordLaplacian g F' y := by
  unfold coordLaplacian
  congr 2
  funext i
  refine pd_congr_of_eventuallyEq ?_ i
  filter_upwards [h.eventually_nhds] with z hz
  unfold coordFlux
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [pd_congr_of_eventuallyEq hz j]

/-- **The first heat-kernel coefficient at the diagonal is minus the Laplacian of the zeroth**, for a world function in
the pairing form `σ(p, y) = g_p(V(p, y), V(p, y))` with `V(p, p) = 0`, `D_y V(p, p) = id`, and coefficients solving the
transport equation of order one in the second variable. -/
theorem IsCoordMetric.heatCoeff_one_diag_eq_neg_laplacian (hg : IsCoordMetric g U)
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hΩU : ∀ q ∈ Ω, q.2 ∈ U) (hVs : ContDiffOn ℝ ∞ V Ω) {p : Fin n → ℝ} (hp : (p, p) ∈ Ω)
    (hV0 : V (p, p) = 0) (hVd : HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p)
    (hσV : ∀ q ∈ Ω, σ q = Geodesic.pairing g q.1 (V q) (V q))
    (htr : IsTransport g {y | (p, y) ∈ Ω} (fun y => σ (p, y)) (fun k y => u k (p, y)) 1) :
    u 1 (p, p) = -coordLaplacian g (fun y => u 0 (p, y)) p := by
  set S : Set (Fin n → ℝ) := {y | (p, y) ∈ Ω} with hSdef
  have hS : IsOpen S := hΩ.preimage (continuous_const.prodMk continuous_id)
  have hpS : p ∈ S := hp
  have hpU : p ∈ U := hΩU _ hp
  set V' : (Fin n → ℝ) → (Fin n → ℝ) := fun y => V (p, y) with hV'
  set P : (Fin n → ℝ) → ℝ := fun y => ∑ a, ∑ b, V' y a * (g p a b * V' y b) with hP
  have hsP : (fun y => σ (p, y)) =ᶠ[𝓝 p] P := by
    filter_upwards [hS.mem_nhds hpS] with y hy
    rw [hσV _ hy]
    rfl
  -- the transport coefficient vanishes at `p`
  have hU' : IsOpen (U ∩ S) := hg.isOpen.inter hS
  have hg' : IsCoordMetric g (U ∩ S) := hg.mono hU' inter_subset_left
  have hVs' : ∀ a, ContDiffOn ℝ ∞ (fun y => V' y a) (U ∩ S) := by
    intro a
    have hc : ContDiffOn ℝ ∞ V' S :=
      hVs.comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy => hy
    exact ((contDiffOn_pi.1 hc) a).mono inter_subset_right
  have hcoef := hg'.transportCoeff_diag ⟨hpU, hpS⟩ hVs' hV0 hVd
  rw [← coordLaplacian_congr_of_eventuallyEq hsP] at hcoef
  -- the gradient of `σ(p, ·)` vanishes at `p`
  have hpd : ∀ i, pd i (fun y => σ (p, y)) p = 0 := by
    intro i
    rw [pd_congr_of_eventuallyEq hsP i]
    have hPeq : P = (fun v => Geodesic.pairing g p v v) ∘ V' := by
      funext y; rfl
    have hdiff : DifferentiableAt ℝ (fun v => Geodesic.pairing g p v v) (V' p) := by
      unfold Geodesic.pairing; fun_prop
    unfold pd
    rw [hPeq, fderiv_comp p hdiff hVd.differentiableAt, hVd.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.id_apply]
    rw [Geodesic.fderiv_pairing_self hg hpU]
    have h0 : V' p = 0 := hV0
    rw [h0]
    simp [Geodesic.pairing]
  have hgp : coordGradPair g (fun y => σ (p, y)) (fun y => u 1 (p, y)) p = 0 := by
    unfold coordGradPair
    simp [hpd]
  have ht := htr 1 le_rfl p hpS
  simp only [hgp, one_ne_zero, ite_false, Nat.sub_self] at ht
  have hc : coordLaplacian g (fun y => σ (p, y)) p / 4 + n / 2 = 0 := hcoef
  rw [hc] at ht
  linarith

end Lightlike

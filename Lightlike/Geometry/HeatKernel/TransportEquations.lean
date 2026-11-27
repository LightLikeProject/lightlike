import Mathlib
import Lightlike.Geometry.HeatKernel.GaussianAnsatz

/-!
# The transport equations and the error of the truncated parametrix

For a coordinate metric `g` on an open `U ⊆ ℝⁿ`, a smooth `σ` with the eikonal equation `g⁻¹(dσ, dσ) = 4σ`, and smooth
coefficients `u₀, u₁, …` on `U`, the **transport equations** (`IsTransport`) are

`g⁻¹(dσ, du_k)/2 + (k − Δσ/4 − n/2) u_k = −Δu_{k−1}`   (`u_{−1} = 0`).

They are the vanishing of the coefficients of `t^{k−1}` when the heat operator is applied to the ansatz
`(4πt)^{-n/2} e^{-σ/4t} Σ_{k ≤ N} tᵏ u_k` (`heatOperator_gaussian_ansatz`). If they hold for `k ≤ N`, the sum telescopes
and the heat operator of the truncated ansatz is exactly

`(4πt)^{-n/2} e^{-σ/4t} t^N Δu_N`   (`heatOperator_truncated_ansatz`),

the source of the error bound `O(t^{N − n/2})` of the Minakshisundaram–Pleijel parametrix.

The supporting linearity: `IsCoordMetric.coordLaplacian_sum_smul`, `IsCoordMetric.coordGradPair_sum_smul_right`.

## References

* `rosenberg-1997`: S. Rosenberg, *The Laplacian on a Riemannian Manifold* (1997), §3.2, the transport equations and the
  error `(∂ₜ + Δ) H_N = (4πt)^{-n/2} e^{-d²/4t} t^N Δu_N` (away from the cutoff). Comparison pending (not read at that
  location).
-/

open Set Filter Real
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Linearity of the pairing in the second slot** over a finite sum with constant coefficients. -/
theorem IsCoordMetric.coordGradPair_sum_smul_right (hg : IsCoordMetric g U) {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) {F : (Fin n → ℝ) → ℝ} {H : ι → (Fin n → ℝ) → ℝ} (hH : ∀ i, ContDiffOn ℝ ∞ (H i) U)
    {y : Fin n → ℝ} (hy : y ∈ U) :
    coordGradPair g F (fun z => ∑ i ∈ S, c i * H i z) y = ∑ i ∈ S, c i * coordGradPair g F (H i) y := by
  have hd : ∀ i, DifferentiableAt ℝ (fun z => c i * H i z) y := fun i =>
    (differentiableAt_of_contDiffOn (hH i) hg.isOpen hy).const_mul (c i)
  have hpd : ∀ k, pd k (fun z => ∑ i ∈ S, c i * H i z) y = ∑ i ∈ S, c i * pd k (H i) y := fun k => by
    rw [pd_sum S (f := fun i z => c i * H i z) (fun i _ => hd i) k]
    exact Finset.sum_congr rfl fun i _ =>
      pd_const_mul (c i) (differentiableAt_of_contDiffOn (hH i) hg.isOpen hy) k
  unfold coordGradPair
  calc ∑ a, ∑ b, (g y)⁻¹ a b * pd a F y * pd b (fun z => ∑ i ∈ S, c i * H i z) y
      = ∑ a, ∑ b, ∑ i ∈ S, c i * ((g y)⁻¹ a b * pd a F y * pd b (H i) y) := by
        simp only [hpd, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by
        simp only [Finset.mul_sum]
        symm
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- **Linearity of the coordinate Laplacian** over a finite sum with constant coefficients. -/
theorem IsCoordMetric.coordLaplacian_sum_smul (hg : IsCoordMetric g U) {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) {F : ι → (Fin n → ℝ) → ℝ} (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordLaplacian g (fun z => ∑ i ∈ S, c i * F i z) y = ∑ i ∈ S, c i * coordLaplacian g (F i) y := by
  have hU := hg.isOpen
  have hflux : ∀ a, coordFlux g (fun z => ∑ i ∈ S, c i * F i z) a =ᶠ[𝓝 y]
      fun z => ∑ i ∈ S, c i * coordFlux g (F i) a z := by
    intro a
    filter_upwards [hU.mem_nhds hy] with z hz
    unfold coordFlux
    have hd : ∀ i, DifferentiableAt ℝ (fun w => c i * F i w) z := fun i =>
      (differentiableAt_of_contDiffOn (hF i) hU hz).const_mul (c i)
    have hpd : ∀ k, pd k (fun w => ∑ i ∈ S, c i * F i w) z = ∑ i ∈ S, c i * pd k (F i) z := fun k => by
      rw [pd_sum S (f := fun i w => c i * F i w) (fun i _ => hd i) k]
      exact Finset.sum_congr rfl fun i _ =>
        pd_const_mul (c i) (differentiableAt_of_contDiffOn (hF i) hU hz) k
    simp only [hpd, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  have hdflux : ∀ a i, DifferentiableAt ℝ (fun z => c i * coordFlux g (F i) a z) y := fun a i =>
    (differentiableAt_of_contDiffOn (hg.contDiffOn_coordFlux (hF i) a) hU hy).const_mul (c i)
  have hpdflux : ∀ a, pd a (coordFlux g (fun z => ∑ i ∈ S, c i * F i z) a) y =
      ∑ i ∈ S, c i * pd a (coordFlux g (F i) a) y := fun a => by
    rw [pd_congr (hflux a) a, pd_sum S (f := fun i z => c i * coordFlux g (F i) a z) (fun i _ => hdflux a i) a]
    exact Finset.sum_congr rfl fun i _ =>
      pd_const_mul (c i) (differentiableAt_of_contDiffOn (hg.contDiffOn_coordFlux (hF i) a) hU hy) a
  unfold coordLaplacian
  simp only [hpdflux, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

/-- **The transport equations** up to order `N`: for `k ≤ N` and `y ∈ U`,
`g⁻¹(dσ, du_k)/2 + (k − Δσ/4 − n/2) u_k = −Δu_{k−1}` (with `u_{−1} = 0`). -/
def IsTransport (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) (σ : (Fin n → ℝ) → ℝ)
    (u : ℕ → (Fin n → ℝ) → ℝ) (N : ℕ) : Prop :=
  ∀ k ≤ N, ∀ y ∈ U, coordGradPair g σ (u k) y / 2 + (k - (coordLaplacian g σ y / 4 + n / 2)) * u k y =
    -(if k = 0 then 0 else coordLaplacian g (u (k - 1)) y)

/-- The truncated ansatz `Σ_{k ≤ N} tᵏ u_k(y)`. -/
def truncAnsatz (u : ℕ → (Fin n → ℝ) → ℝ) (N : ℕ) (t : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), t ^ k * u k y

/-- The telescoping sum: `Σ_{k ≤ N} (t^k a_k − [k ≥ 1] t^{k−1} a_{k−1}) = t^N a_N`. -/
theorem sum_range_telescope (a : ℕ → ℝ) (t : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (t ^ k * a k - if k = 0 then 0 else t ^ (k - 1) * a (k - 1)) = t ^ N * a N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp

/-- **The heat operator on the truncated ansatz**: if the transport equations hold up to order `N`, then for `t > 0`
the time derivative `D` of `(4πt)^{-n/2} e^{-σ(y)/4t} Σ_{k ≤ N} tᵏ u_k(y)` satisfies
`D + (4πt)^{-n/2} Δ(e^{-σ/4t} Σ tᵏ u_k)(y) = (4πt)^{-n/2} e^{-σ(y)/4t} t^N Δu_N(y)`. -/
theorem heatOperator_truncated_ansatz (hg : IsCoordMetric g U) {σ : (Fin n → ℝ) → ℝ} {u : ℕ → (Fin n → ℝ) → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ U) (hu : ∀ k, ContDiffOn ℝ ∞ (u k) U) (heik : coordGradPair g σ σ = fun y => 4 * σ y)
    {N : ℕ} (htr : IsTransport g U σ u N) {t : ℝ} (ht : 0 < t) {y : Fin n → ℝ} (hy : y ∈ U) :
    ∃ D, HasDerivAt (fun s => heatGaussian n (σ y) s * truncAnsatz u N s y) D t ∧
      D + (4 * π * t) ^ (-(n : ℝ) / 2) * coordLaplacian g (fun z => gaussFactor t (σ z) * truncAnsatz u N t z) y =
        heatGaussian n (σ y) t * (t ^ N * coordLaplacian g (u N) y) := by
  have hsm : ∀ s, ContDiffOn ℝ ∞ (truncAnsatz u N s) U := fun s =>
    ContDiffOn.sum fun k _ => contDiffOn_const.mul (hu k)
  have hut : HasDerivAt (fun s => truncAnsatz u N s y)
      (∑ k ∈ Finset.range (N + 1), (k * t ^ (k - 1)) * u k y) t := by
    unfold truncAnsatz
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pow k t).mul_const (u k y)
  obtain ⟨D, hD, hDeq⟩ := heatOperator_gaussian_ansatz hg hσ hsm heik ht hy hut
  refine ⟨D, hD, ?_⟩
  rw [hDeq]
  congr 1
  have hL : coordLaplacian g (truncAnsatz u N t) y =
      ∑ k ∈ Finset.range (N + 1), t ^ k * coordLaplacian g (u k) y :=
    hg.coordLaplacian_sum_smul (Finset.range (N + 1)) (fun k => t ^ k) hu hy
  have hP : coordGradPair g σ (truncAnsatz u N t) y =
      ∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g σ (u k) y :=
    hg.coordGradPair_sum_smul_right (Finset.range (N + 1)) (fun k => t ^ k) hu hy
  rw [hL, hP]
  unfold truncAnsatz
  -- each term of the `1/t` part, by the transport equation
  have hk : ∀ k ∈ Finset.range (N + 1),
      t ^ k * coordGradPair g σ (u k) y / 2 - (coordLaplacian g σ y / 4 + n / 2) * (t ^ k * u k y) =
        t ^ k * (-(k : ℝ) * u k y - if k = 0 then 0 else coordLaplacian g (u (k - 1)) y) := by
    intro k hkN
    have h := htr k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hkN)) y hy
    have h' : coordGradPair g σ (u k) y / 2 - (coordLaplacian g σ y / 4 + n / 2) * u k y =
        -(k : ℝ) * u k y - if k = 0 then 0 else coordLaplacian g (u (k - 1)) y := by
      linear_combination h
    calc t ^ k * coordGradPair g σ (u k) y / 2 - (coordLaplacian g σ y / 4 + n / 2) * (t ^ k * u k y)
        = t ^ k * (coordGradPair g σ (u k) y / 2 - (coordLaplacian g σ y / 4 + n / 2) * u k y) := by ring
      _ = _ := by rw [h']
  have h1 : (∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g σ (u k) y) / 2 -
      (coordLaplacian g σ y / 4 + n / 2) * ∑ k ∈ Finset.range (N + 1), t ^ k * u k y =
      ∑ k ∈ Finset.range (N + 1),
        t ^ k * (-(k : ℝ) * u k y - if k = 0 then 0 else coordLaplacian g (u (k - 1)) y) := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k hk' => by rw [← hk k hk']
  rw [h1]
  -- divide by `t` and telescope
  have ht0 : t ≠ 0 := ht.ne'
  have h2 : (∑ k ∈ Finset.range (N + 1),
      t ^ k * (-(k : ℝ) * u k y - if k = 0 then 0 else coordLaplacian g (u (k - 1)) y)) / t =
      ∑ k ∈ Finset.range (N + 1),
        (-(k * t ^ (k - 1)) * u k y - if k = 0 then 0 else t ^ (k - 1) * coordLaplacian g (u (k - 1)) y) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false, pow_succ]
      field_simp
  rw [h2]
  have h3 := sum_range_telescope (fun k => coordLaplacian g (u k) y) t N
  rw [← h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Lightlike

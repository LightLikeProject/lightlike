import Mathlib
import Lightlike.Geometry.HeatKernel.IsChartParametrix
import Lightlike.Geometry.HeatKernel.GaussDerivBounds

/-!
# Derivative bounds of the heat error of the chart parametrix

The heat error `E(t, p, y) = ∂ₜH + Δ_y H` of the chart parametrix (`Lightlike.IsChartParametrix`) satisfies, for every
order `ℓ`, `‖D^ℓ_{(p, y)} E(t, ·)‖ ≤ C t^{N − n/2 − ℓ}` for `t ∈ (0, 1]` and `p` near the centre, all `y`.

Helpers first: the joint smoothness of the gradient pairing in the second variable, a Leibniz bound for a smooth
function times the Gaussian factor with a constant linear in the bounds of the function, and uniform bounds for
polynomials in `t ∈ [0, 1]` with smooth coefficients.
-/

open Set Filter Metric Real Nat
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A Leibniz bound with the Gaussian factor, linear in the bounds of the smooth factor**: there is `C₀` (depending
only on `σ`, `K`, `ℓ`) with `‖D^ℓ (a e^{-σ/4t})(q)‖ ≤ C₀ M t^{-ℓ} e^{-σ(q)/4t}` whenever the derivatives of `a` of order
`≤ ℓ` are bounded by `M` on `K`. -/
theorem exists_gauss_leibniz {s : Set E} (hs : UniqueDiffOn ℝ s) {σ : E → ℝ} (hσ : ContDiffOn ℝ ∞ σ s)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ s) (ℓ : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ a : E → ℝ, ContDiffOn ℝ ∞ a s → ∀ M : ℝ,
      (∀ i ≤ ℓ, ∀ q ∈ K, ‖iteratedFDerivWithin ℝ i a s q‖ ≤ M) → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ q ∈ K,
        ‖iteratedFDerivWithin ℝ ℓ (fun q => a q * Real.exp (-σ q / (4 * t))) s q‖ ≤
          C₀ * M * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t)) := by
  have hG := fun j => norm_iteratedFDerivWithin_gauss_le hs hσ hK hKs j
  choose Cg hCg0 hCg using hG
  refine ⟨∑ i ∈ Finset.range (ℓ + 1), (ℓ.choose i : ℝ) * Cg (ℓ - i),
    Finset.sum_nonneg fun i _ => by have := hCg0 (ℓ - i); positivity, fun a ha M hM t ht q hq => ?_⟩
  have ht0 : 0 < t := ht.1
  have htinv : 1 ≤ t⁻¹ := one_le_inv₀ ht0 |>.2 ht.2
  have he0 : 0 ≤ Real.exp (-σ q / (4 * t)) := (Real.exp_pos _).le
  have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) ha (contDiffOn_gauss hσ t) hs (hKs hq)
    (n := ℓ) (by exact_mod_cast le_top)
  refine hL.trans ?_
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hiℓ : i ≤ ℓ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 := hM i hiℓ q hq
  have h2 := hCg (ℓ - i) t ht q hq
  have h3 : t⁻¹ ^ (ℓ - i) ≤ t⁻¹ ^ ℓ := pow_le_pow_right₀ htinv (Nat.sub_le ℓ i)
  have hc0 : (0 : ℝ) ≤ ℓ.choose i := by positivity
  have hCg0' := hCg0 (ℓ - i)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans h1
  calc (ℓ.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i a s q‖ *
        ‖iteratedFDerivWithin ℝ (ℓ - i) (fun q => Real.exp (-σ q / (4 * t))) s q‖
      ≤ (ℓ.choose i : ℝ) * M * (Cg (ℓ - i) * t⁻¹ ^ (ℓ - i) * Real.exp (-σ q / (4 * t))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 (norm_nonneg _) (by positivity)
    _ ≤ (ℓ.choose i : ℝ) * M * (Cg (ℓ - i) * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t))) := by
        gcongr
    _ = (ℓ.choose i : ℝ) * Cg (ℓ - i) * M * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t)) := by ring

/-- **Polynomials in `t ∈ [0, 1]` with smooth coefficients have uniformly bounded derivatives** on a compact set. -/
theorem exists_bound_iteratedFDerivWithin_poly {s : Set E} (hs : UniqueDiffOn ℝ s) {β : ℕ → E → ℝ}
    (hβ : ∀ k, ContDiffOn ℝ ∞ (β k) s) {K : Set E} (hK : IsCompact K) (hKs : K ⊆ s) (N ℓ : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ≤ ℓ, ∀ q ∈ K,
      ‖iteratedFDerivWithin ℝ i (fun q => ∑ k ∈ Finset.range (N + 1), t ^ k * β k q) s q‖ ≤ M := by
  have hb := fun k => exists_bound_iteratedFDerivWithin hs (hβ k) hK hKs ℓ
  choose Mk hMk0 hMk using hb
  refine ⟨∑ k ∈ Finset.range (N + 1), Mk k, Finset.sum_nonneg fun k _ => hMk0 k, fun t ht i hi q hq => ?_⟩
  have hfun : (fun q => ∑ k ∈ Finset.range (N + 1), t ^ k * β k q) =
      ∑ k ∈ Finset.range (N + 1), (t ^ k) • β k := by
    funext q; simp [Finset.sum_apply, smul_eq_mul]
  rw [hfun, iteratedFDerivWithin_sum_apply (f := fun k => (t ^ k) • β k) hs (hKs hq) fun k _ =>
    (((hβ k).const_smul (t ^ k)).of_le (by exact_mod_cast le_top)) q (hKs hq)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [iteratedFDerivWithin_const_smul_apply (((hβ k).of_le (by exact_mod_cast le_top)) q (hKs hq)) hs (hKs hq),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1 _)]
  calc t ^ k * ‖iteratedFDerivWithin ℝ i (β k) s q‖ ≤ 1 * Mk k :=
        mul_le_mul (pow_le_one₀ ht.1 ht.2) (hMk k i hi q hq) (norm_nonneg _) zero_le_one
    _ = Mk k := one_mul _

end Helpers

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The pairing of the differentials in the second variable is jointly smooth.** -/
theorem IsCoordMetric.contDiffOn_coordGradPair_param (hg : IsCoordMetric g U)
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hΩ : IsOpen Ω) (hΩU : ∀ q ∈ Ω, q.2 ∈ U)
    {A B : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hA : ContDiffOn ℝ ∞ A Ω) (hB : ContDiffOn ℝ ∞ B Ω) :
    ContDiffOn ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      coordGradPair g (fun y => A (q.1, y)) (fun y => B (q.1, y)) q.2) Ω := by
  have heq : ∀ q ∈ Ω, coordGradPair g (fun y => A (q.1, y)) (fun y => B (q.1, y)) q.2 =
      ∑ i, ∑ j, (g q.2)⁻¹ i j * pdY i A q * pdY j B q := by
    intro q hq
    unfold coordGradPair
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [pd_eq_pdY hΩ hA hq i, pd_eq_pdY hΩ hB hq j]
  refine ContDiffOn.congr ?_ heq
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  exact (((hg.contDiffOn_inv i j).comp contDiffOn_snd fun q hq => hΩU q hq).mul
    (contDiffOn_pdY hΩ hA i)).mul (contDiffOn_pdY hΩ hB j)

/-- **The heat error of the chart parametrix is `O(t^{N − n/2 − ℓ})` with all its derivatives**: for every order `ℓ`
and `ρ < r` there is `C` with `‖D^ℓ_{(p, y)} (∂ₜH + Δ_y H)(t, p, y)‖ ≤ C t^{N − n/2 − ℓ}` for `t ∈ (0, 1]`, `‖p − x‖ ≤ ρ`
and every `y`. Near the diagonal the heat error is `t^N θ Δu_N` times the Gaussian; the cutoff terms live where
`σ ≥ c r²/4`, where the Gaussian factor beats every power of `t`; off the support of the cutoff the heat error
vanishes. -/
theorem IsChartParametrix.heatError_deriv_le {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : IsCoordMetric g U) {ρ : ℝ} (hρ : ρ < r) (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ q : (Fin n → ℝ) × (Fin n → ℝ), ‖q.1 - x‖ ≤ ρ →
      ‖iteratedFDeriv ℝ ℓ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        deriv (fun s => H s q.1 q.2) t + coordLaplacian g (H t q.1) q.2) q‖ ≤ C * t ^ ((N : ℝ) - n / 2 - ℓ) := by
  have hr := h.r_pos
  -- the domain where the expanded heat error holds
  set W : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | ‖q.1 - x‖ < r ∧ ‖q.2 - q.1‖ < r} with hWdef
  have hWo : IsOpen W := (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
    (isOpen_lt (continuous_snd.sub continuous_fst).norm continuous_const)
  have hWΩ : W ⊆ Ω := fun q hq => h.mem_of_lt q.1 q.2 hq.1 hq.2
  have hWs : UniqueDiffOn ℝ W := hWo.uniqueDiffOn
  have hW1U : ∀ q ∈ W, q.1 ∈ U := fun q hq =>
    h.snd_mem (q.1, q.1) (h.mem_of_lt q.1 q.1 hq.1 (by simpa using hr))
  have hW2U : ∀ q ∈ W, q.2 ∈ U := fun q hq => h.snd_mem q (hWΩ hq)
  -- the compact set of the estimates
  set K : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | ‖q.1 - x‖ ≤ ρ ∧ q.2 - q.1 ∈ tsupport θ} with hKdef
  have hKW : K ⊆ W := fun q hq => ⟨lt_of_le_of_lt hq.1 hρ, by
    have := h.θ_tsupport hq.2; rwa [mem_ball, _root_.dist_zero_right] at this⟩
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_fst.sub continuous_const).norm continuous_const).inter
        ((isClosed_tsupport θ).preimage (continuous_snd.sub continuous_fst))
    · refine (Metric.isBounded_closedBall (x := ((x, x) : (Fin n → ℝ) × (Fin n → ℝ))) (r := ρ + r)).subset ?_
      intro q hq
      have h2 := (hKW hq).2
      rw [mem_closedBall, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      refine max_le (by linarith [hq.1]) ?_
      have := norm_sub_le_norm_sub_add_norm_sub q.2 q.1 x
      linarith [hq.1]
  -- the smooth coefficients
  have hθ' : ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) => θ (q.2 - q.1)) :=
    h.θ_smooth.comp (contDiff_snd.sub contDiff_fst)
  have hσs : ContDiffOn ℝ ∞ σ W := by
    refine ContDiffOn.congr ?_ fun q hq => h.σ_eq q (hWΩ hq)
    unfold Geodesic.pairing
    have hV := contDiffOn_pi.1 (h.V_smooth.mono hWΩ)
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (hV i).mul (((hg.smooth i j).comp contDiffOn_fst fun q hq => hW1U q hq).mul (hV j))
  have hLu : ContDiffOn ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      coordLaplacian g (fun z => u N (q.1, z)) q.2) W :=
    hg.contDiffOn_coordLaplacian_param hWo hW2U ((h.u_smooth N).mono hWΩ)
  have hLθ : ContDiffOn ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      coordLaplacian g (fun z => θ (z - q.1)) q.2) W :=
    hg.contDiffOn_coordLaplacian_param (F := fun q => θ (q.2 - q.1)) hWo hW2U hθ'.contDiffOn
  have hGk : ∀ k, ContDiffOn ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      coordGradPair g (fun z => θ (z - q.1)) (fun z => u k (q.1, z)) q.2) W := fun k =>
    hg.contDiffOn_coordGradPair_param (A := fun q => θ (q.2 - q.1)) hWo hW2U hθ'.contDiffOn
      ((h.u_smooth k).mono hWΩ)
  have hGσ : ContDiffOn ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      coordGradPair g (fun z => θ (z - q.1)) (fun z => σ (q.1, z)) q.2) W :=
    hg.contDiffOn_coordGradPair_param (A := fun q => θ (q.2 - q.1)) hWo hW2U hθ'.contDiffOn hσs
  set a : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q =>
    θ (q.2 - q.1) * coordLaplacian g (fun z => u N (q.1, z)) q.2 with ha
  set β : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun k q =>
    u k q * coordLaplacian g (fun z => θ (z - q.1)) q.2 -
      2 * coordGradPair g (fun z => θ (z - q.1)) (fun z => u k (q.1, z)) q.2 with hβ
  set γ : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun k q =>
    u k q * coordGradPair g (fun z => θ (z - q.1)) (fun z => σ (q.1, z)) q.2 / 2 with hγ
  have has : ContDiffOn ℝ ∞ a W := hθ'.contDiffOn.mul hLu
  have hβs : ∀ k, ContDiffOn ℝ ∞ (β k) W := fun k =>
    (((h.u_smooth k).mono hWΩ).mul hLθ).sub (contDiffOn_const.mul (hGk k))
  have hγs : ∀ k, ContDiffOn ℝ ∞ (γ k) W := fun k => (((h.u_smooth k).mono hWΩ).mul hGσ).div_const 2
  -- the constants
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_gauss_leibniz hWs hσs hKc hKW ℓ
  obtain ⟨Ma, hMa0, hMa⟩ := exists_bound_iteratedFDerivWithin hWs has hKc hKW ℓ
  obtain ⟨Mβ, hMβ0, hMβ⟩ := exists_bound_iteratedFDerivWithin_poly hWs hβs hKc hKW N ℓ
  obtain ⟨Mγ, hMγ0, hMγ⟩ := exists_bound_iteratedFDerivWithin_poly hWs hγs hKc hKW N ℓ
  obtain ⟨c, hc, hσlow⟩ := h.σ_lower
  set δ := c * (r / 2) ^ 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set X := C₀ * Mβ * (N ! * (4 / δ) ^ N) + C₀ * Mγ * ((N + 1) ! * (4 / δ) ^ (N + 1)) with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨(4 * π) ^ (-(n : ℝ) / 2) * (C₀ * Ma + X), by positivity, fun t ht q hq => ?_⟩
  have ht0 : 0 < t := ht.1
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht.2⟩
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.2 ht0.le
  -- the target power
  have hsplit : (4 * π) ^ (-(n : ℝ) / 2) * (C₀ * Ma + X) * t ^ ((N : ℝ) - n / 2 - ℓ) =
      (4 * π * t) ^ (-(n : ℝ) / 2) * ((C₀ * Ma + X) * (t ^ N * t⁻¹ ^ ℓ)) := by
    rw [fourPi_rpow_split ht0 n, Real.rpow_sub ht0, Real.rpow_sub ht0, Real.rpow_natCast, Real.rpow_natCast,
      show (-(n : ℝ) / 2) = -((n : ℝ) / 2) by ring, Real.rpow_neg ht0.le, inv_pow]
    field_simp
  rw [hsplit]
  have hGt0 : 0 < (4 * π * t) ^ (-(n : ℝ) / 2) := by positivity
  have hRnn : 0 ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * ((C₀ * Ma + X) * (t ^ N * t⁻¹ ^ ℓ)) := by positivity
  set E : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q =>
    deriv (fun s => H s q.1 q.2) t + coordLaplacian g (H t q.1) q.2 with hEdef
  by_cases hsupp : q.2 - q.1 ∈ tsupport θ
  swap
  · -- off the support of the cutoff the heat error vanishes near `q`
    have hO : IsOpen {q' : (Fin n → ℝ) × (Fin n → ℝ) | q'.2 - q'.1 ∉ tsupport θ} :=
      (isClosed_tsupport θ).isOpen_compl.preimage (continuous_snd.sub continuous_fst)
    have hE0 : E =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hO.mem_nhds hsupp] with q' hq'
      have hθy : θ (q'.2 - q'.1) = 0 := image_eq_zero_of_notMem_tsupport hq'
      have hz : ∀ᶠ z in 𝓝 q'.2, θ (z - q'.1) = 0 := by
        have h0 : ∀ᶠ w in 𝓝 (q'.2 - q'.1), θ w = 0 := notMem_tsupport_iff_eventuallyEq.mp hq'
        exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds h0
      have hHz : H t q'.1 =ᶠ[𝓝 q'.2] fun _ => 0 := by
        filter_upwards [hz] with z hz
        rw [h.H_eq, hz, zero_mul]
      have hd : (fun s => H s q'.1 q'.2) = fun _ => 0 := funext fun s => by rw [h.H_eq, hθy, zero_mul]
      have hL : coordLaplacian g (H t q'.1) q'.2 = 0 := by
        unfold coordLaplacian
        have hflux : ∀ i, coordFlux g (H t q'.1) i =ᶠ[𝓝 q'.2] fun _ => 0 := fun i => by
          filter_upwards [hHz.eventuallyEq_nhds] with z hz'
          simp [coordFlux, pd_congr hz', pd_const]
        simp [pd_congr (hflux _), pd_const]
      simp only [hEdef, hd, hL, deriv_const, add_zero]
    rw [(hE0.iteratedFDeriv (𝕜 := ℝ) ℓ).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact hRnn
  have hqK : q ∈ K := ⟨hq, hsupp⟩
  have hqW := hKW hqK
  set e : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => Real.exp (-σ q / (4 * t)) with he
  set A : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => a q * e q with hA
  set B : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q =>
    (∑ k ∈ Finset.range (N + 1), t ^ k * β k q) * e q with hB
  set Cf : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q =>
    (∑ k ∈ Finset.range (N + 1), t ^ k * γ k q) * e q with hCf
  set G := (4 * π * t) ^ (-(n : ℝ) / 2) with hG
  -- the expanded heat error on `W`
  have hEF : E =ᶠ[𝓝 q] G • ((t ^ N) • A + B + t⁻¹ • Cf) := by
    filter_upwards [hWo.mem_nhds hqW] with q' hq'
    obtain ⟨D, hD, hDeq⟩ := h.heatError_eq t ht0 q'.1 q'.2 hq'.1 hq'.2
    have hsβ : ∑ k ∈ Finset.range (N + 1), t ^ k * β k q' =
        (∑ k ∈ Finset.range (N + 1), t ^ k * u k q') * coordLaplacian g (fun z => θ (z - q'.1)) q'.2 -
          2 * ∑ k ∈ Finset.range (N + 1), t ^ k *
            coordGradPair g (fun z => θ (z - q'.1)) (fun z => u k (q'.1, z)) q'.2 := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [hβ]; ring
    have hsγ : ∑ k ∈ Finset.range (N + 1), t ^ k * γ k q' =
        (∑ k ∈ Finset.range (N + 1), t ^ k * u k q') *
          coordGradPair g (fun z => θ (z - q'.1)) (fun z => σ (q'.1, z)) q'.2 / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by simp only [hγ]; ring
    simp only [hEdef, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hA, hB, hCf]
    rw [hD.deriv, hDeq, hsβ, hsγ]
    simp only [heatGaussian, gaussFactor, truncAnsatz, Prod.mk.eta, ha, he, hG]
    field_simp
    ring
  have hgauss := contDiffOn_gauss hσs t
  have hAs : ContDiffOn ℝ ∞ A W := has.mul hgauss
  have hPβ : ContDiffOn ℝ ∞ (fun q => ∑ k ∈ Finset.range (N + 1), t ^ k * β k q) W :=
    ContDiffOn.sum fun k _ => contDiffOn_const.mul (hβs k)
  have hPγ : ContDiffOn ℝ ∞ (fun q => ∑ k ∈ Finset.range (N + 1), t ^ k * γ k q) W :=
    ContDiffOn.sum fun k _ => contDiffOn_const.mul (hγs k)
  have hBs : ContDiffOn ℝ ∞ B W := hPβ.mul hgauss
  have hCs : ContDiffOn ℝ ∞ Cf W := hPγ.mul hgauss
  have hle : ∀ {f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}, ContDiffOn ℝ ∞ f W → ContDiffWithinAt ℝ ℓ f W q :=
    fun hf => (hf.of_le (by exact_mod_cast le_top)) q hqW
  have hF4 : ContDiffOn ℝ ∞ ((t ^ N) • A) W := hAs.const_smul (t ^ N)
  have hF3 : ContDiffOn ℝ ∞ (t⁻¹ • Cf) W := hCs.const_smul t⁻¹
  have hF2 : ContDiffOn ℝ ∞ ((t ^ N) • A + B) W := hF4.add hBs
  have hF1 : ContDiffOn ℝ ∞ ((t ^ N) • A + B + t⁻¹ • Cf) W := hF2.add hF3
  have hD : iteratedFDeriv ℝ ℓ E q = G • ((t ^ N) • iteratedFDerivWithin ℝ ℓ A W q +
      iteratedFDerivWithin ℝ ℓ B W q + t⁻¹ • iteratedFDerivWithin ℝ ℓ Cf W q) := by
    rw [(hEF.iteratedFDeriv (𝕜 := ℝ) ℓ).eq_of_nhds,
      ← iteratedFDerivWithin_of_isOpen (f := G • ((t ^ N) • A + B + t⁻¹ • Cf)) ℓ hWo hqW,
      iteratedFDerivWithin_const_smul_apply (f := (t ^ N) • A + B + t⁻¹ • Cf) (a := G) (hle hF1) hWs hqW,
      iteratedFDerivWithin_add_apply (f := (t ^ N) • A + B) (g := t⁻¹ • Cf) (hle hF2) (hle hF3) hWs hqW,
      iteratedFDerivWithin_add_apply (f := (t ^ N) • A) (g := B) (hle hF4) (hle hBs) hWs hqW,
      iteratedFDerivWithin_const_smul_apply (f := A) (hle hAs) hWs hqW,
      iteratedFDerivWithin_const_smul_apply (f := Cf) (hle hCs) hWs hqW]
  -- the three estimates
  have hσ0 : 0 ≤ σ q := le_trans (by positivity) (hσlow q.1 q.2 hqW.1 hqW.2)
  have he1 : e q ≤ 1 := by
    simp only [he]; rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hpowN : t ^ N * t⁻¹ ^ N = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht0.ne', one_pow]
  have hAb : ‖iteratedFDerivWithin ℝ ℓ A W q‖ ≤ C₀ * Ma * t⁻¹ ^ ℓ := by
    have := hC₀ a has Ma hMa t ht q hqK
    calc _ ≤ C₀ * Ma * t⁻¹ ^ ℓ * e q := this
      _ ≤ C₀ * Ma * t⁻¹ ^ ℓ * 1 := by gcongr
      _ = _ := mul_one _
  have hBC : ‖iteratedFDerivWithin ℝ ℓ B W q‖ ≤ C₀ * Mβ * (N ! * (4 / δ) ^ N) * (t ^ N * t⁻¹ ^ ℓ) ∧
      t⁻¹ * ‖iteratedFDerivWithin ℝ ℓ Cf W q‖ ≤
        C₀ * Mγ * ((N + 1) ! * (4 / δ) ^ (N + 1)) * (t ^ N * t⁻¹ ^ ℓ) := by
    by_cases hnear : ‖q.2 - q.1‖ < r / 2
    · -- the cutoff is `1` near `q`: the cutoff terms vanish
      have hO2 : IsOpen {q' : (Fin n → ℝ) × (Fin n → ℝ) | ‖q'.2 - q'.1‖ < r / 2} :=
        isOpen_lt (continuous_snd.sub continuous_fst).norm continuous_const
      have hvan : ∀ q' ∈ {q' : (Fin n → ℝ) × (Fin n → ℝ) | ‖q'.2 - q'.1‖ < r / 2}, ∀ k, β k q' = 0 ∧ γ k q' = 0 := by
        intro q' hq' k
        have h1 : (fun z => θ (z - q'.1)) =ᶠ[𝓝 q'.2] fun _ => 1 :=
          (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (h.θ_eventually_one _ hq')
        obtain ⟨hL0, -⟩ := cutoff_terms_eq_zero_of_eventuallyEq_one (g := g) (Φ := fun z => u k (q'.1, z)) h1
        have hG0 := (cutoff_terms_eq_zero_of_eventuallyEq_one (g := g) (Φ := fun z => u k (q'.1, z)) h1).2
        have hS0 := (cutoff_terms_eq_zero_of_eventuallyEq_one (g := g) (Φ := fun z => σ (q'.1, z)) h1).2
        simp only [hβ, hγ, hL0, hG0, hS0, mul_zero, sub_zero, zero_div, and_self]
      have hBev : B =ᶠ[𝓝[W] q] fun _ => 0 := Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Filter.mem_of_superset (hO2.mem_nhds hnear) fun q' hq' => by
          show (∑ k ∈ Finset.range (N + 1), t ^ k * β k q') * e q' = 0
          simp [fun k => (hvan q' hq' k).1])
      have hCev : Cf =ᶠ[𝓝[W] q] fun _ => 0 := Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Filter.mem_of_superset (hO2.mem_nhds hnear) fun q' hq' => by
          show (∑ k ∈ Finset.range (N + 1), t ^ k * γ k q') * e q' = 0
          simp [fun k => (hvan q' hq' k).2])
      have hB0 : B q = 0 := by
        show (∑ k ∈ Finset.range (N + 1), t ^ k * β k q) * e q = 0
        simp [fun k => (hvan q hnear k).1]
      have hC0 : Cf q = 0 := by
        show (∑ k ∈ Finset.range (N + 1), t ^ k * γ k q) * e q = 0
        simp [fun k => (hvan q hnear k).2]
      rw [hBev.iteratedFDerivWithin_eq hB0 ℓ, hCev.iteratedFDerivWithin_eq hC0 ℓ, iteratedFDerivWithin_fun_zero,
        Pi.zero_apply, norm_zero, mul_zero]
      constructor <;> positivity
    · -- away from the diagonal the Gaussian factor beats every power of `t`
      push Not at hnear
      have hσδ : δ ≤ σ q := by
        have hsq : (r / 2) ^ 2 ≤ ‖q.2 - q.1‖ ^ 2 := pow_le_pow_left₀ (by positivity) hnear 2
        exact (mul_le_mul_of_nonneg_left hsq hc.le).trans (hσlow q.1 q.2 hqW.1 hqW.2)
      have hB1 := hC₀ _ hPβ Mβ (fun i hi q' hq' => hMβ t htI i hi q' hq') t ht q hqK
      have hC1 := hC₀ _ hPγ Mγ (fun i hi q' hq' => hMγ t htI i hi q' hq') t ht q hqK
      have hfN := inv_pow_mul_exp_neg_le hδ0 hσδ ht0 N
      have hfN1 := inv_pow_mul_exp_neg_le hδ0 hσδ ht0 (N + 1)
      have hCMβ : 0 ≤ C₀ * Mβ * t⁻¹ ^ ℓ * t ^ N := by positivity
      have hCMγ : 0 ≤ C₀ * Mγ * t⁻¹ ^ ℓ * t ^ N := by positivity
      constructor
      · calc _ ≤ C₀ * Mβ * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t)) := hB1
          _ = C₀ * Mβ * t⁻¹ ^ ℓ * t ^ N * (t⁻¹ ^ N * Real.exp (-σ q / (4 * t))) := by
              rw [show C₀ * Mβ * t⁻¹ ^ ℓ * t ^ N * (t⁻¹ ^ N * Real.exp (-σ q / (4 * t))) =
                C₀ * Mβ * t⁻¹ ^ ℓ * (t ^ N * t⁻¹ ^ N) * Real.exp (-σ q / (4 * t)) by ring, hpowN, mul_one]
          _ ≤ C₀ * Mβ * t⁻¹ ^ ℓ * t ^ N * (N ! * (4 / δ) ^ N) := mul_le_mul_of_nonneg_left hfN hCMβ
          _ = _ := by ring
      · calc t⁻¹ * ‖iteratedFDerivWithin ℝ ℓ Cf W q‖ ≤ t⁻¹ * (C₀ * Mγ * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t))) :=
              mul_le_mul_of_nonneg_left hC1 htinv
          _ = C₀ * Mγ * t⁻¹ ^ ℓ * t ^ N * (t⁻¹ ^ (N + 1) * Real.exp (-σ q / (4 * t))) := by
              rw [show C₀ * Mγ * t⁻¹ ^ ℓ * t ^ N * (t⁻¹ ^ (N + 1) * Real.exp (-σ q / (4 * t))) =
                t⁻¹ * (C₀ * Mγ * t⁻¹ ^ ℓ * (t ^ N * t⁻¹ ^ N) * Real.exp (-σ q / (4 * t))) by ring, hpowN, mul_one]
          _ ≤ C₀ * Mγ * t⁻¹ ^ ℓ * t ^ N * ((N + 1) ! * (4 / δ) ^ (N + 1)) := mul_le_mul_of_nonneg_left hfN1 hCMγ
          _ = _ := by ring
  -- assemble
  rw [hD, norm_smul, Real.norm_eq_abs, abs_of_pos hGt0]
  refine mul_le_mul_of_nonneg_left ?_ hGt0.le
  have hA' := hAb
  have htN : 0 ≤ t ^ N := pow_nonneg ht0.le N
  calc ‖(t ^ N) • iteratedFDerivWithin ℝ ℓ A W q + iteratedFDerivWithin ℝ ℓ B W q +
        t⁻¹ • iteratedFDerivWithin ℝ ℓ Cf W q‖
      ≤ t ^ N * ‖iteratedFDerivWithin ℝ ℓ A W q‖ + ‖iteratedFDerivWithin ℝ ℓ B W q‖ +
          t⁻¹ * ‖iteratedFDerivWithin ℝ ℓ Cf W q‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (le_of_eq ?_)) (le_of_eq ?_))
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htN]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htinv]
    _ ≤ t ^ N * (C₀ * Ma * t⁻¹ ^ ℓ) + C₀ * Mβ * (N ! * (4 / δ) ^ N) * (t ^ N * t⁻¹ ^ ℓ) +
          C₀ * Mγ * ((N + 1) ! * (4 / δ) ^ (N + 1)) * (t ^ N * t⁻¹ ^ ℓ) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hAb htN) hBC.1) hBC.2
    _ = (C₀ * Ma + X) * (t ^ N * t⁻¹ ^ ℓ) := by rw [hX]; ring

end Lightlike

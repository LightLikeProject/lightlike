import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.OppositeL2
import Lightlike.Lorentz.SL2RPlancherel.KTypeOppositeIso
import Lightlike.Lorentz.SL2RPlancherel.LadderOppositeSurjective

/-!
# The opposite-sign block isometry is the principal-series transform on every test function

For natural `l, s` and a smooth `χ` with compact support in `(0, ∞)`, let `src χ = π √(sinh ξ) χ`
in `L²(0, ∞)` (`srcL`) and `T χ = oppTrans s l χ` (`transL`). This file proves that the
continuous part of `src χ`, mapped by the block isometry `blockL2N`, is `T χ`, with no condition on
`χ` beyond smoothness and compact support in `(0, ∞)`. Layer 2c-v of the Plancherel formula on
`SL(2,ℝ)` (opposite-sign blocks), milestone HA3.

* `transL_eq_of_orth`: the case `src χ ⊥ φ_i` for every discrete direction. Then `χ` is a ladder
  image (`exists_hLRN_eq`), so `src χ = blockEN G`, its continuous part is itself, and
  `T χ = blockTgt G = blockL2N (blockEN G)` (`oppTrans_HcN`, `blockL2N_apply`).
* `exists_defect_factor`: hence the defect `T χ - blockL2N (P_cont (src χ))` is a continuous linear
  function of the finitely many moments `⟪φ_i, src χ⟫`.
* `tendsto_srcL_truncT`, `tendsto_oppTrans_truncFun`: the truncations `φ_i η_n / π` by bump
  functions converge to `φ_i` in `L²(0, ∞)`, while their transforms tend to `0` pointwise, since
  `∫ φ_i conj Φ^ν_{s,l} sinh = 0` (`integral_phiN_mul_conj_mcoefP_eq_zero`).
* `blockL2N_srcL`: **`blockL2N (P_cont (src χ)) = T χ` for every test function `χ`**. Subtracting
  from `χ` the truncations of its discrete part gives test functions whose sources converge to the
  continuous part, so their moments tend to `0`; their transforms converge in `L²` to
  `blockL2N (P_cont (src χ))` and pointwise to `T χ`.
* `norm_sq_srcL_eq`: the Plancherel decomposition of the block for every test function,
  `‖src χ‖² = ∫_{(0,∞)} ρ tanh(πρ) |∫ χ conj Φ^{2ρ}_{s,l} sinh|² dρ + ‖P_disc (src χ)‖²`.

## Main results

* `blockL2N_srcL`, `norm_sq_srcL_eq`
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The source function `π √(sinh ξ) χ(ξ)` of a test function. -/
def srcFun (χ : ℝ → ℂ) (ξ : ℝ) : ℂ := ((Real.pi * Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * χ ξ

theorem memLp_srcFun (F : smoothCS) :
    MemLp (srcFun F) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hcont : Continuous (srcFun F) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_sqrt.comp Real.continuous_sinh))).mul F.2.1.continuous
  exact hcont.memLp_of_hasCompactSupport F.2.2.mul_left

/-- The source map `χ ↦ π √(sinh ξ) χ` from the test functions of `(0, ∞)` to `L²(0, ∞)`. -/
def srcL : testPos →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun K := (memLp_srcFun K.1).toLp (srcFun K.1)
  map_add' F G := by
    have h : srcFun ((F + G : testPos).1 : ℝ → ℂ) = srcFun F.1 + srcFun G.1 := by
      funext ξ
      simp only [srcFun, Pi.add_apply]
      rw [show ((F + G : testPos).1 : ℝ → ℂ) = (F.1 : ℝ → ℂ) + G.1 from rfl, Pi.add_apply, mul_add]
    rw [← MemLp.toLp_add (memLp_srcFun F.1) (memLp_srcFun G.1)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : srcFun ((c • F : testPos).1 : ℝ → ℂ) = c • srcFun F.1 := by
      funext ξ
      simp only [srcFun, Pi.smul_apply, smul_eq_mul]
      rw [show ((c • F : testPos).1 : ℝ → ℂ) = c • (F.1 : ℝ → ℂ) from rfl, Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_srcFun F.1)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

lemma integrableOn_pairing (s l : ℕ) (ν : ℝ) {χ : ℝ → ℂ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) :
    IntegrableOn (fun x => χ x * (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)) (Ioi 0) :=
  (((hχ.mul (Complex.continuous_conj.comp (continuous_mcoefP ν s l))).mul
    (Complex.continuous_ofReal.comp Real.continuous_sinh)).integrable_of_hasCompactSupport
    (hc.mul_right.mul_right)).integrableOn

lemma oppPairing_add (s l : ℕ) {χ ψ : ℝ → ℂ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (ν : ℝ) :
    oppPairing s l (χ + ψ) ν = oppPairing s l χ ν + oppPairing s l ψ ν := by
  unfold oppPairing
  rw [← integral_add (integrableOn_pairing s l ν hχ hχc) (integrableOn_pairing s l ν hψ hψc)]
  congr 1
  funext x
  simp only [Pi.add_apply]
  ring

lemma oppPairing_smul (s l : ℕ) (c : ℂ) (χ : ℝ → ℂ) (ν : ℝ) :
    oppPairing s l (c • χ) ν = c * oppPairing s l χ ν := by
  unfold oppPairing
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The pairing only sees `χ` on `(0, ∞)`. -/
lemma oppPairing_congr (s l : ℕ) {χ ψ : ℝ → ℂ} (h : ∀ x, 0 < x → χ x = ψ x) (ν : ℝ) :
    oppPairing s l χ ν = oppPairing s l ψ ν := by
  unfold oppPairing
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [h x hx]

/-- The transform `χ ↦ T χ` from the test functions of `(0, ∞)` to `L²(0, ∞)`. -/
def transL (s l : ℕ) : testPos →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun K := (memLp_oppTrans s l K.1.2.1 K.1.2.2 K.2).toLp (oppTrans s l K.1)
  map_add' F G := by
    have h : oppTrans s l ((F + G : testPos).1 : ℝ → ℂ) = oppTrans s l F.1 + oppTrans s l G.1 := by
      funext ρ
      rw [show ((F + G : testPos).1 : ℝ → ℂ) = (F.1 : ℝ → ℂ) + G.1 from rfl, Pi.add_apply,
        oppTrans, oppTrans, oppTrans, oppPairing_add s l F.1.2.1.continuous F.1.2.2
          G.1.2.1.continuous G.1.2.2]
      ring
    rw [← MemLp.toLp_add (memLp_oppTrans s l F.1.2.1 F.1.2.2 F.2)
      (memLp_oppTrans s l G.1.2.1 G.1.2.2 G.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : oppTrans s l ((c • F : testPos).1 : ℝ → ℂ) = c • oppTrans s l F.1 := by
      funext ρ
      rw [show ((c • F : testPos).1 : ℝ → ℂ) = c • (F.1 : ℝ → ℂ) from rfl, Pi.smul_apply,
        smul_eq_mul, oppTrans, oppTrans, oppPairing_smul]
      ring
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_oppTrans s l F.1.2.1 F.1.2.2 F.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

/-- `⟪φ_i, src χ⟫ = π ∫_{(0,∞)} χ φ_i sinh`. -/
theorem inner_phiVec_srcL (s l : ℕ) (i : DiscIdx s l) (K : testPos) :
    inner ℂ (phiVec s l i) (srcL K) = ((Real.pi : ℝ) : ℂ) *
      ∫ ξ in Ioi (0 : ℝ), (K.1 : ℝ → ℂ) ξ * ((phiN s l i.1 ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  have h1 : (phiVec s l i : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] phiSrc s l i.1 :=
    MemLp.coeFn_toLp (memLp_phiSrc s l i.1 i.2 i.1.2)
  have h2 : (srcL K : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] srcFun K.1 :=
    MemLp.coeFn_toLp (memLp_srcFun K.1)
  refine integral_congr_ae ?_
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 hξ
  rw [e1, e2, phiSrc, srcFun, RCLike.inner_apply', Complex.conj_ofReal]
  have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
  have hr : Real.sqrt (Real.sinh ξ) * phiN s l i.1 ξ * (Real.pi * Real.sqrt (Real.sinh ξ)) =
      Real.pi * phiN s l i.1 ξ * Real.sinh ξ := by
    have := Real.mul_self_sqrt hs
    linear_combination (Real.pi * phiN s l i.1 ξ) * this
  calc (((Real.sqrt (Real.sinh ξ) * phiN s l i.1 ξ : ℝ)) : ℂ) *
        (((Real.pi * Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * (K.1 : ℝ → ℂ) ξ)
      = ((Real.sqrt (Real.sinh ξ) * phiN s l i.1 ξ * (Real.pi * Real.sqrt (Real.sinh ξ)) : ℝ) : ℂ) *
        (K.1 : ℝ → ℂ) ξ := by push_cast; ring
    _ = _ := by rw [hr]; push_cast; ring

/-- **On test functions orthogonal to the discrete directions**, the block isometry of the continuous
part is the principal-series transform: `blockL2N (P_cont (src χ)) = T χ`. -/
theorem transL_eq_of_orth (s l : ℕ) (K : testPos)
    (hK : ∀ i, inner ℂ (phiVec s l i) (srcL K) = 0) :
    transL s l K = blockL2N s l ((contPartN s l).orthogonalProjectionOnto (srcL K)) := by
  have hmom : ∀ i : ℕ, l ≤ i + s → i < l →
      ∫ ξ in Ioi (0 : ℝ), (K.1 : ℝ → ℂ) ξ * ((phiN s l i ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) = 0 := by
    intro i hli hil
    have h := hK ⟨⟨i, hil⟩, hli⟩
    rw [inner_phiVec_srcL] at h
    exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast Real.pi_ne_zero)
  obtain ⟨G, hG, hGc, hGeq⟩ := exists_hLRN_eq s l K.1.2.1 K.1.2.2 K.2 hmom
  set G' : smoothCS := ⟨G, hG, hGc⟩ with hG'
  have hHcN : ∀ ξ, 0 < ξ → HcN s G l ξ = (K.1 : ℝ → ℂ) ξ := fun ξ hξ => by
    rw [HcN_eq_hLRN s hG l hξ, hGeq ξ hξ]
  have hsrc : srcL K = blockEN s l G' := by
    refine MemLp.toLp_congr (memLp_srcFun K.1) (memLp_blockSrcN s l hG hGc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    show srcFun K.1 ξ = blockSrcN s l G ξ
    rw [srcFun, blockSrcN, hHcN ξ hξ]
  have hmem : srcL K = (blockENc s l G' : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) := hsrc
  have hproj : (contPartN s l).orthogonalProjectionOnto (srcL K) = blockENc s l G' := by
    rw [hmem, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [hproj, blockL2N_apply]
  refine MemLp.toLp_congr (memLp_oppTrans s l K.1.2.1 K.1.2.2 K.2) (memLp_blockTgt s l hG hGc)
    (Filter.EventuallyEq.of_eq (funext fun ρ => ?_))
  show oppTrans s l K.1 ρ = blockTgt s l G ρ
  rw [← oppTrans_HcN s l hG hGc ρ]
  unfold oppTrans
  rw [oppPairing_congr s l (fun ξ hξ => (hHcN ξ hξ).symm)]

/-! ### Truncations of the discrete directions -/

/-- Bump functions equal to `1` on `[1/N, N]`, `N = n + 2`, supported in `[1/(2N), N + 1/(2N)]`. -/
def cutoffBump (n : ℕ) : ContDiffBump ((((n : ℝ) + 2) + ((n : ℝ) + 2)⁻¹) / 2) where
  rIn := (((n : ℝ) + 2) - ((n : ℝ) + 2)⁻¹) / 2
  rOut := ((n : ℝ) + 2) / 2
  rIn_pos := by
    have h1 : (1 : ℝ) < (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
    have h2 : ((n : ℝ) + 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  rIn_lt_rOut := by
    have : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
    linarith

lemma tsupport_cutoffBump (n : ℕ) : tsupport (cutoffBump n : ℝ → ℝ) ⊆ Ioi 0 := by
  rw [ContDiffBump.tsupport_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
  show 0 < x
  simp only [cutoffBump] at hx
  linarith [hx.1]

lemma eventually_cutoffBump_eq_one {ξ : ℝ} (hξ : 0 < ξ) :
    ∀ᶠ n : ℕ in atTop, (cutoffBump n : ℝ → ℝ) ξ = 1 := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max ξ ξ⁻¹)
  filter_upwards [eventually_ge_atTop N₀] with n hn
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  have hN : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ξ ≤ (n : ℝ) + 2 := by linarith [le_max_left ξ ξ⁻¹]
  have h2 : ξ⁻¹ ≤ (n : ℝ) + 2 := by linarith [le_max_right ξ ξ⁻¹]
  have h3 : ((n : ℝ) + 2)⁻¹ ≤ ξ := by
    rw [inv_le_comm₀ (by positivity) hξ]; exact h2
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  simp only [cutoffBump]
  constructor <;> linarith

lemma contDiffOn_phiN_infty (s l i : ℕ) : ContDiffOn ℝ ∞ (phiN s l i) (Ioi 0) := by
  unfold phiN
  exact ((Real.contDiff_cosh.sub contDiff_const).pow _).contDiffOn.div
    (Real.contDiff_sinh.pow _).contDiffOn fun ξ hξ => pow_ne_zero _ (Real.sinh_pos_iff.2 hξ).ne'

/-- The truncated discrete direction `φ_i η_n / π`. -/
def truncFun (s l i n : ℕ) (ξ : ℝ) : ℂ :=
  ((phiN s l i ξ * (cutoffBump n : ℝ → ℝ) ξ / Real.pi : ℝ) : ℂ)

lemma tsupport_truncFun (s l i n : ℕ) :
    tsupport (truncFun s l i n) ⊆ tsupport (cutoffBump n : ℝ → ℝ) :=
  closure_mono fun ξ hξ => by
    rw [Function.mem_support] at hξ ⊢
    intro h0
    exact hξ (by simp [truncFun, h0])

lemma contDiff_truncFun (s l i n : ℕ) : ContDiff ℝ ∞ (truncFun s l i n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (cutoffBump n : ℝ → ℝ)
  · have hx0 : 0 < x := tsupport_cutoffBump n hx
    have hφ : ContDiffAt ℝ ∞ (phiN s l i) x :=
      (contDiffOn_phiN_infty s l i).contDiffAt (Ioi_mem_nhds hx0)
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((hφ.mul ((cutoffBump n).contDiff (n := ⊤)).contDiffAt).div_const _)
  · have h0 : truncFun s l i n =ᶠ[𝓝 x] fun _ => 0 := by
      have := (notMem_tsupport_iff_eventuallyEq.1 hx)
      filter_upwards [this] with y hy
      simp only [Pi.zero_apply] at hy
      simp [truncFun, hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- The truncated discrete direction as a test function of `(0, ∞)`. -/
def truncT (s l i n : ℕ) : testPos :=
  ⟨⟨truncFun s l i n, contDiff_truncFun s l i n,
    ((cutoffBump n).hasCompactSupport).mono'
      ((subset_tsupport _).trans (tsupport_truncFun s l i n))⟩,
    (tsupport_truncFun s l i n).trans (tsupport_cutoffBump n)⟩

lemma norm_sq_Lp_two_eq' {μ : Measure ℝ} (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  congr 1
  funext x
  exact inner_self_eq_norm_sq (f x)

/-- **The truncations converge to the discrete direction in `L²(0, ∞)`.** -/
theorem tendsto_srcL_truncT (s l : ℕ) (i : DiscIdx s l) :
    Tendsto (fun n => srcL (truncT s l i.1 n)) atTop (𝓝 (phiVec s l i)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmem := memLp_phiSrc s l i.1 i.2 i.1.2
  have hsq : Tendsto (fun n => ‖srcL (truncT s l i.1 n) - phiVec s l i‖ ^ 2) atTop (𝓝 0) := by
    have he : ∀ n, ‖srcL (truncT s l i.1 n) - phiVec s l i‖ ^ 2 = ∫ ξ in Ioi (0 : ℝ),
        ‖phiSrc s l i.1 ξ * (((cutoffBump n : ℝ → ℝ) ξ - 1 : ℝ) : ℂ)‖ ^ 2 := by
      intro n
      rw [norm_sq_Lp_two_eq']
      refine integral_congr_ae ?_
      have h1 := Lp.coeFn_sub (srcL (truncT s l i.1 n)) (phiVec s l i)
      have h2 : (srcL (truncT s l i.1 n) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
          srcFun (truncT s l i.1 n).1 := MemLp.coeFn_toLp (memLp_srcFun _)
      have h3 : (phiVec s l i : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] phiSrc s l i.1 :=
        MemLp.coeFn_toLp hmem
      filter_upwards [h1, h2, h3] with ξ e1 e2 e3
      rw [e1, Pi.sub_apply, e2, e3]
      congr 2
      show srcFun (truncFun s l i.1 n) ξ - phiSrc s l i.1 ξ = _
      simp only [srcFun, truncFun, phiSrc]
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      push_cast
      field_simp
    simp_rw [he]
    have hint : Integrable (fun ξ => ‖phiSrc s l i.1 ξ‖ ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
      hmem.integrable_norm_pow two_ne_zero
    have hlim := tendsto_integral_of_dominated_convergence (fun ξ => ‖phiSrc s l i.1 ξ‖ ^ 2)
      (F := fun (n : ℕ) ξ => ‖phiSrc s l i.1 ξ * (((cutoffBump n : ℝ → ℝ) ξ - 1 : ℝ) : ℂ)‖ ^ 2)
      (f := fun _ => (0 : ℝ))
      (fun n => ((hmem.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (((cutoffBump n).contDiff (n := 0)).continuous.sub
          continuous_const)).aestronglyMeasurable).norm.pow 2))
      hint (fun n => Eventually.of_forall fun ξ => ?_) ?_
    · simpa using hlim
    · have h0 : 0 ≤ (cutoffBump n : ℝ → ℝ) ξ := (cutoffBump n).nonneg
      have h1 : (cutoffBump n : ℝ → ℝ) ξ ≤ 1 := (cutoffBump n).le_one
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow]
      have : |(cutoffBump n : ℝ → ℝ) ξ - 1| ^ 2 ≤ 1 := by
        rw [sq_abs]; nlinarith
      nlinarith [sq_nonneg ‖phiSrc s l i.1 ξ‖]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_cutoffBump_eq_one hξ] with n hn
      simp [hn]
  have := hsq.sqrt
  simp only [Real.sqrt_zero] at this
  refine this.congr fun n => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- **The transforms of the truncations tend to `0` pointwise**: the pairing of `φ_i` with the
principal-series coefficient vanishes. -/
theorem tendsto_oppTrans_truncFun (s l : ℕ) (i : DiscIdx s l) (ρ : ℝ) :
    Tendsto (fun n => oppTrans s l (truncFun s l i.1 n) ρ) atTop (𝓝 0) := by
  have hP : Tendsto (fun n => oppPairing s l (truncFun s l i.1 n) (2 * ρ)) atTop (𝓝 0) := by
    set ν := 2 * ρ
    have hint := integrableOn_phiN_mul_conj_mcoefP ν s l s l i.1 i.2 i.1.2
    have hz := integral_phiN_mul_conj_mcoefP_eq_zero ν s l i.1 i.2 i.1.2
    have hlim := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (l := (atTop : Filter ℕ))
      (F := fun n x => truncFun s l i.1 n x * (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ))
      (f := fun x => ((phiN s l i.1 x : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefP ν s l x) *
        (Real.sinh x : ℂ) / (Real.pi : ℂ))
      (fun x => ‖((phiN s l i.1 x : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)‖)
      (Eventually.of_forall fun n => (((contDiff_truncFun s l i.1 n).continuous.mul
        (Complex.continuous_conj.comp (continuous_mcoefP ν s l))).mul
        (Complex.continuous_ofReal.comp Real.continuous_sinh)).aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun x => ?_) hint.norm ?_
    · unfold oppPairing
      rw [show (0 : ℂ) = ∫ x in Ioi 0, ((phiN s l i.1 x : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefP ν s l x) *
          (Real.sinh x : ℂ) / (Real.pi : ℂ) by rw [integral_div, hz, zero_div]]
      exact hlim
    · have h0 : 0 ≤ (cutoffBump n : ℝ → ℝ) x := (cutoffBump n).nonneg
      have h1 : (cutoffBump n : ℝ → ℝ) x ≤ 1 := (cutoffBump n).le_one
      simp only [truncFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg h0, abs_of_pos Real.pi_pos]
      have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hk : (cutoffBump n : ℝ → ℝ) x / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 (h1.trans hπ)
      have e : |phiN s l i.1 x| * (cutoffBump n : ℝ → ℝ) x / Real.pi =
          |phiN s l i.1 x| * ((cutoffBump n : ℝ → ℝ) x / Real.pi) := by ring
      rw [e]
      have hk0 : 0 ≤ (cutoffBump n : ℝ → ℝ) x / Real.pi := div_nonneg h0 Real.pi_pos.le
      gcongr
      calc |phiN s l i.1 x| * ((cutoffBump n : ℝ → ℝ) x / Real.pi) ≤ |phiN s l i.1 x| * 1 := by
            gcongr
        _ = _ := mul_one _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_cutoffBump_eq_one hx] with n hn
      simp only [truncFun, hn, mul_one]
      push_cast
      ring
  have := hP.const_mul (((Real.sqrt (ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ) : ℝ) : ℂ) /
    oppConst s l (2 * ρ))
  rw [mul_zero] at this
  exact this

/-! ### The identification on every test function -/

/-- The moments `v ↦ (⟪φ_i, v⟫)_i` against the discrete directions. -/
def momentCLM (s l : ℕ) : L2Ioi →L[ℂ] (DiscIdx s l → ℂ) :=
  ContinuousLinearMap.pi fun i => innerSL ℂ (phiVec s l i)

/-- The block side `χ ↦ blockL2N (P_cont (src χ))`. -/
def blockSide (s l : ℕ) : testPos →ₗ[ℂ] L2Ioi :=
  (blockL2N s l).toLinearMap ∘ₗ
    ((contPartN s l).orthogonalProjectionOnto : L2Ioi →L[ℂ] contPartN s l).toLinearMap ∘ₗ srcL

/-- The transform at a point, as a linear functional of the test function. -/
def evalTrans (s l : ℕ) (ρ : ℝ) : testPos →ₗ[ℂ] ℂ where
  toFun K := oppTrans s l K.1 ρ
  map_add' F G := by
    show oppTrans s l ((F.1 : ℝ → ℂ) + G.1) ρ = _
    rw [oppTrans, oppTrans, oppTrans, oppPairing_add s l F.1.2.1.continuous F.1.2.2
      G.1.2.1.continuous G.1.2.2]
    ring
  map_smul' c F := by
    show oppTrans s l (c • (F.1 : ℝ → ℂ)) ρ = _
    rw [oppTrans, oppTrans, oppPairing_smul, RingHom.id_apply, smul_eq_mul]
    ring

/-- **The defect factors through the moments**: `T χ - blockL2N (P_cont (src χ)) = L (⟪φ_i, src χ⟫)_i`
for a continuous linear `L`, because the defect vanishes when all moments vanish
(`transL_eq_of_orth`). -/
theorem exists_defect_factor (s l : ℕ) :
    ∃ L : (DiscIdx s l → ℂ) →L[ℂ] L2Ioi, ∀ K : testPos,
      transL s l K - blockSide s l K = L (momentCLM s l (srcL K)) := by
  set q : testPos →ₗ[ℂ] (DiscIdx s l → ℂ) := (momentCLM s l).toLinearMap ∘ₗ srcL with hq
  set D : testPos →ₗ[ℂ] L2Ioi := transL s l - blockSide s l with hD
  have hker : ∀ K, q K = 0 → D K = 0 := by
    intro K hK
    have h : ∀ i, inner ℂ (phiVec s l i) (srcL K) = 0 := fun i => by
      have := congrFun hK i
      simpa [hq, momentCLM] using this
    simp only [hD, LinearMap.sub_apply, blockSide, LinearMap.comp_apply, sub_eq_zero]
    exact transL_eq_of_orth s l K h
  have : Module.Free ℂ (LinearMap.range q) := Module.Free.of_divisionRing ℂ _
  have : Module.Projective ℂ (LinearMap.range q) := Module.Projective.of_free
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective q.rangeRestrict
    (LinearMap.range_rangeRestrict q)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (D ∘ₗ r)
  refine ⟨LinearMap.toContinuousLinearMap L, fun K => ?_⟩
  set y : LinearMap.range q := q.rangeRestrict K with hy
  have h1 : L (q K) = D (r y) := by
    have := LinearMap.congr_fun hL y
    simpa [hy] using this
  have h2 : q (r y) = q K := by
    have := LinearMap.congr_fun hr y
    have e : (q.rangeRestrict (r y) : DiscIdx s l → ℂ) = (y : DiscIdx s l → ℂ) := by
      rw [show q.rangeRestrict (r y) = (q.rangeRestrict ∘ₗ r) y from rfl, this]; rfl
    simpa [hy] using e
  have h3 : D (K + (-1 : ℂ) • r y) = 0 := hker _ (by
    rw [map_add, map_smul, h2, neg_one_smul, add_neg_cancel])
  rw [map_add, map_smul, neg_one_smul, add_neg_eq_zero] at h3
  show D K = L (q K)
  rw [h1, h3]

/-- **The opposite-sign block isometry is the principal-series transform on every test function**:
for `χ` smooth with compact support in `(0, ∞)`, `blockL2N (P_cont (π √sinh χ)) = T χ`. -/
theorem blockL2N_srcL (s l : ℕ) (K : testPos) :
    blockL2N s l ((contPartN s l).orthogonalProjectionOnto (srcL K)) = transL s l K := by
  classical
  obtain ⟨L, hL⟩ := exists_defect_factor s l
  set v := srcL K with hv
  set P := (discSpan s l).starProjection v with hP
  have hPmem : P ∈ discSpan s l := (discSpan s l).starProjection_apply_mem v
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hPmem
  set u := v - P with hu
  have huo : u ∈ (discSpan s l)ᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have hmu : momentCLM s l u = 0 := by
    funext i
    simp only [momentCLM, ContinuousLinearMap.pi_apply, innerSL_apply_apply, Pi.zero_apply]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) huo
  have hPc : (contPartN s l).orthogonalProjectionOnto v =
      (contPartN s l).orthogonalProjectionOnto u := by
    have : (contPartN s l).orthogonalProjectionOnto P = 0 := by
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, contPartN, closure_range_blockEN]
      exact Submodule.le_orthogonal_orthogonal _ hPmem
    rw [hu, map_sub, this, sub_zero]
  set ψ : ℕ → testPos := fun n => K + ∑ i, (-c i) • truncT s l i.1 n with hψ
  have hsrcψ : Tendsto (fun n => srcL (ψ n)) atTop (𝓝 u) := by
    have h := (tendsto_const_nhds (x := v)).add
      (tendsto_finsetSum (Finset.univ : Finset (DiscIdx s l))
        fun i _ => (tendsto_srcL_truncT s l i).const_smul (-c i))
    have e : v + ∑ i, (-c i) • phiVec s l i = u := by
      simp only [neg_smul, Finset.sum_neg_distrib, hc, hu, sub_eq_add_neg]
    rw [e] at h
    refine h.congr fun n => ?_
    simp only [hψ, map_add, map_sum, map_smul, hv]
  have hB : Tendsto (fun n => blockSide s l (ψ n)) atTop
      (𝓝 (blockL2N s l ((contPartN s l).orthogonalProjectionOnto u))) :=
    (((blockL2N s l).continuous.comp
      (contPartN s l).orthogonalProjectionOnto.continuous).tendsto u).comp hsrcψ
  have hDψ : Tendsto (fun n => L (momentCLM s l (srcL (ψ n)))) atTop (𝓝 0) := by
    have := ((L.continuous.comp (momentCLM s l).continuous).tendsto u).comp hsrcψ
    simpa [Function.comp_def, hmu] using this
  set Y := blockL2N s l ((contPartN s l).orthogonalProjectionOnto v) with hY
  have hT : Tendsto (fun n => transL s l (ψ n)) atTop (𝓝 Y) := by
    have := hDψ.add hB
    rw [zero_add, ← hPc] at this
    refine this.congr fun n => ?_
    rw [← hL, sub_add_cancel]
  have hpt : ∀ ρ, Tendsto (fun n => oppTrans s l (ψ n).1 ρ) atTop (𝓝 (oppTrans s l K.1 ρ)) := by
    intro ρ
    have h := (tendsto_const_nhds (x := oppTrans s l K.1 ρ)).add
      (tendsto_finsetSum (Finset.univ : Finset (DiscIdx s l))
        fun i _ => (tendsto_oppTrans_truncFun s l i ρ).const_mul (-c i))
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at h
    refine h.congr fun n => ?_
    show _ = evalTrans s l ρ (ψ n)
    simp only [hψ, map_add, map_sum, map_smul, smul_eq_mul]
    rfl
  have hae : ∀ n, (transL s l (ψ n) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      oppTrans s l (ψ n).1 := fun n =>
    MemLp.coeFn_toLp (memLp_oppTrans s l (ψ n).1.2.1 (ψ n).1.2.2 (ψ n).2)
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
  have hYae : (Y : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] oppTrans s l K.1 := by
    filter_upwards [hlim, ae_all_iff.2 hae] with x hx hx'
    have h2 : Tendsto (fun k => (transL s l (ψ (ns k)) : ℝ → ℂ) x) atTop
        (𝓝 (oppTrans s l K.1 x)) :=
      ((hpt x).comp hns.tendsto_atTop).congr fun k => (hx' (ns k)).symm
    exact tendsto_nhds_unique hx h2
  exact Lp.ext (hYae.trans (MemLp.coeFn_toLp (memLp_oppTrans s l K.1.2.1 K.1.2.2 K.2)).symm)

/-- **The Plancherel decomposition of an opposite-sign block, for every test function**: for `χ`
smooth with compact support in `(0, ∞)`,
`‖π √sinh χ‖² = ∫_{(0,∞)} ρ tanh(πρ) |∫ χ conj Φ^{2ρ}_{s,l} sinh|² dρ + ‖P_disc (π √sinh χ)‖²`. -/
theorem norm_sq_srcL_eq (s l : ℕ) (K : testPos) :
    ‖srcL K‖ ^ 2 = (∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) *
        ‖oppPairing s l K.1 (2 * ρ)‖ ^ 2) +
      ‖(discSpan s l).orthogonalProjectionOnto (srcL K)‖ ^ 2 := by
  rw [norm_sq_eq_cont_add_disc s l (srcL K), blockL2N_srcL, norm_sq_Lp_two_eq']
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_oppTrans s l K.1.2.1 K.1.2.2 K.2),
    ae_restrict_mem measurableSet_Ioi] with ρ hρ hρ0
  have hρ0' : (0 : ℝ) ≤ ρ := le_of_lt hρ0
  show ‖(transL s l K : ℝ → ℂ) ρ‖ ^ 2 = _
  rw [show (transL s l K : ℝ → ℂ) ρ = oppTrans s l K.1 ρ from hρ, norm_oppTrans s l _ hρ0', mul_pow,
    Real.sq_sqrt (mul_nonneg hρ0' (tanh_nonneg_of_nonneg (by positivity)))]

end Lightlike.Lorentz.SL2RPlancherel

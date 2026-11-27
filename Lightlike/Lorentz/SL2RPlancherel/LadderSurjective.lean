import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KTypeLR
import Lightlike.Lorentz.SL2RPlancherel.LadderComplete

/-!
# Every test function is a ladder image of a radial generator

For natural `l, r`, every smooth function `H` with compact support in `(0, ∞)` is, on `(0, ∞)`, the
`K`-type `(l, r)` ladder image `hLR r G l` of a smooth compactly supported generator `G`
(`exists_hLR_eq`).  In the variable `v = cosh ξ` the ladder image is
`sinh^{l+r} ξ · u_l(cosh ξ)` with `u₀ = G^{(r)}`, `u_{j+1} = u_j' + r u_j / (v + 1)` (`hLR_eq`), and
both steps are inverted by primitives taken from `+∞`: `u_{j+1} = k` is solved by
`u_j = (v+1)^{-r} ∫_R^v (t+1)^r k`, and `G^{(r)} = u₀` by an `r`-fold primitive, cut off below
`v = 1/2` (the generator only matters on `v ≥ 1`).

Consequence (`norm_sq_eq_of_isTest`): the `K`-type Plancherel identity of layer 1
(`norm_sq_ktype_lr`) holds for every test function of the block, so the chain images of the radial
generators exhaust the block and no part of the block is orthogonal to them: for the same-sign
blocks there is no discrete part.  Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`,
milestone HA3.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **A primitive from `+∞`**: a function smooth on `(0, ∞)` and vanishing on `[R, ∞)` has a smooth
primitive on `(0, ∞)` vanishing on `[R, ∞)`. -/
lemma exists_primitive_top {k : ℝ → ℂ} (hk : ContDiffOn ℝ ∞ k (Ioi 0)) {R : ℝ} (hR : 0 < R)
    (hkR : ∀ v, R ≤ v → k v = 0) :
    ∃ P : ℝ → ℂ, ContDiffOn ℝ ∞ P (Ioi 0) ∧ (∀ v, R ≤ v → P v = 0) ∧
      ∀ v ∈ Ioi (0 : ℝ), HasDerivAt P (k v) v := by
  have hkc := hk.continuousOn
  refine ⟨fun v => ∫ t in R..v, k t, ?_, ?_, ?_⟩
  rotate_left
  · intro v hv
    refine (intervalIntegral.integral_congr fun t ht => ?_).trans intervalIntegral.integral_zero
    rw [uIcc_of_le hv] at ht
    exact hkR t ht.1
  · intro v hv
    exact intervalIntegral.integral_hasDerivAt_right
      ((hkc.mono (ordConnected_Ioi.uIcc_subset (mem_Ioi.2 hR) hv)).intervalIntegrable)
      (hkc.stronglyMeasurableAtFilter isOpen_Ioi v hv) (hkc.continuousAt (isOpen_Ioi.mem_nhds hv))
  have hd : ∀ v ∈ Ioi (0 : ℝ), HasDerivAt (fun v => ∫ t in R..v, k t) (k v) v := fun v hv =>
    intervalIntegral.integral_hasDerivAt_right
      ((hkc.mono (ordConnected_Ioi.uIcc_subset (mem_Ioi.2 hR) hv)).intervalIntegrable)
      (hkc.stronglyMeasurableAtFilter isOpen_Ioi v hv) (hkc.continuousAt (isOpen_Ioi.mem_nhds hv))
  rw [contDiffOn_infty_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
  refine ⟨fun v hv => (hd v hv).differentiableAt.differentiableWithinAt, hk.congr fun v hv => ?_⟩
  exact ((hd v hv).hasDerivWithinAt.derivWithin (isOpen_Ioi.uniqueDiffWithinAt hv))

/-- **An `r`-fold primitive from `+∞`.** -/
lemma exists_iteratedDeriv_eq (j : ℕ) {k : ℝ → ℂ} (hk : ContDiffOn ℝ ∞ k (Ioi 0)) {R : ℝ}
    (hR : 0 < R) (hkR : ∀ v, R ≤ v → k v = 0) :
    ∃ P : ℝ → ℂ, ContDiffOn ℝ ∞ P (Ioi 0) ∧ (∀ v, R ≤ v → P v = 0) ∧
      ∀ v ∈ Ioi (0 : ℝ), iteratedDeriv j P v = k v := by
  induction j generalizing k with
  | zero => exact ⟨k, hk, hkR, fun v _ => by simp⟩
  | succ j ih =>
    obtain ⟨K, hKs, hKR, hKd⟩ := exists_primitive_top hk hR hkR
    obtain ⟨P, hPs, hPR, hPj⟩ := ih hKs hKR
    refine ⟨P, hPs, hPR, fun v hv => ?_⟩
    have hev : iteratedDeriv j P =ᶠ[𝓝 v] K := by
      filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw using hPj w hw
    rw [iteratedDeriv_succ, hev.deriv_eq, (hKd v hv).deriv]

/-- The cutoff `v ↦ smoothTransition (4 v - 1)`: `0` for `v ≤ 1/4`, `1` for `v ≥ 1/2`. -/
def cutQuarter (v : ℝ) : ℝ := Real.smoothTransition (4 * v - 1)

lemma contDiff_cutQuarter : ContDiff ℝ ∞ cutQuarter :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma cutQuarter_eq_zero {v : ℝ} (hv : v ≤ 1 / 4) : cutQuarter v = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma cutQuarter_eq_one {v : ℝ} (hv : 1 / 2 ≤ v) : cutQuarter v = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma tsupport_cutQuarter : tsupport cutQuarter ⊆ Ioi 0 := by
  refine (closure_minimal (fun v hv => ?_) isClosed_Ici).trans (Ici_subset_Ioi.2 (by norm_num : (0 : ℝ) < 1 / 4))
  by_contra h
  exact hv (cutQuarter_eq_zero (le_of_lt (not_le.mp h)))

/-- **The base of the ladder: a generator with a prescribed `r`-th derivative on `v > 1/2`.** -/
lemma exists_generator (r : ℕ) {k : ℝ → ℂ} (hk : ContDiffOn ℝ ∞ k (Ioi 0)) {R : ℝ} (hR : 1 ≤ R)
    (hkR : ∀ v, R ≤ v → k v = 0) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      ∀ v, 1 / 2 < v → iteratedDeriv r G v = k v := by
  obtain ⟨P, hPs, hPR, hPr⟩ := exists_iteratedDeriv_eq r hk (by linarith) hkR
  set χ : ℝ → ℂ := fun v => ((cutQuarter v : ℝ) : ℂ) with hχ
  have hχs : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp contDiff_cutQuarter
  have hχsub : tsupport χ ⊆ Ioi 0 := by
    refine (closure_mono fun v hv => ?_).trans tsupport_cutQuarter
    intro h0; apply hv; simp [hχ, h0]
  refine ⟨fun v => χ v * P v, contDiff_mul_of_tsupport_subset isOpen_Ioi hχs hχsub hPs, ?_, ?_⟩
  · refine HasCompactSupport.intro (isCompact_Icc (a := 1 / 4) (b := R)) fun v hv => ?_
    rcases not_and_or.mp hv with h | h
    · simp [hχ, cutQuarter_eq_zero (le_of_lt (not_le.mp h))]
    · simp [hPR v (le_of_lt (not_le.mp h))]
  · intro v hv
    have hev : (fun v => χ v * P v) =ᶠ[𝓝 v] P := by
      filter_upwards [Ioi_mem_nhds hv] with w hw
      simp [hχ, cutQuarter_eq_one (le_of_lt hw)]
    rw [hev.iteratedDeriv_eq, hPr v (mem_Ioi.2 (by linarith))]

/-- `exp (a log (v + 1))`, the power `(v + 1)^a` for `v > -1`, and its derivative. -/
lemma hasDerivAt_exp_mul_log_add_one (a : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v => Real.exp (a * Real.log (v + 1)))
      (Real.exp (a * Real.log (v + 1)) * (a / (v + 1))) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have h2 := (h1.log (by linarith)).const_mul a
  have h3 := h2.exp
  convert h3 using 1
  ring

lemma contDiffOn_exp_mul_log_add_one (a : ℝ) :
    ContDiffOn ℝ ∞ (fun v => Real.exp (a * Real.log (v + 1))) (Ioi 0) :=
  (contDiffOn_const.mul ((contDiff_id.add contDiff_const).contDiffOn.log fun v hv => by
    simp only [mem_Ioi] at hv; simp only [id]; linarith)).exp

/-- **Inverting the ladder recursion**: for a function `k` smooth on `(0, ∞)` and vanishing on
`[R, ∞)` (`R ≥ 1`) there is a smooth compactly supported generator `G` with `u_l = k` on `v > 1/2`,
where `u_l = uRec r G l` is the recursion of the `K`-type `(l, r)` ladder images. -/
theorem exists_uRec_eq (r l : ℕ) {k : ℝ → ℂ} (hk : ContDiffOn ℝ ∞ k (Ioi 0)) {R : ℝ} (hR : 1 ≤ R)
    (hkR : ∀ v, R ≤ v → k v = 0) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ ∀ v, 1 / 2 < v → uRec r G l v = k v := by
  induction l generalizing k with
  | zero =>
    obtain ⟨G, hGs, hGc, hG⟩ := exists_generator r hk hR hkR
    exact ⟨G, hGs, hGc, fun v hv => by simpa [uRec] using hG v hv⟩
  | succ l ih =>
    set pw : ℝ → ℝ := fun v => Real.exp ((r : ℝ) * Real.log (v + 1)) with hpw
    set E : ℝ → ℝ := fun v => Real.exp (-(r : ℝ) * Real.log (v + 1)) with hE
    set m : ℝ → ℂ := fun t => ((pw t : ℝ) : ℂ) * k t with hm
    have hms : ContDiffOn ℝ ∞ m (Ioi 0) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_exp_mul_log_add_one _)).mul hk
    have hmR : ∀ v, R ≤ v → m v = 0 := fun v hv => by simp [hm, hkR v hv]
    obtain ⟨Q, hQs, hQR, hQd⟩ := exists_primitive_top hms (by linarith) hmR
    set k₁ : ℝ → ℂ := fun v => ((E v : ℝ) : ℂ) * Q v with hk₁
    have hk₁s : ContDiffOn ℝ ∞ k₁ (Ioi 0) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_exp_mul_log_add_one _)).mul hQs
    have hk₁R : ∀ v, R ≤ v → k₁ v = 0 := fun v hv => by simp [hk₁, hQR v hv]
    obtain ⟨G, hGs, hGc, hG⟩ := ih hk₁s hk₁R
    refine ⟨G, hGs, hGc, fun v hv => ?_⟩
    have hv0 : 0 < v := by linarith
    have hev : uRec r G l =ᶠ[𝓝 v] k₁ := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using hG w hw
    have hEd : HasDerivAt (fun v => ((E v : ℝ) : ℂ)) (((E v * (-(r : ℝ) / (v + 1)) : ℝ) : ℂ)) v :=
      (hasDerivAt_exp_mul_log_add_one (-(r : ℝ)) hv0).ofReal_comp
    have hk₁d : HasDerivAt k₁ (((E v * (-(r : ℝ) / (v + 1)) : ℝ) : ℂ) * Q v + ((E v : ℝ) : ℂ) * m v) v :=
      hEd.mul (hQd v hv0)
    have hEpw : E v * pw v = 1 := by
      simp only [hE, hpw, ← Real.exp_add]
      rw [show -(r : ℝ) * Real.log (v + 1) + r * Real.log (v + 1) = 0 by ring, Real.exp_zero]
    show deriv (uRec r G l) v + (((r : ℝ) / (v + 1) : ℝ) : ℂ) * uRec r G l v = k v
    rw [hev.deriv_eq, hk₁d.deriv, hG v hv]
    have hv1 : (v : ℝ) + 1 ≠ 0 := by linarith
    have hEpwC : ((E v : ℝ) : ℂ) * ((pw v : ℝ) : ℂ) = 1 := by exact_mod_cast hEpw
    simp only [hk₁, hm]
    push_cast
    have hv1C : (v : ℂ) + 1 ≠ 0 := by exact_mod_cast hv1
    field_simp
    linear_combination (↑(v : ℝ) + 1) * k v * hEpwC

/-- For `0 < w < cosh a` (`a > 0`), `arcosh w < a`. -/
lemma arcosh_lt_of_lt_cosh {a w : ℝ} (ha : 0 < a) (hw : 0 < w) (hwa : w < Real.cosh a) :
    Real.arcosh w < a := by
  rcases le_or_gt 1 w with h | h
  · exact ((Real.arcosh_lt_arcosh hw (Real.cosh_pos a)).2 hwa).trans_eq (Real.arcosh_cosh ha.le)
  · have hs : √(w ^ 2 - 1) = 0 := Real.sqrt_eq_zero'.2 (by nlinarith)
    have : Real.arcosh w = Real.log w := by simp [Real.arcosh, hs]
    rw [this]
    exact (Real.log_neg hw h).trans ha

/-- **Every test function of `(0, ∞)` is a `K`-type `(l, r)` ladder image of a radial
generator.**  For a smooth `H` with compact support in `(0, ∞)` there is a smooth compactly
supported `G` with `hLR r G l = H` on `(0, ∞)`. -/
theorem exists_hLR_eq (r l : ℕ) {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (hHsub : tsupport H ⊆ Ioi 0) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ ∀ ξ, 0 < ξ → hLR r G l ξ = H ξ := by
  -- bounds `a ≤ ξ ≤ b` of the support, `a > 0`
  have hb : ∃ a b, 0 < a ∧ a ≤ b ∧ ∀ ξ, ξ ∉ Icc a b → H ξ = 0 := by
    rcases (tsupport H).eq_empty_or_nonempty with he | hne
    · refine ⟨1, 1, one_pos, le_rfl, fun ξ _ => ?_⟩
      exact image_eq_zero_of_notMem_tsupport (by rw [he]; exact notMem_empty ξ)
    · obtain ⟨s₀, hs₀, s₁, -, hs, hS⟩ := exists_Icc_of_isCompact hHc.isCompact hne
      exact ⟨s₀, s₁, hHsub hs₀, hs, fun ξ hξ =>
        image_eq_zero_of_notMem_tsupport fun h => hξ (hS h)⟩
  obtain ⟨a, b, ha, hab, hH0⟩ := hb
  set k : ℝ → ℂ := fun v =>
    H (Real.arcosh v) * ((((Real.sinh (Real.arcosh v)) ^ (l + r))⁻¹ : ℝ) : ℂ) with hk
  have hk0 : ∀ w, 0 < w → w < Real.cosh a → k w = 0 := fun w hw hwa => by
    simp [hk, hH0 _ fun h => (arcosh_lt_of_lt_cosh ha hw hwa).not_ge h.1]
  have hks : ContDiffOn ℝ ∞ k (Ioi 0) := by
    intro v hv
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_ge v (Real.cosh a) with h | h
    · have hev : k =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        filter_upwards [Ioo_mem_nhds hv h] with w hw using hk0 w hw.1 hw.2
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hv1 : 1 < v := lt_of_lt_of_le (Real.one_lt_cosh.2 ha.ne') h
      have harc : ContDiffAt ℝ ∞ Real.arcosh v := Real.contDiffAt_arcosh hv1
      have hpos : 0 < Real.sinh (Real.arcosh v) := Real.sinh_pos_iff.2 (Real.arcosh_pos hv1)
      have h1 : ContDiffAt ℝ ∞ (fun v => H (Real.arcosh v)) v := hH.contDiffAt.comp v harc
      have h2 : ContDiffAt ℝ ∞ (fun v => ((((Real.sinh (Real.arcosh v)) ^ (l + r))⁻¹ : ℝ) : ℂ)) v :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp v
          (((Real.contDiff_sinh.contDiffAt.comp v harc).pow _).inv (pow_ne_zero _ hpos.ne'))
      exact h1.mul h2
  set R : ℝ := Real.cosh b + 1 with hR
  have hR1 : 1 ≤ R := by have := Real.cosh_pos b; linarith
  have hkR : ∀ v, R ≤ v → k v = 0 := by
    intro v hv
    have hvb : Real.cosh b < v := by linarith
    have hv0 : 0 < v := by linarith [Real.cosh_pos b]
    have harc : b < Real.arcosh v := by
      have := (Real.arcosh_lt_arcosh (Real.cosh_pos b) hv0).2 hvb
      rwa [Real.arcosh_cosh (ha.le.trans hab)] at this
    simp [hk, hH0 _ fun h => harc.not_ge h.2]
  obtain ⟨G, hGs, hGc, hG⟩ := exists_uRec_eq r l hks hR1 hkR
  refine ⟨G, hGs, hGc, fun ξ hξ => ?_⟩
  have hc1 : 1 / 2 < Real.cosh ξ := by linarith [Real.one_lt_cosh.2 hξ.ne']
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  rw [hLR_eq r hGs l ξ hξ, hG _ hc1, hk]
  simp only [Real.arcosh_cosh hξ.le]
  rw [← mul_assoc, mul_comm (((Real.sinh ξ ^ (l + r) : ℝ) : ℂ)), mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hs), Complex.ofReal_one, mul_one]

/-- **The `K`-type `(l, r)` Plancherel identity for every test function of the block**: for
natural `l, r` and every smooth `H` with compact support in `(0, ∞)` there is a radial generator `G`
with `π² ∫₀^∞ |H|² sinh ξ dξ = ¼ ∫₀^∞ ρ tanh(πρ) w_l(ρ) w_r(ρ) |Ĝ(ρ)|² dρ`. -/
theorem norm_sq_eq_of_isTest (r l : ℕ) {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H)
    (hHc : HasCompactSupport H) (hHsub : tsupport H ⊆ Ioi 0) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ), ‖H ξ‖ ^ 2 * Real.sinh ξ =
        (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ *
          ‖sphTransformH G ρ‖ ^ 2 := by
  obtain ⟨G, hGs, hGc, hG⟩ := exists_hLR_eq r l hH hHc hHsub
  refine ⟨G, hGs, hGc, ?_⟩
  rw [← norm_sq_ktype_lr hGs hGc r l]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => by rw [hG ξ hξ]

/-- Non-vacuity: the hypotheses of `norm_sq_eq_of_isTest` hold for the zero function, and the
generator exists for every block. -/
example (r l : ℕ) : ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
    Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ), ‖(0 : ℂ)‖ ^ 2 * Real.sinh ξ =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ *
        ‖sphTransformH G ρ‖ ^ 2 :=
  norm_sq_eq_of_isTest r l (H := fun _ => 0) contDiff_const HasCompactSupport.zero
    (by simp [tsupport])

end Lightlike.Lorentz.SL2RPlancherel

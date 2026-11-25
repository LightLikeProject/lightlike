import Lightlike.Canonical.BlackHoleEntropyCounting.Upper

/-!
# Puncture counting and the Meissner value `γ_M ≈ 0.2375` (row G2-016, milestone CA6)

The counting condition used here is
`∑ₙ 2 · exp(-π γ √((n+1)(n+3))) = 1`  (`n = 2j - 1`, spin `j = (n+1)/2`, area label
`√((n+1)(n+3)) = 2√(j(j+1))`), i.e. `countSum (fun _ => 2) γ = 1`.

**Caveat on the source.** The weight `2` (one factor for each of the two orientations of a
puncture) is fixed here by the numerical outcome: it reproduces `γ_M = 0.2375` of Meissner 2004
(`meissner-2004`, cited in the task) to four digits, and its `j = 1/2`-only truncation gives
`ln 2 / (π √3) ≈ 0.127`. The equation of the paper itself was *not* checked against the source text,
so no equation number is claimed.

Main results:
* `exists_gammaM`: a root `γ_M` of the counting condition exists in `[0.2374, 0.2376]`;
  it is unique (`gammaM_unique`);
* `gammaM := Classical.choose exists_gammaM`; `entropy γ A = (γ_M/γ) · A/4`;
* `halfSpinGamma = ln 2/(π √3) ∈ (0.127, 0.1275)` is the root when only `j = 1/2` punctures are
  counted, and `halfSpinGamma < gammaM` (`counting_asymptotics`).
-/

open Real

namespace Lightlike.Canonical.BlackHoleEntropyCounting

theorem two_nonneg_w : ∀ n : ℕ, 0 ≤ (fun _ : ℕ => (2 : ℝ)) n := fun _ => by norm_num

theorem two_le_w : ∀ n : ℕ, (fun _ : ℕ => (2 : ℝ)) n ≤ (n : ℝ) + 2 := fun n => by
  have := Nat.cast_nonneg (α := ℝ) n
  show (2 : ℝ) ≤ n + 2
  linarith

/-- There is a root of the counting condition in `[0.2374, 0.2376]`. -/
theorem exists_gammaM :
    ∃ γ ∈ Set.Icc (2374 / 10000 : ℝ) (2376 / 10000), countSum (fun _ => (2 : ℝ)) γ = 1 :=
  exists_root_of_lt_gt two_nonneg_w two_le_w (by norm_num) (by norm_num) countSum_two_gt
    countSum_two_lt

/-- The root `γ_M` of `∑ₙ 2 exp(-π γ √((n+1)(n+3))) = 1` (Meissner's value `≈ 0.2375`). -/
noncomputable def gammaM : ℝ := Classical.choose exists_gammaM

theorem gammaM_mem : gammaM ∈ Set.Icc (2374 / 10000 : ℝ) (2376 / 10000) :=
  (Classical.choose_spec exists_gammaM).1

theorem countSum_gammaM : countSum (fun _ => (2 : ℝ)) gammaM = 1 :=
  (Classical.choose_spec exists_gammaM).2

theorem gammaM_pos : 0 < gammaM := lt_of_lt_of_le (by norm_num) gammaM_mem.1

/-- Uniqueness of the root among positive Barbero–Immirzi parameters. -/
theorem gammaM_unique {γ : ℝ} (hγ : 0 < γ) (h : countSum (fun _ => (2 : ℝ)) γ = 1) :
    γ = gammaM :=
  root_unique two_nonneg_w two_le_w (by norm_num) hγ gammaM_pos h countSum_gammaM

/-- Black-hole entropy `S = (γ_M/γ) · A/4` (area `A` in Planck units) from the counting. -/
noncomputable def entropy (γ A : ℝ) : ℝ := gammaM / γ * (A / 4)

theorem entropy_eq (γ A : ℝ) : entropy γ A = gammaM / γ * (A / 4) := rfl

/-- `S / (A/4) = γ_M / γ`. -/
theorem entropy_div (γ A : ℝ) (hA : A ≠ 0) : entropy γ A / (A / 4) = gammaM / γ := by
  unfold entropy
  field_simp

/-- The `j = 1/2`-only counting sum: the `n = 0` term of `countSum (fun _ => 2)`. -/
noncomputable def halfSum (γ : ℝ) : ℝ := 2 * Real.exp (-(π * γ * areaLabel 0))

/-- The root of `2 exp(-π γ √3) = 1`: `γ = ln 2/(π √3)`. -/
noncomputable def halfSpinGamma : ℝ := Real.log 2 / (π * √3)

theorem areaLabel_zero : areaLabel 0 = √3 := by
  unfold areaLabel; norm_num

theorem halfSum_eq_one_iff (γ : ℝ) : halfSum γ = 1 ↔ γ = halfSpinGamma := by
  have hA := areaLabel_zero
  have hs : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  have hp := Real.pi_pos
  unfold halfSum halfSpinGamma
  rw [hA]
  constructor
  · intro h
    have h1 : Real.exp (-(π * γ * √3)) = 1 / 2 := by linarith
    have h2 := congrArg Real.log h1
    rw [Real.log_exp, one_div, Real.log_inv] at h2
    rw [eq_div_iff (by positivity)]
    linarith
  · intro h
    subst h
    have : π * (Real.log 2 / (π * √3)) * √3 = Real.log 2 := by field_simp
    rw [this, Real.exp_neg, Real.exp_log two_pos]
    norm_num

theorem halfSpinGamma_bounds : (127 / 1000 : ℝ) < halfSpinGamma ∧ halfSpinGamma < 1275 / 10000 := by
  have hs1 : (1732 / 1000 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : √3 < (17321 / 10000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  norm_num at hp1 hp2 hl1 hl2
  have hpos : 0 < π * √3 := by positivity
  unfold halfSpinGamma
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith
  · rw [div_lt_iff₀ hpos]
    nlinarith

/-- **Counting asymptotics (CA6).** The counting condition `∑ₙ 2 exp(-πγ√((n+1)(n+3))) = 1` has the
unique positive root `γ_M ∈ [0.2374, 0.2376]` (so `γ_M = 0.2375` to four digits), giving
`S = (γ_M/γ) A/4`; counting only `j = 1/2` punctures instead gives `ln 2/(π√3) ∈ (0.127, 0.1275)`,
which differs from `γ_M`. -/
theorem counting_asymptotics :
    (2374 / 10000 : ℝ) ≤ gammaM ∧ gammaM ≤ 2376 / 10000 ∧
    countSum (fun _ => (2 : ℝ)) gammaM = 1 ∧
    (∀ γ : ℝ, 0 < γ → countSum (fun _ => (2 : ℝ)) γ = 1 → γ = gammaM) ∧
    (∀ γ A : ℝ, entropy γ A = gammaM / γ * (A / 4)) ∧
    halfSum halfSpinGamma = 1 ∧
    (127 / 1000 : ℝ) < halfSpinGamma ∧ halfSpinGamma < 1275 / 10000 ∧
    halfSpinGamma ≠ gammaM := by
  refine ⟨gammaM_mem.1, gammaM_mem.2, countSum_gammaM, fun γ hγ h => gammaM_unique hγ h,
    entropy_eq, (halfSum_eq_one_iff _).2 rfl, halfSpinGamma_bounds.1, halfSpinGamma_bounds.2, ?_⟩
  have h1 := halfSpinGamma_bounds.2
  have h2 := gammaM_mem.1
  intro h
  rw [h] at h1
  linarith

end Lightlike.Canonical.BlackHoleEntropyCounting

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.areaLabel_zero := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.areaLabel_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.countSum_gammaM := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.countSum_gammaM
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.counting_asymptotics := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.counting_asymptotics
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.entropy := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.entropy
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.entropy_div := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.entropy_div
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.entropy_eq := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.entropy_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.exists_gammaM := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.exists_gammaM
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.gammaM := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.gammaM
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.gammaM_mem := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.gammaM_mem
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.gammaM_pos := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.gammaM_pos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.gammaM_unique := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.gammaM_unique
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.halfSpinGamma := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.halfSpinGamma
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.halfSpinGamma_bounds := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.halfSpinGamma_bounds
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.halfSum := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.halfSum
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.halfSum_eq_one_iff := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.halfSum_eq_one_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.two_le_w := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.two_le_w
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.two_nonneg_w := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.two_nonneg_w

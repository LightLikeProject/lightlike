import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.LadderOppositeOrth
import Lightlike.Lorentz.SL2RPlancherel.LadderSurjective

/-!
# The opposite-sign ladder images: every test function orthogonal to the discrete directions

For natural `l, s`, a smooth `H` with compact support in `(0, ∞)` that is orthogonal in
`L²((0, ∞), sinh ξ dξ)` to the discrete directions `φ_i = (cosh ξ - 1)^{i+s} / sinh^{l+s} ξ`
(`l - s ≤ i < l`, `phiN`) is an opposite-sign ladder image `hLRN s G l` of a smooth compactly
supported radial generator `G` (`exists_hLRN_eq`).  In `v = cosh ξ`: the `l`-fold primitive `P`
from `+∞` of `k = H(arcosh v) (v - 1)^s / sinh^{l+s}(arcosh v)` has `P^{(j)}(1) = 0` for
`j < min(l, s)` (the moments, `integral_pow_mul_iteratedDeriv`), it is a polynomial near `v = 1`
(`eq_taylor_of_iteratedDeriv_eq_zero`), hence `P = (v - 1)^s Q` there, and `G^{(s)} = P / (v - 1)^s`
defines the generator.  Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The change of variables `v = cosh ξ`** for a continuous compactly supported `g` vanishing on
`[B, ∞)`, `B ≥ 1`: `∫₀^∞ sinh ξ · g(cosh ξ) dξ = ∫₁^B g`. -/
theorem integral_Ioi_sinh_smul_comp_cosh {g : ℝ → ℂ} (hg : Continuous g) (hgcs : HasCompactSupport g)
    {B : ℝ} (hB1 : 1 ≤ B) (hgB : ∀ v, B ≤ v → g v = 0) :
    ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ • g (Real.cosh ξ) = ∫ v in (1 : ℝ)..B, g v := by
  have hcomp : Continuous (fun ξ => Real.sinh ξ • g (Real.cosh ξ)) :=
    Real.continuous_sinh.smul (hg.comp Real.continuous_cosh)
  have hz : ∀ ξ : ℝ, 2 * B ≤ ξ → Real.sinh ξ • g (Real.cosh ξ) = 0 := by
    intro ξ hξ
    have := cosh_ge_half ξ
    rw [hgB _ (by linarith), smul_zero]
  have hmain := integral_deriv_smul_comp_Ioi (f := Real.cosh) (f' := Real.sinh) (g := g) (a := 0)
    Real.continuous_cosh.continuousOn tendsto_cosh_atTop
    (fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt) hg.continuousOn
    (hg.integrable_of_hasCompactSupport hgcs).integrableOn
    (integrableOn_Ici_of_zero_complex hcomp (by linarith) hz)
  simp only [Function.comp_def] at hmain
  rw [hmain, Real.cosh_zero]
  have hzero : ∀ v ∈ Ioi (1 : ℝ) \ Ioc 1 B, g v = 0 := by
    intro v hv
    have : B < v := by
      by_contra h
      exact hv.2 ⟨hv.1, not_lt.mp h⟩
    exact hgB v this.le
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hzero,
    ← intervalIntegral.integral_of_le hB1]

/-- **Every test function orthogonal to the discrete directions is an opposite-sign ladder image**:
for a smooth `H` with compact support in `(0, ∞)` with `⟨H, φ_i⟩ = 0` for `l - s ≤ i < l` there is
a smooth compactly supported `G` with `hLRN s G l = H` on `(0, ∞)`. -/
theorem exists_hLRN_eq (s l : ℕ) {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (hHsub : tsupport H ⊆ Ioi 0)
    (hmom : ∀ i : ℕ, l ≤ i + s → i < l →
      ∫ ξ in Ioi (0 : ℝ), H ξ * ((phiN s l i ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) = 0) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ ∀ ξ, 0 < ξ → hLRN s G l ξ = H ξ := by
  -- bounds `a ≤ ξ ≤ b` of the support, `a > 0`
  have hb : ∃ a b, 0 < a ∧ a ≤ b ∧ ∀ ξ, ξ ∉ Icc a b → H ξ = 0 := by
    rcases (tsupport H).eq_empty_or_nonempty with he | hne
    · refine ⟨1, 1, one_pos, le_rfl, fun ξ _ => ?_⟩
      exact image_eq_zero_of_notMem_tsupport (by rw [he]; exact notMem_empty ξ)
    · obtain ⟨s₀, hs₀, s₁, -, hs, hS⟩ := exists_Icc_of_isCompact hHc.isCompact hne
      exact ⟨s₀, s₁, hHsub hs₀, hs, fun ξ hξ =>
        image_eq_zero_of_notMem_tsupport fun h => hξ (hS h)⟩
  obtain ⟨a, b, ha, hab, hH0⟩ := hb
  have hca : 1 < Real.cosh a := Real.one_lt_cosh.2 ha.ne'
  -- the target in `v = cosh ξ`
  set k : ℝ → ℂ := fun v => if 1 < v then H (Real.arcosh v) *
      ((((v - 1) ^ s / Real.sinh (Real.arcosh v) ^ (l + s)) : ℝ) : ℂ) else 0 with hk
  have hk0 : ∀ v, v < Real.cosh a → k v = 0 := by
    intro v hv
    simp only [hk]
    split_ifs with h1
    · rw [hH0 _ fun h => (arcosh_lt_of_lt_cosh ha (by linarith) hv).not_ge h.1, zero_mul]
    · rfl
  have hks : ContDiff ℝ ∞ k := by
    rw [contDiff_iff_contDiffAt]
    intro v
    rcases lt_or_ge v (Real.cosh a) with h | h
    · have hev : k =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds h] with w hw using hk0 w hw
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hv1 : 1 < v := lt_of_lt_of_le hca h
      have harc : ContDiffAt ℝ ∞ Real.arcosh v := Real.contDiffAt_arcosh hv1
      have hpos : 0 < Real.sinh (Real.arcosh v) := Real.sinh_pos_iff.2 (Real.arcosh_pos hv1)
      have hev : k =ᶠ[𝓝 v] fun v => H (Real.arcosh v) *
          ((((v - 1) ^ s / Real.sinh (Real.arcosh v) ^ (l + s)) : ℝ) : ℂ) := by
        filter_upwards [Ioi_mem_nhds hv1] with w hw
        simp only [hk, (mem_Ioi.1 hw), ↓reduceIte]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have h1 : ContDiffAt ℝ ∞ (fun v => H (Real.arcosh v)) v := hH.contDiffAt.comp v harc
      have h2 : ContDiffAt ℝ ∞
          (fun v => ((((v - 1) ^ s / Real.sinh (Real.arcosh v) ^ (l + s)) : ℝ) : ℂ)) v :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp v
          ((((contDiff_id.sub contDiff_const).pow s).contDiffAt).div
            ((Real.contDiff_sinh.contDiffAt.comp v harc).pow _) (pow_ne_zero _ hpos.ne'))
      exact h1.mul h2
  set R : ℝ := Real.cosh b + 1 with hR
  have hR1 : 1 < R := by have := Real.one_le_cosh b; linarith
  have hkR : ∀ v, R ≤ v → k v = 0 := by
    intro v hv
    have hvb : Real.cosh b < v := by linarith
    have hv1 : 1 < v := by linarith [Real.one_le_cosh b]
    have harc : b < Real.arcosh v := by
      have := (Real.arcosh_lt_arcosh (Real.cosh_pos b) (by linarith)).2 hvb
      rwa [Real.arcosh_cosh (ha.le.trans hab)] at this
    simp only [hk, hv1, ↓reduceIte]
    rw [hH0 _ fun h => harc.not_ge h.2, zero_mul]
  -- the `l`-fold primitive from `+∞`, and a global version of it
  obtain ⟨P, hPs, hPR, hPl⟩ := exists_iteratedDeriv_eq l hks.contDiffOn (by linarith) hkR
  set χ : ℝ → ℂ := fun v => ((cutQuarter v : ℝ) : ℂ) with hχ
  have hχs : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp contDiff_cutQuarter
  have hχsub : tsupport χ ⊆ Ioi 0 := by
    refine (closure_mono fun v hv => ?_).trans tsupport_cutQuarter
    intro h0; apply hv; simp [hχ, h0]
  set Pg : ℝ → ℂ := fun v => χ v * P v with hPg
  have hPgs : ContDiff ℝ ∞ Pg := contDiff_mul_of_tsupport_subset isOpen_Ioi hχs hχsub hPs
  have hPgP : ∀ v, 1 / 2 < v → Pg =ᶠ[𝓝 v] P := fun v hv => by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    simp [hPg, hχ, cutQuarter_eq_one (le_of_lt hw)]
  have hPgder : ∀ j v, 1 / 2 < v → iteratedDeriv j Pg v = iteratedDeriv j P v := fun j v hv =>
    (hPgP v hv).iteratedDeriv_eq j
  have hPgB : ∀ j, iteratedDeriv j Pg (R + 1) = 0 := by
    intro j
    have hev : Pg =ᶠ[𝓝 (R + 1)] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds (show R < R + 1 by linarith)] with w hw
      simp [hPg, hPR w hw.le]
    rw [hev.iteratedDeriv_eq]
    simp
  -- the moments give `Pg^{(j)}(1) = 0` for `j < min(l, s)`
  have hmom' : ∀ i : ℕ, l ≤ i + s → i < l → iteratedDeriv (l - 1 - i) Pg 1 = 0 := by
    intro i hli hil
    set gi : ℝ → ℂ := fun v => (((v - 1) ^ i : ℝ) : ℂ) * k v with hgi
    have hgic : Continuous gi :=
      (Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).pow i)).mul hks.continuous
    have hgics : HasCompactSupport gi := by
      refine HasCompactSupport.intro (isCompact_Icc (a := 1) (b := R)) fun v hv => ?_
      rcases not_and_or.mp hv with h | h
      · simp [hgi, hk0 v (by linarith [not_le.mp h])]
      · simp [hgi, hkR v (not_le.mp h).le]
    have hcv := integral_Ioi_sinh_smul_comp_cosh hgic hgics (by linarith : (1 : ℝ) ≤ R + 1)
      (fun v hv => by simp [hgi, hkR v (by linarith)])
    have hl : ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ • gi (Real.cosh ξ) =
        ∫ ξ in Ioi (0 : ℝ), H ξ * ((phiN s l i ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
      have hc1 : 1 < Real.cosh ξ := Real.one_lt_cosh.2 (ne_of_gt hξ)
      simp only [hgi, hk, hc1, ↓reduceIte, Real.arcosh_cosh (le_of_lt hξ), phiN, Complex.real_smul]
      push_cast
      ring
    have hr : ∫ v in (1 : ℝ)..(R + 1), gi v =
        ∫ v in (1 : ℝ)..(R + 1), (((v - 1) ^ i : ℝ) : ℂ) * iteratedDeriv l Pg v := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le (by linarith)] at hv
      simp only [hgi]
      rw [hPgder l v (by linarith [hv.1]), hPl v (mem_Ioi.2 (by linarith [hv.1]))]
    have h := integral_pow_mul_iteratedDeriv hPgs hPgB i l hil
    rw [← hr, ← hcv, hl, hmom i hli hil] at h
    have hne : ((-1 : ℂ) ^ (i + 1) * (i.factorial : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast i.factorial_ne_zero)
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  have hD1 : ∀ j, j < l → j < s → iteratedDeriv j Pg 1 = 0 := by
    intro j hjl hjs
    have := hmom' (l - 1 - j) (by omega) (by omega)
    rwa [show l - 1 - (l - 1 - j) = j by omega] at this
  -- near `v = 1`, `Pg = (v - 1)^s Q` with a polynomial `Q`
  have hI1 : (1 : ℝ) ∈ Ioo (1 / 2) (Real.cosh a) := ⟨by norm_num, hca⟩
  have hPgI : ∀ x ∈ Ioo (1 / 2 : ℝ) (Real.cosh a), iteratedDeriv l Pg x = 0 := fun x hx => by
    rw [hPgder l x hx.1, hPl x (mem_Ioi.2 (by linarith [hx.1]))]
    exact hk0 x hx.2
  have htay := eq_taylor_of_iteratedDeriv_eq_zero hI1 l Pg hPgs hPgI
  set Q : ℝ → ℂ := fun x => ∑ j ∈ Finset.range (l - s),
    iteratedDeriv (s + j) Pg 1 / ((s + j).factorial : ℂ) * ((x : ℂ) - 1) ^ j with hQ
  have hPQ : ∀ x ∈ Ioo (1 / 2 : ℝ) (Real.cosh a), Pg x = (((x - 1) ^ s : ℝ) : ℂ) * Q x := by
    intro x hx
    rw [htay x hx]
    simp only [hQ, Complex.ofReal_one]
    rcases le_or_gt l s with hls | hls
    · rw [show l - s = 0 by omega, Finset.range_zero, Finset.sum_empty, mul_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      rw [hD1 j hj' (by omega), zero_div, zero_mul]
    · have ht : l = s + (l - s) := by omega
      conv_lhs => rw [ht, Finset.sum_range_add]
      have h0 : ∑ j ∈ Finset.range s, iteratedDeriv j Pg 1 / (j.factorial : ℂ) * ((x : ℂ) - 1) ^ j = 0 :=
        Finset.sum_eq_zero fun j hj => by
          have hj' := Finset.mem_range.1 hj
          rw [hD1 j (by omega) hj', zero_div, zero_mul]
      rw [h0, zero_add, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
  -- the generator's `s`-th derivative
  set g : ℝ → ℂ := fun v => if v ≤ 1 then Q v else Pg v * ((((v - 1) ^ s)⁻¹ : ℝ) : ℂ) with hg
  have hQs : ContDiff ℝ ∞ Q := by
    simp only [hQ]
    exact ContDiff.sum fun j _ => contDiff_const.mul
      ((Complex.ofRealCLM.contDiff.sub contDiff_const).pow j)
  have hquot : ∀ v, 1 < v → ContDiffAt ℝ ∞ (fun v => Pg v * ((((v - 1) ^ s)⁻¹ : ℝ) : ℂ)) v := by
    intro v hv
    have hne : (v - 1) ^ s ≠ 0 := pow_ne_zero _ (by linarith : v - 1 ≠ 0)
    exact hPgs.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp v
      (((contDiff_id.sub contDiff_const).pow s).contDiffAt.inv hne))
  have hgQ : ∀ w ∈ Ioo (1 / 2 : ℝ) (Real.cosh a), g w = Q w := by
    intro w hw
    simp only [hg]
    split_ifs with h1
    · rfl
    · have hne : (((w - 1) ^ s : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast pow_ne_zero _ (by linarith [not_le.mp h1] : w - 1 ≠ 0)
      rw [hPQ w hw]
      have hne' : ((w : ℂ) - 1) ^ s ≠ 0 := by exact_mod_cast hne
      push_cast
      field_simp
  have hgs : ContDiffOn ℝ ∞ g (Ioi 0) := by
    intro v hv
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_ge v 1 with h | h
    · have hev : g =ᶠ[𝓝 v] Q := by
        filter_upwards [Iio_mem_nhds h] with w hw
        simp only [hg, (le_of_lt (mem_Iio.1 hw)), ↓reduceIte]
      exact hQs.contDiffAt.congr_of_eventuallyEq hev
    · rcases lt_or_ge v (Real.cosh a) with h' | h'
      · have hev : g =ᶠ[𝓝 v] Q := by
          filter_upwards [Ioo_mem_nhds (show (1 / 2 : ℝ) < v by linarith) h'] with w hw
          exact hgQ w hw
        exact hQs.contDiffAt.congr_of_eventuallyEq hev
      · have hv1 : 1 < v := lt_of_lt_of_le hca h'
        have hev : g =ᶠ[𝓝 v] fun v => Pg v * ((((v - 1) ^ s)⁻¹ : ℝ) : ℂ) := by
          filter_upwards [Ioi_mem_nhds hv1] with w hw
          simp only [hg, (not_le.mpr (mem_Ioi.1 hw)), ↓reduceIte]
        exact (hquot v hv1).congr_of_eventuallyEq hev
  have hgR : ∀ v, R ≤ v → g v = 0 := by
    intro v hv
    simp only [hg, (not_le.mpr (by linarith : 1 < v)), ↓reduceIte, hPg, hPR v hv, mul_zero, zero_mul]
  obtain ⟨G, hGs, hGc, hG⟩ := exists_generator s hgs hR1.le hgR
  refine ⟨G, hGs, hGc, fun ξ hξ => ?_⟩
  -- `oppGen s G = Pg` on `v > 1/2`
  have hop : ∀ v, 1 / 2 < v → oppGen s G v = Pg v := by
    intro v hv
    simp only [oppGen]
    rw [hG v hv]
    simp only [hg]
    split_ifs with h1
    · exact (hPQ v ⟨hv, lt_of_le_of_lt h1 hca⟩).symm
    · have hne : (((v - 1) ^ s : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast pow_ne_zero _ (by linarith [not_le.mp h1] : v - 1 ≠ 0)
      have hne' : ((v : ℂ) - 1) ^ s ≠ 0 := by exact_mod_cast hne
      push_cast
      field_simp
  have hc1 : 1 < Real.cosh ξ := Real.one_lt_cosh.2 hξ.ne'
  have hev : oppGen s G =ᶠ[𝓝 (Real.cosh ξ)] Pg := by
    filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < Real.cosh ξ by linarith)] with w hw
    exact hop w hw
  rw [hLRN_eq s hGs l ξ hξ, uRecN_eq s hGs l _ hc1, hev.iteratedDeriv_eq,
    hPgder l _ (by linarith), hPl _ (mem_Ioi.2 (by linarith))]
  simp only [hk, hc1, ↓reduceIte, Real.arcosh_cosh hξ.le]
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hc0 : Real.cosh ξ - 1 ≠ 0 := (sub_pos.2 hc1).ne'
  have hreal : Real.sinh ξ ^ (l + s) * (Real.cosh ξ - 1) ^ (-(s : ℤ)) *
      ((Real.cosh ξ - 1) ^ s / Real.sinh ξ ^ (l + s)) = 1 := by
    rw [zpow_neg, zpow_natCast]
    field_simp
  calc _ = ((Real.sinh ξ ^ (l + s) * (Real.cosh ξ - 1) ^ (-(s : ℤ)) *
        ((Real.cosh ξ - 1) ^ s / Real.sinh ξ ^ (l + s)) : ℝ) : ℂ) * H ξ := by push_cast; ring
    _ = H ξ := by rw [hreal]; simp

/-- Non-vacuity: the zero function satisfies the hypotheses of `exists_hLRN_eq`. -/
example (s l : ℕ) : ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
    ∀ ξ, 0 < ξ → hLRN s G l ξ = (fun _ => (0 : ℂ)) ξ :=
  exists_hLRN_eq s l contDiff_const HasCompactSupport.zero (by simp [tsupport])
    fun _ _ _ => by simp

end Lightlike.Lorentz.SL2RPlancherel

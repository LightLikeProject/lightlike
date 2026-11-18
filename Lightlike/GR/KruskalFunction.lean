import Mathlib

/-!
# The Kruskal radius function

`F(r) = (r/2M - 1) e^{r/2M}` is strictly increasing on `r > 0` with values exactly `(-1, ∞)`
(`kF_strictMonoOn`, `exists_kF_eq`). Its inverse `kG : s ↦ r` is smooth on `s > -1`
(`contDiffAt_kG`), with `kG' = 1/F'(kG) = 4M² e^{-r/2M} / r`. This is the radius `r(T, X)` of the Kruskal
chart through `X² - T² = F(r)` (Lambert-W-like; Mathlib has no `W`).

Gap row G1-020 (Kruskal extension), supporting file. Source comparison with Kruskal (1960) and
Carroll, ch. 5, pending.
-/

open Real Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- `F(r) = (r/2M - 1) e^{r/2M}`. -/
def kF (r : ℝ) : ℝ := (r / (2 * M) - 1) * exp (r / (2 * M))

/-- Its derivative `r e^{r/2M} / (4M²)`. -/
lemma hasDerivAt_kF (hM : M ≠ 0) (r : ℝ) :
    HasDerivAt (kF M) (r / (4 * M ^ 2) * exp (r / (2 * M))) r := by
  have h1 : HasDerivAt (fun r : ℝ => r / (2 * M)) (1 / (2 * M)) r :=
    ((hasDerivAt_id' r).div_const (2 * M))
  have h2 := (h1.sub_const 1).mul h1.exp
  refine h2.congr_deriv ?_
  field_simp; ring

lemma contDiff_kF (hM : M ≠ 0) : ContDiff ℝ ∞ (kF M) := by
  unfold kF; fun_prop

lemma kF_zero (hM : M ≠ 0) : kF M 0 = -1 := by simp [kF]

lemma kF_strictMonoOn (hM : 0 < M) : StrictMonoOn (kF M) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (contDiff_kF M hM.ne').continuous.continuousOn
    fun r hr => ?_
  rw [interior_Ici] at hr
  rw [(hasDerivAt_kF M hM.ne' r).deriv]
  have : 0 < r := hr
  positivity

lemma exists_kF_eq (hM : 0 < M) {s : ℝ} (hs : -1 < s) : ∃ r, 0 < r ∧ kF M r = s := by
  set r0 := 2 * M * (max s 0 + 2) with hr0
  have hr0pos : 0 < r0 := by positivity
  have hF0 : kF M r0 > s := by
    have h1 : r0 / (2 * M) = max s 0 + 2 := by rw [hr0]; field_simp
    have h2 : 1 ≤ exp (r0 / (2 * M)) := one_le_exp (by positivity)
    unfold kF
    rw [h1] at h2 ⊢
    have : 0 ≤ max s 0 := le_max_right _ _
    have : s ≤ max s 0 := le_max_left _ _
    nlinarith
  have hc : ContinuousOn (kF M) (Icc 0 r0) := (contDiff_kF M hM.ne').continuous.continuousOn
  have := intermediate_value_Ioo hr0pos.le hc
  obtain ⟨r, hr, hrs⟩ := this ⟨by rw [kF_zero M hM.ne']; exact hs, hF0⟩
  exact ⟨r, hr.1, hrs⟩

/-- The inverse of `F` on `(-1, ∞)`: the radius `r` with `F(r) = s`. -/
def kG (s : ℝ) : ℝ := Function.invFunOn (kF M) (Ioi 0) s

lemma kG_pos (hM : 0 < M) {s : ℝ} (hs : -1 < s) : 0 < kG M s := by
  obtain ⟨r, hr, hrs⟩ := exists_kF_eq M hM hs
  exact Function.invFunOn_mem (f := kF M) (s := Ioi 0) (b := s) ⟨r, hr, hrs⟩

lemma kF_kG (hM : 0 < M) {s : ℝ} (hs : -1 < s) : kF M (kG M s) = s := by
  obtain ⟨r, hr, hrs⟩ := exists_kF_eq M hM hs
  exact Function.invFunOn_eq (f := kF M) (s := Ioi 0) (b := s) ⟨r, hr, hrs⟩

lemma kG_kF (hM : 0 < M) {r : ℝ} (hr : 0 < r) : kG M (kF M r) = r := by
  have hs : -1 < kF M r := by
    rw [← kF_zero M hM.ne']; exact kF_strictMonoOn M hM (mem_Ici.2 le_rfl) (mem_Ici.2 hr.le) hr
  have hpos := kG_pos M hM hs
  have heq := kF_kG M hM hs
  exact (kF_strictMonoOn M hM).injOn (le_of_lt hpos) (le_of_lt hr) heq

/-- The derivative of `F` is nonzero for `r > 0`. -/
lemma kF_deriv_ne (hM : 0 < M) {r : ℝ} (hr : 0 < r) : r / (4 * M ^ 2) * exp (r / (2 * M)) ≠ 0 := by
  positivity

/-- **`kG` is smooth on `s > -1`**, by the inverse function theorem. -/
theorem contDiffAt_kG (hM : 0 < M) {s : ℝ} (hs : -1 < s) : ContDiffAt ℝ ∞ (kG M) s := by
  set r := kG M s with hrdef
  have hr : 0 < r := kG_pos M hM hs
  have hFr : kF M r = s := kF_kG M hM hs
  set c := r / (4 * M ^ 2) * exp (r / (2 * M)) with hc
  have hc0 : c ≠ 0 := kF_deriv_ne M hM hr
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc0)
  have hd : HasFDerivAt (kF M) (e : ℝ →L[ℝ] ℝ) r := by
    have := (hasDerivAt_kF M hM.ne' r).hasFDerivAt
    convert this using 1
    ext x; simp [e, hc]
  have hcd : ContDiffAt ℝ ∞ (kF M) r := (contDiff_kF M hM.ne').contDiffAt
  have hloc := hcd.to_localInverse hd (by simp)
  rw [hFr] at hloc
  refine hloc.congr_of_eventuallyEq ?_
  have hst := (hcd.hasStrictFDerivAt' hd (by simp))
  have hright : ∀ᶠ y in 𝓝 (kF M r), kF M (hcd.localInverse hd (by simp) y) = y :=
    hst.eventually_right_inverse
  have hcont : ContinuousAt (hcd.localInverse hd (by simp)) (kF M r) :=
    hst.localInverse_continuousAt
  have hLs : hcd.localInverse hd (by simp) (kF M r) = r := hcd.localInverse_apply_image hd (by simp)
  rw [hFr] at hright hcont hLs
  have hpos : ∀ᶠ y in 𝓝 s, 0 < hcd.localInverse hd (by simp) y :=
    hcont.eventually (lt_mem_nhds (by rw [hLs]; exact hr))
  have hgt : ∀ᶠ y in 𝓝 s, -1 < y := lt_mem_nhds hs
  filter_upwards [hright, hpos, hgt] with y h1 h2 h3
  have hk := kF_kG M hM h3
  exact (kF_strictMonoOn M hM).injOn (mem_Ici.2 (kG_pos M hM h3).le) (mem_Ici.2 h2.le)
    (hk.trans h1.symm)

end Lightlike

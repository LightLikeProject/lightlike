import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.DiscretePlancherelTotal
import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileBdry
import Lightlike.Lorentz.SL2RPlancherel.KTypeOppositeL2
import Lightlike.Lorentz.SL2RPlancherel.KKL2
import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileReal

/-!
# The discrete directions of the opposite-sign blocks are spanned by the radial profiles of `D_{2ν}⁻`

For `s, l ∈ ℕ` and `1 ≤ ν ≤ min(l, s)` the radial profile `ψ_ν = ⟨e_{s-ν}, D_{2ν}(a(ξ)) e_{l-ν}⟩` of the
antiholomorphic series `D_{2ν}⁻` of `K`-type `(l, -s)` times `√(sinh ξ)` is a vector `psiVec s l ν` of
`L²(0, ∞)`. It is orthogonal to every ladder image `blockEN s l G` (`inner_psiVec_blockEN`), hence lies in the discrete
part `discSpan s l` (`psiVec_mem_discSpan`); the `min(l, s)` vectors are mutually orthogonal and nonzero, so they span
`discSpan s l` (`span_psiVec_eq_discSpan`).
-/

open MeasureTheory Set Filter Topology Real Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped ContDiff InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The indices of the antiholomorphic series `D_{2ν}⁻` occurring in the block `(l, -s)`: `ν = i + 1`,
`1 ≤ ν ≤ min(l, s)`. -/
abbrev OppIdx (s l : ℕ) := Fin (min l s)

/-- The number `ν = i + 1` of the antiholomorphic series `D_{2ν}⁻`. -/
def nu {s l : ℕ} (i : OppIdx s l) : ℕ := i.1 + 1

lemma nu_pos {s l : ℕ} (i : OppIdx s l) : 1 ≤ nu i := by simp [nu]
lemma nu_le_l {s l : ℕ} (i : OppIdx s l) : nu i ≤ l := by have := i.2; have := min_le_left l s; simp only [nu]; omega
lemma nu_le_s {s l : ℕ} (i : OppIdx s l) : nu i ≤ s := by have := i.2; have := min_le_right l s; simp only [nu]; omega

/-- **The radial profile of `D_{2ν}⁻`** in the block `(l, -s)`: `ξ ↦ ⟨e_{s-ν}, D_{2ν}(a(ξ)) e_{l-ν}⟩`. -/
def psiFun (s l : ℕ) (ν : OppIdx s l) (ξ : ℝ) : ℂ :=
  profileFun (2 * nu ν) (l - nu ν) (s - nu ν) ((‖kClass (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - nu ν)‖ ^ 2 : ℝ) : ℂ) ξ

lemma psiFun_eq_mcoef (s l : ℕ) (ν : OppIdx s l) (ξ : ℝ) :
    psiFun s l ν ξ = mcoef (2 * nu ν) (kClass (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - nu ν))
      (kClass (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (l - nu ν)) (aR ξ) :=
  profile_eq_mcoef _ _ _ ξ

lemma continuous_psiFun (s l : ℕ) (ν : OppIdx s l) : Continuous (psiFun s l ν) :=
  continuous_profileFun _ _ _ (by have := nu_pos ν; omega) _

/-- The profile of `D_{2ν}⁻` times `√(sinh ξ)`, as a function. -/
def psiSrc (s l : ℕ) (ν : OppIdx s l) (ξ : ℝ) : ℂ := ((Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * psiFun s l ν ξ

theorem memLp_psiSrc (s l : ℕ) (ν : OppIdx s l) :
    MemLp (psiSrc s l ν) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hcont : Continuous (psiSrc s l ν) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_sinh)).mul (continuous_psiFun s l ν)
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hdec : ∀ ξ : ℝ, 0 ≤ ξ → ‖psiFun s l ν ξ‖ ≤
      profConst (2 * nu ν) (l - nu ν) (s - nu ν)
        ((‖kClass (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - nu ν)‖ ^ 2 : ℝ) : ℂ) *
        Real.exp (-(((2 * (nu ν) : ℕ) : ℝ) * ξ / 2)) :=
    fun ξ hξ => norm_profileFun_le _ _ _ _ hξ
  have hprod : IntegrableOn (fun ξ : ℝ => ((Real.sinh ξ : ℝ) : ℂ) *
      (psiFun s l ν ξ * (starRingEnd ℂ) (psiFun s l ν ξ))) (Ioi 0) := by
    have hf : Continuous fun ξ : ℝ => psiFun s l ν ξ * (starRingEnd ℂ) (psiFun s l ν ξ) * ((Real.sinh ξ : ℝ) : ℂ) :=
      ((continuous_psiFun s l ν).mul (Complex.continuous_conj.comp (continuous_psiFun s l ν))).mul
        (Complex.continuous_ofReal.comp Real.continuous_sinh)
    have := integrableOn_of_decay hf _
      (fun ξ hξ => decay_prod (a := 2 * nu ν) (b := 2 * nu ν) (by have := nu_pos ν; omega) hdec hdec hξ)
    exact this.congr_fun (fun ξ _ => by ring) measurableSet_Ioi
  have h2 := integrableOn_sinh_norm_sq hprod
  refine h2.congr_fun (fun ξ hξ => ?_) measurableSet_Ioi
  have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
  simp only [psiSrc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hs]

/-- **The radial profile of `D_{2ν}⁻` as a vector of `L²(0, ∞)`**. -/
def psiVec (s l : ℕ) (ν : OppIdx s l) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_psiSrc s l ν).toLp (psiSrc s l ν)

/-- **The chain `HcN s G i` is orthogonal to the profile `ψ_ν`**:
`∫_0^∞ HcN s G l · conj(ψ_ν) sinh = 0` for a generator `G`. -/
theorem integral_HcN_mul_psiFun (s l : ℕ) (ν : OppIdx s l) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    ∫ ξ in Ioi (0 : ℝ), HcN s G l ξ * (starRingEnd ℂ) (psiFun s l ν ξ) * (Real.sinh ξ : ℂ) = 0 := by
  have hν1 : 1 ≤ (nu ν) := nu_pos ν
  have hνl : (nu ν) ≤ l := nu_le_l ν
  have hνs : (nu ν) ≤ s := nu_le_s ν
  have hn : 1 ≤ 2 * (nu ν) := by omega
  have hn2 : 2 ≤ 2 * (nu ν) := by omega
  set j : ℕ := s - (nu ν) with hj
  set κ : ℂ := ((‖kClass hn2 j‖ ^ 2 : ℝ) : ℂ) with hκ
  have hsj : (nu ν) + j = s := by omega
  have hr : (((2 * (nu ν) + 2 * j : ℕ) : ℝ) / 2) = (s : ℝ) := by
    have : 2 * (nu ν) + 2 * j = 2 * s := by omega
    rw [this]; push_cast; ring
  have hkey := integral_chain_mul_conj_eq_zero (-(s : ℝ)) (nu ν) hν1 (G := fun k ξ => profileFun (2 * nu ν) k j κ ξ)
    (fun k => -((k + 1 : ℕ) : ℝ))
    (fun k => contDiffOn_profileFun (2 * nu ν) k j hn κ)
    (fun k => (continuous_profileFun (2 * nu ν) k j hn κ).continuousOn)
    (fun ξ hξ => by
      have h := ladDown_profileFun_zero_minus (2 * nu ν) j hn κ hξ
      have e1 : (((2 * (nu ν) + 2 * 0 : ℕ) : ℝ) / 2) = (nu ν : ℝ) := by push_cast; ring
      have e2 : (-((2 * (nu ν) + 2 * j : ℕ) : ℝ) / 2) = -(s : ℝ) := by rw [neg_div, hr]
      rw [e1, e2] at h
      exact h)
    (fun k ξ hξ => by
      have h := ladDown_profileFun_succ_minus (2 * nu ν) k j hn κ hξ
      have e1 : (((2 * (nu ν) + 2 * (k + 1) : ℕ) : ℝ) / 2) = ((nu ν + k + 1 : ℕ) : ℝ) := by push_cast; ring
      have e2 : (-((2 * (nu ν) + 2 * j : ℕ) : ℝ) / 2) = -(s : ℝ) := by rw [neg_div, hr]
      rw [e1, e2] at h
      rw [h]; push_cast; ring)
    (H := fun i => HcN s G i)
    (fun i => ((contDiffOn_hLRN s hG i).congr (fun ξ hξ => HcN_eq_hLRN s hG i hξ)).of_le (by norm_cast))
    (fun i => (continuous_HcN s hG i).continuousOn)
    (fun i => by
      obtain ⟨R, hR⟩ := (hasCompactSupport_HcN s hc i).isCompact.isBounded.subset_closedBall (0 : ℝ)
      refine ⟨|R| + 1, by positivity, fun ξ hξ => ?_⟩
      by_contra hne
      have hmem : ξ ∈ tsupport (HcN s G i) := subset_tsupport _ hne
      have := hR hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_abs_self ξ, le_abs_self R, abs_nonneg R])
    (fun i ξ hξ => by
      rw [HcN_eq_hLRN s hG (i + 1) hξ]
      show ladUp (i : ℝ) (-(s : ℝ)) (hLRN s G i) ξ = _
      have hev : HcN s G i =ᶠ[nhds ξ] hLRN s G i := by
        filter_upwards [Ioi_mem_nhds hξ] with y hy using HcN_eq_hLRN s hG i hy
      simp only [ladUp, hev.deriv_eq, hev.self_of_nhds])
    (l - nu ν)
  have hl : (nu ν) + (l - nu ν) = l := by omega
  rw [hl] at hkey
  exact hkey

/-- **The profile `ψ_ν` is orthogonal to every ladder image** `blockEN s l G`. -/
theorem inner_psiVec_blockEN (s l : ℕ) (ν : OppIdx s l) (G : smoothCS) :
    inner ℂ (psiVec s l ν) (blockEN s l G) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (psiVec s l ν : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] psiSrc s l ν :=
    MemLp.coeFn_toLp (memLp_psiSrc s l ν)
  have h2 : (blockEN s l G : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] blockSrcN s l G :=
    MemLp.coeFn_toLp (memLp_blockSrcN s l G.2.1 G.2.2)
  have hint := integral_HcN_mul_psiFun s l ν G.2.1 G.2.2
  calc ∫ a in Ioi (0 : ℝ), inner ℂ ((psiVec s l ν : ℝ → ℂ) a) ((blockEN s l G : ℝ → ℂ) a)
      = ∫ ξ in Ioi (0 : ℝ), ((Real.pi : ℝ) : ℂ) *
          (HcN s G l ξ * (starRingEnd ℂ) (psiFun s l ν ξ) * (Real.sinh ξ : ℂ)) := by
        refine integral_congr_ae ?_
        filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 hξ
        rw [e1, e2, psiSrc, blockSrcN, RCLike.inner_apply', map_mul, Complex.conj_ofReal]
        have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
        have hss : ((Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * ((Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) =
            ((Real.sinh ξ : ℝ) : ℂ) := by exact_mod_cast Real.mul_self_sqrt hs
        simp only [Complex.ofReal_mul]
        linear_combination (((Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (psiFun s l ν ξ) * HcN s G l ξ) * hss
    _ = 0 := by rw [integral_const_mul, hint, mul_zero]

/-- **The profiles of `D_{2ν}⁻` lie in the discrete part of the block `(l, -s)`.** -/
theorem psiVec_mem_discSpan (s l : ℕ) (ν : OppIdx s l) : psiVec s l ν ∈ discSpan s l := by
  refine orthogonal_range_blockEN_le s l ?_
  rw [Submodule.mem_orthogonal']
  rintro _ ⟨G, rfl⟩
  have h := inner_psiVec_blockEN s l ν G
  rw [← inner_conj_symm] at h
  simpa using h

/-- The profiles of two distinct series occurring in the block are orthogonal in `L²(0, ∞)`. -/
theorem inner_psiVec_psiVec_ne (s l : ℕ) {i i' : OppIdx s l} (h : i ≠ i') :
    inner ℂ (psiVec s l i) (psiVec s l i') = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (psiVec s l i : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] psiSrc s l i :=
    MemLp.coeFn_toLp (memLp_psiSrc s l i)
  have h2 : (psiVec s l i' : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] psiSrc s l i' :=
    MemLp.coeFn_toLp (memLp_psiSrc s l i')
  have hνl := nu_le_l i
  have hνl' := nu_le_l i'
  have hνs := nu_le_s i
  have hνs' := nu_le_s i'
  have hp1 := nu_pos i
  have hp2 := nu_pos i'
  have hne : 2 * (nu i) ≠ 2 * (nu i') := by
    intro he
    apply h
    have : nu i = nu i' := by omega
    exact Fin.ext (by simp only [nu] at this; omega)
  have hpair := profPair_eq_zero_of_ne (2 * (nu i)) (l - (nu i)) (s - (nu i))
    ((‖kClass (show 2 ≤ 2 * (nu i) by omega) (s - (nu i))‖ ^ 2 : ℝ) : ℂ)
    (2 * (nu i')) (l - (nu i')) (s - (nu i'))
    ((‖kClass (show 2 ≤ 2 * (nu i') by omega) (s - (nu i'))‖ ^ 2 : ℝ) : ℂ) (by omega) (by omega) (by omega)
    hne (by omega) (by omega)
  unfold profPair at hpair
  have hconj := congrArg (starRingEnd ℂ) hpair
  rw [← integral_conj, map_zero] at hconj
  rw [← hconj]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 hξ
  have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
  have hss : ((Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * ((Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) =
      ((Real.sinh ξ : ℝ) : ℂ) := by exact_mod_cast Real.mul_self_sqrt hs
  rw [e1, e2, psiSrc, psiSrc, RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  unfold psiFun
  linear_combination ((starRingEnd ℂ) (profileFun (2 * nu i) (l - nu i) (s - nu i)
    ((‖kClass (show 2 ≤ 2 * nu i by omega) (s - nu i)‖ ^ 2 : ℝ) : ℂ) ξ) *
    profileFun (2 * nu i') (l - nu i') (s - nu i')
      ((‖kClass (show 2 ≤ 2 * nu i' by omega) (s - nu i')‖ ^ 2 : ℝ) : ℂ) ξ) * hss

/-- **The norm of the profile**: `‖ψ_ν‖² = 2 ‖e_{s-ν}‖² ‖e_{l-ν}‖² / (2ν - 1)` in `L²(0, ∞)`. -/
theorem norm_sq_psiVec (s l : ℕ) (i : OppIdx s l) :
    ‖psiVec s l i‖ ^ 2 =
      2 * ‖kClass (show 2 ≤ 2 * (nu i) by have := nu_pos i; omega) (s - (nu i))‖ ^ 2 *
        ‖kClass (show 2 ≤ 2 * (nu i) by have := nu_pos i; omega) (l - (nu i))‖ ^ 2 /
        (((2 * (nu i) : ℕ) : ℝ) - 1) := by
  have hp := nu_pos i
  have hl := nu_le_l i
  have hs := nu_le_s i
  have hn2 : 2 ≤ 2 * (nu i) := by omega
  have h1 : (psiVec s l i : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] psiSrc s l i :=
    MemLp.coeFn_toLp (memLp_psiSrc s l i)
  have hnorm : inner ℂ (psiVec s l i) (psiVec s l i) = ((‖psiVec s l i‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [MeasureTheory.L2.inner_def] at hnorm
  have hint : ∫ a in Ioi (0 : ℝ), inner ℂ ((psiVec s l i : ℝ → ℂ) a) ((psiVec s l i : ℝ → ℂ) a) =
      ((∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖mcoef (2 * (nu i)) (kClass hn2 (s - (nu i)))
        (kClass hn2 (l - (nu i))) (aR ξ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioi] with ξ e1 hξ
    have hs' : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
    rw [e1, inner_self_eq_norm_sq_to_K, psiSrc, norm_mul, Complex.norm_real, Real.norm_eq_abs, psiFun_eq_mcoef]
    norm_cast
    rw [mul_pow, sq_abs, Real.sq_sqrt hs']
    rfl
  rw [hint] at hnorm
  have hpos := integral_sinh_norm_sq_mcoef_aR hn2 (s - (nu i)) (l - (nu i))
  have : ‖psiVec s l i‖ ^ 2 = ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖mcoef (2 * (nu i)) (kClass hn2 (s - (nu i)))
        (kClass hn2 (l - (nu i))) (aR ξ)‖ ^ 2 := by exact_mod_cast hnorm.symm
  rw [this, hpos]

/-- **The profiles are nonzero**. -/
theorem psiVec_ne_zero (s l : ℕ) (i : OppIdx s l) : psiVec s l i ≠ 0 := by
  intro h0
  have hz : ‖psiVec s l i‖ ^ 2 = 0 := by rw [h0]; simp
  rw [norm_sq_psiVec] at hz
  have hp := nu_pos i
  have hn2 : 2 ≤ 2 * (nu i) := by omega
  have hej := norm_kClass_pos hn2 (s - (nu i))
  have hel := norm_kClass_pos hn2 (l - (nu i))
  have h2n : (1 : ℝ) < ((2 * (nu i) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 * (nu i))
  have : (0 : ℝ) < 2 * ‖kClass hn2 (s - (nu i))‖ ^ 2 * ‖kClass hn2 (l - (nu i))‖ ^ 2 /
      (((2 * (nu i) : ℕ) : ℝ) - 1) := by
    have : (0 : ℝ) < ((2 * (nu i) : ℕ) : ℝ) - 1 := by linarith
    positivity
  linarith

lemma card_discIdx_le (s l : ℕ) : Fintype.card (DiscIdx s l) ≤ min l s := by
  refine le_min ?_ ?_
  · calc Fintype.card (DiscIdx s l) ≤ Fintype.card (Fin l) := Fintype.card_subtype_le _
      _ = l := Fintype.card_fin l
  · have hinj : Function.Injective (fun i : DiscIdx s l =>
        (⟨(i.1 : ℕ) + s - l, by have := i.1.2; have := i.2; omega⟩ : Fin s)) := by
      intro a b hab
      have h := congrArg Fin.val hab
      simp only at h
      apply Subtype.ext
      apply Fin.ext
      have := a.2
      have := b.2
      omega
    calc Fintype.card (DiscIdx s l) ≤ Fintype.card (Fin s) := Fintype.card_le_of_injective _ hinj
      _ = s := Fintype.card_fin s

/-- **The discrete part of the opposite-sign block is spanned by the radial profiles of the antiholomorphic series
`D_{2ν}⁻`**, `1 ≤ ν ≤ min(l, s)`. -/
theorem span_psiVec_eq_discSpan (s l : ℕ) : Submodule.span ℂ (Set.range (psiVec s l)) = discSpan s l := by
  have hli : LinearIndependent ℂ (psiVec s l) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => psiVec_ne_zero s l i)
      (fun i i' h => inner_psiVec_psiVec_ne s l h)
  have hle : Submodule.span ℂ (Set.range (psiVec s l)) ≤ discSpan s l :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact psiVec_mem_discSpan s l i)
  have hrank1 : Module.finrank ℂ (Submodule.span ℂ (Set.range (psiVec s l))) = min l s := by
    rw [finrank_span_eq_card hli]; simp
  have hrank2 : Module.finrank ℂ (discSpan s l) ≤ min l s :=
    (finrank_range_le_card (phiVec s l)).trans (card_discIdx_le s l)
  have : FiniteDimensional ℂ (discSpan s l) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hrank1]; exact hrank2)

/-- **The `K × K` components of a single-weight function**: concentrated at `m = -w`. -/
lemma kkCoeff_block {F : SL2R → ℂ} {w : Fin 2 → ℤ} {φ : ℝ → ℂ}
    (hprof : ∀ (ξ : ℝ) (x : Fin 2 → ℝ), kkProfile F ξ x =
      Complex.exp (-(2 * π * Complex.I * ∑ i, (w i : ℂ) * (x i : ℂ))) * φ ξ) (m : Fin 2 → ℤ) (ξ : ℝ) :
    kkCoeff F m ξ = if m + w = 0 then φ ξ else 0 := by
  unfold kkCoeff
  have h1 : ∀ x : Fin 2 → ℝ, Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) *
      kkProfile F ξ x =
      φ ξ * Complex.exp (-(2 * π * Complex.I * ∑ i, (((m + w) i : ℤ) : ℂ) * (x i : ℂ))) := by
    intro x
    rw [hprof ξ x]
    have hexp : Complex.exp (-(2 * π * Complex.I * ∑ i, (((m + w) i : ℤ) : ℂ) * (x i : ℂ))) =
        Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) *
          Complex.exp (-(2 * π * Complex.I * ∑ i, (w i : ℂ) * (x i : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [hexp]
    ring
  simp_rw [h1]
  rw [integral_const_mul, integral_box_char]
  by_cases h : m + w = 0
  · simp [h]
  · simp [h]

/-- The `K × K` profile of the conjugate coefficient `conj u_p`. -/
lemma kkProfile_uBar {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (ξ : ℝ) (x : Fin 2 → ℝ) :
    kkProfile (fun g => (starRingEnd ℂ) (uFun hn p g)) ξ x =
      Complex.exp (-(2 * π * Complex.I * ∑ i, (((-kkWeight n p.1 p.2) i : ℤ) : ℂ) * (x i : ℂ))) *
        (starRingEnd ℂ) (phiRad hn p ξ) := by
  have h := kkProfile_uFun hn p ξ x
  have h' : kkProfile (fun g => (starRingEnd ℂ) (uFun hn p g)) ξ x = (starRingEnd ℂ) (kkProfile (uFun hn p) ξ x) := rfl
  rw [h', h, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, map_sum, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **The components of `conj u_p`**: concentrated at `m = kkWeight`, with value `conj (phiRad p)`. -/
lemma kkCoeff_uBar {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (m : Fin 2 → ℤ) (ξ : ℝ) :
    kkCoeff (fun g => (starRingEnd ℂ) (uFun hn p g)) m ξ =
      if m = kkWeight n p.1 p.2 then (starRingEnd ℂ) (phiRad hn p ξ) else 0 := by
  rw [kkCoeff_block (kkProfile_uBar hn p) m ξ]
  have : (m + -kkWeight n p.1 p.2 = 0) ↔ m = kkWeight n p.1 p.2 := by
    constructor
    · intro h; have := congrArg (· + kkWeight n p.1 p.2) h; simpa using this
    · intro h; rw [h]; simp
  simp only [this]

lemma conj_psiFun (s l : ℕ) (ν : OppIdx s l) (ξ : ℝ) :
    (starRingEnd ℂ) (psiFun s l ν ξ) = psiFun s l ν ξ :=
  conj_profileFun _ _ _ (by simp [Complex.conj_ofReal]) ξ

lemma kkWeight_two_nu (s l : ℕ) (ν : OppIdx s l) :
    kkWeight (2 * (nu ν)) (s - (nu ν)) (l - (nu ν)) = ![(2 * s : ℤ), (2 * l : ℤ)] := by
  have h1 := nu_le_l ν
  have h2 := nu_le_s ν
  unfold kkWeight
  have e1 : ((2 * (nu ν) + 2 * (s - (nu ν)) : ℕ) : ℤ) = 2 * s := by omega
  have e2 : ((2 * (nu ν) + 2 * (l - (nu ν)) : ℕ) : ℤ) = 2 * l := by omega
  rw [e1, e2]

/-- **The `K × K` components of `conj u_p`, as vectors of `L²(0, ∞)`**: zero away from the weight, and
`u_const · √sinh ψ_ν` at the weight (the profile of `D_{2ν}⁻` is real). -/
theorem kkL2_uLpBar_eq (s l : ℕ) (ν : OppIdx s l) (m : Fin 2 → ℤ) :
    kkL2 (uLpBar (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - (nu ν), l - (nu ν))) m =
      if m = ![(2 * s : ℤ), (2 * l : ℤ)] then
        ((uConst (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - (nu ν), l - (nu ν)) : ℝ) : ℂ) •
          psiVec s l ν
      else 0 := by
  have hn2 : 2 ≤ 2 * (nu ν) := by have := nu_pos ν; omega
  set p : ℕ × ℕ := (s - (nu ν), l - (nu ν)) with hp
  have hw : kkWeight (2 * (nu ν)) p.1 p.2 = ![(2 * s : ℤ), (2 * l : ℤ)] := kkWeight_two_nu s l ν
  have hfc : Continuous (star (uFun hn2 p)) := continuous_star.comp (continuous_uFun hn2 p)
  have hf : MemLp (star (uFun hn2 p)) 2 haarR := (memLp_uFun hn2 p).star
  have hsame : (star (uFun hn2 p)) = fun g => (starRingEnd ℂ) (uFun hn2 p g) := rfl
  have hK := kkL2_toLp hfc hf m
  have hbar : uLpBar hn2 p = hf.toLp (star (uFun hn2 p)) := rfl
  rw [hbar, hK]
  have hcoeff : ∀ ξ, kkCoeff (star (uFun hn2 p)) m ξ =
      if m = kkWeight (2 * (nu ν)) p.1 p.2 then (starRingEnd ℂ) (phiRad hn2 p ξ) else 0 := by
    intro ξ; rw [hsame]; exact kkCoeff_uBar hn2 p m ξ
  by_cases hm : m = ![(2 * s : ℤ), (2 * l : ℤ)]
  · rw [if_pos hm]
    refine Lp.ext ?_
    have h1 : ((memLp_kkSrc hfc hf m).toLp (kkSrc (star (uFun hn2 p)) m) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        kkSrc (star (uFun hn2 p)) m := MemLp.coeFn_toLp _
    have h2 := Lp.coeFn_smul ((uConst hn2 p : ℝ) : ℂ) (psiVec s l ν)
    have h3 : (psiVec s l ν : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] psiSrc s l ν :=
      MemLp.coeFn_toLp (memLp_psiSrc s l ν)
    filter_upwards [h1, h2, h3] with ξ e1 e2 e3
    rw [e1, e2, Pi.smul_apply, e3, smul_eq_mul, kkSrc, hcoeff ξ, if_pos (hm.trans hw.symm), psiSrc]
    have hphi : phiRad hn2 p ξ = (uConst hn2 p : ℂ) * psiFun s l ν ξ := by
      rw [psiFun_eq_mcoef]; rfl
    rw [hphi, map_mul, Complex.conj_ofReal, conj_psiFun]
    ring
  · rw [if_neg hm]
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    have h1 : ((memLp_kkSrc hfc hf m).toLp (kkSrc (star (uFun hn2 p)) m) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        kkSrc (star (uFun hn2 p)) m := MemLp.coeFn_toLp _
    filter_upwards [h1] with ξ e1
    rw [e1, kkSrc, hcoeff ξ, if_neg (fun h => hm (h.trans hw))]
    simp

/-- **The pairing with `conj u_p` in the block**: for `F ∈ L²(SL(2,ℝ))`,
`⟨conj u_p, F⟩ = (2π)² u_const ⟨ψ_ν, F_{(2s, 2l)}⟩`. -/
theorem inner_uLpBar_eq (s l : ℕ) (ν : OppIdx s l) (F : Lp ℂ 2 haarR) :
    inner ℂ (uLpBar (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - (nu ν), l - (nu ν))) F =
      ((2 * π : ℝ) : ℂ) ^ 2 *
        (((uConst (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - (nu ν), l - (nu ν)) : ℝ) : ℂ) *
          inner ℂ (psiVec s l ν) (kkL2 F ![(2 * s : ℤ), (2 * l : ℤ)])) := by
  rw [inner_eq_tsum_kkL2, tsum_eq_single ![(2 * s : ℤ), (2 * l : ℤ)]]
  · rw [kkL2_uLpBar_eq, if_pos rfl, inner_smul_left, Complex.conj_ofReal]
  · intro m hm
    rw [kkL2_uLpBar_eq, if_neg hm, inner_zero_left]

/-- The normalisation identity `(2π)² u_const² ‖ψ_ν‖² = 1`. -/
lemma two_pi_sq_mul_uConst_sq_mul_norm_sq (s l : ℕ) (ν : OppIdx s l) :
    (2 * π) ^ 2 * (uConst (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - (nu ν), l - (nu ν))) ^ 2 *
      ‖psiVec s l ν‖ ^ 2 = 1 := by
  have hp := nu_pos ν
  have hn2 : 2 ≤ 2 * (nu ν) := by omega
  rw [norm_sq_psiVec]
  have hej := norm_kClass_pos hn2 (s - (nu ν))
  have hel := norm_kClass_pos hn2 (l - (nu ν))
  have hsr := schurRatio_eq hn2
  have hsq : (uConst hn2 (s - (nu ν), l - (nu ν))) ^ 2 =
      (schurRatio hn2 * ‖kClass hn2 (s - (nu ν))‖ ^ 2 * ‖kClass hn2 (l - (nu ν))‖ ^ 2)⁻¹ := by
    unfold uConst
    simp only
    rw [inv_pow, mul_pow, mul_pow, Real.sq_sqrt (schurRatio_pos hn2).le]
  rw [hsq, hsr]
  have h2n : (0 : ℝ) < ((2 * (nu ν) : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) < ((2 * (nu ν) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 * (nu ν))
    linarith
  have hpi : 0 < π := Real.pi_pos
  field_simp
  norm_num

/-- **The discrete coefficient squared**: `|⟨conj u_p, F⟩|² = (2π)² |⟨ψ_ν, F_{(2s,2l)}⟩|² / ‖ψ_ν‖²`. -/
theorem norm_sq_inner_uLpBar (s l : ℕ) (ν : OppIdx s l) (F : Lp ℂ 2 haarR) :
    ‖inner ℂ (uLpBar (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega) (s - (nu ν), l - (nu ν))) F‖ ^ 2 =
      (2 * π) ^ 2 * (‖inner ℂ (psiVec s l ν) (kkL2 F ![(2 * s : ℤ), (2 * l : ℤ)])‖ ^ 2 / ‖psiVec s l ν‖ ^ 2) := by
  have hp := nu_pos ν
  have hn2 : 2 ≤ 2 * (nu ν) := by omega
  have hkey := two_pi_sq_mul_uConst_sq_mul_norm_sq s l ν
  have hne : ‖psiVec s l ν‖ ^ 2 ≠ 0 := by
    have := norm_pos_iff.2 (psiVec_ne_zero s l ν)
    positivity
  rw [inner_uLpBar_eq]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (uConst_pos hn2 _), abs_of_pos (two_pos : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  generalize ‖psiVec s l ν‖ = P at hne hkey ⊢
  generalize ‖inner ℂ (psiVec s l ν) (kkL2 F ![(2 * s : ℤ), (2 * l : ℤ)])‖ = a
  generalize uConst hn2 (s - (nu ν), l - (nu ν)) = u at hkey ⊢
  have hP : P ≠ 0 := by rintro rfl; simp at hne
  have e : ((2 * π) ^ 2 * (u * a)) ^ 2 = ((2 * π) ^ 2 * u ^ 2 * P ^ 2) * ((2 * π) ^ 2 * (a ^ 2 / P ^ 2)) := by
    field_simp
  rw [e, hkey, one_mul]

/-- **The norm of the projection onto the span of a finite orthonormal family** is the `ℓ²`-norm of the inner
products. -/
theorem norm_sq_starProjection_span_finite {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} [Finite ι] (v : ι → E) (hv : Orthonormal ℂ v) (f : E) (K : Submodule ℂ E)
    (hK : Submodule.span ℂ (Set.range v) = K) [K.HasOrthogonalProjection] :
    ‖K.starProjection f‖ ^ 2 = ∑' i, ‖inner ℂ (v i) f‖ ^ 2 := by
  classical
  subst hK
  set M := Submodule.span ℂ (Set.range v) with hM
  have hcomplete : CompleteSpace M := by
    have : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    infer_instance
  have hmem : ∀ i, v i ∈ M := fun i => Submodule.subset_span ⟨i, rfl⟩
  set w : ι → M := fun i => ⟨v i, hmem i⟩ with hw
  have hon : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i i'
    have h := hv i i'
    simpa [hw, Submodule.coe_inner] using h
  have hsp : (Submodule.span ℂ (Set.range w))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    have h0 : ∀ i, inner ℂ (v i) (x : E) = 0 := fun i => by
      have := hx (w i) (Submodule.subset_span ⟨i, rfl⟩)
      simpa [hw, Submodule.coe_inner] using this
    have hx2 : inner ℂ (x : E) (x : E) = 0 := by
      have hxM : (x : E) ∈ M := x.2
      have horth : M ≤ (ℂ ∙ (x : E))ᗮ := Submodule.span_le.2 (by
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
        rw [← inner_conj_symm, h0 i]; simp)
      have := horth hxM
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      exact this
    exact Subtype.ext (inner_self_eq_zero.1 hx2)
  let b : HilbertBasis ι ℂ M := HilbertBasis.mkOfOrthogonalEqBot hon hsp
  have hb : ∀ i, b i = w i := fun i => congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp) i
  set g : M := ⟨M.starProjection f, Submodule.starProjection_apply_mem M f⟩ with hg
  have hpar := b.hasSum_inner_mul_inner g g
  have hterm : ∀ i, inner ℂ g (b i) * inner ℂ (b i) g = ((‖inner ℂ (v i) f‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have hin : inner ℂ (b i) g = inner ℂ (v i) f := by
      rw [hb i]
      show inner ℂ (v i) (M.starProjection f) = _
      have h1 := Submodule.starProjection_inner_eq_zero (K := M) f (v i) (hmem i)
      rw [inner_sub_left] at h1
      have h2 : inner ℂ f (v i) = inner ℂ (M.starProjection f) (v i) := sub_eq_zero.1 h1
      rw [← inner_conj_symm (v i) (M.starProjection f), ← h2, inner_conj_symm]
    have : inner ℂ g (b i) = (starRingEnd ℂ) (inner ℂ (b i) g) := by
      simp only [Submodule.coe_inner]; exact (inner_conj_symm _ _).symm
    rw [this, hin, Complex.conj_mul']
    push_cast; ring
  have hnorm : inner ℂ g g = ((‖M.starProjection f‖ ^ 2 : ℝ) : ℂ) := by
    have h0 : inner ℂ g g = inner ℂ (M.starProjection f) (M.starProjection f) := rfl
    rw [h0, inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [hterm, hnorm] at hpar
  have hpar' : HasSum (fun i : ι => ‖inner ℂ (v i) f‖ ^ 2) (‖M.starProjection f‖ ^ 2) := by
    exact_mod_cast hpar
  exact hpar'.tsum_eq.symm

instance discSpan_hasOrthogonalProjection (s l : ℕ) : (discSpan s l).HasOrthogonalProjection := by
  have : FiniteDimensional ℂ (discSpan s l) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The unit vectors `ψ_ν / ‖ψ_ν‖` of the discrete part of the block `(l, -s)`. -/
def psiUnit (s l : ℕ) (ν : OppIdx s l) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (((‖psiVec s l ν‖⁻¹ : ℝ)) : ℂ) • psiVec s l ν

theorem psiUnit_orthonormal (s l : ℕ) : Orthonormal ℂ (psiUnit s l) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have hne : ‖psiVec s l i‖ ≠ 0 := norm_ne_zero_iff.2 (psiVec_ne_zero s l i)
    simp only [psiUnit, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_inv, abs_norm]
    field_simp
  · simp only [psiUnit, inner_smul_left, inner_smul_right, inner_psiVec_psiVec_ne s l hij, mul_zero]

theorem span_psiUnit_eq (s l : ℕ) : Submodule.span ℂ (Set.range (psiUnit s l)) = discSpan s l := by
  rw [← span_psiVec_eq_discSpan]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hne : ‖psiVec s l i‖ ≠ 0 := norm_ne_zero_iff.2 (psiVec_ne_zero s l i)
    have : psiVec s l i = ((‖psiVec s l i‖ : ℝ) : ℂ) • psiUnit s l i := by
      simp only [psiUnit, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The discrete part of a block as an `ℓ²` sum**:
`‖P_{disc} H‖² = Σ_ν |⟨ψ_ν, H⟩|² / ‖ψ_ν‖²`. -/
theorem norm_sq_starProjection_discSpan (s l : ℕ) (H : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ‖(discSpan s l).starProjection H‖ ^ 2 =
      ∑ ν : OppIdx s l, ‖inner ℂ (psiVec s l ν) H‖ ^ 2 / ‖psiVec s l ν‖ ^ 2 := by
  have h := norm_sq_starProjection_span_finite (psiUnit s l) (psiUnit_orthonormal s l) H (discSpan s l)
    (span_psiUnit_eq s l)
  rw [h, tsum_fintype]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [psiUnit, inner_smul_left, Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, abs_norm]
  have hne : ‖psiVec s l ν‖ ≠ 0 := norm_ne_zero_iff.2 (psiVec_ne_zero s l ν)
  field_simp

/-- **The discrete series part of the block `(2s, 2l)`**: for `F ∈ L²(SL(2,ℝ))`,
`Σ_ν |⟨conj u_{ν}, F⟩|² = (2π)² ‖P_{disc}(F_{(2s, 2l)})‖²`, the sum over the antiholomorphic series `D_{2ν}⁻`,
`1 ≤ ν ≤ min(l, s)`, and `P_{disc}` the projection of the block onto the discrete directions. -/
theorem sum_norm_sq_inner_uLpBar (s l : ℕ) (F : Lp ℂ 2 haarR) :
    ∑ ν : OppIdx s l, ‖inner ℂ (uLpBar (show 2 ≤ 2 * (nu ν) by have := nu_pos ν; omega)
        (s - (nu ν), l - (nu ν))) F‖ ^ 2 =
      (2 * π) ^ 2 * ‖(discSpan s l).starProjection (kkL2 F ![(2 * s : ℤ), (2 * l : ℤ)])‖ ^ 2 := by
  rw [norm_sq_starProjection_discSpan, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ν _ => norm_sq_inner_uLpBar s l ν F)

lemma uLpBar_congr {n n' : ℕ} (h : n = n') (hn : 2 ≤ n) (hn' : 2 ≤ n') (p : ℕ × ℕ) :
    uLpBar hn p = uLpBar hn' p := by
  subst h; rfl

/-- The squared coefficient of `conj u^{2(ν+1)}_{jk}`. -/
def coefBarSq (F : Lp ℂ 2 haarR) (t : ℕ × ℕ × ℕ) : ℝ :=
  ‖inner ℂ (uLpBar (show 2 ≤ 2 * (t.1 + 1) by omega) (t.2.1, t.2.2)) F‖ ^ 2

lemma summable_coefBarSq (F : Lp ℂ 2 haarR) : Summable (coefBarSq F) := by
  have hsum : Summable fun i : Bool × ℕ × (ℕ × ℕ) => ‖inner ℂ (discFam i) F‖ ^ 2 :=
    discFam_orthonormal.inner_products_summable F
  have hinj : Function.Injective (fun t : ℕ × ℕ × ℕ => ((false, 2 * t.1, (t.2.1, t.2.2)) : Bool × ℕ × (ℕ × ℕ))) := by
    intro a b h
    simp only [Prod.mk.injEq, true_and] at h
    obtain ⟨h1, h2, h3⟩ := h
    ext <;> simp_all <;> try omega
  have h := hsum.comp_injective hinj
  refine h.congr (fun t => ?_)
  simp only [Function.comp, discFam, uMinus, coefBarSq]
  try rw [uLpBar_congr (show 2 * t.1 + 2 = 2 * (t.1 + 1) by ring)]

/-- The reindexing `(ν, j, k) ↦ ((s, l), ν)`, `s = ν + 1 + j`, `l = ν + 1 + k`. -/
def blockEquiv : (ℕ × ℕ × ℕ) ≃ Σ q : ℕ × ℕ, OppIdx q.1 q.2 where
  toFun t := ⟨(t.1 + 1 + t.2.1, t.1 + 1 + t.2.2), ⟨t.1, by simp; omega⟩⟩
  invFun x := (x.2.1, x.1.1 - (x.2.1 + 1), x.1.2 - (x.2.1 + 1))
  left_inv t := by simp
  right_inv x := by
    obtain ⟨⟨s, l⟩, i⟩ := x
    have := i.2
    have h1 : i.1 + 1 ≤ s := by have := min_le_right l s; omega
    have h2 : i.1 + 1 ≤ l := by have := min_le_left l s; omega
    have e1 : (i.1 + 1 + (s - (i.1 + 1)), i.1 + 1 + (l - (i.1 + 1))) = (s, l) := by
      ext <;> simp <;> omega
    refine Sigma.ext e1 ?_
    have hmin : min (i.1 + 1 + (l - (i.1 + 1))) (i.1 + 1 + (s - (i.1 + 1))) = min l s := by
      rw [show i.1 + 1 + (l - (i.1 + 1)) = l by omega, show i.1 + 1 + (s - (i.1 + 1)) = s by omega]
    exact (Fin.heq_ext_iff hmin).2 rfl

/-- **The even antiholomorphic discrete part, block by block**: for `F ∈ L²(SL(2,ℝ))`,
`Σ_{ν ≥ 1} ‖P_{2ν}⁻ F‖² = (2π)² Σ_{s, l} ‖P_{disc}(F_{(2s, 2l)})‖²`. -/
theorem tsum_norm_sq_discreteBar_even (F : Lp ℂ 2 haarR) :
    ∑' ν : ℕ, ‖(discreteSpaceBar (show 2 ≤ 2 * (ν + 1) by omega)).starProjection F‖ ^ 2 =
      (2 * π) ^ 2 * ∑' q : ℕ × ℕ,
        ‖(discSpan q.1 q.2).starProjection (kkL2 F ![(2 * q.1 : ℤ), (2 * q.2 : ℤ)])‖ ^ 2 := by
  have hsum := summable_coefBarSq F
  have hL : ∑' ν : ℕ, ‖(discreteSpaceBar (show 2 ≤ 2 * (ν + 1) by omega)).starProjection F‖ ^ 2 =
      ∑' t : ℕ × ℕ × ℕ, coefBarSq F t := by
    rw [hsum.tsum_prod' (fun ν => hsum.prod_factor ν)]
    refine tsum_congr (fun ν => ?_)
    rw [norm_sq_starProjection_discreteBar]
    refine tsum_congr (fun p => ?_)
    rfl
  have h1 : ∑' t : ℕ × ℕ × ℕ, coefBarSq F t =
      ∑' x : Σ q : ℕ × ℕ, OppIdx q.1 q.2, coefBarSq F (blockEquiv.symm x) :=
    (blockEquiv.symm.tsum_eq (coefBarSq F)).symm
  have hsum' : Summable (fun x : Σ q : ℕ × ℕ, OppIdx q.1 q.2 => coefBarSq F (blockEquiv.symm x)) :=
    (blockEquiv.symm.summable_iff (f := coefBarSq F)).2 hsum
  rw [hL, h1, hsum'.tsum_sigma' (fun q => Summable.of_finite), ← tsum_mul_left]
  refine tsum_congr (fun q => ?_)
  rw [tsum_fintype, ← sum_norm_sq_inner_uLpBar q.1 q.2 F]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- `⟨star a, star b⟩ = conj ⟨a, b⟩` in `L²`. -/
lemma inner_star_star {α : Type*} [MeasurableSpace α] {μ : Measure α} (a b : Lp ℂ 2 μ) :
    inner ℂ (star a) (star b) = (starRingEnd ℂ) (inner ℂ a b) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star a, Lp.coeFn_star b] with x hxa hxb
  rw [hxa, hxb]
  simp [RCLike.inner_apply, mul_comm]

lemma uLpBar_eq_star {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : uLpBar hn p = star (uLp hn p) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (uLp hn p), (memLp_uFun hn p).coeFn_toLp,
    ((memLp_uFun hn p).star).coeFn_toLp] with x h1 h2 h3
  simp only [uLpBar, uLp] at *
  rw [h3, h1]
  simp only [Pi.star_apply, h2]

/-- **Conjugation exchanges `D_n⁺` and `D_n⁻`**: `‖⟨u_p, F⟩‖ = ‖⟨conj u_p, conj F⟩‖`. -/
lemma norm_inner_uLp_eq {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (F : Lp ℂ 2 haarR) :
    ‖inner ℂ (uLp hn p) F‖ = ‖inner ℂ (uLpBar hn p) (star F)‖ := by
  rw [uLpBar_eq_star, inner_star_star, RCLike.norm_conj]

/-- `‖P_n⁺ F‖ = ‖P_n⁻ (conj F)‖`. -/
lemma norm_sq_starProjection_discrete_eq_bar {n : ℕ} (hn : 2 ≤ n) (F : Lp ℂ 2 haarR) :
    ‖(discreteSpace hn).starProjection F‖ ^ 2 = ‖(discreteSpaceBar hn).starProjection (star F)‖ ^ 2 := by
  rw [norm_sq_starProjection_discrete, norm_sq_starProjection_discreteBar]
  refine tsum_congr (fun p => ?_)
  rw [norm_inner_uLp_eq]

/-- **The even holomorphic discrete part, block by block**:
`Σ_{ν ≥ 1} ‖P_{2ν}⁺ F‖² = (2π)² Σ_{s, l} ‖P_{disc}((conj F)_{(2s, 2l)})‖²`. -/
theorem tsum_norm_sq_discrete_even (F : Lp ℂ 2 haarR) :
    ∑' ν : ℕ, ‖(discreteSpace (show 2 ≤ 2 * (ν + 1) by omega)).starProjection F‖ ^ 2 =
      (2 * π) ^ 2 * ∑' q : ℕ × ℕ,
        ‖(discSpan q.1 q.2).starProjection (kkL2 (star F) ![(2 * q.1 : ℤ), (2 * q.2 : ℤ)])‖ ^ 2 := by
  rw [← tsum_norm_sq_discreteBar_even (star F)]
  exact tsum_congr (fun ν => norm_sq_starProjection_discrete_eq_bar _ F)

end Lightlike.Lorentz.SL2RPlancherel

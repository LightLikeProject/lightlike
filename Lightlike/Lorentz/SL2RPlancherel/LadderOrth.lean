import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.LadderLocal

/-!
# Ladder images are orthogonal to the kernel of the adjoint ladder

If `G` is a classical solution of `ladDown (l+1) r G = 0` on `(0, ∞)` (so `G` spans the kernel of the
ladder adjoint to `ladUp l r` in the weight `sinh ξ dξ`), then every ladder image `ladUp l r F`, with
`F` of class `C¹` on `(0, ∞)`, vanishing for large `ξ` and with `sinh ξ · F(ξ) · conj G(ξ) → 0` at
`0`, is orthogonal to `G` in `L²((0, ∞), sinh ξ dξ)`: `ladUp_orth_ker`.  Layer 2c-iii of the
Plancherel formula on `SL(2,ℝ)`, milestone HA3; the statement the discrete series layer uses.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **A ladder image is orthogonal to the kernel of the adjoint ladder.** -/
theorem ladUp_orth_ker (l r : ℝ) {F G : ℝ → ℂ} (hF : ContDiffOn ℝ 1 F (Ioi 0))
    (hG : ContDiffOn ℝ 1 G (Ioi 0)) (hker : ∀ ξ, 0 < ξ → ladDown (l + 1) r G ξ = 0)
    {R : ℝ} (hR : 0 < R) (hFR : ∀ ξ, R ≤ ξ → F ξ = 0)
    (hbd : Tendsto (fun a => F a * (starRingEnd ℂ) (G a) * (Real.sinh a : ℂ)) (𝓝[>] 0) (𝓝 0))
    (hint : IntegrableOn (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ)) (Ioi 0)) :
    ∫ ξ in Ioi (0 : ℝ), ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) = 0 := by
  set f : ℝ → ℂ := fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) with hf
  -- the integrand vanishes beyond `R`
  have hzero : ∀ ξ ∈ Ioi (0 : ℝ) \ Ioc 0 R, f ξ = 0 := by
    intro ξ hξ
    have hξR : R < ξ := by
      by_contra h
      exact hξ.2 ⟨hξ.1, not_lt.mp h⟩
    have hev : F =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hξR] with y hy using hFR y (le_of_lt hy)
    have hd : deriv F ξ = 0 := by
      rw [hev.deriv_eq]; simp
    simp [hf, ladUp, hd, hFR ξ hξR.le]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hzero]
  -- the integral over `(0, R]` as a limit of integrals over `(R/(n+1), R]`
  have hpos : ∀ n : ℕ, 0 < R / (n + 1) := fun n => by positivity
  have hle : ∀ n : ℕ, R / (n + 1) ≤ R := fun n => by
    rw [div_le_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmono : Monotone fun n : ℕ => Ioc (R / (n + 1)) R := by
    intro m n hmn
    refine Ioc_subset_Ioc_left ?_
    apply div_le_div_of_nonneg_left hR.le (by positivity)
    exact_mod_cast Nat.succ_le_succ hmn
  have hunion : (⋃ n : ℕ, Ioc (R / (n + 1)) R) = Ioc 0 R := by
    ext x
    simp only [mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨lt_trans (hpos n) h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (R / x)
      refine ⟨n, ?_, h2⟩
      rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ h1).mp hn
      nlinarith
  have hfi : IntegrableOn f (⋃ n : ℕ, Ioc (R / (n + 1)) R) := by
    rw [hunion]; exact hint.mono_set Ioc_subset_Ioi_self
  have hlim := tendsto_setIntegral_of_monotone (μ := volume) (fun n => measurableSet_Ioc) hmono hfi
  rw [hunion] at hlim
  have hseq : ∀ n : ℕ, ∫ ξ in Ioc (R / (n + 1)) R, f ξ =
      -(F (R / (n + 1)) * (starRingEnd ℂ) (G (R / (n + 1))) * (Real.sinh (R / (n + 1)) : ℂ)) := by
    intro n
    rw [← intervalIntegral.integral_of_le (hle n)]
    have h := ladder_adjoint_boundary l r (hpos n) (hle n) hF hG
    have hI : ∫ ξ in (R / (n + 1))..R, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      refine Filter.Eventually.of_forall fun ξ hξ => ?_
      have hξ' : 0 < ξ := lt_of_lt_of_le (hpos n) (by
        rw [uIoc_of_le (hle n)] at hξ; exact hξ.1.le)
      simp [hker ξ hξ']
    rw [hI, hFR R le_rfl] at h
    simpa [hf] using h
  have hto0 : Tendsto (fun n : ℕ => ∫ ξ in Ioc (R / (n + 1)) R, f ξ) atTop (𝓝 0) := by
    simp_rw [hseq]
    have ha : Tendsto (fun n : ℕ => R / ((n : ℝ) + 1)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hpos⟩
      exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have := (hbd.comp ha).neg
    simpa using this
  exact tendsto_nhds_unique hlim hto0

end Lightlike.Lorentz.SL2RPlancherel

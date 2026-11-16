import Lightlike.Asymptotics.EPRL.EPRLFormula
import Lightlike.Asymptotics.EPRL.FiniteMax
import Lightlike.Oscillatory.Localisation

/-!
# Suppression of the coherent 15j integral at noncritical maxima

If the coherent integrand `F_n` has finitely many points of modulus one and the logarithmic phase
has nonzero differential at each of them, the integral decays faster than every power of the spin
scale: `∫ F^λ = O(λ^{-k})` for every `k`. This is the case of the asymptotic formula in which the
extended stationary phase has no critical point (Barrett–Dowdall–Fairbairn–Gomes–Hellmann, *J. Math.
Phys.* 50 (2009) 112504, §5.1, eq. (24), and Theorem 1, case 3). Near a unimodular point `G^λ = v^λ
e^{iλφ}` with the logarithmic phase `φ = -i log (G/v)`; the non-stationary phase theorem of
`Lightlike/Oscillatory/Localisation.lean` (Hörmander, *ALPDO I*, Theorem 7.7.1) gives the local bound,
and `localise_pieces` glues the charts. The statement carries no proportionality of the spins to
areas; what it needs is that every point of modulus one is noncritical, which is a hypothesis here.

## Main results

* `local_suppression`: the chart-level statement for a smooth amplitude supported in a neighbourhood
  where `|G| = 1` only at noncritical points.
* `suppression_finite_max`: the `SU(2)^4` statement for a continuous `F` with `|F| ≤ 1` and finitely
  many noncritical maxima.
* `coh15j_dichotomy`: for SU(2) boundary data and any doubled spins, either some point has `|F_n| = 1`
  (the data glue for these spins) or the integral decays exponentially.
* `eprlCoh_exp_decay_of_no_gluing`: the coherent EPRL integral decays exponentially when the self-dual
  spins admit no gluing solution.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, §5.1 and Theorem 1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 7.7.1.
-/

open MeasureTheory Set Metric Complex Filter Asymptotics
open scoped ContDiff

namespace Lightlike.Asymptotics.EPRL

open Lightlike Lightlike.Spin4 Lightlike.Oscillatory

variable {n : ℕ}

/-- **Local suppression at a noncritical unimodular set.** If `|G| ≤ 1`, `|v| = 1`, `G / v` stays within
`1/4` of `1` on the support of the smooth compactly supported amplitude `a`, and the logarithmic phase
has nonzero differential at every point of the support where `|G| = 1`, then `∫ a G^λ = O(λ^{-k})`
for every `k`. -/
theorem local_suppression {G a : (Fin n → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) {v : ℂ} (hv : ‖v‖ = 1)
    (hle : ∀ x, ‖G x‖ ≤ 1) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hnb : ∀ x ∈ tsupport a, ‖G x / v - 1‖ < 1/4)
    (hnc : ∀ x ∈ tsupport a, ‖G x‖ = 1 → fderiv ℝ (logPhase G v) x ≠ 0) (k : ℕ) :
    (fun lam : ℕ => ∫ x, a x * G x ^ lam) =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ k)⁻¹ := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hφ := contDiff_logPhase hG v
  have hw : ∀ x ∈ tsupport a, logPhase G v x = -Complex.I * Complex.log (G x / v) := fun x hx => by
    simp only [logPhase, logCut_eq (hnb x hx)]
  have hne : ∀ x ∈ tsupport a, G x / v ≠ 0 := fun x hx h => by
    have := hnb x hx
    rw [h] at this
    norm_num at this
  have hIm : ∀ x ∈ tsupport a, 0 ≤ (logPhase G v x).im := fun x hx => by
    have := re_logCut_le (z := G x / v) (by rw [norm_div, hv, div_one]; exact hle x)
    simpa [logPhase] using this
  have hnc' : ∀ x ∈ tsupport a, 0 < (logPhase G v x).im ∨ fderiv ℝ (logPhase G v) x ≠ 0 := by
    intro x hx
    by_cases h1 : ‖G x‖ = 1
    · exact Or.inr (hnc x hx h1)
    · left
      have hlt : ‖G x‖ < 1 := lt_of_le_of_ne (hle x) h1
      rw [hw x hx]
      have hpos : 0 < ‖G x / v‖ := norm_pos_iff.mpr (hne x hx)
      have hlt' : ‖G x / v‖ < 1 := by rwa [norm_div, hv, div_one]
      have : (Complex.log (G x / v)).re < 0 := by
        rw [Complex.log_re]; exact Real.log_neg hpos hlt'
      simpa using this
  obtain ⟨C, hC⟩ := exists_bound_noncritical hφ ha hc hIm hnc' k
  have hpt : ∀ (lam : ℕ) (x : Fin n → ℝ), a x * G x ^ lam =
      v ^ lam * (a x * cexp (I * (lam : ℝ) * logPhase G v x)) := by
    intro lam x
    by_cases hx : x ∈ tsupport a
    · have hex : cexp (I * (lam : ℝ) * logPhase G v x) = (G x / v) ^ lam := by
        rw [hw x hx]
        have : I * (lam : ℝ) * (-Complex.I * Complex.log (G x / v)) =
            lam * Complex.log (G x / v) := by
          have : Complex.I * Complex.I = -1 := Complex.I_mul_I
          linear_combination (-(lam : ℂ) * Complex.log (G x / v)) * this
        rw [this, Complex.exp_nat_mul, Complex.exp_log (hne x hx)]
      rw [hex, div_pow]
      field_simp [pow_ne_zero lam hv0]
    · have : a x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hint : ∀ lam : ℕ, (∫ x, a x * G x ^ lam) =
      v ^ lam * ∫ x, a x * cexp (I * (lam : ℝ) * logPhase G v x) := fun lam => by
    simp_rw [hpt lam]
    exact MeasureTheory.integral_const_mul _ _
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with lam hlam
  rw [hint lam, norm_mul, norm_pow, hv, one_pow, one_mul, Real.norm_eq_abs, abs_of_nonneg
    (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg lam) k))]
  exact hC (lam : ℝ) (by exact_mod_cast hlam)

/-- **Suppression with finitely many noncritical maxima.** For a continuous `F` on `SU(2)^4` with
`|F| ≤ 1` whose modulus is one only on a finite set `K` where `F ∘ chart_p` is smooth and its
logarithmic phase has nonzero differential, `∫ F^λ = O(λ^{-k})` for every `k`. -/
theorem suppression_finite_max (F : (Fin 4 → SU2) → ℂ) (hF : Continuous F)
    (hle : ∀ Y, ‖F Y‖ ≤ 1) (K : Finset (Fin 4 → SU2)) (hK : ∀ Y, ‖F Y‖ = 1 → Y ∈ K)
    (hv : ∀ p ∈ K, ‖F p‖ = 1)
    (hG : ∀ p ∈ K, ContDiff ℝ ∞ fun q => F (chartMap p q))
    (hnc : ∀ p ∈ K, fderiv ℝ (logPhase (fun q => F (chartMap p q)) (F p)) 0 ≠ 0) (k : ℕ) :
    (fun lam : ℕ => ∫ Y, F Y ^ lam ∂(haarN 4)) =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ k)⁻¹ := by
  classical
  obtain ⟨r1, hr1, H⟩ := localise_pieces F hF hle K hK
  have hG0 : ∀ p ∈ K, F (chartMap p 0) = F p := fun p _ => by rw [chartMap_zero]
  have hev : ∀ᶠ q in nhds (0 : Fin 12 → ℝ), ∀ p ∈ K,
      ‖F (chartMap p q) / F p - 1‖ < 1/4 := by
    rw [Filter.eventually_all_finset]
    intro p hp
    have hc : ContinuousAt (fun q => F (chartMap p q) / F p - 1) 0 :=
      (((hF.comp (continuous_chartMap p)).div_const _).sub continuous_const).continuousAt
    have hv0 : F p ≠ 0 := by intro h; have := hv p hp; simp [h] at this
    have h0 : F (chartMap p 0) / F p - 1 = 0 := by rw [hG0 p hp, div_self hv0]; simp
    have h2 : ‖(fun q => F (chartMap p q) / F p - 1) 0‖ < 1/4 := by
      simp only []; rw [h0]; norm_num
    exact hc.norm.eventually (gt_mem_nhds h2)
  obtain ⟨δ, hδ, hδq⟩ := Metric.eventually_nhds_iff.mp hev
  set R := min r1 δ / 2 with hR
  have hRpos : 0 < R := by positivity
  let χ : ContDiffBump (0 : Fin 12 → ℝ) := ⟨R / 2, R, by positivity, by linarith⟩
  have hRr1 : χ.rOut < r1 := by
    show R < r1
    have := min_le_left r1 δ; linarith
  have hRδ : R < δ := by have := min_le_right r1 δ; linarith
  obtain ⟨hmax, ρ, hρ0, hρ1, hρ⟩ := H χ hRr1
  set a : (Fin 12 → ℝ) → ℂ := fun q => ((haarDensity4 (reshape.symm q) * χ q : ℝ) : ℂ) with ha
  have haC : ContDiff ℝ ∞ a :=
    Complex.ofRealCLM.contDiff.comp (contDiff_haarDensity4.mul χ.contDiff)
  have haS : tsupport a ⊆ closedBall (0 : Fin 12 → ℝ) χ.rOut := by
    rw [← χ.tsupport_eq]
    refine closure_mono (fun q hq => ?_)
    intro h; apply hq; simp [ha, h]
  have haK : HasCompactSupport a :=
    (χ.hasCompactSupport.mul_left (f := fun q => haarDensity4 (reshape.symm q))).comp_left
      (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
  have hloc : ∀ p ∈ K, (fun lam : ℕ => ∫ q, a q * F (chartMap p q) ^ lam) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ k)⁻¹ := by
    intro p hp
    refine local_suppression (hG p hp) (hv p hp) (fun x => hle _) haC haK
      (fun x hx => hδq (lt_of_le_of_lt (by simpa using haS hx) hRδ) p hp)
      (fun x hx h1 => ?_) k
    have hx0 : x = 0 := hmax p hp x (haS hx) h1
    rw [hx0]
    exact hnc p hp
  have hsum := IsBigO.sum hloc
  have htail : (fun lam : ℕ => ((∫ Y, F Y ^ lam ∂(haarN 4)) - ∑ p ∈ K, ∫ q : Fin 12 → ℝ,
      haarDensity4 (reshape.symm q) • ((χ q : ℂ) * F (chartMap p q) ^ lam))) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ k)⁻¹ :=
    (IsBigO.of_bound 1 (Eventually.of_forall fun lam => by
      rw [Real.norm_of_nonneg (pow_nonneg hρ0 lam), one_mul]; exact hρ lam)).trans
      (pow_isBigO_inv_pow hρ0 hρ1 k)
  refine (htail.add hsum).congr_left (fun lam => ?_)
  have hI : ∑ p ∈ K, ∫ q : Fin 12 → ℝ,
      haarDensity4 (reshape.symm q) • ((χ q : ℂ) * F (chartMap p q) ^ lam) =
      ∑ p ∈ K, ∫ q, a q * F (chartMap p q) ^ lam :=
    Finset.sum_congr rfl fun p _ => integral_congr_ae (ae_of_all _ fun q => by
      simp [ha, Complex.real_smul]; ring)
  simp only [Finset.sum_apply]
  rw [hI]
  ring

/-- **Dichotomy for the coherent 15j integral**: for SU(2) boundary data and any doubled spins, either
some point of `SU(2)^5` has `|F_n| = 1`, that is, the data glue for the spins `n`, or the integral decays
exponentially in the spin scale. -/
theorem coh15j_dichotomy (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g) :
    (∃ X : Fin 5 → SU2, ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1) ∨
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ, ‖coh15j (lam • n) g‖ ≤ q ^ lam := by
  by_cases h : ∃ X : Fin 5 → SU2, ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1
  · exact Or.inl h
  · refine Or.inr (coh15j_exp_decay n g fun X => ?_)
    exact lt_of_le_of_ne (norm_cohAmp_le n hg X) fun h1 => h ⟨X, h1⟩

/-- **The coherent EPRL integral decays exponentially unless both halves glue**: if the self-dual spins
`n` or the anti-self-dual spins `m` admit no gluing solution, then `eprlCoh (λ n) (λ m) g` decays
exponentially (`eprlCoh = coh15j · coh15j`, and the other factor is bounded by one). -/
theorem eprlCoh_exp_decay_of_no_gluing (n m : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    (h : ¬ ∃ X : Fin 5 → SU2, ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ, ‖eprlCoh (lam • n) (lam • m) g‖ ≤ q ^ lam := by
  obtain ⟨q, hq0, hq1, hq⟩ := (coh15j_dichotomy n hg).resolve_left h
  refine ⟨q, hq0, hq1, fun lam => ?_⟩
  rw [eprlCoh_eq_mul, norm_mul]
  have hm : ‖coh15j (lam • m) g‖ ≤ 1 := by
    unfold coh15j
    calc _ ≤ 1 * (haarN (N := 5)).real Set.univ :=
          MeasureTheory.norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun X => by
            rw [cohAmp_smul, norm_pow]
            exact pow_le_one₀ (norm_nonneg _) (norm_cohAmp_le m hg X))
      _ = 1 := by simp
  calc ‖coh15j (lam • n) g‖ * ‖coh15j (lam • m) g‖ ≤ q ^ lam * 1 :=
        mul_le_mul (hq lam) hm (norm_nonneg _) (pow_nonneg hq0 lam)
    _ = q ^ lam := mul_one _

end Lightlike.Asymptotics.EPRL

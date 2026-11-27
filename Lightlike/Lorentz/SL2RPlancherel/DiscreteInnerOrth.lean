module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfilePair

/-!
# Tools for the orthogonality of distinct discrete series in `L²(SL(2,ℝ))`

* `integral_mcoef_orth_gen`: the coefficients `⟨e_j, D_n e_l⟩` and `⟨e_{j'}, D_{n'} e_{l'}⟩` of two (possibly
  different) holomorphic series with different `K × K`-weights are orthogonal (rotation invariance of `haarR`);
* `lintegral_norm_sq_block`, `integral_norm_sq_block`: the Plancherel identity in the `K × K`-components for a
  continuous function with a single `K × K`-weight;
* `integral_re_eq_zero_of_pythag`: if `∫|F + G|² = ∫|F|² + ∫|G|²` then `Re ∫ F conj G = 0`.
-/

@[expose] public section

open MeasureTheory Set Complex Real Filter Topology UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Orthogonality of the coefficients of two holomorphic series with different `K × K`-weights.** -/
theorem integral_mcoef_orth_gen {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') {j l j' l' : ℕ}
    (h : n + 2 * j ≠ n' + 2 * j' ∨ n + 2 * l ≠ n' + 2 * l') :
    ∫ g, mcoef n (kClass hn j) (kClass hn l) g *
      (starRingEnd ℂ) (mcoef n' (kClass hn' j') (kClass hn' l') g) ∂haarR = 0 := by
  set P : SL2R → ℂ := fun g => mcoef n (kClass hn j) (kClass hn l) g *
    (starRingEnd ℂ) (mcoef n' (kClass hn' j') (kClass hn' l') g) with hP
  set a : ℝ := ((n + 2 * j : ℕ) : ℝ) - ((n' + 2 * j' : ℕ) : ℝ) with ha
  set b : ℝ := ((n + 2 * l : ℕ) : ℝ) - ((n' + 2 * l' : ℕ) : ℝ) with hb
  have hrot : ∀ α θ g, P (rot α * g * rot θ) =
      Complex.exp (-((a : ℂ) * (α : ℂ) * Complex.I)) * Complex.exp (-((b : ℂ) * (θ : ℂ) * Complex.I)) * P g := by
    intro α θ g
    simp only [hP]
    rw [mcoef_rot hn j l α θ g, mcoef_rot hn' j' l' α θ g]
    simp only [map_mul, ← Complex.exp_conj]
    have e1 : (starRingEnd ℂ) (-(((n' + 2 * j' : ℕ) : ℂ) * (α : ℂ) * Complex.I)) =
        ((n' + 2 * j' : ℕ) : ℂ) * (α : ℂ) * Complex.I := by
      simp only [map_neg, map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]; ring
    have e2 : (starRingEnd ℂ) (-(((n' + 2 * l' : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) =
        ((n' + 2 * l' : ℕ) : ℂ) * (θ : ℂ) * Complex.I := by
      simp only [map_neg, map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [e1, e2]
    have f1 : Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) *
        Complex.exp (((n' + 2 * j' : ℕ) : ℂ) * (α : ℂ) * Complex.I) =
        Complex.exp (-((a : ℂ) * (α : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; simp only [ha]; push_cast; ring
    have f2 : Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) *
        Complex.exp (((n' + 2 * l' : ℕ) : ℂ) * (θ : ℂ) * Complex.I) =
        Complex.exp (-((b : ℂ) * (θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; simp only [hb]; push_cast; ring
    rw [← f1, ← f2]
    ring
  have hinv : ∀ α θ, ∫ g, P (rot α * g * rot θ) ∂haarR = ∫ g, P g ∂haarR := by
    intro α θ
    have h1 : ∫ g, P (rot α * g * rot θ) ∂haarR = ∫ g, P (rot α * g) ∂haarR := by
      simp only [mul_assoc]
      exact integral_mul_right_eq_self (fun g => P (rot α * g)) (rot θ)
    rw [h1]
    exact integral_mul_left_eq_self P (rot α)
  have key : ∀ α θ : ℝ, Complex.exp (-((a : ℂ) * (α : ℂ) * Complex.I)) *
      Complex.exp (-((b : ℂ) * (θ : ℂ) * Complex.I)) * ∫ g, P g ∂haarR = ∫ g, P g ∂haarR := by
    intro α θ
    have h2 := hinv α θ
    simp_rw [hrot α θ] at h2
    rw [integral_const_mul] at h2
    exact h2
  rcases h with hj | hl
  · have ha0 : a ≠ 0 := by
      intro h0
      apply hj
      have : ((n + 2 * j : ℕ) : ℝ) = ((n' + 2 * j' : ℕ) : ℝ) := sub_eq_zero.1 h0
      exact_mod_cast this
    have h2 := key (π / a) 0
    have hphase : Complex.exp (-((a : ℂ) * ((π / a : ℝ) : ℂ) * Complex.I)) = -1 := by
      have : -((a : ℂ) * ((π / a : ℝ) : ℂ) * Complex.I) = -((π : ℂ) * Complex.I) := by
        push_cast
        have h3 : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
        field_simp
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    rw [hphase] at h2
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at h2
    linear_combination (-1 / 2 : ℂ) * h2
  · have hb0 : b ≠ 0 := by
      intro h0
      apply hl
      have : ((n + 2 * l : ℕ) : ℝ) = ((n' + 2 * l' : ℕ) : ℝ) := sub_eq_zero.1 h0
      exact_mod_cast this
    have h2 := key 0 (π / b)
    have hphase : Complex.exp (-((b : ℂ) * ((π / b : ℝ) : ℂ) * Complex.I)) = -1 := by
      have : -((b : ℂ) * ((π / b : ℝ) : ℂ) * Complex.I) = -((π : ℂ) * Complex.I) := by
        push_cast
        have h3 : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
        field_simp
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    rw [hphase] at h2
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul] at h2
    linear_combination (-1 / 2 : ℂ) * h2

/-- **Plancherel for a function with a single `K × K`-weight `w`** and radial profile `φ`. -/
theorem lintegral_norm_sq_block {F : SL2R → ℂ} (hF : Continuous F) (w : Fin 2 → ℤ) (φ : ℝ → ℂ)
    (hprof : ∀ (ξ : ℝ) (x : Fin 2 → ℝ), kkProfile F ξ x =
      Complex.exp (-(2 * π * Complex.I * ∑ i, (w i : ℂ) * (x i : ℂ))) * φ ξ) :
    ∫⁻ g, ENNReal.ofReal (‖F g‖ ^ 2) ∂haarR =
      ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) * ENNReal.ofReal ((2 * π) ^ 2 * ‖φ ξ‖ ^ 2) := by
  rw [lintegral_norm_sq_eq_kk hF]
  refine lintegral_congr (fun ξ => ?_)
  congr 2
  have hcoeff : ∀ m : Fin 2 → ℤ, kkCoeff F m ξ = if m + w = 0 then φ ξ else 0 := by
    intro m
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
  rw [tsum_eq_single (-w)]
  · rw [hcoeff]; simp
  · intro m hm
    rw [hcoeff, if_neg]
    · simp
    · intro h
      apply hm
      have : m = -w := by
        have := congrArg (fun z => z - w) h
        simpa [sub_eq_add_neg] using this
      exact this

/-- **Plancherel for a single-weight function, as a real integral.** -/
theorem integral_norm_sq_block {F : SL2R → ℂ} (hF : Continuous F) (w : Fin 2 → ℤ) (φ : ℝ → ℂ)
    (hprof : ∀ (ξ : ℝ) (x : Fin 2 → ℝ), kkProfile F ξ x =
      Complex.exp (-(2 * π * Complex.I * ∑ i, (w i : ℂ) * (x i : ℂ))) * φ ξ)
    (hint : IntegrableOn (fun ξ => Real.sinh ξ * ‖φ ξ‖ ^ 2) (Ioi 0)) :
    ∫ g, ‖F g‖ ^ 2 ∂haarR = (2 * π) ^ 2 * ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖φ ξ‖ ^ 2 := by
  have hnn : 0 ≤ᵐ[haarR] fun g => ‖F g‖ ^ 2 := Filter.Eventually.of_forall (fun g => by positivity)
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hF.norm.pow 2).aestronglyMeasurable,
    lintegral_norm_sq_block hF w φ hprof]
  have hnn2 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun ξ => Real.sinh ξ * ((2 * π) ^ 2 * ‖φ ξ‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
    positivity
  have hint2 : IntegrableOn (fun ξ => Real.sinh ξ * ((2 * π) ^ 2 * ‖φ ξ‖ ^ 2)) (Ioi 0) := by
    have : IntegrableOn (fun ξ => (2 * π) ^ 2 * (Real.sinh ξ * ‖φ ξ‖ ^ 2)) (Ioi 0) := hint.const_mul ((2 * π) ^ 2)
    exact this.congr_fun (fun ξ _ => by ring) measurableSet_Ioi
  have e1 : ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) * ENNReal.ofReal ((2 * π) ^ 2 * ‖φ ξ‖ ^ 2) =
      ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ * ((2 * π) ^ 2 * ‖φ ξ‖ ^ 2)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
    have : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
    rw [ENNReal.ofReal_mul this]
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint2 hnn2]
  have hnn3 : 0 ≤ ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ((2 * π) ^ 2 * ‖φ ξ‖ ^ 2) :=
    integral_nonneg_of_ae hnn2
  rw [ENNReal.toReal_ofReal hnn3, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only
  ring

/-- **If `∫|F + G|² = ∫|F|² + ∫|G|²`, then `Re ∫ F conj G = 0`.** -/
theorem integral_re_eq_zero_of_pythag {F G : SL2R → ℂ} (hF : MemLp F 2 haarR) (hG : MemLp G 2 haarR)
    (h : ∫ g, ‖F g + G g‖ ^ 2 ∂haarR = ∫ g, ‖F g‖ ^ 2 ∂haarR + ∫ g, ‖G g‖ ^ 2 ∂haarR) :
    (∫ g, F g * (starRingEnd ℂ) (G g) ∂haarR).re = 0 := by
  have hiF := integrable_norm_sq_of_memLp hF
  have hiG := integrable_norm_sq_of_memLp hG
  have hiFG := integrable_mul_conj_of_memLp hF hG
  have hpt : ∀ x, ‖F x + G x‖ ^ 2 = ‖F x‖ ^ 2 + ‖G x‖ ^ 2 + 2 * (F x * (starRingEnd ℂ) (G x)).re := by
    intro x
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have hre : Integrable (fun x => (F x * (starRingEnd ℂ) (G x)).re) haarR := hiFG.re
  have hint : ∫ x, ‖F x + G x‖ ^ 2 ∂haarR =
      ∫ x, ‖F x‖ ^ 2 ∂haarR + ∫ x, ‖G x‖ ^ 2 ∂haarR + 2 * (∫ x, F x * (starRingEnd ℂ) (G x) ∂haarR).re := by
    have hsum2 : Integrable (fun x => ‖F x‖ ^ 2 + ‖G x‖ ^ 2) haarR := hiF.add hiG
    simp_rw [hpt]
    have hre0 : ∫ x, (F x * (starRingEnd ℂ) (G x)).re ∂haarR =
        (∫ x, F x * (starRingEnd ℂ) (G x) ∂haarR).re := integral_re hiFG
    rw [integral_add hsum2 (hre.const_mul 2), integral_add hiF hiG, integral_const_mul, hre0]
  linarith

end Lightlike.Lorentz.SL2RPlancherel

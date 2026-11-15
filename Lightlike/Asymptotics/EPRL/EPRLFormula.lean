import Lightlike.Asymptotics.EPRL.MaxSetFinite

/-!
# The asymptotic formula for the Euclidean EPRL vertex

The coherent EPRL integral over `Spin(4)^5 = (SU(2) × SU(2))^5` is the product of two coherent 15j
integrals, one for the self-dual spins `n` and one for the anti-self-dual spins `m`
(`eprlCoh_eq_mul`). For `0 < γ < 1` the EPRL labels satisfy `n = (1 + γ)/2 (n + m)` and
`m = (1 - γ)/2 (n + m)`, so the Regge actions are `S_n = (1 + γ)/2 S` and `S_m = (1 - γ)/2 S` with
`S = S(n + m)`. Multiplying the two expansions of `coh15jAsymptoticFormula`, with the leading terms
of order `λ^{-6}` and the errors of order `λ^{-7}`, gives the four phases
`S_n + S_m = S`, `-S`, `S_n - S_m = γ S`, `-γ S` and the error `O(λ^{-13})`.
-/

open Matrix Finset Filter MeasureTheory Complex Asymptotics
open scoped Real

namespace Lightlike.Asymptotics.EPRL

open Lightlike Lightlike.Spin4 Lightlike.Oscillatory Lightlike.Regge4

/-- **The coherent EPRL integral is the product of two coherent 15j integrals**: the integrand on
`Spin(4)^5 = (SU(2) × SU(2))^5` is a product of a function of the first factors and a function of
the second. -/
theorem eprlCoh_eq_mul (n m : Fin 10 → ℕ) (g : BdryData) :
    eprlCoh n m g = coh15j n g * coh15j m g := by
  have hmp := measurePreserving_arrowProdEquivProdArrow SU2 SU2 (Fin 5)
    (fun _ => haarSU2) (fun _ => haarSU2)
  unfold eprlCoh coh15j haarSpin4 haarN
  rw [← integral_prod_mul (μ := Measure.pi fun _ : Fin 5 => haarSU2)
    (ν := Measure.pi fun _ : Fin 5 => haarSU2)
    (fun Y : Fin 5 → SU2 => cohAmp n g (fun a => (Y a : Matrix (Fin 2) (Fin 2) ℂ)))
    (fun Y : Fin 5 → SU2 => cohAmp m g (fun a => (Y a : Matrix (Fin 2) (Fin 2) ℂ)))]
  exact hmp.integral_comp' (g := fun p : (Fin 5 → SU2) × (Fin 5 → SU2) =>
    cohAmp n g (fun a => (p.1 a : Matrix (Fin 2) (Fin 2) ℂ)) *
      cohAmp m g (fun a => (p.2 a : Matrix (Fin 2) (Fin 2) ℂ)))

/-- The leading term of the coherent 15j asymptotics. -/
noncomputable def cohLead (σ : Simplex4) (n : Fin 10 → ℕ) (lam : ℕ) : ℂ :=
  (((2 * Real.pi / lam) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 : ℝ) : ℂ) *
    (cexp (I * lam * reggeAction σ n) * ampPlus n σ +
      cexp (-(I * lam * reggeAction σ n)) * ampMinus n σ)

lemma norm_cexp_phase (lam : ℕ) (S : ℝ) : ‖cexp (I * lam * S)‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma norm_cexp_neg_phase (lam : ℕ) (S : ℝ) : ‖cexp (-(I * lam * S))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- The leading term is of order `λ^{-6}`. -/
lemma cohLead_isBigO (σ : Simplex4) (n : Fin 10 → ℕ) :
    (fun lam : ℕ => cohLead σ n lam) =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ 6)⁻¹ := by
  refine IsBigO.of_bound ((2 * Real.pi) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 *
    (‖ampPlus n σ‖ + ‖ampMinus n σ‖)) (Eventually.of_forall fun lam => ?_)
  unfold cohLead
  have hC : ‖(((2 * Real.pi / lam) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 : ℝ) : ℂ)‖ =
      (2 * Real.pi) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 * ‖((lam : ℝ) ^ 6)⁻¹‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    rw [div_pow]
    ring
  rw [norm_mul, hC]
  have hs : ‖cexp (I * lam * reggeAction σ n) * ampPlus n σ +
      cexp (-(I * lam * reggeAction σ n)) * ampMinus n σ‖ ≤ ‖ampPlus n σ‖ + ‖ampMinus n σ‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_cexp_phase, norm_cexp_neg_phase, one_mul, one_mul]
  calc (2 * Real.pi) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 * ‖((lam : ℝ) ^ 6)⁻¹‖ *
        ‖cexp (I * lam * reggeAction σ n) * ampPlus n σ +
          cexp (-(I * lam * reggeAction σ n)) * ampMinus n σ‖
      ≤ (2 * Real.pi) ^ 6 * 2 ^ 4 / (4 * Real.pi) ^ 8 * ‖((lam : ℝ) ^ 6)⁻¹‖ *
          (‖ampPlus n σ‖ + ‖ampMinus n σ‖) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

lemma isBigO_inv_pow_succ (k : ℕ) :
    (fun lam : ℕ => ((lam : ℝ) ^ (k + 1))⁻¹) =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ k)⁻¹ := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with lam hlam
  have h1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have h0 : (0 : ℝ) < (lam : ℝ) ^ k := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  exact inv_anti₀ h0 (pow_le_pow_right₀ h1 (Nat.le_succ k))

/-- **The asymptotic formula for the Euclidean EPRL vertex**, `0 < γ < 1`. -/
theorem eprlAsymptoticFormula : EPRLAsymptoticFormula := by
  intro γ hγ0 hγ1 σ n m hlab hnm hevn hevm hpn hmn hpm hmm
  have hnr : ∀ e, (n e : ℝ) = (1 + γ) / 2 * ((n e + m e : ℕ) : ℝ) := fun e => by
    have h := (hlab e).1
    simp only [jPlus] at h
    rw [abs_of_pos (by linarith)] at h
    linarith
  have hmr : ∀ e, (m e : ℝ) = (1 - γ) / 2 * ((n e + m e : ℕ) : ℝ) := fun e => by
    have h := (hlab e).2
    simp only [jMinus] at h
    rw [abs_of_pos (by linarith)] at h
    linarith
  obtain ⟨c, hc, hce⟩ := hnm
  have harn : ∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e :=
    ⟨(1 + γ) / 2 * c, by positivity, fun e => by rw [hnr e, hce e]; ring⟩
  have harm : ∃ c : ℝ, 0 < c ∧ ∀ e, (m e : ℝ) = c * triArea σ e :=
    ⟨(1 - γ) / 2 * c, mul_pos (by linarith) hc, fun e => by rw [hmr e, hce e]; ring⟩
  have hSn : reggeAction σ n = (1 + γ) / 2 * reggeAction σ (n + m) := by
    simp only [reggeAction, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hnr e]
    simp only [Pi.add_apply]
    ring
  have hSm : reggeAction σ m = (1 - γ) / 2 * reggeAction σ (n + m) := by
    simp only [reggeAction, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hmr e]
    simp only [Pi.add_apply]
    ring
  have hn := coh15jAsymptoticFormula σ n harn hevn hpn hmn
  have hm := coh15jAsymptoticFormula σ m harm hevm hpm hmm
  have hAn := cohLead_isBigO σ n
  have hAm := cohLead_isBigO σ m
  have hprod : ∀ lam : ℕ, cohLead σ n lam * cohLead σ m lam =
      (((2 * π / lam) ^ 12 * 2 ^ 8 / (4 * π) ^ 16 : ℝ) : ℂ) *
        (cexp (I * lam * reggeAction σ (n + m)) * (ampPlus n σ * ampPlus m σ) +
          cexp (-(I * lam * reggeAction σ (n + m))) * (ampMinus n σ * ampMinus m σ) +
          cexp (I * lam * (γ * reggeAction σ (n + m))) * (ampPlus n σ * ampMinus m σ) +
          cexp (-(I * lam * (γ * reggeAction σ (n + m)))) * (ampMinus n σ * ampPlus m σ)) := by
    intro lam
    unfold cohLead
    set S := reggeAction σ (n + m) with hS
    have e1 : cexp (I * lam * reggeAction σ n) * cexp (I * lam * reggeAction σ m) =
        cexp (I * lam * S) := by
      rw [← Complex.exp_add, hSn, hSm]; congr 1; push_cast; ring
    have e2 : cexp (-(I * lam * reggeAction σ n)) * cexp (-(I * lam * reggeAction σ m)) =
        cexp (-(I * lam * S)) := by
      rw [← Complex.exp_add, hSn, hSm]; congr 1; push_cast; ring
    have e3 : cexp (I * lam * reggeAction σ n) * cexp (-(I * lam * reggeAction σ m)) =
        cexp (I * lam * (γ * S)) := by
      rw [← Complex.exp_add, hSn, hSm]; congr 1; push_cast; ring
    have e4 : cexp (-(I * lam * reggeAction σ n)) * cexp (I * lam * reggeAction σ m) =
        cexp (-(I * lam * (γ * S))) := by
      rw [← Complex.exp_add, hSn, hSm]; congr 1; push_cast; ring
    have hC : ((((2 * π / lam) ^ 6 * 2 ^ 4 / (4 * π) ^ 8 : ℝ) : ℂ)) *
        (((2 * π / lam) ^ 6 * 2 ^ 4 / (4 * π) ^ 8 : ℝ) : ℂ) =
        (((2 * π / lam) ^ 12 * 2 ^ 8 / (4 * π) ^ 16 : ℝ) : ℂ) := by
      push_cast; ring
    rw [← hC, ← e1, ← e2, ← e3, ← e4]
    ring
  have hfun : (fun lam : ℕ => eprlCoh (lam • n) (lam • m) (reggeState σ) -
      (((2 * π / lam) ^ 12 * 2 ^ 8 / (4 * π) ^ 16 : ℝ) : ℂ) *
        (cexp (I * lam * reggeAction σ (n + m)) * (ampPlus n σ * ampPlus m σ) +
          cexp (-(I * lam * reggeAction σ (n + m))) * (ampMinus n σ * ampMinus m σ) +
          cexp (I * lam * (γ * reggeAction σ (n + m))) * (ampPlus n σ * ampMinus m σ) +
          cexp (-(I * lam * (γ * reggeAction σ (n + m)))) * (ampMinus n σ * ampPlus m σ))) =
      fun lam : ℕ =>
        cohLead σ n lam * (coh15j (lam • m) (reggeState σ) - cohLead σ m lam) +
          (coh15j (lam • n) (reggeState σ) - cohLead σ n lam) * cohLead σ m lam +
          (coh15j (lam • n) (reggeState σ) - cohLead σ n lam) *
            (coh15j (lam • m) (reggeState σ) - cohLead σ m lam) := by
    funext lam
    rw [← hprod lam, eprlCoh_eq_mul]
    ring
  rw [hfun]
  have h13 : (fun lam : ℕ => ((lam : ℝ) ^ 6)⁻¹ * ((lam : ℝ) ^ 7)⁻¹) =
      fun lam : ℕ => ((lam : ℝ) ^ 13)⁻¹ := by
    funext lam; rw [← mul_inv, ← pow_add]
  have h14 : (fun lam : ℕ => ((lam : ℝ) ^ 7)⁻¹ * ((lam : ℝ) ^ 7)⁻¹) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ 13)⁻¹ := by
    have : (fun lam : ℕ => ((lam : ℝ) ^ 7)⁻¹ * ((lam : ℝ) ^ 7)⁻¹) =
        fun lam : ℕ => ((lam : ℝ) ^ (13 + 1))⁻¹ := by
      funext lam; rw [← mul_inv, ← pow_add]
    rw [this]
    exact isBigO_inv_pow_succ 13
  have t1 := (hAn.mul hm).congr_right (fun lam => by rw [← mul_inv, ← pow_add])
  have t2 := (hn.mul hAm).congr_right (fun lam => by rw [← mul_inv, ← pow_add])
  have t3 := hn.mul hm
  exact ((t1.add t2).add (t3.trans h14))

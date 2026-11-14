import Lightlike.Asymptotics.EPRL.Gluing

/-!
# Exponential suppression of the coherent 15j integral

If the boundary data admit no gluing solution, the coherent 15j integral decays exponentially in
the spins (Barrett, Dowdall, Fairbairn, Gomes, Hellmann, J. Math. Phys. 50 (2009) 112504,
arXiv:0902.1170, section 5.1.2; BDFGH below). Scaling the spins raises the integrand to a power,
`F_{λn} = F_n^λ` (`cohAmp_smul`); `F_n` is continuous on the compact group `SU(2)^5`
(`continuous_cohAmp`), and the Haar measure is a probability measure, so
`|coh15j (λn) g| ≤ (max |F_n|)^λ` (`coh15j_exp_decay`).

* Trust checks: for the data `g_ab = g_ba = 1` and spins that are nonzero on the triangle `014`,
  the gluing conditions force `ν(X_1) = ν(X_4) = −ν(X_1)`, so no gluing solution exists and the
  integral decays (`coh15j_oneData_decay`). With all spins zero the integral is `1`
  (`coh15j_zero`) and does not decay (`not_decay_zero`).
-/

open Matrix MeasureTheory Complex

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

/-- Scaling the spins raises the integrand to a power: `F_{λn} = F_n^λ`. -/
theorem cohAmp_smul (lam : ℕ) (n : Fin 10 → ℕ) (g : BdryData)
    (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) : cohAmp (lam • n) g X = cohAmp n g X ^ lam := by
  simp only [cohAmp, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]

/-- The propagator is continuous on `SU(2)^5`. -/
theorem continuous_prop (g : BdryData) (e : Fin 10) :
    Continuous fun X : Fin 5 → SU2 => prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e := by
  have hX : ∀ a, Continuous fun X : Fin 5 → SU2 => (X a : Matrix (Fin 2) (Fin 2) ℂ) :=
    fun a => continuous_subtype_val.comp (continuous_apply a)
  unfold prop
  exact ((((continuous_const.matrix_mul (hX _).matrix_conjTranspose).matrix_mul
    (hX _)).matrix_mul continuous_const).matrix_elem 0 0)

/-- The integrand `F_n` is continuous on `SU(2)^5`. -/
theorem continuous_cohAmp (n : Fin 10 → ℕ) (g : BdryData) :
    Continuous fun X : Fin 5 → SU2 => cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold cohAmp
  exact continuous_finsetProd _ fun e _ => (continuous_prop g e).pow _

/-- **Exponential suppression without gluing solutions** (BDFGH, section 5.1.2: the points that
do not maximise the real part of the action are exponentially damped): if `|F_n| < 1` everywhere
on `SU(2)^5`, then `|coh15j (λn) g| ≤ q^λ` for all `λ`, for some `0 ≤ q < 1`. -/
theorem coh15j_exp_decay (n : Fin 10 → ℕ) (g : BdryData)
    (h : ∀ X : Fin 5 → SU2, ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ, ‖coh15j (lam • n) g‖ ≤ q ^ lam := by
  obtain ⟨X₀, -, hX₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_cohAmp n g).norm.continuousOn
  refine ⟨_, norm_nonneg _, h X₀, fun lam => ?_⟩
  have hb : ∀ X : Fin 5 → SU2,
      ‖cohAmp (lam • n) g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ ≤
        ‖cohAmp n g (fun a => (X₀ a : Matrix (Fin 2) (Fin 2) ℂ))‖ ^ lam := fun X => by
    rw [cohAmp_smul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hX₀ (Set.mem_univ X)) lam
  calc ‖coh15j (lam • n) g‖ ≤ _ * (haarN (N := 5)).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)
    _ = _ := by simp

/-! ## Trust checks -/

/-- The boundary data `g_ab = g_ba = 1` on every edge. -/
noncomputable def oneData : BdryData := fun _ _ => 1

/-- The data `oneData` are SU(2) data. -/
lemma isSU2Data_oneData : IsSU2Data oneData := fun _ _ => one_mem _

/-- **No gluing solution on the triangle `014`** for the data `oneData`: gluing the edges `01`,
`04` and `14` would force `ν(X_1) = −ν(X_0) = ν(X_4) = −ν(X_1)`, but `ν(X_1)` is a unit vector. -/
theorem oneData_not_glued (X : Fin 5 → SU2) :
    ¬ (bloch (frameSrc isSU2Data_oneData X 0 : Matrix (Fin 2) (Fin 2) ℂ) =
          bloch (frameTgt isSU2Data_oneData X 0 : Matrix (Fin 2) (Fin 2) ℂ) ∧
        bloch (frameSrc isSU2Data_oneData X 3 : Matrix (Fin 2) (Fin 2) ℂ) =
          bloch (frameTgt isSU2Data_oneData X 3 : Matrix (Fin 2) (Fin 2) ℂ) ∧
        bloch (frameSrc isSU2Data_oneData X 6 : Matrix (Fin 2) (Fin 2) ℂ) =
          bloch (frameTgt isSU2Data_oneData X 6 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rintro ⟨h0, h3, h6⟩
  have ht : ∀ e, (frameTgt isSU2Data_oneData X e : Matrix (Fin 2) (Fin 2) ℂ) =
      X (edgeTgt e) := fun e => by
    simp [frameTgt, oneData]
  simp only [bloch_frameSrc, ht, oneData, Matrix.mul_one] at h0 h3 h6
  simp only [edgeSrc, edgeTgt] at h0 h3 h6
  change -bloch (X 0 : Matrix (Fin 2) (Fin 2) ℂ) = bloch (X 1 : Matrix (Fin 2) (Fin 2) ℂ) at h0
  change -bloch (X 0 : Matrix (Fin 2) (Fin 2) ℂ) = bloch (X 4 : Matrix (Fin 2) (Fin 2) ℂ) at h3
  change -bloch (X 1 : Matrix (Fin 2) (Fin 2) ℂ) = bloch (X 4 : Matrix (Fin 2) (Fin 2) ℂ) at h6
  have hneg : bloch (X 1 : Matrix (Fin 2) (Fin 2) ℂ) = -bloch (X 1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [h6, ← h3, h0]
  have hd := bloch_dot_self (X 1)
  have hd' := hd
  nth_rewrite 2 [hneg] at hd'
  rw [dotProduct_neg, hd] at hd'
  norm_num at hd'

/-- **Known decay**: for the data `oneData` and spins that are nonzero on the edges `01`, `04`
and `14`, the coherent 15j integral is exponentially suppressed. -/
theorem coh15j_oneData_decay (n : Fin 10 → ℕ) (h0 : n 0 ≠ 0) (h3 : n 3 ≠ 0) (h6 : n 6 ≠ 0) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ, ‖coh15j (lam • n) oneData‖ ≤ q ^ lam :=
  coh15j_exp_decay n oneData fun X =>
    lt_of_le_of_ne (norm_cohAmp_le n isSU2Data_oneData X) fun h1 => by
      have hg := (norm_cohAmp_eq_one_iff n isSU2Data_oneData X).mp h1
      exact oneData_not_glued X ⟨hg 0 h0, hg 3 h3, hg 6 h6⟩

/-- **Known value**: with all spins zero the integrand is `1`, so the integral is `1`. -/
theorem coh15j_zero (g : BdryData) : coh15j 0 g = 1 := by
  simp [coh15j, cohAmp]

/-- **Wrong input**: with all spins zero there is no exponential decay. -/
theorem not_decay_zero (g : BdryData) :
    ¬ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ, ‖coh15j (lam • (0 : Fin 10 → ℕ)) g‖ ≤ q ^ lam := by
  rintro ⟨q, -, hq, h⟩
  have h1 := h 1
  rw [smul_zero, coh15j_zero, norm_one, pow_one] at h1
  linarith

end Lightlike.Asymptotics.EPRL

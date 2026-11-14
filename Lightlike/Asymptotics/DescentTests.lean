import Lightlike.Asymptotics.Descent
import Lightlike.Asymptotics.ContourTests

/-!
# Trust checks for the descent paths

* **Known value (escape lemma).** The flow of `x' = 1` from `0` in `(−∞, 1)` leaves at time `1`
  through the point `1`, and every escape that `exists_isLift_tendsto_not_mem` produces is this
  one (`escape_one`).
* **Wrong input fails (escape lemma).** In all of `ℝ` the same flow never leaves, and indeed the
  bounded-lifetime hypothesis of the escape lemma fails: there are lifts of every length
  (`not_bdd_lifetime_univ`).
* **Known value (saddle level).** For the regular unit tetrahedron, `Re ψ(s) = 6 log 3`
  (`re_phaseC_saddle_regular`), from `|s − 3|² = 1/2` and `|s − 4|² = 1/6`. A direct numerical
  evaluation of `ψ` at `s = 11/3 + i√2/6` gives `6.5917`, the same number.
* **Junk value.** The descent field is Lean's `0` at the saddle, where `ψ' = 0`; the descent
  domain leaves the saddle out (`descentField_saddle_regular`).
* **Non-vacuity.** `Re ψ(0) = 12 log 3 − 12 log 4 < 6 log 3` for the regular tetrahedron, so
  points `iε` with small `ε > 0` lie below the saddle level, and the descent path from such a
  point lands on the real axis (`exists_descent_regular`).
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- A lift of `x' = 1` from `0` is the identity on its interval of definition. -/
lemma isLift_one_eqOn {U : Set ℝ} {T : ℝ} {α : ℝ → ℝ} (hα : IsLift (fun _ => (1 : ℝ)) U 0 T α) :
    EqOn α id (Ico 0 T) :=
  eqOn_Ico_of_hasDerivWithinAt (U := U) (fun _ _ => contDiffAt_const) hα.deriv hα.mem
    (fun t _ => (hasDerivAt_id t).hasDerivWithinAt) hα.start

/-- **Known value** of the escape lemma: the flow of `x' = 1` from `0` in `(−∞, 1)` escapes, and
every escape is at time `1` through the point `1`. -/
theorem escape_one :
    (∃ T α p, IsLift (fun _ => (1 : ℝ)) (Iio 1) 0 T α ∧ Tendsto α (𝓝[<] T) (𝓝 p) ∧
      p ∉ Iio (1 : ℝ)) ∧
    ∀ T α p, IsLift (fun _ => (1 : ℝ)) (Iio 1) 0 T α → Tendsto α (𝓝[<] T) (𝓝 p) →
      p ∉ Iio (1 : ℝ) → T = 1 ∧ p = 1 := by
  have hT : ∀ T α, IsLift (fun _ => (1 : ℝ)) (Iio 1) 0 T α → T ≤ 1 := by
    intro T α hα
    by_contra hlt
    have h1 : (1 : ℝ) ∈ Ico 0 T := ⟨zero_le_one, not_le.1 hlt⟩
    have := hα.mem 1 h1
    rw [isLift_one_eqOn hα h1] at this
    exact lt_irrefl (1 : ℝ) this
  refine ⟨exists_isLift_tendsto_not_mem (T₁ := 1) (M := 1) isOpen_Iio
    (fun _ _ => contDiffAt_const) (by norm_num) hT (fun T α _ t _ => by simp),
    fun T α p hα hp hpU => ?_⟩
  have hid : Tendsto α (𝓝[<] T) (𝓝 T) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
      (mem_of_superset (Ioo_mem_nhdsLT hα.pos) fun t ht =>
        (isLift_one_eqOn hα (Ioo_subset_Ico_self ht)).symm)
  have hpT := tendsto_nhds_unique hp hid
  have h1 := hT T α hα
  have h2 : 1 ≤ p := not_lt.1 hpU
  constructor <;> linarith

/-- **Wrong input fails**: in `U = ℝ` the flow of `x' = 1` has lifts of every length, so the
bounded-lifetime hypothesis of the escape lemma fails, as it must, since nothing can escape
from `ℝ`. -/
theorem not_bdd_lifetime_univ :
    ¬ ∃ T₁, ∀ T α, IsLift (fun _ => (1 : ℝ)) univ 0 T α → T ≤ T₁ := by
  rintro ⟨T₁, hT⟩
  have hl : IsLift (fun _ => (1 : ℝ)) univ 0 (|T₁| + 1) id :=
    ⟨by positivity, rfl, fun _ _ => mem_univ _, fun t _ => (hasDerivAt_id t).hasDerivWithinAt⟩
  linarith [hT _ _ hl, le_abs_self T₁]

/-- `log |w| = log (Re w² + Im w²) / 2`. -/
lemma log_norm_eq_half (w : ℂ) : Real.log ‖w‖ = Real.log (w.re ^ 2 + w.im ^ 2) / 2 := by
  rw [norm_eq_sqrt_sq_add_sq, Real.log_sqrt (by positivity)]

/-- **Known value**: `Re ψ(s) = 6 log 3` at the regular saddle `s = 11/3 + i√2/6`. -/
theorem re_phaseC_saddle_regular :
    (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).re =
      6 * Real.log 3 := by
  rw [isEuclid_regular.re_phaseC_saddle, faceSum_regular, quadSum_regular, saddle_regular]
  have hs : (√2 / 6) ^ 2 = (1 / 18 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h6 : Real.log (1 / 6) = Real.log (1 / 2) - Real.log 3 := by
    rw [show (1 / 6 : ℝ) = (1 / 2) / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, log_norm_eq_half, sub_re, sub_im, ofReal_re,
    ofReal_im, sub_zero, hs]
  norm_num
  rw [h6]
  ring

/-- **Junk value**: the descent field is `0` at the saddle of the regular tetrahedron, where
`ψ' = 0`, and the descent domain does not contain the saddle. -/
theorem descentField_saddle_regular :
    descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1)) = 0 ∧
      saddle (fun _ => 1) ∉ descentDomain (fun _ => 1) :=
  ⟨by simp [descentField, isEuclid_regular.dphaseC_saddle], fun h => h.2 rfl⟩

/-- `Re ψ 0 = Σᵢ Aᵢ log |Aᵢ| − Σₖ Bₖ log |Bₖ|`. -/
lemma re_phaseC_zero (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) :
    (phaseC A B 0).re = ∑ i, A i * Real.log |A i| - ∑ k, B k * Real.log |B k| := by
  have := phaseC_sub_mul_dphaseC A B 0
  rw [zero_mul, sub_zero] at this
  rw [this]
  simp [re_sum, im_sum, mul_re, log_re]

/-- **Non-vacuity** of the hypotheses of `IsEuclid.exists_descent`: for the regular tetrahedron
some point of the open upper half-plane lies below the saddle level. -/
theorem exists_below_saddle_regular : ∃ z₀ : ℂ, 0 < z₀.im ∧
    (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) z₀).re <
      (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).re := by
  have h0 : (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) 0).re <
      (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).re := by
    rw [re_phaseC_saddle_regular, re_phaseC_zero, faceSum_regular, quadSum_regular]
    simp only [Fin.sum_univ_four, Fin.sum_univ_three]
    have h34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    norm_num
    linarith
  have hpath : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨((continuous_ofReal.mul continuous_const).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => by simp [hε.le]⟩
  have hc := ((continuous_re.comp_continuousOn
    (continuousOn_phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))) 0 (by simp)).tendsto.comp
    hpath
  obtain ⟨ε, hε, hεpos⟩ := ((hc.eventually (gt_mem_nhds h0)).and self_mem_nhdsWithin).exists
  exact ⟨ε * I, by simpa using hεpos, hε⟩

/-- **Non-vacuity** of `IsEuclid.exists_descent`: for the regular tetrahedron a descent path
from a point below the saddle level lands at a real point `x` with `bdry A B x = Im ψ z₀`. -/
theorem exists_descent_regular : ∃ z₀ : ℂ, 0 < z₀.im ∧ ∃ T α, ∃ x : ℝ,
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₀ T α ∧ Tendsto α (𝓝[<] T) (𝓝 (x : ℂ)) ∧
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) x =
      (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) z₀).im := by
  obtain ⟨z₀, hz₀, hD⟩ := exists_below_saddle_regular
  obtain ⟨T, α, x, hα, hx, -, hb, -⟩ := isEuclid_regular.exists_descent hz₀ hD
  exact ⟨z₀, hz₀, T, α, x, hα, hx, hb⟩

end Lightlike.Asymptotics

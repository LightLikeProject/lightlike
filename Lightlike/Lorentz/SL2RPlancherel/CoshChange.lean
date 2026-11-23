import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KernelInner
import Lightlike.Lorentz.SL2RPlancherel.AbelKernelTanh
import Lightlike.Lorentz.SL2RPlancherel.LogTanhKernel

/-!
# The triple integral of Abel slices as a quadrant integral in `t = arcosh a`

Step (ii)(b) of the Plancherel route for `SL(2,ℝ)` (milestone HA3, density `ρ tanh(πρ)`).
After the substitution `a = cosh t`, `b = cosh s` the iterated integral
`∫_a ∫_b ∫_{v>1} (φ a/√(a-v)) (ψ b/√(b-v))` becomes
`∫_{t>0} ∫_{s>0} (sinh t φ(cosh t)) (sinh s ψ(cosh s)) (L(s-t) - L(s+t))`
with `L = logTanhKernel`, the kernel of the quadrant Plancherel identity
(`integral_logTanhKernel_deriv_quadrant`).
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set

/-- The inner `v`-integral `∫_1^{min a b} dv/√((a-v)(b-v))` of two Abel slices. -/
noncomputable def abelKern (a b : ℝ) : ℝ :=
  ∫ v in Ioc (1 : ℝ) (min a b), abelKernelIntegrand a b v

/-- The kernel `L(s-t) - L(s+t)` of the quadrant Plancherel identity, `L = logTanhKernel`. -/
noncomputable def quadKernel (t s : ℝ) : ℝ := logTanhKernel (s - t) - logTanhKernel (s + t)

lemma abelKern_symm (a b : ℝ) : abelKern a b = abelKern b a := by
  unfold abelKern
  rw [min_comm]
  refine setIntegral_congr_fun measurableSet_Ioc (fun v _ => ?_)
  unfold abelKernelIntegrand
  rw [mul_comm]

lemma abelKern_eq_zero_left {a : ℝ} (b : ℝ) (ha : a ≤ 1) : abelKern a b = 0 := by
  unfold abelKern
  rw [Ioc_eq_empty (not_lt.2 (le_trans (min_le_left _ _) ha))]
  simp

lemma abelKern_eq_zero_right (a : ℝ) {b : ℝ} (hb : b ≤ 1) : abelKern a b = 0 := by
  rw [abelKern_symm]
  exact abelKern_eq_zero_left a hb

lemma abelKern_of_lt {a b : ℝ} (h1 : 1 ≤ a) (hab : a < b) :
    abelKern a b = 2 * Real.log (Real.sqrt (a - 1) + Real.sqrt (b - 1)) -
        2 * Real.log (Real.sqrt (b - a)) := by
  unfold abelKern
  rw [min_eq_left hab.le, ← intervalIntegral.integral_of_le h1, integral_abelKernel h1 hab]

lemma tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.2 hx) (Real.cosh_pos x)

lemma quadKernel_symm (t s : ℝ) : quadKernel s t = quadKernel t s := by
  unfold quadKernel
  rw [← logTanhKernel_neg (t - s), neg_sub, add_comm t s]

lemma abelKern_cosh_of_lt {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    abelKern (Real.cosh t) (Real.cosh s) = quadKernel t s := by
  have hs : 0 < s := ht.trans hts
  have hlt : Real.cosh t < Real.cosh s := by
    rw [Real.cosh_lt_cosh, abs_of_pos ht, abs_of_pos hs]; exact hts
  rw [abelKern_of_lt (Real.one_le_cosh t) hlt, abelKernel_eq_log_tanh ht hts]
  unfold quadKernel logTanhKernel
  rw [abs_of_pos (by linarith : 0 < s - t), abs_of_pos (by linarith : 0 < s + t),
    Real.log_div (tanh_pos_of_pos (by linarith)).ne' (tanh_pos_of_pos (by linarith)).ne']
  ring

/-- For `t, s > 0`, `t ≠ s`: the Abel kernel at `(cosh t, cosh s)` is `L(s-t) - L(s+t)`. -/
lemma abelKern_cosh {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hne : t ≠ s) :
    abelKern (Real.cosh t) (Real.cosh s) = quadKernel t s := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact abelKern_cosh_of_lt ht h
  · rw [abelKern_symm, abelKern_cosh_of_lt hs h, quadKernel_symm]

/-- Substitution `a = cosh t`: `∫_{a>1} G a = ∫_{t>0} sinh t G(cosh t)`. -/
lemma integral_Ioi_one_cosh (G : ℝ → ℂ) :
    ∫ a in Ioi (1 : ℝ), G a = ∫ t in Ioi (0 : ℝ), (Real.sinh t : ℂ) * G (Real.cosh t) := by
  have himg : Real.cosh '' Ioi (0 : ℝ) = Ioi 1 := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Real.one_lt_cosh.2 (ne_of_gt hs)
    · intro hy
      have hy' : (1 : ℝ) < y := hy
      exact ⟨Real.arcosh y, Real.arcosh_pos hy', Real.cosh_arcosh hy'.le⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (f' := Real.sinh) (fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt)
    (fun a ha b hb hab => Real.cosh_injOn (Set.mem_Ici.2 (le_of_lt ha)) (Set.mem_Ici.2 (le_of_lt hb)) hab) G]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have : (0 : ℝ) < t := ht
  rw [abs_of_pos (Real.sinh_pos_iff.2 this), Complex.real_smul]

/-- **Triple integral of Abel slices as a quadrant integral.** -/
theorem triple_integral_eq_quadrant (φ ψ : ℝ → ℂ) :
    ∫ a, ∫ b, ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice ψ v b =
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        ((Real.sinh t : ℂ) * φ (Real.cosh t)) * ((Real.sinh s : ℂ) * ψ (Real.cosh s)) *
          ((quadKernel t s : ℝ) : ℂ) := by
  have key : ∀ a b : ℝ, ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice ψ v b =
      φ a * ψ b * ((abelKern a b : ℝ) : ℂ) := fun a b => integral_abelSlice_mul φ ψ a b
  simp only [key]
  have e1 : ∀ a, ∫ b, φ a * ψ b * ((abelKern a b : ℝ) : ℂ) =
      ∫ b in Ioi (1 : ℝ), φ a * ψ b * ((abelKern a b : ℝ) : ℂ) := by
    intro a
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun b hb => ?_)).symm
    have : b ≤ 1 := not_lt.1 hb
    simp [abelKern_eq_zero_right a this]
  simp only [e1]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (1 : ℝ))]
  · rw [integral_Ioi_one_cosh (fun a => ∫ b in Ioi (1 : ℝ), φ a * ψ b * ((abelKern a b : ℝ) : ℂ))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [integral_Ioi_one_cosh (fun b => φ (Real.cosh t) * ψ b * ((abelKern (Real.cosh t) b : ℝ) : ℂ))]
    rw [← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [(Set.countable_singleton t).ae_notMem volume] with s hs hs0
    have hs0' : (0 : ℝ) < s := hs0
    have hne : t ≠ s := fun h => hs (by simp [h])
    rw [abelKern_cosh ht0 hs0' hne]
    ring
  · intro a ha
    have : a ≤ 1 := not_lt.1 ha
    simp [abelKern_eq_zero_left _ this]

end Lightlike.Lorentz.SL2RPlancherel

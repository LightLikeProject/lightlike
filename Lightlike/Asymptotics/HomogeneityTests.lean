import Lightlike.Asymptotics.Homogeneity
import Lightlike.Asymptotics.Tests

/-!
# Trust checks for the homogeneity of the phase

* **Known values.** The regular tetrahedron with edges `2` has saddle point `22/3 + i√2/3`,
  computed from the definition (`saddle_two_regular`). That is twice the saddle `11/3 + i√2/6` of
  the unit tetrahedron, as `saddle_smul` predicts (`saddle_two_regular_eq`). Its Regge action,
  computed from the dihedral angles (`im_phase_saddle`), is `12 (π − arccos ⅓)`, twice that of the
  unit tetrahedron, as `phase_smul` and `saddle_smul` predict (`im_phase_two_regular`).
* **Wrong input fails.** Without `ΣA = ΣB` the continued phase is not homogeneous: for
  `A = (1, 0, 0, 0)`, `B = 0` and `c = 2`, `phaseC (2A) (2B) (2z) ≠ 2 phaseC A B z` at every `z`,
  since the two sides differ by `2 log 2` (`phaseC_smul_wrong`).
* **Non-vacuity.** The regular tetrahedron with edges `2` is Euclidean (`isEuclid_two_regular`),
  and for the spins `j = (1, …, 1)` the lengths `ℓ = λj + ½` are Euclidean for some `λ > 0`
  (`exists_isEuclid_lengths_ones`, from `eventually_isEuclid_lengths`).
* **Junk values.** `dphaseC_smul` assumes `Im z > 0`. At `z = 0` the identity fails, because
  Lean's `log 0 = 0` is not shifted by `log c`: for the unit spins and `c = 2`,
  `dphaseC (2A) (2B) 0 = dphaseC A B 0 − log 2` (`dphaseC_smul_zero`). `d2phase_smul` holds also at
  the poles, where both sides use Lean's `1/0 = 0`.
-/

open Complex
open scoped Real

namespace Lightlike.Asymptotics

/-- The regular tetrahedron with edges `2` is the rescaled unit tetrahedron. -/
lemma two_regular_eq_smul : (fun _ : Fin 6 => (2 : ℝ)) = (2 : ℝ) • fun _ : Fin 6 => (1 : ℝ) := by
  funext e; simp

/-- **Known value**: the saddle point of the regular tetrahedron with edges `2` is
`22/3 + i√2/3`, computed from the definition. -/
theorem saddle_two_regular : saddle (fun _ => 2) = ⟨22 / 3, √2 / 3⟩ := by
  have hv : vol2l (fun _ => 2) = 8 / 9 := by
    simp only [vol2l]; rw [PR.vol2_regular]; norm_num
  have hs : √(8 / 9 : ℝ) = 2 * √2 / 3 := by
    rw [show (8 / 9 : ℝ) = 2 ^ 2 * 2 / 3 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
  apply Complex.ext
  · simp [qb, qa]; norm_num
  · simp only [saddle_im, hv, hs, qa]; norm_num; ring

/-- **Consistency of `saddle_smul`**: the saddle of the tetrahedron with edges `2`, computed
directly, is twice the saddle of the unit tetrahedron. -/
theorem saddle_two_regular_eq :
    saddle (fun _ => 2) = (2 : ℝ) * saddle (fun _ => 1) := by
  rw [saddle_two_regular, saddle_regular]
  apply Complex.ext <;> simp <;> ring

/-- **Non-vacuity**: the regular tetrahedron with edges `2` is Euclidean. -/
theorem isEuclid_two_regular : IsEuclid (fun _ => (2 : ℝ)) := by
  rw [two_regular_eq_smul, isEuclid_smul_iff _ two_pos]
  exact isEuclid_regular

/-- **Known value**: the Regge action of the regular tetrahedron with edges `2`, computed from
its dihedral angles, is twice that of the unit tetrahedron, as `phase_smul` and `saddle_smul`
predict for `Im ψ` at the saddle. -/
theorem im_phase_two_regular :
    (phase (fun _ => 2) (saddle (fun _ => 2))).im =
      2 * (phase (fun _ => 1) (saddle (fun _ => 1))).im := by
  rw [isEuclid_two_regular.im_phase_saddle, im_phase_regular]
  have hc : PR.cosDihedral 2 2 2 2 2 2 = 1 / 3 := PR.cos_dihedral_regular two_pos
  simp only [PR.reggeAction, PR.extAngles, PR.dihedral, Fin.sum_univ_six, hc]
  simp
  ring

/-- The scaling law of `phase_smul` and `saddle_smul` gives the same value as
`im_phase_two_regular`. -/
theorem im_phase_two_regular_of_smul :
    (phase (fun _ => 2) (saddle (fun _ => 2))).im =
      2 * (phase (fun _ => 1) (saddle (fun _ => 1))).im := by
  rw [two_regular_eq_smul, saddle_smul _ two_pos, phase_smul _ two_pos]
  simp

/-- **Wrong input fails**: for `A = (1, 0, 0, 0)` and `B = 0`, where `ΣA ≠ ΣB`, the continued
phase is not homogeneous of degree one: the two sides differ by `2 log 2` at every `z`. -/
theorem phaseC_smul_wrong (z : ℂ) :
    phaseC ((2 : ℝ) • ![1, 0, 0, 0]) ((2 : ℝ) • (0 : Fin 3 → ℝ)) ((2 : ℝ) * z) ≠
      (2 : ℝ) * phaseC ![1, 0, 0, 0] 0 z := by
  intro h
  rw [phaseC_smul_add _ _ two_pos] at h
  have h2 : (((2 : ℝ) * Real.log 2 : ℝ) : ℂ) *
      (∑ i, ((![1, 0, 0, 0] : Fin 4 → ℝ) i : ℂ) - ∑ k, ((0 : Fin 3 → ℝ) k : ℂ)) = 0 := by
    linear_combination h
  simp [Fin.sum_univ_four] at h2
  have h3 : Real.log 2 = 0 := by
    have h4 := congrArg Complex.re h2
    rwa [Complex.log_re, show ‖(2 : ℂ)‖ = 2 by simp, Complex.zero_re] at h4
  exact (Real.log_pos one_lt_two).ne' h3

/-- `log (−2) = log 2 + iπ`. -/
lemma log_neg_two : log (-((2 : ℝ) : ℂ)) = Real.log 2 + π * I := by
  rw [show (-((2 : ℝ) : ℂ)) = ((2 : ℝ) : ℂ) * (-1) by ring,
    log_ofReal_mul two_pos (by norm_num), log_neg_one]

/-- **Junk value**: at `z = 0`, outside the upper half-plane, `dphaseC_smul` fails, because
Lean's `log 0 = 0` is not shifted by `log c`. -/
theorem dphaseC_smul_zero :
    dphaseC ((2 : ℝ) • fun _ => 1) ((2 : ℝ) • fun _ => 1) ((2 : ℝ) * 0) =
      dphaseC (fun _ => 1) (fun _ => 1) 0 - Real.log 2 := by
  simp only [dphaseC, Fin.sum_univ_four, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul,
    mul_zero, mul_one, log_zero, zero_sub, ofReal_one, log_neg_two, log_neg_one]
  ring

/-- **Non-vacuity** of `eventually_isEuclid_lengths`: for the spins `j = (1, …, 1)` the lengths
`ℓ = λj + ½` are Euclidean for some `λ > 0`. -/
theorem exists_isEuclid_lengths_ones :
    ∃ lam : ℕ, 0 < lam ∧ IsEuclid (PR.lengths (fun _ => 1) lam) := by
  have h : IsEuclid fun e => (((fun _ => 1) : Fin 6 → ℕ) e : ℝ) := by
    simpa using isEuclid_regular
  obtain ⟨lam, hlam, h0⟩ :=
    ((eventually_isEuclid_lengths h).and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨lam, h0, hlam.2⟩

end Lightlike.Asymptotics

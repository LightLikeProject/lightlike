import Lightlike.Asymptotics.Saddle

/-!
# Trust checks for the saddle-point algebra

* **Known values.** For the regular tetrahedron with unit edges, the saddle point is
  `11/3 + i √2/6` (`saddle_regular`), and the saddle value has imaginary part
  `6 (π − arccos ⅓)`, the Regge action (`im_phase_regular`).
* **Wrong inputs fail.** The lengths `(1, 1, 1, 1, 1, 2)` satisfy every triangle inequality but
  have `vol2 < 0` (no Euclidean tetrahedron). They are not `IsEuclid` (`not_isEuclid_lorentzian`),
  and the saddle-point quadratic has the real root `4` (`saddleQ_lorentzian`): the saddles are
  real, so there is no oscillation (the 6j symbol decays there). The phase with interior instead
  of exterior dihedral angles is wrong (`im_phase_regular_ne_interior`).
-/

open Real

namespace Lightlike.Asymptotics

/-- The vol2 of the regular unit tetrahedron is `1/72`. -/
lemma vol2l_regular : vol2l (fun _ => 1) = 1 / 72 := by
  simp only [vol2l]; rw [PR.vol2_regular]; norm_num

/-- The regular unit tetrahedron is Euclidean. -/
theorem isEuclid_regular : IsEuclid (fun _ => 1) := by
  refine ⟨fun i k => ?_, by rw [vol2l_regular]; norm_num⟩
  fin_cases i <;> fin_cases k <;> simp

/-- **Known value**: the saddle point of the regular unit tetrahedron is `11/3 + i √2/6`. -/
theorem saddle_regular : saddle (fun _ => 1) = ⟨11 / 3, √2 / 6⟩ := by
  have hs : √(1 / 72 : ℝ) = √2 / 12 := by
    rw [show (1 / 72 : ℝ) = 2 / 144 by norm_num, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 144),
      show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  apply Complex.ext
  · simp [qb, qa]; norm_num
  · simp only [saddle_im, vol2l_regular, hs, qa]; norm_num; ring

/-- **Known value**: at the regular unit tetrahedron, `Im ψ(s) = 6 (π − arccos ⅓)`, the Regge
action `Σₑ θₑ` with exterior angle `π − arccos ⅓` at every edge. -/
theorem im_phase_regular :
    (phase (fun _ => 1) (saddle (fun _ => 1))).im = 6 * (π - Real.arccos (1 / 3)) := by
  rw [isEuclid_regular.im_phase_saddle]
  have hc : PR.cosDihedral 1 1 1 1 1 1 = 1 / 3 := PR.cos_dihedral_regular one_pos
  simp only [PR.reggeAction, PR.extAngles, PR.dihedral, Fin.sum_univ_six, hc]
  simp
  ring

/-- **Wrong model fails**: with interior instead of exterior angles, the phase would be
`6 arccos ⅓`, which differs from the true saddle value. -/
theorem im_phase_regular_ne_interior :
    (phase (fun _ => 1) (saddle (fun _ => 1))).im ≠ 6 * Real.arccos (1 / 3) := by
  rw [im_phase_regular]
  intro h
  have h2 : Real.arccos (1 / 3) = π / 2 := by linarith
  have : Real.cos (Real.arccos (1 / 3)) = Real.cos (π / 2) := by rw [h2]
  rw [Real.cos_arccos (by norm_num) (by norm_num), Real.cos_pi_div_two] at this
  norm_num at this

/-- The lengths `(1, 1, 1, 1, 1, 2)`: every face is a strict triangle, but `vol2 < 0`. -/
lemma vol2l_lorentzian : vol2l ![1, 1, 1, 1, 1, 2] = -1 / 36 := by
  simp [vol2l, PR.vol2]; norm_num

/-- **Wrong input fails**: the lengths `(1, 1, 1, 1, 1, 2)` are not a Euclidean tetrahedron. -/
theorem not_isEuclid_lorentzian : ¬ IsEuclid ![1, 1, 1, 1, 1, 2] := fun h => by
  have := h.vol2_pos; rw [vol2l_lorentzian] at this; norm_num at this

/-- **Wrong input fails**: for the lengths `(1, 1, 1, 1, 1, 2)` the saddle-point quadratic has the
real root `4` (discriminant `16 > 0`): the saddles are real, not a complex-conjugate pair. -/
theorem saddleQ_lorentzian : saddleQ ![1, 1, 1, 1, 1, 2] 4 = 0 ∧
    qb ![1, 1, 1, 1, 1, 2] ^ 2 - 4 * qa ![1, 1, 1, 1, 1, 2] * qc ![1, 1, 1, 1, 1, 2] = 16 := by
  constructor
  · simp [saddleQ]; norm_num
  · rw [disc_eq, vol2l_lorentzian]; norm_num

end Lightlike.Asymptotics

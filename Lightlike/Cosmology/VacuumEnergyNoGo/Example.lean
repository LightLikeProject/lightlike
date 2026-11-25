import Mathlib
import Lightlike.Cosmology.VacuumEnergyNoGo.Scale

/-!
# Weinberg's no-go theorem: a scale-invariant example, and the dropped hypotheses

Two scalar fields `x = (x₀, x₁)` with the potential
`V_{a,b}(x) = (x₀ - a x₁²)² + (x₀ - b x₁²)²`, scale covariant of degree `4` for the weights `(2, 1)`.
By `weinberg_vanish` every vacuum has energy `0` without any adjustment. But vacua with `x₁ ≠ 0`
(non-trivial, i.e. along a flat direction) exist iff `a = b`: for `a ≠ b` the only vacuum is the
origin. The free parameter `a - b` has to be tuned to zero for the flat direction.

The conclusion of the no-go theorem fails when a hypothesis is dropped:
* covariance: a field-independent shift `V + c` is no longer covariant for `c ≠ 0` and has a vacuum
  of energy `c ≠ 0`;
* stationarity: at a non-vacuum point the potential is not zero.

## Main results

* `exampleV`, `exampleV_scaleCovariant`.
* `isVacuum_exampleV_iff`: the vacua of the example.
* `exists_flat_vacuum_iff`: a vacuum with `x₁ ≠ 0` exists iff `a = b`.
* `not_scaleCovariant_shift`: a non-zero shift destroys scale covariance.
* `shifted_vacuum_energy_ne_zero`, `not_vacuum_energy_ne_zero`: the dropped-hypothesis counterexamples.
-/

namespace Lightlike.Rows.G1_045

/-- The scale-covariant example potential on two fields. -/
def exampleV (a b : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (x 0 - a * x 1 ^ 2) ^ 2 + (x 0 - b * x 1 ^ 2) ^ 2

/-- The weights `(2, 1)`. -/
noncomputable def exampleWeights : Fin 2 → ℝ := ![2, 1]

/-- The example potential is scale covariant of degree `4`. -/
theorem exampleV_scaleCovariant (a b : ℝ) : ScaleCovariant (exampleV a b) exampleWeights 4 := by
  intro t ht x
  have h2 : t ^ (2 : ℝ) = t ^ 2 := by
    exact_mod_cast Real.rpow_natCast t 2
  have h4 : t ^ (4 : ℝ) = t ^ 4 := by
    exact_mod_cast Real.rpow_natCast t 4
  simp only [exampleV, scale, exampleWeights, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.rpow_one, h2, h4]
  ring

/-- The derivative of the example potential. -/
noncomputable def exampleDV (a b : ℝ) (x : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (4 * x 0 - 2 * (a + b) * x 1 ^ 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0
  + (-4 * a * x 1 * (x 0 - a * x 1 ^ 2) - 4 * b * x 1 * (x 0 - b * x 1 ^ 2)) •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

/-- `exampleDV` is the Fréchet derivative of the example potential. -/
theorem hasFDerivAt_exampleV (a b : ℝ) (x : Fin 2 → ℝ) :
    HasFDerivAt (exampleV a b) (exampleDV a b x) x := by
  have h0 : HasFDerivAt (fun y : Fin 2 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x := hasFDerivAt_apply 0 x
  have h1 : HasFDerivAt (fun y : Fin 2 → ℝ => y 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) x := hasFDerivAt_apply 1 x
  have hA := (h0.sub ((h1.pow 2).const_mul a)).pow 2
  have hB := (h0.sub ((h1.pow 2).const_mul b)).pow 2
  refine (hA.add hB).congr_fderiv ?_
  ext v
  simp [exampleDV]
  ring

/-- **The vacua of the example**: `x₀ = (a+b)/2 · x₁²` and `(a-b)² x₁³ = 0`. -/
theorem isVacuum_exampleV_iff (a b : ℝ) (x : Fin 2 → ℝ) :
    IsVacuum (exampleV a b) x ↔
      x 0 = (a + b) / 2 * x 1 ^ 2 ∧ (a - b) ^ 2 * x 1 ^ 3 = 0 := by
  have hf := (hasFDerivAt_exampleV a b x).fderiv
  have hd := (hasFDerivAt_exampleV a b x).differentiableAt
  unfold IsVacuum
  rw [hf]
  constructor
  · rintro ⟨-, h⟩
    have e0 := congrArg (fun L => L (Pi.single 0 1)) h
    have e1 := congrArg (fun L => L (Pi.single 1 1)) h
    simp [exampleDV] at e0 e1
    have hx : x 0 = (a + b) / 2 * x 1 ^ 2 := by linarith
    refine ⟨hx, ?_⟩
    rw [hx] at e1
    nlinarith [e1]
  · rintro ⟨h0, h1⟩
    refine ⟨hd, ?_⟩
    have c0 : 4 * x 0 - 2 * (a + b) * x 1 ^ 2 = 0 := by rw [h0]; ring
    have c1 : -4 * a * x 1 * (x 0 - a * x 1 ^ 2) - 4 * b * x 1 * (x 0 - b * x 1 ^ 2) = 0 := by
      rw [h0]; linear_combination 2 * h1
    ext v
    simp only [exampleDV, add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, zero_apply]
    rw [c0, c1]
    ring

/-- **The example is tuned**: a vacuum with `x₁ ≠ 0` (a flat direction through the vacuum, along
which the vacuum energy is zero, by `weinberg_vanish`) exists iff the free parameters satisfy
`a = b`. For `a ≠ b` the only vacuum is the origin. -/
theorem exists_flat_vacuum_iff (a b : ℝ) :
    (∃ x : Fin 2 → ℝ, IsVacuum (exampleV a b) x ∧ x 1 ≠ 0) ↔ a = b := by
  constructor
  · rintro ⟨x, hx, hx1⟩
    have h := ((isVacuum_exampleV_iff a b x).mp hx).2
    rcases mul_eq_zero.mp h with h | h
    · have := pow_eq_zero_iff (two_ne_zero) |>.mp h
      linarith
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hx1
  · rintro rfl
    refine ⟨![(a + a) / 2, 1], (isVacuum_exampleV_iff a a _).mpr ?_, by simp⟩
    simp

/-- For `a ≠ b` every vacuum is the origin. -/
theorem vacuum_eq_zero_of_ne {a b : ℝ} (hab : a ≠ b) {x : Fin 2 → ℝ}
    (hx : IsVacuum (exampleV a b) x) : x = 0 := by
  by_contra hne
  have h1 : x 1 ≠ 0 := by
    intro h1
    obtain ⟨h0, -⟩ := (isVacuum_exampleV_iff a b x).mp hx
    apply hne
    funext i
    fin_cases i
    · simp [h0, h1]
    · simpa using h1
  exact hab ((exists_flat_vacuum_iff a b).mp ⟨x, hx, h1⟩)

/-- A non-zero constant shift destroys scale covariance (of any non-zero degree). -/
theorem not_scaleCovariant_shift {ι : Type*} {V : (ι → ℝ) → ℝ} {d : ι → ℝ} {deg : ℝ}
    (hV : ScaleCovariant V d deg) (hdeg : deg ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    ¬ ScaleCovariant (shiftPot V c) d deg := by
  intro hS
  have h0 : ∀ t : ℝ, 0 < t → scale d t (0 : ι → ℝ) = 0 := by
    intro t _; funext i; simp [scale]
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hlt : (1 : ℝ) < 2 := by norm_num
  have e := hS 2 hpos 0
  have e' := hV 2 hpos 0
  rw [h0 2 hpos] at e e'
  simp only [shiftPot] at e
  have hne : (2 : ℝ) ^ deg ≠ 1 := by
    rcases lt_or_gt_of_ne hdeg with h | h
    · exact (Real.rpow_lt_one_of_one_lt_of_neg hlt h).ne
    · exact (Real.one_lt_rpow hlt h).ne'
  have hV0 : V 0 = 0 := by
    have : (2 ^ deg - 1) * V 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith) hne
    · exact h
  rw [hV0] at e
  apply hc
  have : (1 - 2 ^ deg) * c = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (by linarith) hne
  · exact h

/-- **Dropping covariance**: the shifted potential `V + c`, `c ≠ 0`, has the vacuum `0` of
non-zero energy `c`. -/
theorem shifted_vacuum_energy_ne_zero (a b : ℝ) {c : ℝ} (hc : c ≠ 0) :
    IsVacuum (shiftPot (exampleV a b) c) 0 ∧ vacuumEnergy (shiftPot (exampleV a b) c) 0 ≠ 0 := by
  refine ⟨(isVacuum_add_const _ _ _).mpr ((isVacuum_exampleV_iff a b 0).mpr (by simp)), ?_⟩
  simpa [vacuumEnergy, shiftPot, exampleV] using hc

/-- **Dropping stationarity**: at the point `(1, 0)` the covariant potential does not vanish, and the
point is not a vacuum. -/
theorem not_vacuum_energy_ne_zero (a b : ℝ) :
    exampleV a b ![1, 0] ≠ 0 ∧ ¬ IsVacuum (exampleV a b) ![1, 0] := by
  refine ⟨by simp [exampleV], fun h => ?_⟩
  have := ((isVacuum_exampleV_iff a b _).mp h).1
  simp at this

end Lightlike.Rows.G1_045

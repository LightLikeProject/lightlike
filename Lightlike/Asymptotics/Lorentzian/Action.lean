import Mathlib

/-!
# The action of the Lorentzian EPRL vertex amplitude: the real part and its maximum

Barrett, Dowdall, Fairbairn, Hellmann and Pereira (arXiv:0907.2440, Section 4) write the
Lorentzian EPRL 4-simplex amplitude in coherent boundary states as an integral of `e^S` over
`SL(2,ℂ)^4` and one spinor `z_ab ∈ ℂ² \ 0` per triangle (their eq. (17)), with `Z_ab = X_a† z_ab`,
`Z_ba = X_b† z_ab` and, per triangle `a < b`,

  `S_ab = k_ab log(⟨Z_ab, ξ_ab⟩² ⟨Jξ_ba, Z_ba⟩² / (⟨Z_ab, Z_ab⟩ ⟨Z_ba, Z_ba⟩))
          + i p_ab log(⟨Z_ba, Z_ba⟩ / ⟨Z_ab, Z_ab⟩)`,

where `ξ_ab`, `ξ_ba` are the unit spinors of the SU(2) coherent boundary states and `J` is the
antilinear structure of `ℂ²`.

This file treats one triangle at the level of the spinors `Z`, `Z'` (the group variables enter
only through `Z_ab = X_a† z`, `Z_ba = X_b† z`).

* `triWeight k Z ξ Z' ξ'`, the modulus `|e^{S_ab}| = (|⟨Z,ξ⟩|² |⟨Jξ',Z'⟩|² / (‖Z‖² ‖Z'‖²))^k`.
  It is written with a real power, not as `exp (k log ·)`, so that no Lean junk value
  (`log 0 = 0`) can make the modulus look maximal where an overlap vanishes.
* `triWeight_le_one`: `Re S_ab ≤ 0`, by the Cauchy-Schwarz inequality.
* `triWeight_eq_one_iff`: for `k > 0` the maximum `Re S_ab = 0` is attained exactly when `ξ` is
  proportional to `Z` and `Z'` to `Jξ'` (BDFHP eq. (18), (19)).
* `norm_exp_triAction`: `|e^{S_ab}| = triWeight` for the complex action `triAction`, when the two
  overlaps do not vanish.
* `exists_critical_relation`: eliminating `z` from `Z = A z`, `Z' = B z` with `A`, `B` standing for
  `X_a†`, `X_b†` gives `A⁻¹ ξ = c B⁻¹ Jξ'` with `‖c‖ = ‖Z'‖/‖Z‖` (BDFHP eq. (20)).
* Trust checks: `jMap_jMap` (`J² = -1`), `inner_jMap_self` (`⟨ξ, Jξ⟩ = 0`), a wrong-overlap
  example that is not maximal (`triWeight_lt_one_example`) and a maximal one
  (`triWeight_eq_one_example`).
-/

open Complex
open scoped ComplexConjugate

namespace Lightlike.Asymptotics.Lorentzian

/-- The two-component complex spinors with the Hermitian inner product, conjugate linear in the
first argument, as in the source. -/
abbrev Spinor := EuclideanSpace ℂ (Fin 2)

/-- The antilinear structure `J(ξ₀, ξ₁) = (-conj ξ₁, conj ξ₀)` of `ℂ²`. -/
noncomputable def jMap (ξ : Spinor) : Spinor :=
  !₂[-(conj (ξ 1)), conj (ξ 0)]

@[simp] lemma jMap_zero_apply (ξ : Spinor) : jMap ξ 0 = -(conj (ξ 1)) := rfl

@[simp] lemma jMap_one_apply (ξ : Spinor) : jMap ξ 1 = conj (ξ 0) := rfl

/-- `J` preserves the norm. -/
lemma norm_jMap (ξ : Spinor) : ‖jMap ξ‖ = ‖ξ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, add_comm]

/-- `J² = -1`. -/
lemma jMap_jMap (ξ : Spinor) : jMap (jMap ξ) = -ξ := by
  ext i
  fin_cases i <;> simp

/-- `J ξ` is orthogonal to `ξ`. -/
lemma inner_jMap_self (ξ : Spinor) : inner ℂ ξ (jMap ξ) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- `jMap ξ ≠ 0` for `ξ ≠ 0`. -/
lemma jMap_ne_zero {ξ : Spinor} (h : ξ ≠ 0) : jMap ξ ≠ 0 := fun h0 =>
  h (norm_eq_zero.mp (by rw [← norm_jMap, h0, norm_zero]))

/-- The quantity `|⟨Z,ξ⟩|² |⟨Jξ',Z'⟩|² / (‖Z‖² ‖Z'‖²)` whose power `k` is `|e^{S_ab}|`. -/
noncomputable def triReal (Z ξ Z' ξ' : Spinor) : ℝ :=
  (‖inner ℂ Z ξ‖ ^ 2 * ‖inner ℂ (jMap ξ') Z'‖ ^ 2) / (‖Z‖ ^ 2 * ‖Z'‖ ^ 2)

/-- **The modulus of `e^{S_ab}`**: `triReal ^ k`. -/
noncomputable def triWeight (k : ℝ) (Z ξ Z' ξ' : Spinor) : ℝ :=
  triReal Z ξ Z' ξ' ^ k

/-- The complex action of one triangle, BDFHP eq. (17), in the form whose exponential is the
integrand for every spin: for `2k ∈ ℕ`,
`e^S = (⟨Z,ξ⟩⟨Jξ',Z'⟩)^{2k} / (‖Z‖ ‖Z'‖)^{2k} · (‖Z'‖²/‖Z‖²)^{ip}`.
The first term of (17) is `k log(u²)` with `u = ⟨Z,ξ⟩⟨Jξ',Z'⟩/(‖Z‖‖Z'‖)`; BDFHP (p. 16) define `S`
only modulo `2πi`, which is harmless for integer `k` but changes the sign of `e^S` for odd `2k`.
Here the logarithm is taken of `⟨Z,ξ⟩⟨Jξ',Z'⟩` itself, `2k log(⟨Z,ξ⟩⟨Jξ',Z'⟩)`, so that `e^S` is the
power for `2k ∈ ℕ`. The two forms have the same real part, `k log triReal`, and the same
derivative wherever both are defined; the imaginary part `p log (‖Z'‖²/‖Z‖²)` has a positive real
argument. -/
noncomputable def triAction (k p : ℝ) (Z ξ Z' ξ' : Spinor) : ℂ :=
  ((2 * k : ℝ) : ℂ) * Complex.log (inner ℂ Z ξ * inner ℂ (jMap ξ') Z') -
    (k : ℂ) * Complex.log (((‖Z‖ ^ 2 : ℝ) : ℂ) * ((‖Z'‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * (p : ℂ) * Complex.log (((‖Z'‖ ^ 2 : ℝ) : ℂ) / ((‖Z‖ ^ 2 : ℝ) : ℂ))

lemma triReal_nonneg (Z ξ Z' ξ' : Spinor) : 0 ≤ triReal Z ξ Z' ξ' := by
  unfold triReal; positivity

/-- **Cauchy-Schwarz**: `triReal ≤ 1` for unit `ξ`, `ξ'` (so `Re S_ab ≤ 0`). -/
lemma triReal_le_one {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0)
    (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1) : triReal Z ξ Z' ξ' ≤ 1 := by
  have h1 : ‖inner ℂ Z ξ‖ ≤ ‖Z‖ := by
    simpa [hξ] using norm_inner_le_norm (𝕜 := ℂ) Z ξ
  have h2 : ‖inner ℂ (jMap ξ') Z'‖ ≤ ‖Z'‖ := by
    simpa [norm_jMap, hξ'] using norm_inner_le_norm (𝕜 := ℂ) (jMap ξ') Z'
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  unfold triReal
  rw [div_le_one (mul_pos (pow_pos hz 2) (pow_pos hz' 2))]
  gcongr

/-- `triReal = 1` exactly when `ξ` is proportional to `Z` and `Z'` to `Jξ'`. -/
lemma triReal_eq_one_iff {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0)
    (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1) :
    triReal Z ξ Z' ξ' = 1 ↔
      (∃ r : ℂ, r ≠ 0 ∧ ξ = r • Z) ∧ ∃ r : ℂ, r ≠ 0 ∧ Z' = r • jMap ξ' := by
  have hξ0 : ξ ≠ 0 := fun h => by simp [h] at hξ
  have hjξ : jMap ξ' ≠ 0 := jMap_ne_zero fun h => by simp [h] at hξ'
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  have h1 : ‖inner ℂ Z ξ‖ ≤ ‖Z‖ := by
    simpa [hξ] using norm_inner_le_norm (𝕜 := ℂ) Z ξ
  have h2 : ‖inner ℂ (jMap ξ') Z'‖ ≤ ‖Z'‖ := by
    simpa [norm_jMap, hξ'] using norm_inner_le_norm (𝕜 := ℂ) (jMap ξ') Z'
  have e1 : ‖inner ℂ Z ξ‖ = ‖Z‖ ↔ ∃ r : ℂ, r ≠ 0 ∧ ξ = r • Z := by
    rw [← norm_inner_eq_norm_iff hZ hξ0, hξ, mul_one]
  have e2 : ‖inner ℂ (jMap ξ') Z'‖ = ‖Z'‖ ↔ ∃ r : ℂ, r ≠ 0 ∧ Z' = r • jMap ξ' := by
    rw [← norm_inner_eq_norm_iff hjξ hZ', norm_jMap, hξ', one_mul]
  rw [← e1, ← e2]
  unfold triReal
  rw [div_eq_one_iff_eq (mul_pos (pow_pos hz 2) (pow_pos hz' 2)).ne']
  constructor
  · intro h
    have a1 : ‖inner ℂ Z ξ‖ ^ 2 ≤ ‖Z‖ ^ 2 := by gcongr
    have a2 : ‖inner ℂ (jMap ξ') Z'‖ ^ 2 ≤ ‖Z'‖ ^ 2 := by gcongr
    have b1 : ‖inner ℂ Z ξ‖ ^ 2 = ‖Z‖ ^ 2 := by
      by_contra hne
      have hlt : ‖inner ℂ Z ξ‖ ^ 2 < ‖Z‖ ^ 2 := lt_of_le_of_ne a1 hne
      have : ‖inner ℂ Z ξ‖ ^ 2 * ‖inner ℂ (jMap ξ') Z'‖ ^ 2 < ‖Z‖ ^ 2 * ‖Z'‖ ^ 2 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left a2 (by positivity))
          (mul_lt_mul_of_pos_right hlt (pow_pos hz' 2))
      exact this.ne h
    have b2 : ‖inner ℂ (jMap ξ') Z'‖ ^ 2 = ‖Z'‖ ^ 2 := by
      have : ‖Z‖ ^ 2 * ‖inner ℂ (jMap ξ') Z'‖ ^ 2 = ‖Z‖ ^ 2 * ‖Z'‖ ^ 2 := by
        rw [b1] at h; exact h
      exact mul_left_cancel₀ (pow_pos hz 2).ne' this
    exact ⟨(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp b1,
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp b2⟩
  · rintro ⟨h, h'⟩
    rw [h, h']

/-- **`Re S_ab ≤ 0`**: the weight of a triangle is at most `1` for `k ≥ 0`. -/
lemma triWeight_le_one {k : ℝ} (hk : 0 ≤ k) {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0)
    (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1) : triWeight k Z ξ Z' ξ' ≤ 1 :=
  Real.rpow_le_one (triReal_nonneg _ _ _ _) (triReal_le_one hZ hZ' hξ hξ') hk

/-- **The maximum of `Re S_ab`** (BDFHP eq. (18), (19)): for `k > 0` the weight is `1` exactly when
`ξ ∥ Z` and `Z' ∥ Jξ'`. -/
theorem triWeight_eq_one_iff {k : ℝ} (hk : 0 < k) {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0)
    (hZ' : Z' ≠ 0) (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1) :
    triWeight k Z ξ Z' ξ' = 1 ↔
      (∃ r : ℂ, r ≠ 0 ∧ ξ = r • Z) ∧ ∃ r : ℂ, r ≠ 0 ∧ Z' = r • jMap ξ' := by
  rw [← triReal_eq_one_iff hZ hZ' hξ hξ', triWeight]
  constructor
  · intro h
    by_contra hne
    have hlt : triReal Z ξ Z' ξ' < 1 := lt_of_le_of_ne (triReal_le_one hZ hZ' hξ hξ') hne
    have := Real.rpow_lt_one (triReal_nonneg _ _ _ _) hlt hk
    exact this.ne h
  · intro h; rw [h, Real.one_rpow]

/-- `|e^{S_ab}| = triWeight` when the two overlaps do not vanish (the action is singular there:
`e^S` is `0`, and Lean's `log 0 = 0` must not be read as a value). -/
lemma norm_exp_triAction {k p : ℝ} {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0)
    (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    ‖Complex.exp (triAction k p Z ξ Z' ξ')‖ = triWeight k Z ξ Z' ξ' := by
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  rw [Complex.norm_exp]
  have hre : (triAction k p Z ξ Z' ξ').re = k * Real.log (triReal Z ξ Z' ξ') := by
    have hq : ((‖Z'‖ ^ 2 : ℝ) : ℂ) / ((‖Z‖ ^ 2 : ℝ) : ℂ) =
        (((‖Z'‖ ^ 2 / ‖Z‖ ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    have harg : (Complex.log (((‖Z'‖ ^ 2 : ℝ) : ℂ) / ((‖Z‖ ^ 2 : ℝ) : ℂ))).im = 0 := by
      rw [hq, Complex.log_im, Complex.arg_ofReal_of_nonneg (by positivity)]
    have hnn : ((‖Z‖ ^ 2 : ℝ) : ℂ) * ((‖Z'‖ ^ 2 : ℝ) : ℂ) = (((‖Z‖ ^ 2 * ‖Z'‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast; rfl
    have ha : ‖inner ℂ Z ξ‖ ≠ 0 := norm_ne_zero_iff.mpr h1
    have hb : ‖inner ℂ (jMap ξ') Z'‖ ≠ 0 := norm_ne_zero_iff.mpr h2
    have hlog : (triReal Z ξ Z' ξ') = (‖inner ℂ Z ξ‖ * ‖inner ℂ (jMap ξ') Z'‖) ^ 2 /
        (‖Z‖ ^ 2 * ‖Z'‖ ^ 2) := by unfold triReal; ring
    simp only [triAction, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.log_re, zero_mul, sub_zero, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_add, one_mul, harg, mul_zero, hnn, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖Z‖ ^ 2 * ‖Z'‖ ^ 2)]
    rw [hlog, Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hre, triWeight]
  by_cases h0 : triReal Z ξ Z' ξ' = 0
  · exfalso
    unfold triReal at h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact h1 (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0))
      · exact h2 (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0))
    · exact (mul_pos (pow_pos hz 2) (pow_pos hz' 2)).ne' h0
  · rw [mul_comm, Real.rpow_def_of_pos (lt_of_le_of_ne (triReal_nonneg _ _ _ _) (Ne.symm h0))]

/-- **Elimination of the spinor `z`** (BDFHP eq. (20)): if `Z = A z` and `Z' = B z` for invertible
`A`, `B` (standing for `X_a†`, `X_b†`) and the weight is maximal, then
`A⁻¹ ξ = c B⁻¹ (Jξ')` with `‖c‖ = ‖Z'‖/‖Z‖`. -/
theorem exists_critical_relation {A B : Spinor ≃ₗ[ℂ] Spinor} {z Z ξ Z' ξ' : Spinor}
    (hZ : Z = A z) (hZ' : Z' = B z) (hz : z ≠ 0) (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1)
    (h : (∃ r : ℂ, r ≠ 0 ∧ ξ = r • Z) ∧ ∃ r : ℂ, r ≠ 0 ∧ Z' = r • jMap ξ') :
    ∃ c : ℂ, ‖c‖ = ‖Z'‖ / ‖Z‖ ∧ A.symm ξ = c • B.symm (jMap ξ') := by
  obtain ⟨⟨r, hr, hrξ⟩, ⟨s, hs, hsξ⟩⟩ := h
  have hZ0 : Z ≠ 0 := fun h0 => hz (A.map_eq_zero_iff.mp (hZ ▸ h0))
  have hnr : ‖r‖ * ‖Z‖ = 1 := by
    rw [← norm_smul, ← hrξ, hξ]
  have hns : ‖s‖ = ‖Z'‖ := by
    have := congrArg norm hsξ
    rw [norm_smul, norm_jMap, hξ', mul_one] at this
    exact this.symm
  refine ⟨r * s, ?_, ?_⟩
  · have hZpos : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
    rw [norm_mul, hns, eq_div_iff hZpos.ne']
    have : ‖r‖ * ‖Z'‖ * ‖Z‖ = ‖Z'‖ * (‖r‖ * ‖Z‖) := by ring
    rw [this, hnr, mul_one]
  · have e1 : A.symm ξ = r • z := by
      rw [hrξ, map_smul, hZ, A.symm_apply_apply]
    have e2 : B.symm Z' = z := by rw [hZ', B.symm_apply_apply]
    have e3 : B.symm (jMap ξ') = s⁻¹ • z := by
      have : jMap ξ' = s⁻¹ • Z' := by rw [hsξ, smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [this, map_smul, e2]
    rw [e1, e3, smul_smul, mul_assoc, mul_inv_cancel₀ hs, mul_one]

/-! ## Non-vacuity and a wrong-input control -/

/-- The first basis spinor. -/
noncomputable def e0 : Spinor := !₂[1, 0]

/-- The second basis spinor. -/
noncomputable def e1 : Spinor := !₂[0, 1]

lemma norm_e0 : ‖e0‖ = 1 := by simp [e0, EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma norm_e1 : ‖e1‖ = 1 := by simp [e1, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- **Non-vacuity**: for `ξ = e0`, `ξ' = e0` (so `Jξ' = (0, 1)`), the data `Z = e0`, `Z' = e1`
give a maximal weight. -/
lemma triWeight_eq_one_example (k : ℝ) (hk : 0 < k) : triWeight k e0 e0 e1 e0 = 1 := by
  have hj : jMap e0 = e1 := by
    ext i; fin_cases i <;> simp [e0, e1]
  have h0 : e0 ≠ 0 := fun h => by simpa [h] using norm_e0
  have h1 : e1 ≠ 0 := fun h => by simpa [h] using norm_e1
  rw [triWeight_eq_one_iff hk h0 h1 norm_e0 norm_e0]
  refine ⟨⟨1, one_ne_zero, by simp⟩, ⟨1, one_ne_zero, by simp [hj]⟩⟩

/-- **Wrong-input control**: with `Z' = e0` instead of `e1`, the overlap with `Jξ' = e1` is zero
and the weight is not `1` (it is `0`). -/
lemma triWeight_lt_one_example (k : ℝ) (hk : 0 < k) : triWeight k e0 e0 e0 e0 < 1 := by
  have hj : jMap e0 = e1 := by
    ext i; fin_cases i <;> simp [e0, e1]
  have h0 : e0 ≠ 0 := fun h => by simpa [h] using norm_e0
  have hle := triWeight_le_one hk.le h0 h0 norm_e0 norm_e0
  refine lt_of_le_of_ne hle fun h => ?_
  obtain ⟨-, r, hr0, hr⟩ := (triWeight_eq_one_iff hk h0 h0 norm_e0 norm_e0).mp h
  rw [hj] at hr
  have := congrArg (fun v : Spinor => v 1) hr
  simp [e0, e1] at this
  exact hr0 this.symm

end Lightlike.Asymptotics.Lorentzian

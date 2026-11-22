import Mathlib
import Lightlike.Dirac.RadialEigen

/-!
# Eigenspinors of the Dirac operator of `S²` for every eigenvalue `±(k+1)`

`diracF_stereo_poly_eigen` reduces the eigenvalue problem for radial spinors of the form
`h^{-1/2}(P(1/h) v + Q(1/h) y·v)` to the polynomial system `−(X P)' = λ Q`, `(2 − X) Q' − Q = λ P`.
Eliminating `Q` gives `(2 − X)(X P)'' − (X P)' + λ² P = 0`, whose coefficients satisfy the two-term
recurrence `2(j+1)(j+2) p_{j+1} = ((j+1)² − λ²) p_j`.  For `λ² = m²` the solution truncates at degree `m − 1`
(a hypergeometric polynomial).  We prove `D f = ±(k+1) f` for every `k` (`diracF_stereo_eigen_general`).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open Polynomial

/-- The coefficient sequence of the radial eigenpolynomial: `a₀ = 1`,
`a_{j+1} = ((j+1)² − m²) / (2 (j+1)(j+2)) · a_j`. -/
noncomputable def eigA (m : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => ((((j : ℝ) + 1) ^ 2 - (m : ℝ) ^ 2) / (2 * ((j : ℝ) + 1) * ((j : ℝ) + 2))) * eigA m j

/-- The two-term recurrence in cleared-denominator form. -/
lemma eigA_rec (m j : ℕ) :
    2 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * eigA m (j + 1) + ((m : ℝ) ^ 2 - ((j : ℝ) + 1) ^ 2) * eigA m j = 0 := by
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  simp only [eigA]
  field_simp
  ring

/-- The sequence truncates: `a_j = 0` for `j ≥ m` when `m ≥ 1`. -/
lemma eigA_eq_zero (k j : ℕ) : eigA (k + 1) (k + 1 + j) = 0 := by
  induction j with
  | zero =>
    show eigA (k + 1) (k + 1) = 0
    simp only [eigA]
    push_cast
    ring_nf
  | succ j ih =>
    rw [← add_assoc]
    simp only [eigA]
    rw [show k + 1 + j = k + 1 + j from rfl] at ih
    rw [ih]
    ring

lemma eigA_eq_zero_of_le {k j : ℕ} (h : k + 1 ≤ j) : eigA (k + 1) j = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  exact eigA_eq_zero k i

/-- The eigenpolynomial `P_m = Σ_{j<m} a_j X^j` (degree `m − 1`). -/
noncomputable def eigP (m : ℕ) : ℝ[X] := ∑ j ∈ Finset.range m, C (eigA m j) * X ^ j

lemma coeff_eigP (k i : ℕ) : (eigP (k + 1)).coeff i = eigA (k + 1) i := by
  unfold eigP
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases h : i < k + 1
  · simp [h]
  · rw [Finset.sum_eq_zero]
    · exact (eigA_eq_zero_of_le (not_lt.mp h)).symm
    · intro j hj
      have : i ≠ j := by
        have := Finset.mem_range.mp hj
        omega
      simp [this]

lemma eigP_coeff_zero (k : ℕ) : (eigP (k + 1)).coeff 0 = 1 := by
  rw [coeff_eigP]; rfl

lemma eigP_ne_zero (k : ℕ) : eigP (k + 1) ≠ 0 := by
  intro h
  have := eigP_coeff_zero k
  rw [h] at this
  simp at this

/-- Coefficients of the second-order operator `(2 − X)(XP)'' − (XP)' + c P`. -/
lemma coeff_ode (P : ℝ[X]) (c : ℝ) (j : ℕ) :
    (((C 2 : ℝ[X]) - X) * (X * P).derivative.derivative - (X * P).derivative + C c * P).coeff j =
      2 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * P.coeff (j + 1) + (c - ((j : ℝ) + 1) ^ 2) * P.coeff j := by
  have hR : ∀ i, (X * P).coeff (i + 1) = P.coeff i := fun i => coeff_X_mul P i
  rcases j with _ | j
  · simp only [sub_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero, coeff_derivative]
    have h1 : (X * P).coeff 1 = P.coeff 0 := hR 0
    have h2 : (X * P).coeff (0 + 1 + 1) = P.coeff 1 := hR 1
    rw [h1, h2]
    push_cast
    ring
  · simp only [sub_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
    rw [show j + 1 + 1 = j + 2 from rfl]
    push_cast
    ring

/-- The elimination identity `(2 − X)(XP)'' − (XP)' + m² P = 0` for `P = eigP (k+1)`. -/
lemma eigP_ode (k : ℕ) :
    (C 2 - X) * (X * eigP (k + 1)).derivative.derivative - (X * eigP (k + 1)).derivative +
      C (((k : ℝ) + 1) ^ 2) * eigP (k + 1) = 0 := by
  ext j
  rw [coeff_ode, coeff_eigP, coeff_eigP, coeff_zero]
  have := eigA_rec (k + 1) j
  push_cast at this
  linear_combination this

/-- **Dirac eigenspinors of `S²` for every eigenvalue `ε (k+1)`**, `ε = ±1`: the radial spinor
`f = h^{-1/2}(P(1/h) v + Q(1/h) y·v)` with `P = eigP (k+1)` and `Q = −(ε/(k+1)) (X P)'`
satisfies `D f = ε (k+1) f` for the Dirac operator of the unit 2-sphere in the stereographic chart. -/
theorem diracF_stereo_eigen_general {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep 2 V) (v : V) (k : ℕ) {ε : ℝ} (hε : ε * ε = 1) (x : E 2) :
    diracF ρ stereoF stereoOmega
        (fun y => (stereoH y ^ (-(1 / 2 : ℝ)) * (eigP (k + 1)).eval (stereoH y)⁻¹) • v +
          (stereoH y ^ (-(1 / 2 : ℝ)) *
            (-(C (ε / ((k : ℝ) + 1)) * (X * eigP (k + 1)).derivative)).eval (stereoH y)⁻¹) •
              Yop ρ y v) x =
      (ε * ((k : ℝ) + 1)) •
        ((stereoH x ^ (-(1 / 2 : ℝ)) * (eigP (k + 1)).eval (stereoH x)⁻¹) • v +
          (stereoH x ^ (-(1 / 2 : ℝ)) *
            (-(C (ε / ((k : ℝ) + 1)) * (X * eigP (k + 1)).derivative)).eval (stereoH x)⁻¹) •
              Yop ρ x v) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hCε : (C (ε * ((k : ℝ) + 1)) * C (ε / ((k : ℝ) + 1)) : ℝ[X]) = 1 := by
    rw [← C_mul, ← C_1]
    congr 1
    field_simp
    linear_combination hε
  have hode := eigP_ode k
  refine diracF_stereo_poly_eigen ρ v _ _ (ε * ((k : ℝ) + 1)) ?_ ?_ x
  · linear_combination ((X * eigP (k + 1)).derivative) * hCε
  · have e1 : (C 2 - X) * (-(C (ε / ((k : ℝ) + 1)) * (X * eigP (k + 1)).derivative)).derivative -
        (-(C (ε / ((k : ℝ) + 1)) * (X * eigP (k + 1)).derivative)) =
        -(C (ε / ((k : ℝ) + 1))) * ((C 2 - X) * (X * eigP (k + 1)).derivative.derivative -
          (X * eigP (k + 1)).derivative) := by
      simp only [derivative_neg, derivative_mul, derivative_C, zero_mul, zero_add]
      ring
    rw [e1]
    have e2 : (C 2 - X) * (X * eigP (k + 1)).derivative.derivative - (X * eigP (k + 1)).derivative =
        -(C (((k : ℝ) + 1) ^ 2) * eigP (k + 1)) := by
      linear_combination hode
    rw [e2]
    have hCe : (C (ε / ((k : ℝ) + 1)) * C (((k : ℝ) + 1) ^ 2) : ℝ[X]) = C (ε * ((k : ℝ) + 1)) := by
      rw [← C_mul]
      congr 1
      field_simp
    linear_combination (eigP (k + 1)) * hCe

end Lightlike.Dirac

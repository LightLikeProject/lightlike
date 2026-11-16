import Lightlike.TuraevViro.Reflect.RacahCore
import Lightlike.TuraevViro.Reflect.RacahEval

/-!
# The q-Racah recurrence in a field, from the cleared identity

`recurrence_poly` is the recurrence `2a M+ + 2b M0 + 2c M- - C M0 = MG1 - MG0` of the q-Racah sum,
written with the values of the bracket factors (`Poly.eval` of `fQ0, ..., fW1`), for every evaluation
of `(u, p1, p2, p3, p4, q2, q3, Z)` in a field at which `[x], [x+1], [x+2]` and `Dc` are nonzero.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

variable {K : Type*} [Field K]

/-- The pure-field content: the cleared combination vanishes, so the recurrence holds. -/
theorem cleared_abstract {Q0 Q1 Q2 Na Nc bn Mp M0 Mm Cq W0 W1 Dc N1 N3 N5 u Z : K}
    (h2 : (2 : K) ≠ 0) (hQ0 : Q0 ≠ 0) (hQ1 : Q1 ≠ 0) (hQ2 : Q2 ≠ 0) (hDc : Dc ≠ 0) (hu : u ≠ 0) (hZ : Z ≠ 0)
    (hcore : Dc * (2 * Q0 * Na * Mp + 2 * Q1 * bn * M0 + 2 * Q2 * Nc * Mm - 2 * (Q0 * Q1 * Q2) * Cq * M0)
      + N1 * (-(2 * (Q0 * Q1 * Q2)) * ((u ^ (-2 : ℤ) * Z ^ (-2 : ℤ)) * W1 - Z ^ (-2 : ℤ) * W0))
      + N3 * (-(2 * (Q0 * Q1 * Q2)) * (W1 - W0))
      + N5 * (-(2 * (Q0 * Q1 * Q2)) * ((u ^ (2 : ℤ) * Z ^ (2 : ℤ)) * W1 - Z ^ (2 : ℤ) * W0)) = 0) :
    2 * (Na / 2 / (Q1 * Q2)) * Mp + 2 * (bn / (2 * Q0 * Q2)) * M0 + 2 * (Nc / 2 / (Q0 * Q1)) * Mm
      - Cq * M0
      - (W1 * ((N1 / Dc) * (u * Z) ^ (-2 : ℤ) + N3 / Dc + (N5 / Dc) * (u * Z) ^ (2 : ℤ))
          - W0 * ((N1 / Dc) * Z ^ (-2 : ℤ) + N3 / Dc + (N5 / Dc) * Z ^ (2 : ℤ))) = 0 := by
  have e1 : u ^ (-2 : ℤ) = (u ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  have e2 : Z ^ (-2 : ℤ) = (Z ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  have e3 : (u * Z) ^ (-2 : ℤ) = (u ^ 2)⁻¹ * (Z ^ 2)⁻¹ := by
    rw [zpow_neg, mul_zpow]; norm_cast; rw [mul_inv]
  have e4 : (u * Z) ^ (2 : ℤ) = u ^ 2 * Z ^ 2 := by rw [mul_zpow]; norm_cast
  have e5 : u ^ (2 : ℤ) = u ^ 2 := by norm_cast
  have e6 : Z ^ (2 : ℤ) = Z ^ 2 := by norm_cast
  rw [e1, e2, e5, e6] at hcore
  rw [e3, e4, e2, e6]
  have hne : 2 * (Q0 * Q1 * Q2) * Dc ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 (mul_ne_zero (mul_ne_zero hQ0 hQ1) hQ2)) hDc
  have key : (2 * (Na / 2 / (Q1 * Q2)) * Mp + 2 * (bn / (2 * Q0 * Q2)) * M0 + 2 * (Nc / 2 / (Q0 * Q1)) * Mm
      - Cq * M0
      - (W1 * ((N1 / Dc) * ((u ^ 2)⁻¹ * (Z ^ 2)⁻¹) + N3 / Dc + (N5 / Dc) * (u ^ 2 * Z ^ 2))
          - W0 * ((N1 / Dc) * (Z ^ 2)⁻¹ + N3 / Dc + (N5 / Dc) * Z ^ 2))) * (2 * (Q0 * Q1 * Q2) * Dc)
      = Dc * (2 * Q0 * Na * Mp + 2 * Q1 * bn * M0 + 2 * Q2 * Nc * Mm - 2 * (Q0 * Q1 * Q2) * Cq * M0)
      + N1 * (-(2 * (Q0 * Q1 * Q2)) * ((u ^ 2)⁻¹ * (Z ^ 2)⁻¹ * W1 - (Z ^ 2)⁻¹ * W0))
      + N3 * (-(2 * (Q0 * Q1 * Q2)) * (W1 - W0))
      + N5 * (-(2 * (Q0 * Q1 * Q2)) * (u ^ 2 * Z ^ 2 * W1 - Z ^ 2 * W0)) := by
    field_simp
    ring
  rw [hcore] at key
  exact (mul_eq_zero.1 key).resolve_right hne

theorem eval_ftwo (E : Env K) : Poly.eval E ftwo = 2 := by
  simp [ftwo, Poly.eval, Mono.eval]

theorem eval_X0 {E : Env K} (hE : E.NZ) : Poly.eval E X0 =
    2 * Poly.eval E fQ0 * Poly.eval E fNa * Poly.eval E fMp
    + 2 * Poly.eval E fQ1 * Poly.eval E fbn * Poly.eval E fM0
    + 2 * Poly.eval E fQ2 * Poly.eval E fNc * Poly.eval E fMm
    - 2 * Poly.eval E fQ012 * Poly.eval E fCq * Poly.eval E fM0 := by
  simp only [X0, T1, T2, T3, T4, eval_add, eval_neg, eval_mul hE, eval_ftwo]
  ring

theorem eval_Ei {E : Env K} (hE : E.NZ) (a b : Mono) (W : Poly) :
    Poly.eval E (neg (mul (mul ftwo fQ012) (add (mul [(a, 1)] fW1) (neg (mul [(b, 1)] W))))) =
    -(2 * Poly.eval E fQ012) * (Mono.eval E a * Poly.eval E fW1 - Mono.eval E b * Poly.eval E W) := by
  simp only [eval_add, eval_neg, eval_mul hE, eval_ftwo, Poly.eval]
  ring

theorem recurrence_poly {E : Env K} (hE : E.NZ) (h2 : (2 : K) ≠ 0)
    (hQ0 : Poly.eval E fQ0 ≠ 0) (hQ1 : Poly.eval E fQ1 ≠ 0) (hQ2 : Poly.eval E fQ2 ≠ 0)
    (hDc : Poly.eval E Dc ≠ 0) :
    2 * (Poly.eval E fNa / 2 / (Poly.eval E fQ1 * Poly.eval E fQ2)) * Poly.eval E fMp
      + 2 * (Poly.eval E fbn / (2 * Poly.eval E fQ0 * Poly.eval E fQ2)) * Poly.eval E fM0
      + 2 * (Poly.eval E fNc / 2 / (Poly.eval E fQ0 * Poly.eval E fQ1)) * Poly.eval E fMm
      - Poly.eval E fCq * Poly.eval E fM0
      - (Poly.eval E fW1 * ((Poly.eval E N1 / Poly.eval E Dc) * (E.v0 * E.v7) ^ (-2 : ℤ)
            + Poly.eval E N3 / Poly.eval E Dc + (Poly.eval E N5 / Poly.eval E Dc) * (E.v0 * E.v7) ^ (2 : ℤ))
          - Poly.eval E fW0 * ((Poly.eval E N1 / Poly.eval E Dc) * E.v7 ^ (-2 : ℤ)
            + Poly.eval E N3 / Poly.eval E Dc + (Poly.eval E N5 / Poly.eval E Dc) * E.v7 ^ (2 : ℤ))) = 0 := by
  have hc := core_identity hE
  have hQ012 : Poly.eval E fQ012 = Poly.eval E fQ0 * Poly.eval E fQ1 * Poly.eval E fQ2 := by
    simp only [fQ012, eval_mul hE]
  refine cleared_abstract (u := E.v0) (Z := E.v7) h2 hQ0 hQ1 hQ2 hDc hE.h0 hE.h7 ?_
  rw [eval_X0 hE, E1, E3, E5, eval_Ei hE, eval_Ei hE, eval_Ei hE, hQ012] at hc
  have m1 : Mono.eval E ⟨-2, 0, 0, 0, 0, 0, 0, -2⟩ = E.v0 ^ (-2 : ℤ) * E.v7 ^ (-2 : ℤ) := by
    simp [Mono.eval]
  have m2 : Mono.eval E ⟨0, 0, 0, 0, 0, 0, 0, -2⟩ = E.v7 ^ (-2 : ℤ) := by simp [Mono.eval]
  have m3 : Mono.eval E ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ = 1 := by simp [Mono.eval]
  have m4 : Mono.eval E ⟨2, 0, 0, 0, 0, 0, 0, 2⟩ = E.v0 ^ (2 : ℤ) * E.v7 ^ (2 : ℤ) := by
    simp [Mono.eval]
  have m5 : Mono.eval E ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ = E.v7 ^ (2 : ℤ) := by simp [Mono.eval]
  rw [m1, m2, m3, m4, m5] at hc
  linear_combination hc

end Lightlike.TV.Refl

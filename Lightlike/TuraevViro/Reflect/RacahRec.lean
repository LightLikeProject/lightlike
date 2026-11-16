import Lightlike.TuraevViro.Reflect.RacahNoZ
import Lightlike.TuraevViro.Reflect.RacahGTerm

/-!
# The q-Racah recurrence for the Racah terms, pointwise in `z`

For `u ≠ 0` with `u - u⁻¹ ≠ 0`, `Fi` with `Fi n = [n+1] Fi (n+1)` and `Pn` with
`Pn (n+1) = [n+1] Pn n` (`[k] = (u^k - u^-k)/(u - u⁻¹)`), balance `u^b1 = Π p_i / (q2 q3)`, and the
explicit nonvanishing hypotheses `hQ0 hQ1 hQ2 hDc` (the quantum integers that appear as
denominators), the Racah terms obey, for every integer `z`,
`2A t₊(z) + 2B t₀(z) + 2C t₋(z) - Cq t₀(z) = G(z+1) - G(z)`
with `z`-independent coefficients and `G(z) = ρ(u^z) [z-a2][z-a3] Gb(z)`.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

variable {K : Type*} [Field K]

/-- The `z`-independent coefficients (evaluated at `Z = 1`; they do not depend on `Z`). -/
noncomputable def recCoef (P : Poly) (u p1 p2 p3 p4 q2 q3 : K) : K :=
  Poly.eval (env u p1 p2 p3 p4 q2 q3 1) P

/-- The certificate multiplier `ρ(Z) = c1 Z^-2 + c3 + c5 Z^2`. -/
noncomputable def rhoC (u p1 p2 p3 p4 q2 q3 : K) (Z : K) : K :=
  (recCoef N1 u p1 p2 p3 p4 q2 q3 / recCoef Dc u p1 p2 p3 p4 q2 q3) * Z ^ (-2 : ℤ)
    + recCoef N3 u p1 p2 p3 p4 q2 q3 / recCoef Dc u p1 p2 p3 p4 q2 q3
    + (recCoef N5 u p1 p2 p3 p4 q2 q3 / recCoef Dc u p1 p2 p3 p4 q2 q3) * Z ^ (2 : ℤ)

section Pointwise
variable {u : K} {N : ℤ} {Fi Pn : ℤ → K}

theorem recCoef_eq (P : Poly) (hP : noZ P = true) (u p1 p2 p3 p4 q2 q3 Z : K) :
    Poly.eval (env u p1 p2 p3 p4 q2 q3 Z) P = recCoef P u p1 p2 p3 p4 q2 q3 :=
  eval_noZ P hP u p1 p2 p3 p4 q2 q3 Z 1

theorem pointwise (hu : u ≠ 0) (hd : u - u⁻¹ ≠ 0) (h2 : (2 : K) ≠ 0)
    (hF : ∀ n : ℤ, n ≤ N → Fi n = bk (u ^ (n + 1)) / (u - u⁻¹) * Fi (n + 1))
    (a1 a2 a3 a4 b1 b2 b3 z : ℤ) (p1 p2 p3 p4 q2 q3 : K)
    (hP : Pn (z + 1 + 1) = bk (u ^ (z + 1 + 1)) / (u - u⁻¹) * Pn (z + 1))
    (hB1 : z - a1 ≤ N) (hB2 : z - a2 ≤ N) (hB3 : z - a3 ≤ N) (hB4 : z - a4 ≤ N)
    (hB5 : b1 - z - 1 ≤ N) (hB6 : b2 - z ≤ N) (hB7 : b3 - z ≤ N)
    (hp1 : p1 = u ^ a1) (hp2 : p2 = u ^ a2) (hp3 : p3 = u ^ a3) (hp4 : p4 = u ^ a4)
    (hq2 : q2 = u ^ b2) (hq3 : q3 = u ^ b3) (hb : u ^ b1 = p1 * p2 * p3 * p4 * q2⁻¹ * q3⁻¹)
    (hQ0 : recCoef fQ0 u p1 p2 p3 p4 q2 q3 ≠ 0) (hQ1 : recCoef fQ1 u p1 p2 p3 p4 q2 q3 ≠ 0)
    (hQ2 : recCoef fQ2 u p1 p2 p3 p4 q2 q3 ≠ 0) (hDc : recCoef Dc u p1 p2 p3 p4 q2 q3 ≠ 0) :
    2 * (recCoef fNa u p1 p2 p3 p4 q2 q3 / 2 /
          (recCoef fQ1 u p1 p2 p3 p4 q2 q3 * recCoef fQ2 u p1 p2 p3 p4 q2 q3))
        * tt Fi Pn (a1 + 1) a2 a3 (a4 + 1) b1 (b2 + 1) (b3 + 1) z
      + 2 * (recCoef fbn u p1 p2 p3 p4 q2 q3 /
          (2 * recCoef fQ0 u p1 p2 p3 p4 q2 q3 * recCoef fQ2 u p1 p2 p3 p4 q2 q3))
        * tt Fi Pn a1 a2 a3 a4 b1 b2 b3 z
      + 2 * (recCoef fNc u p1 p2 p3 p4 q2 q3 / 2 /
          (recCoef fQ0 u p1 p2 p3 p4 q2 q3 * recCoef fQ1 u p1 p2 p3 p4 q2 q3))
        * tt Fi Pn (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) z
      - recCoef fCq u p1 p2 p3 p4 q2 q3 * tt Fi Pn a1 a2 a3 a4 b1 b2 b3 z
    = Gq (Fi := Fi) (Pn := Pn) u (rhoC u p1 p2 p3 p4 q2 q3) a1 a2 a3 a4 b1 b2 b3 (z + 1)
      - Gq (Fi := Fi) (Pn := Pn) u (rhoC u p1 p2 p3 p4 q2 q3) a1 a2 a3 a4 b1 b2 b3 z := by
  set Z : K := u ^ z with hZ
  have h7 : Z ≠ 0 := zpow_ne_zero _ hu
  have h1 : p1 ≠ 0 := by rw [hp1]; exact zpow_ne_zero _ hu
  have h2' : p2 ≠ 0 := by rw [hp2]; exact zpow_ne_zero _ hu
  have h3 : p3 ≠ 0 := by rw [hp3]; exact zpow_ne_zero _ hu
  have h4 : p4 ≠ 0 := by rw [hp4]; exact zpow_ne_zero _ hu
  have h5 : q2 ≠ 0 := by rw [hq2]; exact zpow_ne_zero _ hu
  have h6 : q3 ≠ 0 := by rw [hq3]; exact zpow_ne_zero _ hu
  have hE : (env u p1 p2 p3 p4 q2 q3 Z).NZ := ⟨hu, h1, h2', h3, h4, h5, h6, h7⟩
  have key := recurrence_poly hE h2
    (by rwa [recCoef_eq _ noZ_Q0]) (by rwa [recCoef_eq _ noZ_Q1]) (by rwa [recCoef_eq _ noZ_Q2])
    (by rwa [recCoef_eq _ noZ_Dc])
  simp only [recCoef_eq _ noZ_Q0, recCoef_eq _ noZ_Q1, recCoef_eq _ noZ_Q2, recCoef_eq _ noZ_Dc,
    recCoef_eq _ noZ_N1, recCoef_eq _ noZ_N3, recCoef_eq _ noZ_N5, recCoef_eq _ noZ_Na,
    recCoef_eq _ noZ_Nc, recCoef_eq _ noZ_bn, recCoef_eq _ noZ_Cq] at key
  have s0 := t0_scaling (Pn := Pn) hu hu hd hF a1 a2 a3 a4 b1 b2 b3 z p1 p2 p3 p4 q2 q3 Z hp1 hp2 hp3 hp4 hq2 hq3 hZ hB1 hB2 hB3 hB4 hB5 hB6 hB7
  have sp := tp_scaling (Pn := Pn) hu hu hd hF a1 a2 a3 a4 b1 b2 b3 z p1 p2 p3 p4 q2 q3 Z hp1 hp2 hp3 hp4 hq2 hq3 hZ hB1 hB2 hB3 hB4 hB5 hB6 hB7
  have sm := tm_scaling (Pn := Pn) hu hu hd hF a1 a2 a3 a4 b1 b2 b3 z p1 p2 p3 p4 q2 q3 Z hp1 hp2 hp3 hp4 hq2 hq3 hZ hB1 hB2 hB3 hB4 hB5 hB6 hB7
  have g0 := G0_scaling (Pn := Pn) hu hu hd hF (rhoC u p1 p2 p3 p4 q2 q3) a1 a2 a3 a4 b1 b2 b3 z p1 p2 p3 p4 q2 q3 Z hp1 hp2 hp3 hp4 hq2 hq3 hZ hB1 hB2 hB3 hB4 hB5 hB6 hB7
  have g1 := G1_scaling (Pn := Pn) hu hu hd hF (rhoC u p1 p2 p3 p4 q2 q3) a1 a2 a3 a4 b1 b2 b3 z p1 p2 p3 p4 q2 q3 Z hp1 hp2 hp3 hp4 hq2 hq3 hZ hB1 hB2 hB3 hB4 hB5 hB6 hB7 hP hb
  have hd6 : (u - u⁻¹) ^ 6 ≠ 0 := pow_ne_zero _ hd
  apply mul_left_cancel₀ hd6
  simp only [rhoC, mul_zpow] at g0 g1
  simp only [mul_zpow] at key
  change _ = (0 : K) at key
  have kk := key
  simp only [env] at kk s0 sp sm g0 g1
  linear_combination (2 * (recCoef fNa u p1 p2 p3 p4 q2 q3 / 2 /
          (recCoef fQ1 u p1 p2 p3 p4 q2 q3 * recCoef fQ2 u p1 p2 p3 p4 q2 q3))) * sp
    + (2 * (recCoef fbn u p1 p2 p3 p4 q2 q3 /
          (2 * recCoef fQ0 u p1 p2 p3 p4 q2 q3 * recCoef fQ2 u p1 p2 p3 p4 q2 q3))
        - recCoef fCq u p1 p2 p3 p4 q2 q3) * s0
    + (2 * (recCoef fNc u p1 p2 p3 p4 q2 q3 / 2 /
          (recCoef fQ0 u p1 p2 p3 p4 q2 q3 * recCoef fQ1 u p1 p2 p3 p4 q2 q3))) * sm
    - g1 + g0 + Psi Fi Pn a1 a2 a3 a4 b1 b2 b3 z * kk

end Pointwise

end Lightlike.TV.Refl

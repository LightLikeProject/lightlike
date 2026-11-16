import Lightlike.TuraevViro.Reflect.RacahAssemble

/-!
# The q-Racah terms as ratios of a common base

For a function `Fi : ℤ → K` with `Fi n = [n+1] Fi (n+1)` (`[k] = bk(u^k)/δ`, `δ = u - u⁻¹`, so
`Fi = 1/[n]!`) and `Pn` with `Pn (n+1) = [n+1] Pn n`, the Racah term with parameters
`(α1..α4, β1, β2, β3)` at `z` is `tt`. The terms at `x+2`, `x`, `x-2` are `tt` with the parameters
`α1, α4, β2, β3` shifted by `+1`, `0`, `-1`; each is a product of brackets times the common base `Psi`.

Peak memory of one Lean process on this module: 4.8 GB (the `field_simp` calls).
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

variable {K : Type*} [Field K]

section Term
variable (Fi Pn : ℤ → K)

/-- The Racah term (`(-1)^z [z+1]! / (prod [z-α_i]! prod [β_j-z]!)`). -/
def tt (A1 A2 A3 A4 B1 B2 B3 z : ℤ) : K :=
  (-1 : K) ^ z * Pn (z + 1) * Fi (z - A1) * Fi (z - A2) * Fi (z - A3) * Fi (z - A4) *
    Fi (B1 - z) * Fi (B2 - z) * Fi (B3 - z)

/-- The common base. -/
def Psi (a1 a2 a3 a4 b1 b2 b3 z : ℤ) : K :=
  (-1 : K) ^ z * Pn (z + 1) * Fi (z - a1 + 1) * Fi (z - a2 + 1) * Fi (z - a3 + 1) * Fi (z - a4 + 1) *
    Fi (b1 - z) * Fi (b2 - z + 1) * Fi (b3 - z + 1)

/-- The base of the certificate term `G`: the Racah term with `Fi (z-a_i)` and `Fi (b2-z+1)`,
`Fi (b3-z+1)`. -/
def Gb (a1 a2 a3 a4 b1 b2 b3 z : ℤ) : K :=
  (-1 : K) ^ z * Pn (z + 1) * Fi (z - a1) * Fi (z - a2) * Fi (z - a3) * Fi (z - a4) *
    Fi (b1 - z) * Fi (b2 - z + 1) * Fi (b3 - z + 1)

/-- The certificate term `G(z) = ρ(u^z) [z-a2] [z-a3] Gb(z)`, with `[k] = bk(u^k)/δ`. -/
def Gq (u : K) (rho : K → K) (a1 a2 a3 a4 b1 b2 b3 z : ℤ) : K :=
  rho (u ^ z) * (bk (u ^ (z - a2)) / (u - u⁻¹)) * (bk (u ^ (z - a3)) / (u - u⁻¹)) *
    Gb Fi Pn a1 a2 a3 a4 b1 b2 b3 z

end Term

section Scaling
variable {u : K} {N : ℤ} {Fi Pn : ℤ → K} (hu : u ≠ 0) (h0' : u ≠ 0) (hd : u - u⁻¹ ≠ 0)
  (hF : ∀ n : ℤ, n ≤ N → Fi n = bk (u ^ (n + 1)) / (u - u⁻¹) * Fi (n + 1))

include hF in
theorem hFs (n m : ℤ) (hn : n ≤ N) (h : n + 1 = m) : Fi n = bk (u ^ m) / (u - u⁻¹) * Fi m := by
  rw [hF n hn, h]

include hu h0' hd hF in
theorem t0_scaling (a1 a2 a3 a4 b1 b2 b3 z : ℤ) (p1 p2 p3 p4 q2 q3 Z : K)
    (hp1 : p1 = u ^ a1) (hp2 : p2 = u ^ a2) (hp3 : p3 = u ^ a3) (hp4 : p4 = u ^ a4)
    (hq2 : q2 = u ^ b2) (hq3 : q3 = u ^ b3) (hZ : Z = u ^ z) (hB1 : z - a1 ≤ N) (hB2 : z - a2 ≤ N) (hB3 : z - a3 ≤ N) (hB4 : z - a4 ≤ N) (hB5 : b1 - z - 1 ≤ N) (hB6 : b2 - z ≤ N) (hB7 : b3 - z ≤ N) :
    (u - u⁻¹) ^ 6 * tt Fi Pn a1 a2 a3 a4 b1 b2 b3 z =
      Poly.eval (env u p1 p2 p3 p4 q2 q3 Z) fM0 * Psi Fi Pn a1 a2 a3 a4 b1 b2 b3 z := by
  have h1 : p1 ≠ 0 := by rw [hp1]; exact zpow_ne_zero _ hu
  have h2 : p2 ≠ 0 := by rw [hp2]; exact zpow_ne_zero _ hu
  have h3 : p3 ≠ 0 := by rw [hp3]; exact zpow_ne_zero _ hu
  have h4 : p4 ≠ 0 := by rw [hp4]; exact zpow_ne_zero _ hu
  have h5 : q2 ≠ 0 := by rw [hq2]; exact zpow_ne_zero _ hu
  have h6 : q3 ≠ 0 := by rw [hq3]; exact zpow_ne_zero _ hu
  have h7 : Z ≠ 0 := by rw [hZ]; exact zpow_ne_zero _ hu
  rw [eval_fM0 h0' h1 h2 h3 h4 h5 h6 h7]
  unfold tt Psi
  rw [hFs hF (z - a1) (z - a1 + 1) (by omega) rfl, hFs hF (z - a2) (z - a2 + 1) (by omega) rfl,
    hFs hF (z - a3) (z - a3 + 1) (by omega) rfl, hFs hF (z - a4) (z - a4 + 1) (by omega) rfl,
    hFs hF (b2 - z) (b2 - z + 1) (by omega) rfl, hFs hF (b3 - z) (b3 - z + 1) (by omega) rfl]
  have e1 : u ^ (z - a1 + 1) = u * p1⁻¹ * Z := by
    rw [hp1, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e2 : u ^ (z - a2 + 1) = u * p2⁻¹ * Z := by
    rw [hp2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e3 : u ^ (z - a3 + 1) = u * p3⁻¹ * Z := by
    rw [hp3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e4 : u ^ (z - a4 + 1) = u * p4⁻¹ * Z := by
    rw [hp4, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e5 : u ^ (b2 - z + 1) = u * q2 * Z⁻¹ := by
    rw [hq2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e6 : u ^ (b3 - z + 1) = u * q3 * Z⁻¹ := by
    rw [hq3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  rw [e1, e2, e3, e4, e5, e6]
  generalize u - u⁻¹ = d at hd ⊢
  have key : d ^ 6 * (d⁻¹) ^ 6 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  simp only [div_eq_mul_inv]
  linear_combination (bk (u * p1⁻¹ * Z) * bk (u * p2⁻¹ * Z) * bk (u * p3⁻¹ * Z) * bk (u * p4⁻¹ * Z) * bk (u * q2 * Z⁻¹) * bk (u * q3 * Z⁻¹) * ((-1) ^ z * Pn (z + 1) * Fi (z - a1 + 1) * Fi (z - a2 + 1) * Fi (z - a3 + 1) * Fi (z - a4 + 1) * Fi (b1 - z) * Fi (b2 - z + 1) * Fi (b3 - z + 1))) * key

include hu h0' hd hF in
theorem tp_scaling (a1 a2 a3 a4 b1 b2 b3 z : ℤ) (p1 p2 p3 p4 q2 q3 Z : K)
    (hp1 : p1 = u ^ a1) (hp2 : p2 = u ^ a2) (hp3 : p3 = u ^ a3) (hp4 : p4 = u ^ a4)
    (hq2 : q2 = u ^ b2) (hq3 : q3 = u ^ b3) (hZ : Z = u ^ z) (hB1 : z - a1 ≤ N) (hB2 : z - a2 ≤ N) (hB3 : z - a3 ≤ N) (hB4 : z - a4 ≤ N) (hB5 : b1 - z - 1 ≤ N) (hB6 : b2 - z ≤ N) (hB7 : b3 - z ≤ N) :
    (u - u⁻¹) ^ 6 * tt Fi Pn (a1 + 1) a2 a3 (a4 + 1) b1 (b2 + 1) (b3 + 1) z =
      Poly.eval (env u p1 p2 p3 p4 q2 q3 Z) fMp * Psi Fi Pn a1 a2 a3 a4 b1 b2 b3 z := by
  have h1 : p1 ≠ 0 := by rw [hp1]; exact zpow_ne_zero _ hu
  have h2 : p2 ≠ 0 := by rw [hp2]; exact zpow_ne_zero _ hu
  have h3 : p3 ≠ 0 := by rw [hp3]; exact zpow_ne_zero _ hu
  have h4 : p4 ≠ 0 := by rw [hp4]; exact zpow_ne_zero _ hu
  have h5 : q2 ≠ 0 := by rw [hq2]; exact zpow_ne_zero _ hu
  have h6 : q3 ≠ 0 := by rw [hq3]; exact zpow_ne_zero _ hu
  have h7 : Z ≠ 0 := by rw [hZ]; exact zpow_ne_zero _ hu
  rw [eval_fMp h0' h1 h2 h3 h4 h5 h6 h7]
  unfold tt Psi
  have f1 : Fi (z - (a1 + 1)) =
      bk (u ^ (z - a1)) / (u - u⁻¹) * (bk (u ^ (z - a1 + 1)) / (u - u⁻¹)) * Fi (z - a1 + 1) := by
    rw [hFs hF (z - (a1 + 1)) (z - a1) (by omega) (by ring), hFs hF (z - a1) (z - a1 + 1) (by omega) rfl]; ring
  have f4 : Fi (z - (a4 + 1)) =
      bk (u ^ (z - a4)) / (u - u⁻¹) * (bk (u ^ (z - a4 + 1)) / (u - u⁻¹)) * Fi (z - a4 + 1) := by
    rw [hFs hF (z - (a4 + 1)) (z - a4) (by omega) (by ring), hFs hF (z - a4) (z - a4 + 1) (by omega) rfl]; ring
  have g5 : Fi (b2 + 1 - z) = Fi (b2 - z + 1) := by congr 1; ring
  have g6 : Fi (b3 + 1 - z) = Fi (b3 - z + 1) := by congr 1; ring
  rw [f1, f4, g5, g6, hFs hF (z - a2) (z - a2 + 1) (by omega) rfl, hFs hF (z - a3) (z - a3 + 1) (by omega) rfl]
  have e1 : u ^ (z - a1) = p1⁻¹ * Z := by
    rw [hp1, hZ, zpow_sub₀ hu]; ring
  have e1' : u ^ (z - a1 + 1) = u * p1⁻¹ * Z := by
    rw [hp1, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e4 : u ^ (z - a4) = p4⁻¹ * Z := by
    rw [hp4, hZ, zpow_sub₀ hu]; ring
  have e4' : u ^ (z - a4 + 1) = u * p4⁻¹ * Z := by
    rw [hp4, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e2 : u ^ (z - a2 + 1) = u * p2⁻¹ * Z := by
    rw [hp2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e3 : u ^ (z - a3 + 1) = u * p3⁻¹ * Z := by
    rw [hp3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  rw [e1, e1', e4, e4', e2, e3]
  generalize u - u⁻¹ = d at hd ⊢
  have key : d ^ 6 * (d⁻¹) ^ 6 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  simp only [div_eq_mul_inv]
  linear_combination (bk (p1⁻¹ * Z) * bk (u * p1⁻¹ * Z) * bk (u * p2⁻¹ * Z) * bk (u * p3⁻¹ * Z) * bk (p4⁻¹ * Z) * bk (u * p4⁻¹ * Z) * ((-1) ^ z * Pn (z + 1) * Fi (z - a1 + 1) * Fi (z - a2 + 1) * Fi (z - a3 + 1) * Fi (z - a4 + 1) * Fi (b1 - z) * Fi (b2 - z + 1) * Fi (b3 - z + 1))) * key

include hu h0' hd hF in
theorem tm_scaling (a1 a2 a3 a4 b1 b2 b3 z : ℤ) (p1 p2 p3 p4 q2 q3 Z : K)
    (hp1 : p1 = u ^ a1) (hp2 : p2 = u ^ a2) (hp3 : p3 = u ^ a3) (hp4 : p4 = u ^ a4)
    (hq2 : q2 = u ^ b2) (hq3 : q3 = u ^ b3) (hZ : Z = u ^ z) (hB1 : z - a1 ≤ N) (hB2 : z - a2 ≤ N) (hB3 : z - a3 ≤ N) (hB4 : z - a4 ≤ N) (hB5 : b1 - z - 1 ≤ N) (hB6 : b2 - z ≤ N) (hB7 : b3 - z ≤ N) :
    (u - u⁻¹) ^ 6 * tt Fi Pn (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) z =
      Poly.eval (env u p1 p2 p3 p4 q2 q3 Z) fMm * Psi Fi Pn a1 a2 a3 a4 b1 b2 b3 z := by
  have h1 : p1 ≠ 0 := by rw [hp1]; exact zpow_ne_zero _ hu
  have h2 : p2 ≠ 0 := by rw [hp2]; exact zpow_ne_zero _ hu
  have h3 : p3 ≠ 0 := by rw [hp3]; exact zpow_ne_zero _ hu
  have h4 : p4 ≠ 0 := by rw [hp4]; exact zpow_ne_zero _ hu
  have h5 : q2 ≠ 0 := by rw [hq2]; exact zpow_ne_zero _ hu
  have h6 : q3 ≠ 0 := by rw [hq3]; exact zpow_ne_zero _ hu
  have h7 : Z ≠ 0 := by rw [hZ]; exact zpow_ne_zero _ hu
  rw [eval_fMm h0' h1 h2 h3 h4 h5 h6 h7]
  unfold tt Psi
  have g1 : Fi (z - (a1 - 1)) = Fi (z - a1 + 1) := by congr 1; ring
  have g4 : Fi (z - (a4 - 1)) = Fi (z - a4 + 1) := by congr 1; ring
  have f5 : Fi (b2 - 1 - z) =
      bk (u ^ (b2 - z)) / (u - u⁻¹) * (bk (u ^ (b2 - z + 1)) / (u - u⁻¹)) * Fi (b2 - z + 1) := by
    rw [hFs hF (b2 - 1 - z) (b2 - z) (by omega) (by ring), hFs hF (b2 - z) (b2 - z + 1) (by omega) rfl]; ring
  have f6 : Fi (b3 - 1 - z) =
      bk (u ^ (b3 - z)) / (u - u⁻¹) * (bk (u ^ (b3 - z + 1)) / (u - u⁻¹)) * Fi (b3 - z + 1) := by
    rw [hFs hF (b3 - 1 - z) (b3 - z) (by omega) (by ring), hFs hF (b3 - z) (b3 - z + 1) (by omega) rfl]; ring
  rw [g1, g4, f5, f6, hFs hF (z - a2) (z - a2 + 1) (by omega) rfl, hFs hF (z - a3) (z - a3 + 1) (by omega) rfl]
  have e5 : u ^ (b2 - z) = q2 * Z⁻¹ := by
    rw [hq2, hZ, zpow_sub₀ hu]; ring
  have e5' : u ^ (b2 - z + 1) = u * q2 * Z⁻¹ := by
    rw [hq2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e6 : u ^ (b3 - z) = q3 * Z⁻¹ := by
    rw [hq3, hZ, zpow_sub₀ hu]; ring
  have e6' : u ^ (b3 - z + 1) = u * q3 * Z⁻¹ := by
    rw [hq3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e2 : u ^ (z - a2 + 1) = u * p2⁻¹ * Z := by
    rw [hp2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e3 : u ^ (z - a3 + 1) = u * p3⁻¹ * Z := by
    rw [hp3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  rw [e5, e5', e6, e6', e2, e3]
  generalize u - u⁻¹ = d at hd ⊢
  have key : d ^ 6 * (d⁻¹) ^ 6 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  simp only [div_eq_mul_inv]
  linear_combination (bk (u * p2⁻¹ * Z) * bk (u * p3⁻¹ * Z) * bk (q2 * Z⁻¹) * bk (u * q2 * Z⁻¹) * bk (q3 * Z⁻¹) * bk (u * q3 * Z⁻¹) * ((-1) ^ z * Pn (z + 1) * Fi (z - a1 + 1) * Fi (z - a2 + 1) * Fi (z - a3 + 1) * Fi (z - a4 + 1) * Fi (b1 - z) * Fi (b2 - z + 1) * Fi (b3 - z + 1))) * key

end Scaling


end Lightlike.TV.Refl

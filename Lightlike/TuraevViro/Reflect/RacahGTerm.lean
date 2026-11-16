import Lightlike.TuraevViro.Reflect.RacahTerm

/-! # The certificate term `G(z)` and `G(z+1)` as bracket multiples of the base `Psi`. -/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

variable {K : Type*} [Field K]

section Scaling
variable {u : K} {N : ℤ} {Fi Pn : ℤ → K} (hu : u ≠ 0) (h0' : u ≠ 0) (hd : u - u⁻¹ ≠ 0)
  (hF : ∀ n : ℤ, n ≤ N → Fi n = bk (u ^ (n + 1)) / (u - u⁻¹) * Fi (n + 1))

include hF in
theorem hFs' (n m : ℤ) (hn : n ≤ N) (h : n + 1 = m) : Fi n = bk (u ^ m) / (u - u⁻¹) * Fi m := by
  rw [hF n hn, h]

include hu h0' hd hF in
theorem G0_scaling
    (rho : K → K) (a1 a2 a3 a4 b1 b2 b3 z : ℤ) (p1 p2 p3 p4 q2 q3 Z : K)
    (hp1 : p1 = u ^ a1) (hp2 : p2 = u ^ a2) (hp3 : p3 = u ^ a3) (hp4 : p4 = u ^ a4)
    (hq2 : q2 = u ^ b2) (hq3 : q3 = u ^ b3) (hZ : Z = u ^ z) (hB1 : z - a1 ≤ N) (hB2 : z - a2 ≤ N) (hB3 : z - a3 ≤ N) (hB4 : z - a4 ≤ N) (hB5 : b1 - z - 1 ≤ N) (hB6 : b2 - z ≤ N) (hB7 : b3 - z ≤ N) :
    (u - u⁻¹) ^ 6 * Gq (Fi := Fi) (Pn := Pn) u rho a1 a2 a3 a4 b1 b2 b3 z =
      Poly.eval (env u p1 p2 p3 p4 q2 q3 Z) fW0 * rho Z *
        Psi Fi Pn a1 a2 a3 a4 b1 b2 b3 z := by
  have h1 : p1 ≠ 0 := by rw [hp1]; exact zpow_ne_zero _ hu
  have h2 : p2 ≠ 0 := by rw [hp2]; exact zpow_ne_zero _ hu
  have h3 : p3 ≠ 0 := by rw [hp3]; exact zpow_ne_zero _ hu
  have h4 : p4 ≠ 0 := by rw [hp4]; exact zpow_ne_zero _ hu
  have h5 : q2 ≠ 0 := by rw [hq2]; exact zpow_ne_zero _ hu
  have h6 : q3 ≠ 0 := by rw [hq3]; exact zpow_ne_zero _ hu
  have h7 : Z ≠ 0 := by rw [hZ]; exact zpow_ne_zero _ hu
  rw [eval_fW0 h0' h1 h2 h3 h4 h5 h6 h7]
  unfold Gq Gb Psi
  rw [← hZ]
  rw [hFs' hF (z - a1) (z - a1 + 1) (by omega) rfl, hFs' hF (z - a2) (z - a2 + 1) (by omega) rfl,
    hFs' hF (z - a3) (z - a3 + 1) (by omega) rfl, hFs' hF (z - a4) (z - a4 + 1) (by omega) rfl]
  have e1 : u ^ (z - a1 + 1) = u * p1⁻¹ * Z := by
    rw [hp1, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e2 : u ^ (z - a2 + 1) = u * p2⁻¹ * Z := by
    rw [hp2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e3 : u ^ (z - a3 + 1) = u * p3⁻¹ * Z := by
    rw [hp3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e4 : u ^ (z - a4 + 1) = u * p4⁻¹ * Z := by
    rw [hp4, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have d2 : u ^ (z - a2) = p2⁻¹ * Z := by rw [hp2, hZ, zpow_sub₀ hu]; ring
  have d3 : u ^ (z - a3) = p3⁻¹ * Z := by rw [hp3, hZ, zpow_sub₀ hu]; ring
  rw [e1, e2, e3, e4, d2, d3]
  generalize u - u⁻¹ = d at hd ⊢
  have key : d ^ 6 * (d⁻¹) ^ 6 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  simp only [div_eq_mul_inv]
  linear_combination (bk (p2⁻¹ * Z) * bk (p3⁻¹ * Z) * bk (u * p1⁻¹ * Z) * bk (u * p2⁻¹ * Z) * bk (u * p3⁻¹ * Z) * bk (u * p4⁻¹ * Z) * rho Z * ((-1) ^ z * Pn (z + 1) * Fi (z - a1 + 1) * Fi (z - a2 + 1) * Fi (z - a3 + 1) * Fi (z - a4 + 1) * Fi (b1 - z) * Fi (b2 - z + 1) * Fi (b3 - z + 1))) * key

include hu h0' hd hF in
theorem G1_scaling
    (rho : K → K) (a1 a2 a3 a4 b1 b2 b3 z : ℤ) (p1 p2 p3 p4 q2 q3 Z : K)
    (hp1 : p1 = u ^ a1) (hp2 : p2 = u ^ a2) (hp3 : p3 = u ^ a3) (hp4 : p4 = u ^ a4)
    (hq2 : q2 = u ^ b2) (hq3 : q3 = u ^ b3) (hZ : Z = u ^ z) (hB1 : z - a1 ≤ N) (hB2 : z - a2 ≤ N) (hB3 : z - a3 ≤ N) (hB4 : z - a4 ≤ N) (hB5 : b1 - z - 1 ≤ N) (hB6 : b2 - z ≤ N) (hB7 : b3 - z ≤ N)
    (hP : Pn (z + 1 + 1) = bk (u ^ (z + 1 + 1)) / (u - u⁻¹) * Pn (z + 1))
    (hb : u ^ b1 = p1 * p2 * p3 * p4 * q2⁻¹ * q3⁻¹) :
    (u - u⁻¹) ^ 6 * Gq (Fi := Fi) (Pn := Pn) u rho a1 a2 a3 a4 b1 b2 b3 (z + 1) =
      Poly.eval (env u p1 p2 p3 p4 q2 q3 Z) fW1 * rho (u * Z) *
        Psi Fi Pn a1 a2 a3 a4 b1 b2 b3 z := by
  have h1 : p1 ≠ 0 := by rw [hp1]; exact zpow_ne_zero _ hu
  have h2 : p2 ≠ 0 := by rw [hp2]; exact zpow_ne_zero _ hu
  have h3 : p3 ≠ 0 := by rw [hp3]; exact zpow_ne_zero _ hu
  have h4 : p4 ≠ 0 := by rw [hp4]; exact zpow_ne_zero _ hu
  have h5 : q2 ≠ 0 := by rw [hq2]; exact zpow_ne_zero _ hu
  have h6 : q3 ≠ 0 := by rw [hq3]; exact zpow_ne_zero _ hu
  have h7 : Z ≠ 0 := by rw [hZ]; exact zpow_ne_zero _ hu
  rw [eval_fW1 h0' h1 h2 h3 h4 h5 h6 h7]
  unfold Gq Gb Psi
  have uz : u ^ (z + 1) = u * Z := by rw [hZ, zpow_add₀ hu, zpow_one]; ring
  rw [uz]
  have s1 : (-1 : K) ^ (z + 1) = -(-1 : K) ^ z := by
    rw [zpow_add₀ (by norm_num), zpow_one]; ring
  have i1 : z + 1 - a1 = z - a1 + 1 := by ring
  have i2 : z + 1 - a2 = z - a2 + 1 := by ring
  have i3 : z + 1 - a3 = z - a3 + 1 := by ring
  have i4 : z + 1 - a4 = z - a4 + 1 := by ring
  have i5 : b2 - (z + 1) + 1 = b2 - z := by ring
  have i6 : b3 - (z + 1) + 1 = b3 - z := by ring
  rw [s1, i1, i2, i3, i4, i5, i6, hP, hFs' hF (b1 - (z + 1)) (b1 - z) (by omega) (by ring),
    hFs' hF (b2 - z) (b2 - z + 1) (by omega) rfl, hFs' hF (b3 - z) (b3 - z + 1) (by omega) rfl]
  have e2 : u ^ (z - a2 + 1) = u * p2⁻¹ * Z := by
    rw [hp2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e3 : u ^ (z - a3 + 1) = u * p3⁻¹ * Z := by
    rw [hp3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e5 : u ^ (b2 - z + 1) = u * q2 * Z⁻¹ := by
    rw [hq2, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have e6 : u ^ (b3 - z + 1) = u * q3 * Z⁻¹ := by
    rw [hq3, hZ, zpow_add₀ hu, zpow_sub₀ hu, zpow_one]; ring
  have eb : u ^ (b1 - z) = p1 * p2 * p3 * p4 * q2⁻¹ * q3⁻¹ * Z⁻¹ := by
    rw [zpow_sub₀ hu, hb, hZ]; ring
  have eP : u ^ (z + 1 + 1) = u ^ 2 * Z := by
    rw [hZ, zpow_add₀ hu, zpow_add₀ hu, zpow_one]; ring
  rw [e2, e3, e5, e6, eb, eP]
  generalize u - u⁻¹ = d at hd ⊢
  have key : d ^ 6 * (d⁻¹) ^ 6 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  simp only [div_eq_mul_inv]
  linear_combination (-(bk (u ^ 2 * Z) * bk (p1 * p2 * p3 * p4 * q2⁻¹ * q3⁻¹ * Z⁻¹) * bk (u * q2 * Z⁻¹) * bk (u * q3 * Z⁻¹) * bk (u * p2⁻¹ * Z) * bk (u * p3⁻¹ * Z)) * rho (u * Z) * ((-1) ^ z * Pn (z + 1) * Fi (z - a1 + 1) * Fi (z - a2 + 1) * Fi (z - a3 + 1) * Fi (z - a4 + 1) * Fi (b1 - z) * Fi (b2 - z + 1) * Fi (b3 - z + 1))) * key

end Scaling

end Lightlike.TV.Refl

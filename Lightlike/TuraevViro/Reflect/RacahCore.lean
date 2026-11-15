import Lightlike.TuraevViro.Reflect.RacahCert0
import Lightlike.TuraevViro.Reflect.RacahCert2
import Lightlike.TuraevViro.Reflect.RacahCert4
import Lightlike.TuraevViro.Reflect.RacahCert6
import Lightlike.TuraevViro.Reflect.RacahCert8
import Lightlike.TuraevViro.Reflect.RacahCert10
import Lightlike.TuraevViro.Reflect.RacahCert12

import Lightlike.TuraevViro.Reflect.RacahBase
import Lightlike.TuraevViro.Reflect.RacahTreeX0
import Lightlike.TuraevViro.Reflect.RacahTreeE1
import Lightlike.TuraevViro.Reflect.RacahTreeE3
import Lightlike.TuraevViro.Reflect.RacahTreeE5

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl



theorem eqA2_0 : A2_0 = A0_0 := by decide +kernel
theorem eqA2_1 : A2_1 = A0_1 := by decide +kernel
theorem eqA2_2 : A2_2 = A0_2 := by decide +kernel
theorem eqA4_0 : A4_0 = A0_0 := by decide +kernel
theorem eqA4_1 : A4_1 = A0_1 := by decide +kernel
theorem eqA4_2 : A4_2 = A0_2 := by decide +kernel
theorem eqA4_3 : A4_3 = A2_3 := by decide +kernel
theorem eqA6_0 : A6_0 = A0_0 := by decide +kernel
theorem eqA6_1 : A6_1 = A0_1 := by decide +kernel
theorem eqA6_2 : A6_2 = A0_2 := by decide +kernel
theorem eqA6_3 : A6_3 = A2_3 := by decide +kernel
theorem eqA8_0 : A8_0 = A0_0 := by decide +kernel
theorem eqA8_1 : A8_1 = A0_1 := by decide +kernel
theorem eqA8_2 : A8_2 = A0_2 := by decide +kernel
theorem eqA8_3 : A8_3 = A2_3 := by decide +kernel
theorem eqA10_0 : A10_0 = A0_0 := by decide +kernel
theorem eqA10_1 : A10_1 = A0_1 := by decide +kernel
theorem eqA10_2 : A10_2 = A0_2 := by decide +kernel
theorem eqA10_3 : A10_3 = A2_3 := by decide +kernel
theorem eqA12_0 : A12_0 = A0_0 := by decide +kernel
theorem eqA12_1 : A12_1 = A0_2 := by decide +kernel
theorem eqA12_2 : A12_2 = A2_3 := by decide +kernel

theorem eval_Zk {K : Type*} [Field K] (E : Env K) (k : ℤ) : Mono.eval E (Zk k) = E.v7 ^ k := by
  simp [Zk, Mono.eval]

/-- **The cleared identity**: `Dc X0 + N1 E1 + N3 E3 + N5 E5 = 0` for every evaluation of the variables
in a field. -/
theorem core_identity {K : Type*} [Field K] {E : Env K} (hE : E.NZ) :
    Poly.eval E Dc * Poly.eval E X0 + Poly.eval E N1 * Poly.eval E E1 + Poly.eval E N3 * Poly.eval E E3
      + Poly.eval E N5 * Poly.eval E E5 = 0 := by
  have h0 := coeff0 hE
  have h2 := coeff2 hE
  rw [eqA2_0, eqA2_1, eqA2_2] at h2
  have h4 := coeff4 hE
  rw [eqA4_0, eqA4_1, eqA4_2, eqA4_3] at h4
  have h6 := coeff6 hE
  rw [eqA6_0, eqA6_1, eqA6_2, eqA6_3] at h6
  have h8 := coeff8 hE
  rw [eqA8_0, eqA8_1, eqA8_2, eqA8_3] at h8
  have h10 := coeff10 hE
  rw [eqA10_0, eqA10_1, eqA10_2, eqA10_3] at h10
  have h12 := coeff12 hE
  rw [eqA12_0, eqA12_1, eqA12_2] at h12
  rw [tree_X0, tree_E1, tree_E3, tree_E5]
  simp only [Dc, N1, N3, N5, bigX0, bigE1, bigE3, bigE5, eval_add, eval_scale hE, Mono.eval_mul hE]
  simp only [eval_Zk]
  linear_combination ((-2 * Mono.eval E muInv * E.v7 ^ (0:ℤ)) * h0) + ((-2 * Mono.eval E muInv * E.v7 ^ (2:ℤ)) * h2) + ((-2 * Mono.eval E muInv * E.v7 ^ (4:ℤ)) * h4) + ((-2 * Mono.eval E muInv * E.v7 ^ (6:ℤ)) * h6) + ((-2 * Mono.eval E muInv * E.v7 ^ (8:ℤ)) * h8) + ((-2 * Mono.eval E muInv * E.v7 ^ (10:ℤ)) * h10) + ((-2 * Mono.eval E muInv * E.v7 ^ (12:ℤ)) * h12)

end Lightlike.TV.Refl

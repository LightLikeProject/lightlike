import Lightlike.SpinFoam.EPRLStateSum.NodeCoefMixed

/-!
# The positional gluing differs from the Ooguri gluing

`NodeCoefMixed` shows that for `t₀ + t₂` odd the positional sum over a shared tetrahedron label
`i`, seen at rotations of different parity, vanishes. Here we put it next to the same-parity sum
(`δ_{ll'}`, `sum_nodeCoef_zero_mul_left`) and give a concrete instance. So a closed complex in which
a tetrahedron sits at nodes of different parity is *not* glued by orthogonality in EPRL.lean's
positional basis: this is the obstruction to stating `amplitude 1 = Ooguri` for the positional
`EPRL.amplitude` (the intrinsic sorted-basis amplitude is the open programme item `L4b`).

* `positional_gluing_ne_intrinsic`: same-parity sum `1`, mixed-parity sum `0` for one admissible `l`;
* `positional_gluing_instance`: the instance `t = (1,0,0,1)`, `l = 1`.
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam.EPRLStateSum

/-- For `t₀ + t₂` odd and an admissible intrinsic label `l`, the positional sum of a tetrahedron
seen at two rotations of the same parity is `1` (Ooguri gluing `δ_{ll}`), but at rotations of
different parity it is `0`; so the two cannot agree. -/
theorem positional_gluing_ne_intrinsic {t₀ t₁ t₂ t₃ r r' : ℕ} (hr : r % 2 = 0) (hr' : r' % 2 = 1)
    (hodd : (t₀ + t₂) % 2 = 1) {l : ℕ} (hl : Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃) :
    ∑ i ∈ range (t₀ + t₁ + 1), nodeCoef t₀ t₁ t₂ t₃ 0 i l * nodeCoef t₀ t₁ t₂ t₃ 0 i l = 1 ∧
      ∑ i ∈ range (t₀ + t₁ + 1), nodeCoef t₀ t₁ t₂ t₃ r i l * nodeCoef t₀ t₁ t₂ t₃ r' i l = 0 := by
  refine ⟨?_, sum_nodeCoef_even_odd_eq_zero hr hr' hodd _ l l⟩
  rw [sum_nodeCoef_zero_mul_left]
  simp [hl]

/-- Instance: tetrahedron with doubled spins `(1,0,0,1)` and `l = 1`: rotations `0` and `1`
give `1` on the diagonal for `0,0` and `0` for the mixed pair `0,1`. -/
theorem positional_gluing_instance :
    ∑ i ∈ range 2, nodeCoef 1 0 0 1 0 i 1 * nodeCoef 1 0 0 1 0 i 1 = 1 ∧
      ∑ i ∈ range 2, nodeCoef 1 0 0 1 0 i 1 * nodeCoef 1 0 0 1 1 i 1 = 0 := by
  have h := positional_gluing_ne_intrinsic (t₀ := 1) (t₁ := 0) (t₂ := 0) (t₃ := 1) (r := 0)
    (r' := 1) (by norm_num) (by norm_num) (by norm_num) (l := 1)
    ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
      ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
  exact h

end Lightlike.SpinFoam.EPRLStateSum

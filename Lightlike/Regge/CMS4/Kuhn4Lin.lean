import Lightlike.Regge.CMS4.Kuhn4Hinge0
import Lightlike.Regge.CMS4.Kuhn4Hinge1
import Lightlike.Regge.CMS4.Kuhn4Hinge2
import Lightlike.Regge.CMS4.Kuhn4Hinge3

/-!
# The ten hinge angles of the Kuhn 4-orthoscheme and their first variations

`kuhn4_dih h δ ε` is the dihedral angle of hinge `h : Fin 10` of the Kuhn 4-orthoscheme
for the squared-length matrix `kd4 + ε δ`; `kuhn4_dih_lin h δ` is its derivative at `ε = 0`,
collecting the ten explicit formulas `kuhn4_hinge0_deriv` to `kuhn4_hinge9_deriv`.
-/

open Real

namespace Lightlike.Regge4

/-- The dihedral angle of hinge `h` of the Kuhn 4-orthoscheme, for the perturbed
squared-length matrix `kd4 + ε δ`. -/
noncomputable def kuhn4_dih (h : Fin 10) (δ : Fin 5 → Fin 5 → ℝ) (ε : ℝ) : ℝ :=
  let g : Fin 5 → Fin 5 → ℝ := fun x y => kd4 x y + ε * δ x y
  match h with
  | 0 => dihS g 2 3 4 0 1
  | 1 => dihS g 1 3 4 0 2
  | 2 => dihS g 1 2 4 0 3
  | 3 => dihS g 1 2 3 0 4
  | 4 => dihS g 0 3 4 1 2
  | 5 => dihS g 0 2 4 1 3
  | 6 => dihS g 0 2 3 1 4
  | 7 => dihS g 0 1 4 2 3
  | 8 => dihS g 0 1 3 2 4
  | 9 => dihS g 0 1 2 3 4

/-- The first variation of the hinge angle `h` of the Kuhn 4-orthoscheme: a linear form
in the perturbation `δ` of the squared lengths. -/
noncomputable def kuhn4_dih_lin (h : Fin 10) (δ : Fin 5 → Fin 5 → ℝ) : ℝ :=
  match h with
  | 0 => -(2 * δ 2 0 - 4 * δ 0 1 + δ 0 0 + 2 * δ 1 1) / 8
  | 1 => -(δ 1 0 / 2 + δ 1 2 - δ 0 2 - δ 1 3 / 2 + δ 0 3 / 2) / √2
  | 2 => -(δ 1 3 - δ 0 3 - δ 1 4 / 2 + δ 0 4 / 2 - δ 1 2 / 2 + δ 0 2 / 2) / √2
  | 3 => -(δ 1 4 / 2 - δ 0 4 / 2 - δ 1 3 / 2 + δ 0 3 / 2)
  | 4 => -(-(1 / 2) * δ 0 3 - (1 / 8) * δ 3 3 + (3 / 4) * δ 0 2 + (1 / 4) * δ 3 2
          - (3 / 2) * δ 1 2 + (7 / 8) * δ 1 3 - (1 / 8) * δ 3 1 + (3 / 8) * δ 1 1
          + (3 / 8) * δ 2 2 - (1 / 4) * δ 2 3) / √3
  | 5 => -(-(δ 0 2 + δ 2 2 + δ 0 4 + δ 2 4) / 2 + δ 2 3 + δ 0 3 - δ 1 3 * 2 + δ 1 4 + δ 1 2) / 2
  | 6 => -(-(δ 0 3 + δ 2 3) / 2 + (δ 0 4 + δ 2 4) / 2 - δ 1 4 + δ 1 3) / √2
  | 7 => -(-(1 / 8) * δ 1 1 - (1 / 2) * δ 1 4 + (7 / 8) * δ 1 3 - (1 / 8) * δ 4 4
          + (1 / 4) * δ 4 3 - (3 / 2) * δ 2 3 + (7 / 8) * δ 2 4 + (1 / 4) * δ 2 1
          - (1 / 4) * δ 1 2 - (1 / 8) * δ 4 2 + (3 / 8) * δ 2 2 + (3 / 8) * δ 3 3
          - (1 / 4) * δ 3 4 - (1 / 8) * δ 3 1) / √3
  | 8 => -(-(δ 1 3 + δ 3 3) / 2 + (δ 1 4 + δ 3 4) / 2 - δ 2 4 + δ 2 3) / √2
  | 9 => -(-(1 / 8) * δ 2 2 + (3 / 8) * δ 2 4 - (1 / 2) * δ 3 4 + (1 / 4) * δ 3 2
          - (1 / 4) * δ 2 3 + (1 / 4) * δ 3 3 + (1 / 8) * δ 4 4 - (1 / 8) * δ 4 2)

/-- Every hinge angle of the Kuhn 4-orthoscheme is differentiable in the perturbation at `0`,
with derivative `kuhn4_dih_lin h δ`. -/
theorem kuhn4_dih_hasDerivAt (h : Fin 10) (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (kuhn4_dih h δ) (kuhn4_dih_lin h δ) 0 := by
  fin_cases h
  · exact kuhn4_hinge0_deriv δ
  · exact kuhn4_hinge1_deriv δ
  · exact kuhn4_hinge2_deriv δ
  · exact kuhn4_hinge3_deriv δ
  · exact kuhn4_hinge4_deriv δ
  · exact kuhn4_hinge5_deriv δ
  · exact kuhn4_hinge6_deriv δ
  · exact kuhn4_hinge7_deriv δ
  · exact kuhn4_hinge8_deriv δ
  · exact kuhn4_hinge9_deriv δ

end Lightlike.Regge4

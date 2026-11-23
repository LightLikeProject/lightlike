import Lightlike.Regge.CMS4.Pert4
import Lightlike.Regge.CMS4.Assemble4

/-!
# The dihedral angle of the moved star is a fan angle of moved lattice vectors

In a class `c` every incidence has its hinge vertex `p` at the same position `Pc c`, so the moved
vertices `Phi t (kpos4 σ h a)` of all incidences of the class are moved lattice points
`Phi t (Pc c + z)`. The dihedral angle of the moved star is the fan angle of the moved integer
vectors, so that the class sum of the moved star closes up exactly like the Gram star.

## Main results

* `kpos4_hP_eq`, `kpos4_eq_Pc_add`: the hinge vertex of a class incidence is `Pc c`.
* `incAng4_gram`: the dihedral angle of the Gram star of arbitrary vertices is a fan angle.
* `incAng4_Qt_class`: the dihedral angle of the moved star of a class incidence is
  `fanAng4` of the moved integer vectors `Psi`.
-/

open Lightlike Real
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The common position of the hinge vertex `p` in the star of the class `c`: minus the centroid
offset `(2 w₁ + w₂) / 3`. -/
noncomputable def Pc (c : Fin 4 → Fin 3) : Fin 4 → ℝ := fun i => -(2 * clsW1 c i + clsW2 c i) / 3

/-- The hinge vertex of an incidence of the class `c` is at `Pc c`. -/
theorem kpos4_hP_eq (c : Fin 4 → Fin 3) (σ : Fin 24) (h : Fin 10) (hc : InClass4 c σ h) :
    kpos4 σ h (hP h) = Pc c := by
  obtain ⟨h1, h2⟩ := hc
  funext i
  have a := h1 i
  have b := h2 i
  simp only [kpos4, Pc]
  linarith

/-- Every vertex of an incidence of the class `c` is `Pc c` plus its integer edge vector. -/
theorem kpos4_eq_Pc_add (c : Fin 4 → Fin 3) (σ : Fin 24) (h : Fin 10) (a : Fin 5)
    (hc : InClass4 c σ h) :
    kpos4 σ h a = Pc c + fun i => (vZ σ a (hP h) i : ℝ) := by
  rw [← kpos4_hP_eq c σ h hc]
  funext i
  have := congrFun (kpos4_sub_cast σ h a (hP h)) i
  simp only [Pi.sub_apply] at this
  simp only [Pi.add_apply]
  linarith

/-- The moved lattice vector: the image under `Phi t` of the edge `Pc c → Pc c + z`. -/
noncomputable def Psi (m : Fin 4 → ℝ) (c : Fin 4 → Fin 3) (t : ℝ) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  Phi g m t (Pc c + z) - Phi g m t (Pc c)

/-- **The dihedral angle of a Gram star of arbitrary vertices is a fan angle.** -/
theorem incAng4_gram {G : Matrix (Fin 4) (Fin 4) ℝ} (hs : Gᵀ = G) (y : Fin 5 → Fin 4 → ℝ)
    (h : Fin 10) (hD : 0 < gramW G (y (hQ h) - y (hP h)) (y (hR h) - y (hP h))) :
    incAng4 h (fun a b => (y b - y a) ⬝ᵥ (G *ᵥ (y b - y a))) =
      fanAng4 G (y (hQ h) - y (hP h)) (y (hR h) - y (hP h)) (y (hS h) - y (hP h))
        (y (hU h) - y (hP h)) := by
  unfold incAng4 dihF dihS fanAng4
  rw [cosS_gram hs y (hP h) (hQ h) (hR h) (hS h) (hU h) hD]

/-- The integer edge vectors of the hinge of a class incidence are the axis vectors. -/
theorem vZ_axes (c : Fin 4 → Fin 3) (σ : Fin 24) (h : Fin 10) (he : (σ, h) ∈ incsOf c) :
    vZ σ (hQ h) (hP h) = cw1 c ∧ vZ σ (hR h) (hP h) = ax2 c := by
  obtain ⟨e1, e2⟩ := incAxes4 c σ h he
  rw [kpos4_sub_cast] at e1 e2
  constructor
  · funext i
    exact_mod_cast congrFun e1 i
  · funext i
    exact_mod_cast congrFun e2 i

/-- **The dihedral angle of the moved star of a class incidence** is the fan angle of the moved
integer vectors, in the oriented order. -/
theorem incAng4_Qt_class {m : Fin 4 → ℝ} (hs : ∀ y, (g y)ᵀ = g y) (c : Fin 4 → Fin 3)
    (e : Fin 24 × Fin 10) (he : e ∈ incsOf c) (t : ℝ)
    (hD : 0 < gramW (g m) (Psi g m c t (fun i => (cw1 c i : ℝ)))
      (Psi g m c t (fun i => (ax2 c i : ℝ)))) :
    incAng4 e.2 (Qt g m e.1 e.2 t) =
      fanAng4 (g m) (Psi g m c t (fun i => (cw1 c i : ℝ))) (Psi g m c t (fun i => (ax2 c i : ℝ)))
        (Psi g m c t (fun i => ((orient c e).1 i : ℝ)))
        (Psi g m c t (fun i => ((orient c e).2 i : ℝ))) := by
  obtain ⟨σ, h⟩ := e
  have hc := (mem_incsOf_iff c (σ, h)).1 he
  have hsm : (g m)ᵀ = g m := hs m
  obtain ⟨z1, z2⟩ := vZ_axes c σ h he
  set y : Fin 5 → Fin 4 → ℝ := fun a => Phi g m t (kpos4 σ h a) with hy
  have hq : Qt g m σ h t = fun a b => (y b - y a) ⬝ᵥ ((g m) *ᵥ (y b - y a)) := rfl
  have hyd : ∀ a, y a - y (hP h) = Psi g m c t (fun i => (vZ σ a (hP h) i : ℝ)) := by
    intro a
    simp only [hy, Psi]
    rw [kpos4_eq_Pc_add c σ h a hc, kpos4_hP_eq c σ h hc]
  have hQ' : y (hQ h) - y (hP h) = Psi g m c t (fun i => (cw1 c i : ℝ)) := by
    rw [hyd, z1]
  have hR' : y (hR h) - y (hP h) = Psi g m c t (fun i => (ax2 c i : ℝ)) := by
    rw [hyd, z2]
  show incAng4 h (Qt g m σ h t) = _
  rw [hq, incAng4_gram hsm y h (by rw [hQ', hR']; exact hD), hQ', hR', hyd, hyd]
  simp only [orient]
  split_ifs
  · rfl
  · exact fanAng4_symm hsm _ _ _ _

end Lightlike.Regge4

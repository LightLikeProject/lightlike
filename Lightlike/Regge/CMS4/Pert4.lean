import Lightlike.Regge.CMS4.Gauge4
import Lightlike.Regge.CMS4.Valid4

/-!
# The gauge-moved star and the derivative of its dihedral angles

Moving the vertices of the star of an incidence `(σ, h)` by `Phi g m t` (a normal-coordinate change
at `m`) gives the squared-length matrix `Qt t = q + t c + t² r`, where `q = incQ4` and `c = incC4`.
Hence the dihedral angle of the moved star has `t`-derivative at `0` equal to the first-order
coefficient `angC14`.

## Main results

* `Qt_eq`: `Qt t = incQ4 + t • incC4 + t² • Rt`.
* `hasDerivAt_Qt`: `HasDerivAt (Qt ·) (incC4 g m σ h) 0`.
* `hasDerivAt_angQt`: `HasDerivAt (fun t => incAng4 h (Qt t)) (angC14 g m σ h) 0`.
-/

open Lightlike Real
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The squared lengths of the star of `(σ, h)` after the vertex move `Phi g m t`. -/
noncomputable def Qt (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) (t : ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun a b =>
    (Phi g m t (kpos4 σ h b) - Phi g m t (kpos4 σ h a)) ⬝ᵥ
      ((g m) *ᵥ (Phi g m t (kpos4 σ h b) - Phi g m t (kpos4 σ h a)))

/-- The quadratic remainder matrix of the moved star. -/
noncomputable def Rt (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) : Fin 5 → Fin 5 → ℝ :=
  fun a b =>
    chr1 g m (fun i => kpos4 σ h b i - kpos4 σ h a i)
        (fun i => (kpos4 σ h a i + kpos4 σ h b i) / 2) ⬝ᵥ
      ((g m)⁻¹ *ᵥ chr1 g m (fun i => kpos4 σ h b i - kpos4 σ h a i)
        (fun i => (kpos4 σ h a i + kpos4 σ h b i) / 2))

/-- The moved star has squared lengths `q + t c + t² r`. -/
theorem Qt_eq (hs : ∀ y, (g y)ᵀ = g y) (m : Fin 4 → ℝ) (hdet : IsUnit (g m).det)
    (σ : Fin 24) (h : Fin 10) (t : ℝ) :
    Qt g m σ h t = incQ4 g m σ h + t • incC4 g m σ h + t ^ 2 • Rt g m σ h := by
  funext a b
  have := sq_Phi g hs m hdet t (kpos4 σ h a) (kpos4 σ h b)
  simp only [Qt, Rt, incQ4, incC4, incMat4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact this

/-- At `t = 0` the moved star is the Gram star. -/
theorem Qt_zero (hs : ∀ y, (g y)ᵀ = g y) (m : Fin 4 → ℝ) (hdet : IsUnit (g m).det)
    (σ : Fin 24) (h : Fin 10) : Qt g m σ h 0 = incQ4 g m σ h := by
  rw [Qt_eq g hs m hdet]; simp

/-- The squared lengths of the moved star have `t`-derivative `incC4` at `0`. -/
theorem hasDerivAt_Qt (hs : ∀ y, (g y)ᵀ = g y) (m : Fin 4 → ℝ) (hdet : IsUnit (g m).det)
    (σ : Fin 24) (h : Fin 10) : HasDerivAt (Qt g m σ h) (incC4 g m σ h) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => incQ4 g m σ h + t • incC4 g m σ h + t ^ 2 • Rt g m σ h)
      (0 + (1 : ℝ) • incC4 g m σ h + ((2 : ℕ) * (0 : ℝ) ^ (2 - 1) : ℝ) • Rt g m σ h) 0 :=
    (((hasDerivAt_const _ _).add ((hasDerivAt_id (0 : ℝ)).smul_const (incC4 g m σ h))).add
      ((hasDerivAt_pow 2 (0 : ℝ)).smul_const (Rt g m σ h)))
  have e : Qt g m σ h = fun t : ℝ => incQ4 g m σ h + t • incC4 g m σ h + t ^ 2 • Rt g m σ h :=
    funext fun t => Qt_eq g hs m hdet σ h t
  rw [e]
  simpa using h1

/-- **The dihedral angle of the moved star** has `t`-derivative `angC14` at `t = 0`. -/
theorem hasDerivAt_angQt {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (σ : Fin 24) (h : Fin 10) :
    HasDerivAt (fun t => incAng4 h (Qt g m σ h t)) (angC14 g m σ h) 0 := by
  have hdet : IsUnit (g m).det := isUnit_iff_ne_zero.2 hG.det_pos.ne'
  have hd : DifferentiableAt ℝ (incAng4 h) (incQ4 g m σ h) :=
    (contDiffAt_dihS (valid4_incQ g hG σ h)).differentiableAt (by norm_num)
  have hl : HasFDerivAt (incAng4 h) (fderiv ℝ (incAng4 h) (incQ4 g m σ h))
      (Qt g m σ h 0) := by
    rw [Qt_zero g hs m hdet]; exact hd.hasFDerivAt
  exact hl.comp_hasDerivAt 0 (hasDerivAt_Qt g hs m hdet σ h)

end Lightlike.Regge4

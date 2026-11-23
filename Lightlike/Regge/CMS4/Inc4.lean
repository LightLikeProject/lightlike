import Lightlike.Regge.CMS4.Plucker4
import Lightlike.Regge.CMS4.Valid4

/-!
# The dihedral angle of an incidence is a fan angle (dimension 4)

For an incidence `(σ, h)` of the Kuhn triangulation of the 4-cube and a positive definite metric
`g m`, the dihedral angle `incAng4 h (incQ4 g m σ h)` equals the angle `fanAng4` between the two
vectors `x t - x p`, `x u - x p` in the plane quotient by the hinge triangle `(x q - x p, x r - x p)`.
This connects the Gram star to the fan theorems `quad_fan4`, `hex_fan4`.

## Main results

* `kpos4_indep`: the hinge edge vectors `x q - x p`, `x r - x p` of every incidence are independent.
* `gramW_incidence_pos`: their Gram determinant is positive.
* `incAng4_eq_fanAng4`: the dihedral angle of the incidence is `fanAng4` of the quotient vectors.
-/

open Real Matrix
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The four edge vectors of an incidence from the first hinge vertex are linearly independent
(as the columns of a matrix, an injective map). -/
theorem kpos4_inj (σ : Fin 24) (h : Fin 10) :
    Function.Injective (Matrix.of fun i j : Fin 4 =>
      (![kpos4 σ h (hQ h), kpos4 σ h (hR h), kpos4 σ h (hS h), kpos4 σ h (hU h)] j
        - kpos4 σ h (hP h)) i).mulVec := by
  have hinj0 : Function.Injective (edgeMat4 h).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (edgeMat4_det_ne h)))
  have hcoef : ∀ (j : Fin 4) (i : Fin 4),
      (![kpos4 σ h (hQ h), kpos4 σ h (hR h), kpos4 σ h (hS h), kpos4 σ h (hU h)] j
        - kpos4 σ h (hP h)) i = edgeMat4 h (perms4 σ i) j := by
    intro j i
    fin_cases j <;> simp [kpos4, edgeMat4]
  intro c c' hcc
  apply hinj0
  funext k
  obtain ⟨i, rfl⟩ := perms4_surj σ k
  have := congrFun hcc i
  simpa [Matrix.mulVec, dotProduct, hcoef] using this

/-- The two hinge edge vectors `x q - x p`, `x r - x p` of an incidence are independent. -/
theorem kpos4_indep (σ : Fin 24) (h : Fin 10) (c d : ℝ)
    (hcd : c • (kpos4 σ h (hQ h) - kpos4 σ h (hP h)) + d • (kpos4 σ h (hR h) - kpos4 σ h (hP h))
      = 0) : c = 0 ∧ d = 0 := by
  have hinj := kpos4_inj σ h
  have e : (Matrix.of fun i j : Fin 4 =>
      (![kpos4 σ h (hQ h), kpos4 σ h (hR h), kpos4 σ h (hS h), kpos4 σ h (hU h)] j
        - kpos4 σ h (hP h)) i).mulVec ![c, d, 0, 0] =
      (Matrix.of fun i j : Fin 4 =>
      (![kpos4 σ h (hQ h), kpos4 σ h (hR h), kpos4 σ h (hS h), kpos4 σ h (hU h)] j
        - kpos4 σ h (hP h)) i).mulVec 0 := by
    rw [Matrix.mulVec_zero]
    funext i
    have := congrFun hcd i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    simp at this ⊢
    linarith
  have h0 := hinj e
  have h1 := congrFun h0 0
  have h2 := congrFun h0 1
  simp at h1 h2
  exact ⟨h1, h2⟩

/-- The Gram determinant of the hinge edge vectors of an incidence is positive. -/
theorem gramW_incidence_pos {m : Fin 4 → ℝ} (hG : (g m).PosDef) (σ : Fin 24) (h : Fin 10) :
    0 < gramW (g m) (kpos4 σ h (hQ h) - kpos4 σ h (hP h))
      (kpos4 σ h (hR h) - kpos4 σ h (hP h)) :=
  gramW_pos hG _ _ fun c d hcd => kpos4_indep σ h c d hcd

/-- **The dihedral angle of an incidence is a fan angle.** For a positive definite `g m`, the
dihedral angle of the Gram simplex of `(σ, h)` is the angle between the vectors `x t - x p` and
`x u - x p` in the plane quotient by the hinge triangle `(x q - x p, x r - x p)`. -/
theorem incAng4_eq_fanAng4 {m : Fin 4 → ℝ} (hG : (g m).PosDef) (σ : Fin 24) (h : Fin 10) :
    incAng4 h (incQ4 g m σ h) =
      fanAng4 (g m) (kpos4 σ h (hQ h) - kpos4 σ h (hP h)) (kpos4 σ h (hR h) - kpos4 σ h (hP h))
        (kpos4 σ h (hS h) - kpos4 σ h (hP h)) (kpos4 σ h (hU h) - kpos4 σ h (hP h)) := by
  have hs : (g m)ᵀ = g m := by simpa [Matrix.IsSymm] using hG.1
  have e : incQ4 g m σ h =
      fun a b => (kpos4 σ h b - kpos4 σ h a) ⬝ᵥ (g m *ᵥ (kpos4 σ h b - kpos4 σ h a)) := by
    funext a b
    rfl
  have hD := gramW_incidence_pos g hG σ h
  unfold incAng4 dihF dihS fanAng4
  rw [e, cosS_gram hs (kpos4 σ h) (hP h) (hQ h) (hR h) (hS h) (hU h) hD]

end Lightlike.Regge4

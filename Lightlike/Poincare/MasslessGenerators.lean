module

public import Lightlike.Poincare.LightConeUnitary

/-!
# Helicity from the generators of the massless representation at the standard momentum

At the standard light-like momentum `K = diag(2, 0)` the standard lift is the identity (`coneLift_coneBase`), so an
element `A` of the little group acts on the states of momentum `K` by its helicity character:
`(U(A) ψ)(K) = (A₀₀)ⁿ ψ(K)` (`helicityAct_base`). Differentiating along the curves of the little group:

* the rotation `R(θ) = diag(e^{iθ/2}, e^{−iθ/2})` about the momentum gives `i (n/2) ψ(K)` (`hasDerivAt_helicityAct_rot`):
  helicity `h = n/2`;
* the two "translations" `[[1, t], [0, 1]]` and `[[1, i t], [0, 1]]` of the little group give `0`
  (`hasDerivAt_helicityAct_trans`): finite helicity.

These are derivatives of the representation `U` itself. At `K` the Pauli–Lubanski components are the little-group
generators (`W⁰ = W³ = J₃`, `W¹, W²` the two translations; Bekaert–Boulanger §3.2, page 12 of v2), so
`W ψ(K) = h K ψ(K)`.

The same holds at every momentum `P` of the light cone for the little group `L(P) H L(P)⁻¹` of `P`
(`helicityAct_conj`, `hasDerivAt_helicityAct_rot_at`, `hasDerivAt_helicityAct_trans_at`): `W = h P` in the
little-group form of `W` at every momentum.

**Difference from the source (kind: weaker).** The Pauli–Lubanski components are taken in their little-group form
(at `K` the little-group generators, transported by `L(P)`), with the generators derived from `U`; the identity
`W^μ = ½ ε^{μνρσ} M_{νρ} P_σ` for the full generators, including those that move the momentum, is not formalised.

**Attempts recorded** (`docs/notes/ha6-pauli-lubanski-attempts.md`): (1) generators at the standard momentum, this
file; (2) a direct computation at a general momentum, stopped by the discontinuity of the massless standard lift
near `P₀₀ = 0` (no continuous global section exists) and, in the massive case, by the length of the computation of
the derivative of the standard lift along the orbit.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2 (page 12: the little algebra of a light-like momentum; the rotation generator and the
  generators `M_{m−}` that act as translations), §3.3 (pages 14–15: helicity representations, translations trivial).
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz

namespace Lightlike.Poincare

lemma coneLiftMat_base : coneLiftMat masslessH = 1 := by
  have ha : alphaC masslessH = 2 := by simp [alphaC, masslessH]
  have hpos : 0 < alphaC masslessH := by rw [ha]; norm_num
  have hs : Real.sqrt (alphaC masslessH / 2) = 1 := by rw [ha]; simp
  unfold coneLiftMat
  rw [if_pos hpos, hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [masslessH]

/-- The standard lift of the base point is the identity. -/
lemma coneLift_coneBase : coneLift coneBase = 1 := Subtype.ext coneLiftMat_base

/-- **The little group acts on the states of momentum `K` by the helicity character.** -/
theorem helicityAct_base (n : ℤ) {A : SL2C} (hA : A ∈ MulAction.stabilizer SL2C coneBase)
    (ψ : LightCone → ℂ) :
    helicityAct n A ψ coneBase = (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ n * ψ coneBase := by
  have h1 : A⁻¹ • coneBase = coneBase := by
    rw [inv_smul_eq_iff]; exact (MulAction.mem_stabilizer_iff.1 hA).symm
  have h2 : wignerG coneLift A coneBase = A := by
    rw [wignerG, MulAction.mem_stabilizer_iff.1 hA, coneLift_coneBase, inv_one, one_mul, mul_one]
  simp only [helicityAct, inducedActG, h1]
  have h3 : wignerStab coneLift_smul A coneBase = ⟨A, hA⟩ := Subtype.ext h2
  rw [h3]
  simp [helicityChar]

/-- **Helicity from the rotation generator**: `d/dθ (U(R(θ)) ψ)(K) = i (n/2) ψ(K)`. -/
theorem hasDerivAt_helicityAct_rot (n : ℤ) (ψ : LightCone → ℂ) :
    HasDerivAt (fun θ : ℝ => helicityAct n (coneRot θ) ψ coneBase)
      (Complex.I * (n / 2) * ψ coneBase) 0 := by
  have h : (fun θ : ℝ => helicityAct n (coneRot θ) ψ coneBase) =
      fun θ : ℝ => Complex.exp (Complex.I * (n / 2 * θ)) * ψ coneBase := by
    funext θ
    rw [helicityAct_base n (coneRot_mem θ)]
    congr 1
    simp only [coneRot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [h]
  have hd : HasDerivAt (fun θ : ℝ => Complex.I * (n / 2 * (θ : ℂ))) (Complex.I * (n / 2)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (Complex.I * (n / 2 : ℂ))
    simpa [mul_assoc] using this
  have := (hd.cexp).mul_const (ψ coneBase)
  simpa using this

/-- The little-group translations `[[1, c t], [0, 1]]` lie in the stabiliser. -/
lemma masslessTrans_mem (b : ℂ) : masslessTrans b ∈ MulAction.stabilizer SL2C coneBase := by
  rw [MulAction.mem_stabilizer_iff]
  exact Subtype.ext (masslessTrans_fix b)

/-- **Finite helicity from the translation generators**: `d/dt (U(T_c(t)) ψ)(K) = 0`. -/
theorem hasDerivAt_helicityAct_trans (n : ℤ) (c : ℂ) (ψ : LightCone → ℂ) :
    HasDerivAt (fun t : ℝ => helicityAct n (masslessTrans (c * t)) ψ coneBase) 0 0 := by
  have h : (fun t : ℝ => helicityAct n (masslessTrans (c * t)) ψ coneBase) = fun _ => ψ coneBase := by
    funext t
    rw [helicityAct_base n (masslessTrans_mem _)]
    simp [masslessTrans]
  rw [h]
  exact hasDerivAt_const _ _


/-! ## Transport to every momentum of the light cone -/

/-- The little group of `P` is `L(P) H L(P)⁻¹`; its elements act on the states of momentum `P` by the helicity
character: `(U(L(P) A L(P)⁻¹) ψ)(P) = (A₀₀)ⁿ ψ(P)` for `A` in the little group of `K`. -/
theorem helicityAct_conj (n : ℤ) (P : LightCone) {A : SL2C}
    (hA : A ∈ MulAction.stabilizer SL2C coneBase) (ψ : LightCone → ℂ) :
    helicityAct n (coneLift P * A * (coneLift P)⁻¹) ψ P = (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ n * ψ P := by
  have hfix : (coneLift P * A * (coneLift P)⁻¹) • P = P := by
    rw [mul_smul, mul_smul]
    have h1 : (coneLift P)⁻¹ • P = coneBase := by rw [inv_smul_eq_iff, coneLift_smul]
    rw [h1, MulAction.mem_stabilizer_iff.1 hA, coneLift_smul]
  have hinv : (coneLift P * A * (coneLift P)⁻¹)⁻¹ • P = P := by
    rw [inv_smul_eq_iff, hfix]
  have hW : wignerG coneLift (coneLift P * A * (coneLift P)⁻¹) P = A := by
    rw [wignerG, hfix]
    group
  simp only [helicityAct, inducedActG, hinv]
  have h3 : wignerStab coneLift_smul (coneLift P * A * (coneLift P)⁻¹) P = ⟨A, hA⟩ := Subtype.ext hW
  rw [h3]
  simp [helicityChar]

/-- **Helicity at every momentum**: `d/dθ (U(L(P) R(θ) L(P)⁻¹) ψ)(P) = i (n/2) ψ(P)`. -/
theorem hasDerivAt_helicityAct_rot_at (n : ℤ) (P : LightCone) (ψ : LightCone → ℂ) :
    HasDerivAt (fun θ : ℝ => helicityAct n (coneLift P * coneRot θ * (coneLift P)⁻¹) ψ P)
      (Complex.I * (n / 2) * ψ P) 0 := by
  have h : (fun θ : ℝ => helicityAct n (coneLift P * coneRot θ * (coneLift P)⁻¹) ψ P) =
      fun θ : ℝ => Complex.exp (Complex.I * (n / 2 * θ)) * ψ P := by
    funext θ
    rw [helicityAct_conj n P (coneRot_mem θ)]
    congr 1
    simp only [coneRot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [h]
  have hd : HasDerivAt (fun θ : ℝ => Complex.I * (n / 2 * (θ : ℂ))) (Complex.I * (n / 2)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (Complex.I * (n / 2 : ℂ))
    simpa [mul_assoc] using this
  have := (hd.cexp).mul_const (ψ P)
  simpa using this

/-- **Finite helicity at every momentum**: the transported translations act trivially. -/
theorem hasDerivAt_helicityAct_trans_at (n : ℤ) (c : ℂ) (P : LightCone) (ψ : LightCone → ℂ) :
    HasDerivAt (fun t : ℝ => helicityAct n (coneLift P * masslessTrans (c * t) * (coneLift P)⁻¹) ψ P) 0 0 := by
  have h : (fun t : ℝ => helicityAct n (coneLift P * masslessTrans (c * t) * (coneLift P)⁻¹) ψ P) =
      fun _ => ψ P := by
    funext t
    rw [helicityAct_conj n P (masslessTrans_mem _)]
    simp [masslessTrans]
  rw [h]
  exact hasDerivAt_const _ _

end Lightlike.Poincare

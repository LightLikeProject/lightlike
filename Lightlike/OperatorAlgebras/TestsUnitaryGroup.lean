import Lightlike.OperatorAlgebras.UnitaryGroup
import Lightlike.OperatorAlgebras.StoneGenerator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Trust checks for `UnitaryGroup` and its generator

The phase group `U t = exp (i λ t) • 1` on a complex Hilbert space is a strongly continuous unitary group.
Its generator is `λ • 1` on the whole space, so the sign and the factor `i` of the convention
`U t = exp (i t A)` are tested: the generator of `λ = 1` is `1`, and differs from the generator of
`λ = -1`, which is `-1`. This also shows that `UnitaryGroup` is non-empty and that the generator
domain is not always trivial.
-/

namespace Lightlike.OperatorAlgebras

open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The phase `exp (i λ t)` as a complex number of norm one. -/
private lemma norm_phase (l t : ℝ) : ‖Complex.exp (Complex.I * (l * t))‖ = 1 := by
  have h : Complex.I * ((l : ℂ) * (t : ℂ)) = ((l * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The phase group** `U t = exp (i λ t) • 1`. -/
noncomputable def phaseGroup (l : ℝ) : UnitaryGroup H where
  toFun t :=
    { toFun := fun ψ => Complex.exp (Complex.I * (l * t)) • ψ
      invFun := fun ψ => Complex.exp (-(Complex.I * (l * t))) • ψ
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]; exact smul_comm _ _ _
      left_inv := fun ψ => by
        simp [smul_smul, ← Complex.exp_add]
      right_inv := fun ψ => by
        simp [smul_smul, ← Complex.exp_add]
      norm_map' := fun ψ => by
        show ‖Complex.exp (Complex.I * (l * t)) • ψ‖ = ‖ψ‖
        rw [norm_smul, norm_phase, one_mul] }
  map_zero' := by ext ψ; simp
  map_add' := by
    intro s t; ext ψ
    simp [smul_smul, ← Complex.exp_add]
    congr 1; ring_nf
  continuous' := by
    intro ψ
    exact (Complex.continuous_exp.comp (continuous_const.mul
      (continuous_const.mul Complex.continuous_ofReal))).smul continuous_const


/-- The derivative at `0` of `t ↦ exp (i λ t) • ψ` is `(i λ) • ψ`. -/
private lemma hasDerivAt_phase (l : ℝ) (ψ : H) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (l * t)) • ψ) ((Complex.I * l) • ψ) 0 := by
  have h0 : HasDerivAt (fun z : ℂ => Complex.I * ((l : ℂ) * z)) (Complex.I * l) ((0 : ℝ) : ℂ) := by
    simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul (l : ℂ)).const_mul Complex.I
  have h1 := HasDerivAt.cexp h0
  have h2 := (HasDerivAt.comp_ofReal h1).smul_const ψ
  simpa using h2

/-- The generator domain of the phase group is the whole space. -/
theorem phaseGroup_domain (l : ℝ) :
    (phaseGroup l : UnitaryGroup H).generatorDomain = ⊤ := by
  refine top_unique fun ψ _ => ?_
  exact (hasDerivAt_phase l ψ).differentiableAt

private lemma mem_domain (l : ℝ) (ψ : H) : ψ ∈ (phaseGroup l : UnitaryGroup H).generator.domain := by
  have h : ψ ∈ (phaseGroup l : UnitaryGroup H).generatorDomain := by
    rw [phaseGroup_domain]; trivial
  exact h

/-- **Trust check, sign and factor `i`**: the generator of the phase group `exp (i λ t)` acts as `λ • 1`,
so the convention is `U t = exp (i t A)`. -/
theorem phaseGroup_generator (l : ℝ) (ψ : H) :
    (phaseGroup l : UnitaryGroup H).generator ⟨ψ, mem_domain l ψ⟩ = (l : ℂ) • ψ := by
  show (-Complex.I) • deriv (fun t => (phaseGroup l : UnitaryGroup H) t ψ) 0 = _
  have : deriv (fun t => (phaseGroup l : UnitaryGroup H) t ψ) 0 = (Complex.I * l) • ψ :=
    (hasDerivAt_phase l ψ).deriv
  rw [this, smul_smul]
  congr 1
  ring_nf
  simp

/-- **Negative control**: the phase groups of `λ = 1` and `λ = -1` have different generators (on the
vector `1 : ℂ` they give `1` and `-1`), so the generator distinguishes the direction of the flow, and
`generator` is not constant. -/
theorem phaseGroup_generator_ne :
    (phaseGroup 1 : UnitaryGroup ℂ).generator ⟨1, mem_domain 1 1⟩ ≠
      (phaseGroup (-1) : UnitaryGroup ℂ).generator ⟨1, mem_domain (-1) 1⟩ := by
  rw [phaseGroup_generator, phaseGroup_generator]
  norm_num

/-- **Non-vacuity of `UnitaryGroup.generator_isSelfAdjoint`**: it applies to the phase group, whose
generator is `λ • 1` on the whole space. -/
theorem phaseGroup_generator_isSelfAdjoint [CompleteSpace H] (l : ℝ) :
    IsSelfAdjoint (phaseGroup (H := H) l).generator :=
  UnitaryGroup.generator_isSelfAdjoint _

end Lightlike.OperatorAlgebras

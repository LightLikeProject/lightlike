import Lightlike.OperatorAlgebras.StoneGenerator

/-!
# Uniqueness in Stone's theorem

Helper lemmas for `T-OP1-P3` (`Tasks/OP/T_OP1_P3.lean`): two strongly continuous unitary groups with the
same generator are equal. For `ψ` in the common domain, `w t = U t ψ - V t ψ` solves `w' = i A w`, and
`A` is symmetric, so `‖w t‖²` is constant, hence zero; density of the domain finishes the proof.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.UnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Equal partial operators agree on equal vectors (whatever the membership proofs). -/
omit [CompleteSpace H] in
lemma pmap_apply_congr {B C : H →ₗ.[ℂ] H} (h : B = C) (x : H) (hx : x ∈ B.domain)
    (hx' : x ∈ C.domain) : B ⟨x, hx⟩ = C ⟨x, hx'⟩ := by
  subst h; rfl

/-- Two unitary groups with the same generator agree on the domain of the generator. -/
lemma apply_eq_of_generator_eq {U V : UnitaryGroup H} (h : U.generator = V.generator)
    (ψ : H) (hψ : ψ ∈ U.generator.domain) (t : ℝ) : U t ψ = V t ψ := by
  set A := U.generator with hA
  have hdom : V.generator.domain = A.domain := (congrArg LinearPMap.domain h).symm
  have hψV : ψ ∈ V.generator.domain := hdom ▸ hψ
  have hψ' : DifferentiableAt ℝ (fun t => U t ψ) 0 := hψ
  have hψV' : DifferentiableAt ℝ (fun t => V t ψ) 0 := hψV
  have memU : ∀ t, U t ψ ∈ A.domain := fun t => U.differentiableAt_apply hψ' t
  have memV : ∀ t, V t ψ ∈ V.generator.domain := fun t => V.differentiableAt_apply hψV' t
  have memV' : ∀ t, V t ψ ∈ A.domain := fun t => hdom ▸ memV t
  have hU : ∀ t, HasDerivAt (fun s => U s ψ) (Complex.I • A ⟨U t ψ, memU t⟩) t := by
    intro t
    have h1 := U.hasDerivAt_of_mem hψ' t
    have h2 := U.dvec_apply hψ' t
    have h3 := U.dvec_eq ⟨U t ψ, memU t⟩
    simp only at h3
    rw [h2] at h3
    rw [← h3]; exact h1
  have hV : ∀ t, HasDerivAt (fun s => V s ψ) (Complex.I • A ⟨V t ψ, memV' t⟩) t := by
    intro t
    have h1 := V.hasDerivAt_of_mem hψV' t
    have h2 := V.dvec_apply hψV' t
    have h3 := V.dvec_eq ⟨V t ψ, memV t⟩
    simp only at h3
    rw [h2] at h3
    have h4 := pmap_apply_congr h.symm (V t ψ) (memV t) (memV' t)
    rw [h4] at h3
    rw [← h3]; exact h1
  let w : ℝ → H := fun t => U t ψ - V t ψ
  have memW : ∀ t, w t ∈ A.domain := fun t => A.domain.sub_mem (memU t) (memV' t)
  have hAw : ∀ t, A ⟨w t, memW t⟩ = A ⟨U t ψ, memU t⟩ - A ⟨V t ψ, memV' t⟩ := by
    intro t
    have : (⟨w t, memW t⟩ : A.domain) = ⟨U t ψ, memU t⟩ - ⟨V t ψ, memV' t⟩ := rfl
    rw [this]; exact A.toFun.map_sub _ _
  have hw : ∀ t, HasDerivAt w (Complex.I • A ⟨w t, memW t⟩) t := by
    intro t
    rw [hAw, smul_sub]
    exact (hU t).sub (hV t)
  let Φ : ℝ → ℂ := fun t => ⟪w t, w t⟫_ℂ
  have hΦ : ∀ t, HasDerivAt Φ 0 t := by
    intro t
    have := HasDerivAt.inner ℂ (hw t) (hw t)
    refine this.congr_deriv ?_
    have hs : ⟪(A ⟨w t, memW t⟩ : H), w t⟫_ℂ = ⟪w t, (A ⟨w t, memW t⟩ : H)⟫_ℂ :=
      U.generator_isFormalAdjoint ⟨w t, memW t⟩ ⟨w t, memW t⟩
    simp only [inner_smul_left, inner_smul_right]
    rw [hs, Complex.conj_I]; ring
  have hc := is_const_of_deriv_eq_zero (f := Φ) (fun x => (hΦ x).differentiableAt)
    (fun x => (hΦ x).deriv) t 0
  have h0 : Φ 0 = 0 := by simp [Φ, w, apply_zero]
  have : ⟪w t, w t⟫_ℂ = 0 := by
    have := hc.trans h0
    exact this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

/-- **Uniqueness in Stone's theorem**: two strongly continuous unitary groups with the same generator
are equal. -/
theorem eq_of_generator_eq {U V : UnitaryGroup H} (h : U.generator = V.generator) : U = V := by
  have hd : ∀ t, ∀ ψ, U t ψ = V t ψ := by
    intro t ψ
    have h1 : Continuous fun x : H => U t x := (U t).continuous
    have h2 : Continuous fun x : H => V t x := (V t).continuous
    exact congrFun (Continuous.ext_on U.dense_generatorDomain h1 h2
      (fun x hx => U.apply_eq_of_generator_eq h x hx t)) ψ
  ext t ψ
  exact hd t ψ

end Lightlike.OperatorAlgebras.UnitaryGroup

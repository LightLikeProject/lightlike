import Lightlike.OperatorAlgebras.StoneGenerator
import Physlib.QuantumMechanics.Operators.Unbounded

/-!
# A dense invariant subspace of the domain of the generator is a core

Helper lemmas for `T-OP1-P4` (`Tasks/OP/T_OP1_P4.lean`). Let `U` be a strongly continuous unitary group with
generator `A`, and `D` a dense subspace of the domain of `A` with `U t D ⊆ D`. Then the closure of `A`
restricted to `D` is `A` (a theorem of Nelson type; the proof follows the one that the generator is
self-adjoint, `UnitaryGroup.generator_isSelfAdjoint`, with `D` in place of the whole domain): the adjoint of
`A|_D` lies below `A`, so it equals `A` (the other inequality is `A|_D ≤ A`, `A` self-adjoint), and
`closure (A|_D) = (A|_D)†† = A† = A` (Physlib: `LinearPMap.IsUnbounded.adjoint_adjoint_eq_closure`).

The lemmas about `y` with `⟪w, x⟫ = ⟪y, A x⟫` for `x ∈ D` are those of `StoneGenerator.lean` for the adjoint
`A†`, which is the case `D = ` the domain of `A`.
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras.UnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : UnitaryGroup H) (D : Submodule ℂ H)

/-- The weak equation `⟪w, x⟫ = ⟪y, A x⟫` for all `x` in `D`. -/
def WeakGen (y w : H) : Prop :=
  ∀ x (hx : x ∈ U.generator.domain), x ∈ D → ⟪w, x⟫_ℂ = ⟪y, (U.generator ⟨x, hx⟩ : H)⟫_ℂ

variable {U D}

lemma hasDerivAt_inner_weak (hinv : ∀ t, ∀ x ∈ D, U t x ∈ D) {y w : H} (hyw : U.WeakGen D y w)
    (ψ : U.generator.domain) (hψD : (ψ : H) ∈ D) (t : ℝ) :
    HasDerivAt (fun t => ⟪U t y, (ψ : H)⟫_ℂ) ⟪Complex.I • U t w, (ψ : H)⟫_ℂ t := by
  have hψ : DifferentiableAt ℝ (fun t => U t (ψ : H)) 0 := ψ.2
  have hg := U.hasDerivAt_of_mem hψ (-t)
  have h2 : HasDerivAt (fun s : ℝ => U (-s) (ψ : H)) ((-1 : ℝ) • U (-t) (U.dvec (ψ : H))) t :=
    HasDerivAt.scomp t hg (hasDerivAt_neg t)
  have h3 := HasDerivAt.inner ℂ (hasDerivAt_const t y) h2
  have hfun : (fun t => ⟪U t y, (ψ : H)⟫_ℂ) = fun s => ⟪y, U (-s) (ψ : H)⟫_ℂ := by
    funext s; exact U.inner_apply s _ _
  rw [hfun]
  refine h3.congr_deriv ?_
  have hx : U (-t) (ψ : H) ∈ U.generator.domain := U.differentiableAt_apply hψ (-t)
  have hd : U.dvec (U (-t) (ψ : H)) = U (-t) (U.dvec (ψ : H)) := U.dvec_apply hψ (-t)
  have hdv := U.dvec_eq ⟨_, hx⟩
  have hw := hyw (U (-t) (ψ : H)) hx (hinv (-t) _ hψD)
  simp only at hdv
  rw [hd] at hdv
  rw [hdv]
  simp only [inner_zero_left, add_zero, neg_smul, one_smul, inner_neg_right, inner_smul_right,
    inner_smul_left]
  rw [← hw, U.inner_apply t]
  simp

/-- A vector orthogonal to a dense subspace is zero. -/
lemma eq_zero_of_inner_dense (hdense : Dense (D : Set H)) {v : H} (h : ∀ ψ ∈ D, ⟪v, ψ⟫_ℂ = 0) :
    v = 0 := by
  have h1 : Continuous fun x : H => ⟪v, x⟫_ℂ := continuous_const.inner continuous_id
  have h2 : ⟪v, v⟫_ℂ = 0 := by
    have := Continuous.ext_on hdense h1 continuous_const (f := fun x : H => ⟪v, x⟫_ℂ)
      (g := fun _ => (0 : ℂ)) (fun x hx => h x hx)
    exact congrFun this v
  exact inner_self_eq_zero.1 h2

/-- The integral form of the evolution of a vector `y` with `WeakGen`:
`U t y = y + i ∫₀ᵗ U s w ds`. -/
lemma apply_eq_of_weak (hdense : Dense (D : Set H)) (hD : D ≤ U.generatorDomain)
    (hinv : ∀ t, ∀ x ∈ D, U t x ∈ D) {y w : H} (hyw : U.WeakGen D y w) (t : ℝ) :
    U t y = y + Complex.I • U.prim w t := by
  have key : ∀ ψ ∈ D, ⟪U t y - y - Complex.I • U.prim w t, ψ⟫_ℂ = 0 := by
    intro ψ hψ
    let Φ : ℝ → ℂ := fun t => ⟪U t y - y - Complex.I • U.prim w t, ψ⟫_ℂ
    have hd : ∀ x, HasDerivAt Φ 0 x := by
      intro x
      have a := hasDerivAt_inner_weak hinv hyw ⟨ψ, hD hψ⟩ hψ x
      have b : HasDerivAt (fun t => Complex.I • U.prim w t) (Complex.I • U x w) x :=
        (U.hasDerivAt_prim w x).const_smul Complex.I
      have c := HasDerivAt.inner ℂ b (hasDerivAt_const x ψ)
      have hΦ : Φ = fun t => ⟪U t y, ψ⟫_ℂ - ⟪y, ψ⟫_ℂ - ⟪Complex.I • U.prim w t, ψ⟫_ℂ := by
        funext t; simp only [Φ, inner_sub_left]
      rw [hΦ]
      have := (a.sub (hasDerivAt_const x ⟪y, ψ⟫_ℂ)).sub c
      refine this.congr_deriv ?_
      simp
    have hconst := is_const_of_deriv_eq_zero (f := Φ) (fun x => (hd x).differentiableAt)
      (fun x => (hd x).deriv) t 0
    have h0 : Φ 0 = 0 := by simp [Φ, apply_zero, prim_zero]
    rw [← h0]; exact hconst
  have hz := eq_zero_of_inner_dense hdense key
  exact sub_eq_zero.1 (by rw [sub_sub] at hz; exact hz)

/-- A vector with `WeakGen` lies in the domain of the generator, and its image is `w`. -/
lemma mem_domain_of_weak (hdense : Dense (D : Set H)) (hD : D ≤ U.generatorDomain)
    (hinv : ∀ t, ∀ x ∈ D, U t x ∈ D) {y w : H} (hyw : U.WeakGen D y w) :
    ∃ hy : y ∈ U.generator.domain, (U.generator ⟨y, hy⟩ : H) = w := by
  have hfun : (fun t => U t y) = fun t => y + Complex.I • U.prim w t := by
    funext t; exact apply_eq_of_weak hdense hD hinv hyw t
  have hder : HasDerivAt (fun t => U t y) (Complex.I • w) 0 := by
    rw [hfun]
    have := (hasDerivAt_const (0 : ℝ) y).add ((U.hasDerivAt_prim w 0).const_smul Complex.I)
    refine this.congr_deriv ?_
    rw [apply_zero, zero_add]
  have hy : y ∈ U.generator.domain := hder.differentiableAt
  refine ⟨hy, ?_⟩
  have hdv : U.dvec y = Complex.I • w := hder.deriv
  rw [generator_apply, hdv, smul_smul]
  simp

/-- **Nelson-type core theorem**: the closure of the generator restricted to a dense `U`-invariant subspace
`D` of its domain is the generator. -/
theorem closure_domRestrict_generator (hdense : Dense (D : Set H)) (hD : D ≤ U.generatorDomain)
    (hinv : ∀ t, ∀ x ∈ D, U t x ∈ D) :
    (U.generator.domRestrict D).closure = U.generator := by
  set A := U.generator with hA
  set AD := A.domRestrict D with hAD
  have hdom : AD.domain = D := by
    rw [hAD, LinearPMap.domRestrict_domain]; exact inf_eq_left.2 hD
  have hdAD : Dense (AD.domain : Set H) := by rw [hdom]; exact hdense
  have hsa : IsSelfAdjoint A := U.generator_isSelfAdjoint
  have hle : AD ≤ A := by
    refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
    · exact (inf_le_right : D ⊓ A.domain ≤ A.domain) (by rwa [hAD, LinearPMap.domRestrict_domain] at hx)
    · exact LinearPMap.domRestrict_apply hxy
  have hcl : AD.IsClosable := (hsa.isClosed.isClosable).leIsClosable hle
  have hun : AD.IsUnbounded := ⟨hdAD, hcl⟩
  rw [← hun.adjoint_adjoint_eq_closure]
  have hwk : ∀ y (hy : y ∈ (AD†).domain), U.WeakGen D y ((AD† ⟨y, hy⟩ : H)) := by
    intro y hy x hx hxD
    have hxAD : x ∈ AD.domain := by rw [hdom]; exact hxD
    have := LinearPMap.adjoint_isFormalAdjoint hdAD ⟨y, hy⟩ ⟨x, hxAD⟩
    rw [this]
    congr 1
  have hadj : AD† = A := by
    refine le_antisymm ?_ ?_
    · refine ⟨fun y hy => (mem_domain_of_weak hdense hD hinv (hwk y hy)).1, ?_⟩
      intro y' y'' hy
      have hy' : (y' : H) = y'' := hy
      have hmem := mem_domain_of_weak hdense hD hinv (hwk y' y'.2)
      obtain ⟨hy1, hy2⟩ := hmem
      have : (⟨(y' : H), hy1⟩ : A.domain) = y'' := Subtype.ext hy'
      rw [← this]
      exact hy2.symm
    · refine LinearPMap.IsFormalAdjoint.le_adjoint hdAD (fun x y => ?_)
      have hxA : (x : H) ∈ A.domain := by
        have hiff : ∀ z : H, z ∈ AD.domain ↔ z ∈ D ⊓ A.domain := fun z => by
          rw [hAD, LinearPMap.domRestrict_domain]
        exact ((hiff x).1 x.2).2
      have h2 : AD x = A ⟨x, hxA⟩ := LinearPMap.domRestrict_apply (rfl : ((x : H)) = ((⟨x, hxA⟩ : A.domain) : H))
      rw [h2]
      exact U.generator_isFormalAdjoint ⟨x, hxA⟩ y
  rw [hadj]
  exact hsa

end Lightlike.OperatorAlgebras.UnitaryGroup

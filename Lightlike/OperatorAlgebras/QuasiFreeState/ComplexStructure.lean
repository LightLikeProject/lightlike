import Lightlike.OperatorAlgebras.QuasiFreeState.FockEquiv

/-!
# Purity of a quasi-free state from a complex structure

On a real symplectic space `(V, ω)` with a covariance `η`, a **compatible complex structure** is a real-linear `J` with
`J² = -1`, `η(Jx, Jy) = η(x, y)`, `ω(x, y) = -η(x, Jy)`, and `η` positive definite. Then `V` is a complex inner product
space with `(a + i b) • x = a x + b J x` and `⟨x, y⟩ = η(x, y) + i ω(x, y)`, whose real part is `η` and whose
imaginary part is `ω`, so the quasi-free state `ω_η` is the Fock vacuum state of this space and is pure
(`isPureState_qfState_of_complexStructure`; this file proves the sufficiency half of the purity criterion, via
`isPureState_qfState_of_equiv`).

In a basis this is the finite-dimensional matrix condition used for the Sorkin-Johnston state: with `Ω` the matrix of
`ω`, `H` that of `η`, the condition `ω(x, y) = -η(x, Jy)`, `J² = -1` says `Ω H⁻¹ Ω = -H` (`η` nondegenerate).
-/

open scoped InnerProductSpace ComplexConjugate

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

/-- **A compatible complex structure** for `(V, ω, η)`: `J² = -1`, `η` is `J`-invariant and positive definite, and
`ω(x, y) = -η(x, J y)`. -/
structure CompatibleComplexStructure {V : Type u} [AddCommGroup V] [Module ℝ V]
    (ω η : LinearMap.BilinForm ℝ V) where
  /-- The complex structure. -/
  J : V →ₗ[ℝ] V
  /-- `J² = -1`. -/
  J_sq : ∀ x, J (J x) = -x
  /-- `η` is symmetric. -/
  symm : ∀ x y, η x y = η y x
  /-- `η` is invariant under `J`. -/
  eta_J : ∀ x y, η (J x) (J y) = η x y
  /-- `η` is positive definite. -/
  eta_pos : ∀ x, x ≠ 0 → 0 < η x x
  /-- `ω(x, y) = -η(x, J y)`. -/
  omega_eq : ∀ x y, ω x y = -η x (J y)

variable {V : Type u} [AddCommGroup V] [Module ℝ V] {ω η : LinearMap.BilinForm ℝ V}

namespace CompatibleComplexStructure

variable (S : CompatibleComplexStructure ω η)

include S

/-- `η(x, J x) = 0`. -/
lemma eta_J_self (x : V) : η x (S.J x) = 0 := by
  have h1 : η (S.J x) (S.J (S.J x)) = η x (S.J x) := S.eta_J x (S.J x)
  rw [S.J_sq, map_neg, S.symm] at h1
  linarith

/-- **`ω` is antisymmetric.** -/
lemma omega_antisymm (x y : V) : ω x y = -ω y x := by
  rw [S.omega_eq, S.omega_eq]
  have h1 : η y (S.J x) = η (S.J y) (S.J (S.J x)) := (S.eta_J y (S.J x)).symm
  rw [S.J_sq, map_neg, S.symm (S.J y) x] at h1
  linarith

/-- `η(J x, y) = ω(x, y)`. -/
lemma eta_J_left (x y : V) : η (S.J x) y = ω x y := by
  have h1 := S.eta_J (S.J x) y
  rw [S.J_sq, map_neg, LinearMap.neg_apply] at h1
  rw [S.omega_eq]; linarith

/-- `ω(J x, y) = -η(x, y)`. -/
lemma omega_J_left (x y : V) : ω (S.J x) y = -η x y := by
  rw [S.omega_eq, S.eta_J]

/-- **A compatible complex structure gives a covariance**: `ω(a, b)² ≤ η(a, a) η(b, b)` (Cauchy-Schwarz for `η`, with
`η(J b, J b) = η(b, b)`), so `qfFact` produces the instance needed to state purity. -/
lemma isCovariance : IsCovariance ω η where
  symm := S.symm
  nonneg a := by
    by_cases ha : a = 0
    · subst ha; simp
    · exact (S.eta_pos a ha).le
  sq_le a b := by
    have hcs : ∀ x y : V, η x y ^ 2 ≤ η x x * η y y := by
      intro x y
      have hq : ∀ t : ℝ, 0 ≤ η y y * (t * t) + (2 * η x y) * t + η x x := by
        intro t
        have h0 : 0 ≤ η (x + t • y) (x + t • y) := by
          by_cases hz : x + t • y = 0
          · rw [hz]; simp
          · exact (S.eta_pos _ hz).le
        have h1 : η (x + t • y) (x + t • y) = η x x + 2 * t * η x y + t ^ 2 * η y y := by
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [S.symm y x]; ring
        nlinarith
      have := discrim_le_zero hq
      unfold discrim at this
      nlinarith
    rw [S.omega_eq, neg_sq]
    have := hcs a (S.J b)
    rw [S.eta_J b b] at this
    exact this

/-- The complex scalar multiplication `(a + i b) • x = a x + b J x`. -/
def smulC (z : ℂ) (x : V) : V := z.re • x + z.im • S.J x

/-- `1 • x = x`. -/
lemma smulC_one (x : V) : S.smulC 1 x = x := by simp [smulC]

/-- `(z w) • x = z • (w • x)`. -/
lemma smulC_mul (z w : ℂ) (x : V) : S.smulC (z * w) x = S.smulC z (S.smulC w x) := by
  simp only [smulC, map_add, map_smul, S.J_sq, Complex.mul_re, Complex.mul_im]
  module

/-- `z • 0 = 0`. -/
lemma smulC_zero_vec (z : ℂ) : S.smulC z 0 = 0 := by simp [smulC]

/-- `z • (x + y) = z • x + z • y`. -/
lemma smulC_add_vec (z : ℂ) (x y : V) : S.smulC z (x + y) = S.smulC z x + S.smulC z y := by
  simp only [smulC, map_add]
  module

/-- `(z + w) • x = z • x + w • x`. -/
lemma add_smulC (z w : ℂ) (x : V) : S.smulC (z + w) x = S.smulC z x + S.smulC w x := by
  simp only [smulC, Complex.add_re, Complex.add_im]
  module

/-- `0 • x = 0`. -/
lemma zero_smulC (x : V) : S.smulC 0 x = 0 := by simp [smulC]

/-- **The complex module structure** `(a + i b) • x = a x + b J x`. -/
abbrev cmodule : Module ℂ V where
  smul := S.smulC
  one_smul := S.smulC_one
  mul_smul := S.smulC_mul
  smul_zero := S.smulC_zero_vec
  smul_add := S.smulC_add_vec
  add_smul := S.add_smulC
  zero_smul := S.zero_smulC

/-- **The inner product** `⟨x, y⟩ = η(x, y) + i ω(x, y)` as a core inner product space over the complex module
structure `cmodule`. -/
def innerCore : @InnerProductSpace.Core ℂ V _ _ S.cmodule :=
  letI := S.cmodule
  { inner := fun x y => (η x y : ℂ) + Complex.I * (ω x y : ℂ)
    conj_inner_symm := fun x y => by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      rw [S.symm y x, S.omega_antisymm y x]
      push_cast; ring
    re_inner_nonneg := fun x => by
      have h0 : ω x x = 0 := by have := S.omega_antisymm x x; linarith
      by_cases hx : x = 0
      · subst hx; simp [map_zero]
      · simp [h0, (S.eta_pos x hx).le]
    add_left := fun x y z => by simp only [map_add, LinearMap.add_apply]; push_cast; ring
    smul_left := fun x y r => by
      show (η (r.re • x + r.im • S.J x) y : ℂ) + Complex.I * (ω (r.re • x + r.im • S.J x) y : ℂ) = _
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [S.eta_J_left, S.omega_J_left]
      have hc : (starRingEnd ℂ) r = (r.re : ℂ) - r.im * Complex.I := by
        apply Complex.ext <;> simp
      rw [hc]; push_cast; ring_nf; simp [Complex.I_sq]
    definite := fun x hx => by
      by_contra hne
      have := S.eta_pos x hne
      have h0 : ω x x = 0 := by have := S.omega_antisymm x x; linarith
      simp [h0] at hx
      linarith }

end CompatibleComplexStructure

/-- **Purity of a quasi-free state with a compatible complex structure** (sufficiency half of the purity criterion): if
`J² = -1`, `η` is `J`-invariant and positive definite and `ω(x, y) = -η(x, J y)`, then the quasi-free state `ω_η` is
pure. The proof makes `V` a complex inner product space with `⟨x, y⟩ = η(x, y) + i ω(x, y)` and applies
`isPureState_qfState_of_equiv` with `e = id`. -/
theorem isPureState_qfState_of_complexStructure [Fact (qfKerM ω η).PosSemidef]
    (S : CompatibleComplexStructure ω η) :
    IsPureState (qfState ω η S.omega_antisymm) := by
  letI : Module ℂ V := S.cmodule
  letI c : InnerProductSpace.Core ℂ V := S.innerCore
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ c
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  refine isPureState_qfState_of_equiv ω η S.omega_antisymm (h := V) (AddEquiv.refl V) ?_ ?_
  · intro a b
    show ω a b = ((η a b : ℂ) + Complex.I * (ω a b : ℂ)).im
    simp
  · intro a b
    show η a b = ((η a b : ℂ) + Complex.I * (ω a b : ℂ)).re
    simp


end Lightlike.OperatorAlgebras.QuasiFreeState

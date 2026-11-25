import Mathlib
import Lightlike.Canonical.PolymerEvolution.Polymer
import Lightlike.OperatorAlgebras.Spectral.Unbounded.Basic

/-!
# The `μ̄` evolution operator on the polymer Hilbert space

Row G2-017 (milestone CA7).  The Hamiltonian-constraint ("evolution") operator of the improved
(`μ̄`) dynamics of loop quantum cosmology is a second order difference operator on the polymer Hilbert
space,
`(Θ ψ)(v) = c(v) ψ(v) - a(v) ψ(v + h) - a(v - h) ψ(v - h)`,
with real coefficients `a`, `c` (for the Ashtekar–Pawlowski–Singh model `h = 4`).  Here `Θ` is the
general operator `diffOp h a c`, an unbounded operator (`LinearPMap`) with domain the finite linear
combinations of kets.

## Main definitions and statements

* `formal h a c`: the formal difference expression on functions `ℝ → ℂ`;
* `diffOp h a c`: the operator `Θ` with domain `polymerDomain`;
* `diffOp_ket`: `Θ |v⟩ = c(v) |v⟩ - a(v - h) |v - h⟩ - a(v) |v + h⟩`;
* `diffOp_isSymmetric`: `Θ` is symmetric.

References: Ashtekar–Pawlowski–Singh 2006 (`aps-2006`), Kamiński–Lewandowski 2008
(`kaminski-lewandowski-2008`).
-/

open scoped InnerProductSpace LinearPMap
open Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Rows.G2_017

noncomputable section

/-- **The formal difference expression** `(ψ ↦ c(v) ψ(v) - a(v) ψ(v+h) - a(v-h) ψ(v-h))`. -/
def formal (h : ℝ) (a c : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun v => (c v : ℂ) * ψ v - (a v : ℂ) * ψ (v + h) - (a (v - h) : ℂ) * ψ (v - h)

theorem formal_add (h : ℝ) (a c : ℝ → ℝ) (ψ φ : ℝ → ℂ) :
    formal h a c (ψ + φ) = formal h a c ψ + formal h a c φ := by
  funext v
  simp only [formal, Pi.add_apply]
  ring

theorem formal_smul (h : ℝ) (a c : ℝ → ℝ) (r : ℂ) (ψ : ℝ → ℂ) :
    formal h a c (r • ψ) = r • formal h a c ψ := by
  funext v
  simp only [formal, Pi.smul_apply, smul_eq_mul]
  ring

/-- Elements of the span of the kets have finite support. -/
theorem finite_support_of_mem_polymerDomain {ψ : PolymerSpace} (hψ : ψ ∈ polymerDomain) :
    {v : ℝ | ψ v ≠ 0}.Finite := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine (Set.finite_singleton v).subset ?_
    intro w hw
    by_contra hne
    apply hw
    rw [ket_apply]
    simp only [Set.mem_singleton_iff] at hne
    simp [hne]
  | zero => simp
  | add x y _ _ hx hy =>
    refine (hx.union hy).subset ?_
    intro w hw
    by_contra hne
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hne
    apply hw
    simp [hne.1, hne.2]
  | smul r x _ hx =>
    refine hx.subset ?_
    intro w hw
    by_contra hne
    simp only [Set.mem_ofPred_eq, not_not] at hne
    apply hw
    simp [hne]

/-- The formal expression of a finitely supported function is finitely supported. -/
theorem finite_support_formal {h : ℝ} {a c : ℝ → ℝ} {ψ : ℝ → ℂ} (hψ : {v : ℝ | ψ v ≠ 0}.Finite) :
    {v : ℝ | formal h a c ψ v ≠ 0}.Finite := by
  have h1 := hψ.image (fun v => v - h)
  have h2 := hψ.image (fun v => v + h)
  refine (hψ.union (h1.union h2)).subset ?_
  intro v hv
  by_contra hne
  apply hv
  have e0 : ψ v = 0 := by
    by_contra h0
    exact hne (Or.inl h0)
  have e1 : ψ (v + h) = 0 := by
    by_contra h0
    exact hne (Or.inr (Or.inl ⟨v + h, h0, by simp⟩))
  have e2 : ψ (v - h) = 0 := by
    by_contra h0
    exact hne (Or.inr (Or.inr ⟨v - h, h0, by simp⟩))
  simp [formal, e0, e1, e2]

/-- The formal expression of an element of the polymer domain is square summable. -/
theorem memℓp_formal (h : ℝ) (a c : ℝ → ℝ) {ψ : PolymerSpace} (hψ : ψ ∈ polymerDomain) :
    Memℓp (formal h a c ψ) 2 :=
  Memℓp.of_exponent_ge (memℓp_zero (finite_support_formal (finite_support_of_mem_polymerDomain hψ)))
    bot_le

/-- **The evolution operator** `Θ ψ (v) = c(v) ψ(v) - a(v) ψ(v+h) - a(v-h) ψ(v-h)` on the polymer
Hilbert space, with domain the finite linear combinations of kets. -/
def diffOp (h : ℝ) (a c : ℝ → ℝ) : PolymerSpace →ₗ.[ℂ] PolymerSpace where
  domain := polymerDomain
  toFun :=
    { toFun := fun ψ => ⟨formal h a c (ψ : PolymerSpace), memℓp_formal h a c ψ.2⟩
      map_add' := fun _ _ => Subtype.ext (formal_add h a c _ _)
      map_smul' := fun r _ => Subtype.ext (formal_smul h a c r _) }

/-- The domain of `diffOp` is the span of the kets. -/
@[simp] theorem diffOp_domain (h : ℝ) (a c : ℝ → ℝ) : (diffOp h a c).domain = polymerDomain :=
  rfl

/-- Pointwise formula for `Θ`. -/
theorem diffOp_apply (h : ℝ) (a c : ℝ → ℝ) (ψ : (diffOp h a c).domain) (v : ℝ) :
    (diffOp h a c ψ) v = (c v : ℂ) * ψ.1 v - (a v : ℂ) * ψ.1 (v + h) - (a (v - h) : ℂ) * ψ.1 (v - h) :=
  rfl

/-- The ket `|v⟩` lies in the domain of `Θ`. -/
theorem ket_mem_domain (h : ℝ) (a c : ℝ → ℝ) (v : ℝ) : ket v ∈ (diffOp h a c).domain :=
  Submodule.subset_span ⟨v, rfl⟩

/-- **`Θ` on a ket**: `Θ |v⟩ = c(v) |v⟩ - a(v - h) |v - h⟩ - a(v) |v + h⟩`. -/
theorem diffOp_ket (h : ℝ) (a c : ℝ → ℝ) (v : ℝ) :
    diffOp h a c ⟨ket v, ket_mem_domain h a c v⟩ =
      (c v : ℂ) • ket v - (a (v - h) : ℂ) • ket (v - h) - (a v : ℂ) • ket (v + h) := by
  apply Subtype.ext
  funext w
  rw [diffOp_apply]
  show _ = (c v : ℂ) * ket v w - (a (v - h) : ℂ) * ket (v - h) w - (a v : ℂ) * ket (v + h) w
  simp only [ket_apply]
  have e1 : (w + h = v) ↔ (w = v - h) := by constructor <;> intro e <;> linarith
  have e2 : (w - h = v) ↔ (w = v + h) := by constructor <;> intro e <;> linarith
  simp only [e1, e2]
  by_cases h1 : w = v
  · subst h1
    by_cases h2 : w = w - h
    · have h3 : h = 0 := by linarith
      subst h3
      simp
    · by_cases h3 : w = w + h
      · have h4 : h = 0 := by linarith
        subst h4
        simp at h2
      · simp [h2, h3]
  · by_cases h2 : w = v - h
    · have h3 : w ≠ v + h := by
        intro e
        have : h = 0 := by linarith
        subst this
        simp at h2
        exact h1 h2
      subst h2
      simp [h1, h3]
    · by_cases h3 : w = v + h
      · subst h3
        simp [h1, h2]
      · simp [h1, h2, h3]

/-- Symmetry of `Θ` on a pair of kets. -/
theorem diffOp_symm_ket (h : ℝ) (a c : ℝ → ℝ) (u v : ℝ) :
    ⟪ket u, diffOp h a c ⟨ket v, ket_mem_domain h a c v⟩⟫_ℂ =
      ⟪diffOp h a c ⟨ket u, ket_mem_domain h a c u⟩, ket v⟫_ℂ := by
  rw [diffOp_ket, diffOp_ket]
  simp only [inner_sub_right, inner_smul_right, inner_sub_left, inner_smul_left,
    inner_ket, Complex.conj_ofReal]
  have e1 : (u = v - h) ↔ (u + h = v) := by constructor <;> intro e <;> linarith
  have e2 : (u = v + h) ↔ (u - h = v) := by constructor <;> intro e <;> linarith
  simp only [e1, e2]
  by_cases h1 : u = v
  · subst h1
    by_cases h2 : u + h = u
    · have h3 : h = 0 := by linarith
      subst h3
      simp
    · have h3 : u - h ≠ u := fun e => h2 (by linarith)
      simp [h2, h3]
  · by_cases h2 : u + h = v
    · have h3 : ¬ (u - h = v) := by
        intro e
        have : h = 0 := by linarith
        subst this
        simp at h2
        exact h1 h2
      subst h2
      simp [h1, h3]
    · by_cases h3 : u - h = v
      · subst h3
        simp [h1, h2]
      · simp [h1, h2, h3]

/-- Symmetry of `Θ` between a ket and an arbitrary element of the domain. -/
theorem diffOp_symm_ket_left (h : ℝ) (a c : ℝ → ℝ) (u : ℝ) {ψ : PolymerSpace}
    (hψ : ψ ∈ (diffOp h a c).domain) :
    ⟪ket u, diffOp h a c ⟨ψ, hψ⟩⟫_ℂ = ⟪diffOp h a c ⟨ket u, ket_mem_domain h a c u⟩, ψ⟫_ℂ := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact diffOp_symm_ket h a c u v
  | zero =>
    have : (⟨0, Submodule.zero_mem _⟩ : (diffOp h a c).domain) = 0 := rfl
    rw [this]
    simp
  | add x y hx hy ihx ihy =>
    have := (diffOp h a c).map_add ⟨x, hx⟩ ⟨y, hy⟩
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : (diffOp h a c).domain) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, this, inner_add_right, inner_add_right, ihx, ihy]
  | smul r x hx ihx =>
    have := (diffOp h a c).map_smul r ⟨x, hx⟩
    have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : (diffOp h a c).domain) = r • ⟨x, hx⟩ := rfl
    rw [e, this, inner_smul_right, inner_smul_right, ihx]

/-- **`Θ` is symmetric**: `⟨φ, Θ ψ⟩ = ⟨Θ φ, ψ⟩` on the domain of finite linear combinations of kets. -/
theorem diffOp_isSymmetric (h : ℝ) (a c : ℝ → ℝ) : IsSymmetric (diffOp h a c) := by
  intro φ ψ
  obtain ⟨φ, hφ⟩ := φ
  obtain ⟨ψ, hψ⟩ := ψ
  show ⟪φ, diffOp h a c ⟨ψ, hψ⟩⟫_ℂ = ⟪diffOp h a c ⟨φ, hφ⟩, ψ⟫_ℂ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    exact diffOp_symm_ket_left h a c u hψ
  | zero =>
    have : (⟨0, Submodule.zero_mem _⟩ : (diffOp h a c).domain) = 0 := rfl
    rw [this]
    simp
  | add x y hx hy ihx ihy =>
    have := (diffOp h a c).map_add ⟨x, hx⟩ ⟨y, hy⟩
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : (diffOp h a c).domain) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, this, inner_add_left, inner_add_left, ihx, ihy]
  | smul r x hx ihx =>
    have := (diffOp h a c).map_smul r ⟨x, hx⟩
    have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : (diffOp h a c).domain) = r • ⟨x, hx⟩ := rfl
    rw [e, this, inner_smul_left, inner_smul_left, ihx]

end

end Lightlike.Rows.G2_017

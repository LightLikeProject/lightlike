module

public import Mathlib

/-!
# Induced actions from a section of an orbit (the Wigner–Mackey construction, algebraic part)

Let a group `G` act on a set `X`, let `x₀ ∈ X`, and let `L : X → G` be a section of the orbit map, `L x • x₀ = x`
(on an orbit). The *Wigner element* `W(g, x) = L(g • x)⁻¹ g L(x)` lies in the stabiliser of `x₀`
(`wignerG_mem_stabilizer`) and satisfies the cocycle identity `W(g'g, x) = W(g', g • x) W(g, x)` (`wignerG_mul`).
For a homomorphism `D` from the stabiliser to the linear endomorphisms of `V`, the formula
`(U(g) ψ)(x) = D(W(g, g⁻¹ • x)) ψ(g⁻¹ • x)` is an action of `G` on functions `X → V` (`inducedActG_mul`,
`inducedActG_one`): the induced representation, before any measure is chosen.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1, equations (10)–(13) (page 10 of v2), and §3.3 (page 14 of v2: the same method for the
  massless little group `ISO(D − 2)`).
-/

@[expose] public section

noncomputable section

namespace Lightlike.Poincare

variable {G X : Type*} [Group G] [MulAction G X]

/-- The Wigner element `W(g, x) = L(g • x)⁻¹ g L(x)`. -/
def wignerG (L : X → G) (g : G) (x : X) : G := (L (g • x))⁻¹ * g * L x

/-- The Wigner element lies in the stabiliser of the base point. -/
lemma wignerG_mem_stabilizer {x₀ : X} {L : X → G} (hL : ∀ x, L x • x₀ = x) (g : G) (x : X) :
    wignerG L g x ∈ MulAction.stabilizer G x₀ := by
  rw [MulAction.mem_stabilizer_iff, wignerG, mul_smul, mul_smul, hL, inv_smul_eq_iff, hL]

/-- **Cocycle identity.** -/
lemma wignerG_mul (L : X → G) (g' g : G) (x : X) :
    wignerG L (g' * g) x = wignerG L g' (g • x) * wignerG L g x := by
  simp only [wignerG, mul_smul]
  group

lemma wignerG_one (L : X → G) (x : X) : wignerG L 1 x = 1 := by
  simp [wignerG]

/-- The Wigner element as an element of the stabiliser. -/
def wignerStab {x₀ : X} {L : X → G} (hL : ∀ x, L x • x₀ = x) (g : G) (x : X) :
    MulAction.stabilizer G x₀ := ⟨wignerG L g x, wignerG_mem_stabilizer hL g x⟩

lemma wignerStab_mul {x₀ : X} {L : X → G} (hL : ∀ x, L x • x₀ = x) (g' g : G) (x : X) :
    wignerStab hL (g' * g) x = wignerStab hL g' (g • x) * wignerStab hL g x :=
  Subtype.ext (wignerG_mul L g' g x)

lemma wignerStab_one {x₀ : X} {L : X → G} (hL : ∀ x, L x • x₀ = x) (x : X) :
    wignerStab hL 1 x = 1 := Subtype.ext (wignerG_one L x)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The induced action** `(U(g) ψ)(x) = D(W(g, g⁻¹ • x)) ψ(g⁻¹ • x)`. -/
def inducedActG {x₀ : X} {L : X → G} (hL : ∀ x, L x • x₀ = x)
    (D : MulAction.stabilizer G x₀ →* (V →ₗ[ℂ] V)) (g : G) (ψ : X → V) : X → V :=
  fun x => D (wignerStab hL g (g⁻¹ • x)) (ψ (g⁻¹ • x))

/-- **The induced action is an action.** -/
theorem inducedActG_mul {x₀ : X} {L : X → G} (hL : ∀ x, L x • x₀ = x)
    (D : MulAction.stabilizer G x₀ →* (V →ₗ[ℂ] V)) (g' g : G) (ψ : X → V) :
    inducedActG hL D (g' * g) ψ = inducedActG hL D g' (inducedActG hL D g ψ) := by
  funext x
  simp only [inducedActG]
  have h1 : (g' * g)⁻¹ • x = g⁻¹ • (g'⁻¹ • x) := by rw [_root_.mul_inv_rev, mul_smul]
  have h2 : g • (g⁻¹ • (g'⁻¹ • x)) = g'⁻¹ • x := smul_inv_smul g _
  rw [h1, wignerStab_mul, h2, map_mul, Module.End.mul_apply]

theorem inducedActG_one {x₀ : X} {L : X → G} (hL : ∀ x, L x • x₀ = x)
    (D : MulAction.stabilizer G x₀ →* (V →ₗ[ℂ] V)) (ψ : X → V) :
    inducedActG hL D 1 ψ = ψ := by
  funext x
  simp [inducedActG, wignerStab_one]

end Lightlike.Poincare

import Lightlike.OperatorAlgebras.QuasiFreeState.State

/-!
# The two-point function of a quasi-free state

For the quasi-free state `ρ_η` of `QuasiFreeState.State` the product of two Weyl elements is
`ρ_η(W(φ) W(ψ)) = exp(-i ω(φ, ψ)/2) exp(-¼ η(φ + ψ, φ + ψ))` (`qfState_W_mul`), so that
`ρ_η(W(tf) W(sg)) = exp(a t s + b t² + c s²)` with `a = -½ (η(f, g) + i ω(f, g))`, `b = -¼ η(f, f)`,
`c = -¼ η(g, g)` (`qfState_W_smul_mul`).  The two-point function of the fields `φ(f) = -i d/dt W(tf)|₀` is
`ρ(φ(f) φ(g)) = -∂ₜ∂ₛ ρ(W(tf) W(sg))|₀`; it equals `½ (η(f, g) + i ω(f, g))`
(`qfState_twoPoint`, the same formula as `CCRRep.IsQuasiFree.npoint_two` for the quasi-free vectors).
-/

open scoped InnerProductSpace ComplexOrder ComplexConjugate

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

universe u

section State

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (ω η : LinearMap.BilinForm ℝ V)
  [Fact (qfKerM ω η).PosSemidef]

/-- **Product of two Weyl elements in the quasi-free state**:
`ρ_η(W(φ) W(ψ)) = exp(-i ω(φ, ψ)/2) exp(-¼ η(φ + ψ, φ + ψ))`. -/
theorem qfState_W_mul (hω : ∀ a b, ω a b = -ω b a) (φ ψ : V) :
    qfState ω η hω (qfWA ω η hω φ * qfWA ω η hω ψ) =
      Complex.exp (-(Complex.I * ((ω φ ψ / 2 : ℝ) : ℂ))) * ((gaussVal η (φ + ψ) : ℝ) : ℂ) := by
  rw [(isWeylSystem_qfWA ω η hω).mul, map_smul, qfState_W, smul_eq_mul]

/-- The explicit form of `ρ_η(W(tf) W(sg))` as the exponential of a quadratic polynomial in `(t, s)`. -/
theorem qfState_W_smul_mul (hω : ∀ a b, ω a b = -ω b a) (hη : ∀ a b, η a b = η b a) (f g : V) (t s : ℝ) :
    qfState ω η hω (qfWA ω η hω (t • f) * qfWA ω η hω (s • g)) =
      Complex.exp ((-(1 / 2 : ℂ) * ((η f g : ℝ) + Complex.I * (ω f g : ℝ))) * (t : ℂ) * (s : ℂ) +
        (-(1 / 4 : ℂ) * (η f f : ℝ)) * (t : ℂ) ^ 2 + (-(1 / 4 : ℂ) * (η g g : ℝ)) * (s : ℂ) ^ 2) := by
  rw [qfState_W_mul, gaussVal, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hη g f]
  push_cast
  ring

end State

/-- Mixed derivative of a Gaussian exponent at the origin. -/
lemma deriv_deriv_exp_quadratic (a b c : ℂ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => Complex.exp (a * (t : ℂ) * (s : ℂ) + b * (t : ℂ) ^ 2 + c * (s : ℂ) ^ 2)) 0)
      0 = a := by
  have hofReal : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := fun x => Complex.ofRealCLM.hasDerivAt
  have h1 : ∀ t : ℝ, deriv (fun s : ℝ => Complex.exp (a * (t : ℂ) * (s : ℂ) + b * (t : ℂ) ^ 2 + c * (s : ℂ) ^ 2)) 0 =
      Complex.exp (b * (t : ℂ) ^ 2) * (a * (t : ℂ)) := by
    intro t
    have hs := hofReal 0
    have h2 : HasDerivAt (fun s : ℝ => a * (t : ℂ) * (s : ℂ) + b * (t : ℂ) ^ 2 + c * (s : ℂ) ^ 2)
        (a * (t : ℂ)) 0 :=
      (((hs.const_mul (a * (t : ℂ))).add_const (b * (t : ℂ) ^ 2)).add (((hs.pow 2).const_mul c))).congr_deriv
        (by simp)
    have h3 := h2.cexp
    rw [h3.deriv]
    simp
  simp only [h1]
  have ht := hofReal 0
  have h4 : HasDerivAt (fun t : ℝ => Complex.exp (b * (t : ℂ) ^ 2) * (a * (t : ℂ)))
      a 0 :=
    ((((ht.pow 2).const_mul b).cexp).mul (ht.const_mul a)).congr_deriv (by simp)
  rw [h4.deriv]

/-- **The two-point function of a quasi-free state**:
`-∂ₜ∂ₛ ρ_η(W(tf) W(sg))|₀ = ½ (η(f, g) + i ω(f, g))`, as in `CCRRep.IsQuasiFree.npoint_two` for quasi-free vectors. -/
theorem qfState_twoPoint {V : Type u} [AddCommGroup V] [Module ℝ V] (ω η : LinearMap.BilinForm ℝ V)
    [Fact (qfKerM ω η).PosSemidef] (hω : ∀ a b, ω a b = -ω b a) (hη : ∀ a b, η a b = η b a) (f g : V) :
    -deriv (fun t : ℝ => deriv (fun s : ℝ => qfState ω η hω (qfWA ω η hω (t • f) * qfWA ω η hω (s • g))) 0) 0 =
      (1 / 2 : ℂ) * ((η f g : ℝ) + Complex.I * (ω f g : ℝ)) := by
  simp only [qfState_W_smul_mul ω η hω hη]
  rw [deriv_deriv_exp_quadratic]
  ring

end Lightlike.OperatorAlgebras.QuasiFreeState

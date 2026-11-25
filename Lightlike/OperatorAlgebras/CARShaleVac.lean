import Lightlike.OperatorAlgebras.CARShaleHS
import Lightlike.OperatorAlgebras.CARProjections

/-!
# The transformed ladder operators in terms of the Fock operators

`annV u = a*(β u) + a(α u)` and `creV u = a*(α u) + a(β u)`, with `α`, `β` the linear and antilinear parts of `R`
(`alphaPart`, `betaPart`). Consequently `annV u` applied to the vacuum is `a*(β u)` on the vacuum, and the anticommutators
with a Fock creation operator `a*(x)` are scalars: `{annV u, a*(x)} = ⟪α u, x⟫`, `{creV u, a*(x)} = ⟪β u, x⟫`.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.CARShale

variable {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  (B : HilbertBasis (Finset ι) ℂ Γ) {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  (b : HilbertBasis ι ℂ Z) (R : Z →ₗ[ℝ] Z)

omit [LinearOrder ι] in
/-- `a(c w) = conj c · a(w)`. -/
lemma annW_smul' [LinearOrder ι] (c : ℂ) (w : Z) : annW B b (c • w) = conj c • annW B b w := by
  rw [annW, creW_smul, map_smulₛₗ]; rfl

/-- Auxiliary lemma `annW_add'` for the fermionic Shale theorem. -/
lemma annW_add' (u v : Z) : annW B b (u + v) = annW B b u + annW B b v := by
  rw [annW, creW_add, map_add]; rfl

/-- Auxiliary lemma `annW_neg_I` for the fermionic Shale theorem. -/
lemma annW_neg_I (w : Z) : annW B b ((-Complex.I) • w) = Complex.I • annW B b w := by
  rw [annW_smul']; simp

/-- Auxiliary lemma `annW_I` for the fermionic Shale theorem. -/
lemma annW_I (w : Z) : annW B b (Complex.I • w) = (-Complex.I) • annW B b w := by
  rw [annW_smul']; simp

/-- Auxiliary lemma `annW_half` for the fermionic Shale theorem. -/
lemma annW_half (w : Z) : annW B b ((1 / 2 : ℂ) • w) = (1 / 2 : ℂ) • annW B b w := by
  rw [annW_smul']
  have : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [this]

/-- `annV u = a*(β u) + a(α u)`. -/
lemma annV_eq (u : Z) : annV B b R u = creW B b (betaPart R u) + annW B b (alphaPart R u) := by
  simp only [annV, betaPart, alphaPart, fockField]
  rw [creW_smul, annW_half, creW_add, creW_smul, sub_eq_add_neg, annW_add', ← neg_smul, annW_neg_I]
  module

/-- `creV u = a*(α u) + a(β u)`. -/
lemma creV_eq (u : Z) : creV B b R u = creW B b (alphaPart R u) + annW B b (betaPart R u) := by
  have hs : R u - Complex.I • R (Complex.I • u) = R u + (-Complex.I) • R (Complex.I • u) := by
    rw [neg_smul, sub_eq_add_neg]
  simp only [creV, betaPart, alphaPart, fockField]
  rw [hs, creW_smul, annW_half, creW_add, creW_smul, annW_add', annW_I]
  module

/-- `annV u` applied to the vacuum is `a*(β u)` on the vacuum. -/
lemma annV_vac (u : Z) : annV B b R u (B ∅) = creW B b (betaPart R u) (B ∅) := by
  rw [annV_eq, ContinuousLinearMap.add_apply, annW_vac B b, add_zero]

/-- Auxiliary lemma `norm_annV_vac` for the fermionic Shale theorem. -/
lemma norm_annV_vac (u : Z) : ‖annV B b R u (B ∅)‖ = ‖betaPart R u‖ := by
  rw [annV_vac, norm_creW_vac B b]

/-- `{annV u, a*(x)} = ⟪α u, x⟫`. -/
lemma annV_creW_anticomm (u x : Z) :
    annV B b R u * creW B b x + creW B b x * annV B b R u = ⟪alphaPart R u, x⟫_ℂ • (1 : Γ →L[ℂ] Γ) := by
  have e : annV B b R u * creW B b x + creW B b x * annV B b R u =
      (creW B b (betaPart R u) * creW B b x + creW B b x * creW B b (betaPart R u)) +
      (annW B b (alphaPart R u) * creW B b x + creW B b x * annW B b (alphaPart R u)) := by
    rw [annV_eq]; noncomm_ring
  rw [e, creW_anticomm, annW_creW_anticomm, zero_add]

/-- `{creV u, a*(x)} = ⟪β u, x⟫`. -/
lemma creV_creW_anticomm (u x : Z) :
    creV B b R u * creW B b x + creW B b x * creV B b R u = ⟪betaPart R u, x⟫_ℂ • (1 : Γ →L[ℂ] Γ) := by
  have e : creV B b R u * creW B b x + creW B b x * creV B b R u =
      (creW B b (alphaPart R u) * creW B b x + creW B b x * creW B b (alphaPart R u)) +
      (annW B b (betaPart R u) * creW B b x + creW B b x * annW B b (betaPart R u)) := by
    rw [creV_eq]; noncomm_ring
  rw [e, creW_anticomm, annW_creW_anticomm, zero_add]

end Lightlike.OperatorAlgebras.CARShale

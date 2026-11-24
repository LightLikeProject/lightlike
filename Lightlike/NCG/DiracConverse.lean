import Lightlike.NCG.DiracDecomposition

/-!
# The converse of `D = Δ + J Δ J`: every admissible `Δ` gives a real graded finite spectral triple

T. Krajewski, arXiv:hep-th/9701081, Section 3.4, p. 15 (read): "the Dirac operator of a finite spectral triple is given by
`D = Δ + J Δ J⁻¹`, where `Δ` is a hermitian operator on `H`, which commutes with `J π(A) J⁻¹` and anticommutes with `χ`".
`DiracDecomposition.lean` proves that every Dirac operator has this form. Here the other direction is proved: for a
real graded finite spectral triple `(T, R, G)` and a hermitian `Δ` that commutes with `J π(b) J` for all `b` and anticommutes
with `γ`, the operator `D' = Δ + J Δ J` is self-adjoint, satisfies the first-order condition, commutes with `J` and
anticommutes with `γ`, so `(π, D', J, γ)` is again a real graded finite spectral triple.

* `conjOp R S`: the operator `x ↦ J S J x`; `conjOp_selfAdjoint`, `conjOp_conjOp`, `conjOp_commute_pi`, `conjOp_gamma`;
* `ofDelta`, `realOfDelta`, `gradingOfDelta`: the triple, its real structure and its grading;
* `ofDelta_D`: its Dirac operator is `Δ + J Δ J`.
-/

open scoped InnerProductSpace

namespace Lightlike.NCG

noncomputable section

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple A H} (R : RealStructure T)

/-- The operator `x ↦ J S J x`. -/
def conjOp (S : H →L[ℂ] H) : H →L[ℂ] H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => R.J (S (R.J x))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }

lemma conjOp_apply (S : H →L[ℂ] H) (x : H) : conjOp R S x = R.J (S (R.J x)) := rfl

lemma conjOp_conjOp (S : H →L[ℂ] H) : conjOp R (conjOp R S) = S := by
  ext x
  simp [conjOp_apply, R.J_J]

/-- `J S J` is self-adjoint when `S` is. -/
lemma conjOp_selfAdjoint {S : H →L[ℂ] H} (hS : IsSelfAdjoint S) : IsSelfAdjoint (conjOp R S) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hS' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS
  show ⟪conjOp R S x, y⟫_ℂ = ⟪x, conjOp R S y⟫_ℂ
  rw [conjOp_apply, conjOp_apply]
  calc ⟪R.J (S (R.J x)), y⟫_ℂ = ⟪R.J (S (R.J x)), R.J (R.J y)⟫_ℂ := by rw [R.J_J]
    _ = ⟪R.J y, S (R.J x)⟫_ℂ := R.inner_J _ _
    _ = ⟪S (R.J y), R.J x⟫_ℂ := (hS' (R.J y) (R.J x)).symm
    _ = ⟪x, R.J (S (R.J y))⟫_ℂ := by
        have := R.inner_J (R.J x) (S (R.J y))
        rw [R.J_J] at this
        exact this.symm

/-- Hypothesis on `Δ`: it commutes with `J π(b) J`. -/
def CommutesJ (Δ : H →L[ℂ] H) : Prop :=
  ∀ b x, Δ (R.J (T.π b (R.J x))) = R.J (T.π b (R.J (Δ x)))

/-- `J Δ J` commutes with `π(b)`. -/
lemma conjOp_commute_pi {Δ : H →L[ℂ] H} (h : CommutesJ R Δ) (b : A) (x : H) :
    conjOp R Δ (T.π b x) = T.π b (conjOp R Δ x) := by
  rw [conjOp_apply, conjOp_apply]
  have := congrArg R.J (h b (R.J x))
  rw [R.J_J] at this
  simpa [R.J_J] using this

/-- `J Δ J` anticommutes with `γ` when `Δ` does and `γ` commutes with `J`. -/
lemma conjOp_gamma {γ Δ : H →L[ℂ] H} (hJ : ∀ x, γ (R.J x) = R.J (γ x)) (h : Δ * γ = -(γ * Δ)) :
    conjOp R Δ * γ = -(γ * conjOp R Δ) := by
  ext x
  have h1 : Δ (γ (R.J x)) = -(γ (Δ (R.J x))) := by
    have := congrArg (fun f : H →L[ℂ] H => f (R.J x)) h
    simpa using this
  simp only [ContinuousLinearMap.mul_apply, neg_apply, conjOp_apply]
  rw [← hJ, h1, map_neg, hJ]

variable {Δ : H →L[ℂ] H}

/-- The Dirac operator `Δ + J Δ J`. -/
def diracOfDelta (Δ : H →L[ℂ] H) : H →L[ℂ] H := Δ + conjOp R Δ

/-- **The triple with Dirac operator `D' = Δ + J Δ J`** (same algebra, representation and Hilbert space). -/
def ofDelta (hΔ : IsSelfAdjoint Δ) : FiniteSpectralTriple A H :=
  { T with
    D := diracOfDelta R Δ
    isSelfAdjoint_D := hΔ.add (conjOp_selfAdjoint R hΔ) }

lemma ofDelta_D (hΔ : IsSelfAdjoint Δ) : (ofDelta R hΔ).D = Δ + conjOp R Δ := rfl

/-- `J` is a real structure for `ofDelta`: the first-order condition and `D J = J D` hold. -/
def realOfDelta (hΔ : IsSelfAdjoint Δ) (h : CommutesJ R Δ) : RealStructure (ofDelta R hΔ) where
  J := R.J
  inner_J := R.inner_J
  J_J := R.J_J
  order_zero := R.order_zero
  first_order := fun a b x => by
    have hc : ∀ y, (ofDelta R hΔ).D (T.π a y) - T.π a ((ofDelta R hΔ).D y)
        = Δ (T.π a y) - T.π a (Δ y) := fun y => by
      simp only [ofDelta_D, add_apply, conjOp_commute_pi R h a y, map_add]
      abel
    have e1 : Δ (T.π a (R.J (T.π b (R.J x)))) = R.J (T.π b (R.J (Δ (T.π a x)))) := by
      rw [R.order_zero a b x]; exact h b _
    have e2 : T.π a (Δ (R.J (T.π b (R.J x)))) = R.J (T.π b (R.J (T.π a (Δ x)))) := by
      rw [h b x, R.order_zero a b (Δ x)]
    show (ofDelta R hΔ).D (T.π a (R.J (T.π b (R.J x)))) - T.π a ((ofDelta R hΔ).D (R.J (T.π b (R.J x))))
      = R.J (T.π b (R.J ((ofDelta R hΔ).D (T.π a x) - T.π a ((ofDelta R hΔ).D x))))
    rw [hc, hc, e1, e2, map_sub, map_sub, map_sub]
  D_J := fun x => by
    simp only [ofDelta_D, add_apply, conjOp_apply, R.J_J, map_add]
    abel

/-- `γ` is a grading for `ofDelta` when `Δ` anticommutes with it. -/
def gradingOfDelta (hΔ : IsSelfAdjoint Δ) (h : CommutesJ R Δ) (G : Grading T R)
    (hγ : Δ * G.γ = -(G.γ * Δ)) :
    Grading (ofDelta R hΔ) (realOfDelta R hΔ h) where
  γ := G.γ
  isSelfAdjoint_γ := G.isSelfAdjoint_γ
  γ_γ := G.γ_γ
  γ_J := G.γ_J
  γ_π := G.γ_π
  D_γ := by
    simp only [ofDelta_D, add_mul, mul_add]
    rw [hγ, conjOp_gamma R G.γ_J hγ]
    abel

/-- Non-vacuity: `Δ = 0` is admissible and gives the zero Dirac operator. -/
example (hz : IsSelfAdjoint (0 : H →L[ℂ] H)) : (ofDelta R hz).D = 0 := by
  ext x
  simp [ofDelta_D, conjOp_apply]

end

end Lightlike.NCG

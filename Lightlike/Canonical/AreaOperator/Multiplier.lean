import Lightlike.HarmonicAnalysis.SU2PeterWeyl

/-!
# Peter–Weyl multipliers on `SU(2)` (row G2-012)

The functions `Dⁿ_{ij}` (`Lightlike.HarmonicAnalysis.su2Coeff`) are the spin-`n/2` matrix elements of
`SU(2)`; on one edge of a graph they are the spin-network functions.  A *Peter–Weyl multiplier*
`pwMultiplier μ φ` multiplies the spin-`n/2` component of a function by `φ n`.  It is the spectral
calculus of the Casimir operator of `SU(2)`: the Casimir acts on the spin-`n/2` component by
`j (j + 1)`, `j = n / 2`, so a function `F (j (j + 1))` of it is the multiplier `φ n = F (n (n + 2) / 4)`.

The multiplier is defined by the Peter–Weyl expansion
`f = Σ_{n,i,j} (n + 1) ⟨f, Dⁿ_{ij}⟩ Dⁿ_{ij}` with a `finsum`; on a function with finitely many nonzero
coefficients (a cylindrical function) it is the finite sum, elsewhere the `finsum` is the junk value `0`.
Every statement below is therefore about the spin-network functions themselves.
-/

open MeasureTheory Lightlike.HarmonicAnalysis UnitaryMatrixRep

namespace Lightlike.Canonical.AreaOperator

noncomputable section

variable (μ : Measure SU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- The Peter–Weyl coefficient `(n + 1) ∫ f · conj Dⁿ_{ij} dμ` of `f` at the index `(n, i, j)`. -/
def pwCoeff (f : SU2 → ℂ) (a : SU2CoeffIdx) : ℂ :=
  ((a.1 : ℂ) + 1) * ∫ g, f g * starRingEnd ℂ (su2Coeff a.1 a.2.1 a.2.2 g) ∂μ

/-- The Peter–Weyl multiplier of `φ : ℕ → ℝ`: it multiplies the spin-`n/2` component by `φ n`.
For a function with finitely many nonzero Peter–Weyl coefficients it is the finite sum
`Σ φ n · pwCoeff · Dⁿ_{ij}`. -/
def pwMultiplier (φ : ℕ → ℝ) (f : SU2 → ℂ) : SU2 → ℂ :=
  fun g => ∑ᶠ a : SU2CoeffIdx, (φ a.1 : ℂ) * pwCoeff μ f a * su2Coeff a.1 a.2.1 a.2.2 g

/-- **The coefficients of a matrix element are a Kronecker delta** (Schur orthogonality): the
function `Dᵐ_{ab}` has Peter–Weyl coefficient `1` at `(m, a, b)` and `0` elsewhere. -/
theorem pwCoeff_su2Coeff (m : ℕ) (a b : Fin (m + 1)) (x : SU2CoeffIdx) :
    pwCoeff μ (fun g => su2Coeff m a b g) x = if x = ⟨m, a, b⟩ then 1 else 0 := by
  obtain ⟨n, i, j⟩ := x
  simp only [pwCoeff]
  by_cases hnm : n = m
  · subst hnm
    have hs : ∫ g, su2Coeff n a b g * starRingEnd ℂ (su2Coeff n i j g) ∂μ =
        if a = i ∧ b = j then 1 / ((Fintype.card (Fin (n + 1)) : ℕ) : ℂ) else 0 :=
      schur_orthogonality_eq μ (su2Spin_isIrreducible n) a b j i
    rw [hs]
    have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Fintype.card_fin, and_self, ↓reduceIte]
      push_cast
      rw [mul_one_div, div_self hn]
    · have h2 : ¬ (⟨n, i, j⟩ : SU2CoeffIdx) = ⟨n, a, b⟩ := by
        intro h'
        apply h
        have h1 := eq_of_heq (Sigma.mk.inj_iff.1 h').2
        exact ⟨(Prod.mk.inj h1).1.symm, (Prod.mk.inj h1).2.symm⟩
      simp only [h, h2, ↓reduceIte, mul_zero]
  · have h0 : ∫ g, su2Coeff m a b g * starRingEnd ℂ (su2Coeff n i j g) ∂μ = 0 :=
      schur_orthogonality_ne μ (su2Spin_isIrreducible m) (su2Spin_isIrreducible n)
        (su2Spin_not_equivalent (Ne.symm hnm)) a b j i
    have h2 : ¬ (⟨n, i, j⟩ : SU2CoeffIdx) = ⟨m, a, b⟩ := fun h' => hnm (congrArg Sigma.fst h')
    simp only [h0, h2, ↓reduceIte, mul_zero]

/-- **A multiplier acts on a spin-`m/2` matrix element by the scalar `φ m`**: for every constant
`c`, `pwMultiplier μ φ (c · Dᵐ_{ab}) = φ m · c · Dᵐ_{ab}`. -/
theorem pwMultiplier_const_mul_su2Coeff (φ : ℕ → ℝ) (c : ℂ) (m : ℕ) (a b : Fin (m + 1)) :
    pwMultiplier μ φ (fun g => c * su2Coeff m a b g) =
      fun g => (φ m : ℂ) * c * su2Coeff m a b g := by
  funext g
  have hc : ∀ x : SU2CoeffIdx, pwCoeff μ (fun g => c * su2Coeff m a b g) x =
      c * pwCoeff μ (fun g => su2Coeff m a b g) x := by
    intro x
    simp only [pwCoeff, mul_assoc, integral_const_mul]
    ring
  simp only [pwMultiplier, hc, pwCoeff_su2Coeff]
  rw [finsum_eq_single _ (⟨m, a, b⟩ : SU2CoeffIdx)]
  · simp
  · intro x hx
    simp [hx]

/-- A multiplier acts on a spin-`m/2` matrix element by the scalar `φ m`. -/
theorem pwMultiplier_su2Coeff (φ : ℕ → ℝ) (m : ℕ) (a b : Fin (m + 1)) :
    pwMultiplier μ φ (fun g => su2Coeff m a b g) = fun g => (φ m : ℂ) * su2Coeff m a b g := by
  simpa using pwMultiplier_const_mul_su2Coeff μ φ 1 m a b

end

end Lightlike.Canonical.AreaOperator

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.pwCoeff := _root_.Lightlike.Canonical.AreaOperator.pwCoeff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.pwCoeff_su2Coeff := _root_.Lightlike.Canonical.AreaOperator.pwCoeff_su2Coeff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.pwMultiplier := _root_.Lightlike.Canonical.AreaOperator.pwMultiplier
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.pwMultiplier_const_mul_su2Coeff := _root_.Lightlike.Canonical.AreaOperator.pwMultiplier_const_mul_su2Coeff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.pwMultiplier_su2Coeff := _root_.Lightlike.Canonical.AreaOperator.pwMultiplier_su2Coeff

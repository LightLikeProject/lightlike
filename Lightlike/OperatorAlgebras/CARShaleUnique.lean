import Lightlike.OperatorAlgebras.CARShaleNec

/-!
# Fermionic Shale: uniqueness of the implementer up to a phase

Two unitaries implementing the same `R` differ by a phase (Dereziński, Theorem 31 (2), p. 32). The quotient
`V = U⁻¹ U'` commutes with every field `φ(w)`. It maps the vacuum to a vector killed by every annihilator, i.e. to a
multiple `c Ω₀` of the vacuum, and the closed subspace `{x | V x = c x}` is invariant under all fields, hence everything
by the irreducibility of the Fock representation; `|c| = 1` because `V` is isometric.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.CARShale

variable {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  (B : HilbertBasis (Finset ι) ℂ Γ) {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  (b : HilbertBasis ι ℂ Z) (R : Z →ₗ[ℝ] Z)

/-- **A vector killed by every annihilator is a multiple of the vacuum.** -/
lemma eq_smul_vac_of_killed (φ : Γ) (h : ∀ j, fermiAnn B j φ = 0) : φ = (B.repr φ ∅ : ℂ) • B ∅ := by
  classical
  apply B.repr.injective
  ext T
  by_cases hT : T = ∅
  · subst hT
    simp [HilbertBasis.repr_self]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hT
    have h1 := repr_fermiAnn_apply B j φ (T.erase j)
    rw [h j, if_neg (Finset.notMem_erase j T), Finset.insert_erase hj] at h1
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply] at h1
    have h2 : B.repr φ T = 0 := by
      have hs := fermiSign_mul_self (T.erase j) j
      have : B.repr φ T = fermiSign (T.erase j) j * (fermiSign (T.erase j) j * B.repr φ T) := by
        rw [← mul_assoc, hs, one_mul]
      rw [this, ← h1, mul_zero]
    rw [h2]
    simp [HilbertBasis.repr_self, Finset.ne_empty_of_mem hj, hT, lp.single_apply]

/-- **Uniqueness of the implementer up to a phase** (Dereziński, Theorem 31 (2), p. 32): two unitaries of the fermionic
Fock space with `U φ(w) = φ(R w) U` differ by a phase `c`, `|c| = 1`. -/
theorem implementer_unique (U U' : Γ ≃ₗᵢ[ℂ] Γ)
    (hU : ∀ w x, U (fockField B b w x) = fockField B b (R w) (U x))
    (hU' : ∀ w x, U' (fockField B b w x) = fockField B b (R w) (U' x)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, U' x = c • U x := by
  classical
  set Vc : Γ →L[ℂ] Γ := (U.symm.toContinuousLinearEquiv : Γ →L[ℂ] Γ).comp
    (U'.toContinuousLinearEquiv : Γ →L[ℂ] Γ) with hVc
  have hVx : ∀ x, Vc x = U.symm (U' x) := fun x => rfl
  have hcomm : ∀ w x, Vc (fockField B b w x) = fockField B b w (Vc x) := by
    intro w x
    rw [hVx, hVx, hU' w x]
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hU w (U.symm (U' x)), LinearIsometryEquiv.apply_symm_apply]
  have hann : ∀ j, fermiAnn B j (Vc (B ∅)) = 0 := by
    intro j
    have h1 : fermiAnn B j (Vc (B ∅)) = Vc (fermiAnn B j (B ∅)) := by
      simp only [← annW_basis B b j, annW_eq_field B b (b j), ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, map_smul, map_add, hcomm]
    rw [h1, ← annW_basis B b j, annW_vac, map_zero]
  set c : ℂ := B.repr (Vc (B ∅)) ∅ with hc
  have hvac : Vc (B ∅) = c • B ∅ := eq_smul_vac_of_killed B _ hann
  set W : Submodule ℂ Γ := LinearMap.ker ((Vc - c • ContinuousLinearMap.id ℂ Γ : Γ →L[ℂ] Γ) : Γ →ₗ[ℂ] Γ) with hW
  have hWc : IsClosed (W : Set Γ) := ContinuousLinearMap.isClosed_ker (Vc - c • ContinuousLinearMap.id ℂ Γ)
  have hmem : ∀ x, x ∈ W ↔ Vc x = c • x := fun x => by
    simp [hW, LinearMap.mem_ker, sub_eq_zero]
  have hWinv : ∀ w, ∀ ψ ∈ W, fockField B b w ψ ∈ W := by
    intro w ψ hψ
    rw [hmem] at hψ ⊢
    rw [hcomm, hψ, map_smul]
  have hne : W ≠ ⊥ := by
    intro h
    have : B ∅ ∈ W := (hmem _).2 hvac
    rw [h] at this
    have h1 : ‖B ∅‖ = 1 := B.orthonormal.1 ∅
    have : B ∅ = 0 := by simpa using this
    rw [this, norm_zero] at h1; exact zero_ne_one h1
  have htop : W = ⊤ := (fockField_irreducible B b W hWc hWinv).resolve_left hne
  have hall : ∀ x, Vc x = c • x := fun x => (hmem x).1 (by rw [htop]; trivial)
  refine ⟨c, ?_, fun x => ?_⟩
  · have h1 : ‖B ∅‖ = 1 := B.orthonormal.1 ∅
    have h2 : ‖Vc (B ∅)‖ = 1 := by rw [hVx, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, h1]
    rw [hvac, norm_smul, h1, mul_one] at h2
    exact h2
  · have := hall x
    rw [hVx] at this
    calc U' x = U (U.symm (U' x)) := (U.apply_symm_apply _).symm
      _ = c • U x := by rw [this, map_smul]

end Lightlike.OperatorAlgebras.CARShale

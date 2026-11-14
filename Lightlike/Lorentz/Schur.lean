module

public import Lightlike.SU2.SpinRep

/-!
# Schur's lemma for the spin representations of SU(2)

The SU(2) decomposition of the principal series compares maps between the spin representations
`spinMat m` of `Lightlike/SU2/SpinRep.lean`. Both forms of Schur's lemma follow from their
irreducibility (`Lightlike.SU2.isInvariant_eq_bot_or_eq_top`):

* `schur_eq_zero`: a linear map `ℂ^{m+1} → ℂ^{m'+1}` intertwining `spinMat m` and `spinMat m'` with
  `m ≠ m'` is zero;
* `schur_eq_smul`: a linear endomorphism of `ℂ^{m+1}` commuting with `spinMat m` is a scalar.

Reference: B. C. Hall, *Lie Groups, Lie Algebras, and Representations* (Springer, 2nd ed. 2015),
Chapter 4 (Schur's lemma).
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz

open Lightlike.SU2

/-- `S` intertwines the spin representations `spinMat m` and `spinMat m'` of `SU(2)`. -/
def IsSpinIntertwiner (m m' : ℕ) (S : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m' + 1) → ℂ)) : Prop :=
  ∀ (u : SU2) (x : Fin (m + 1) → ℂ), S (spinMat m u *ᵥ x) = spinMat m' u *ᵥ S x

lemma isInvariant_ker {m m' : ℕ} {S : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m' + 1) → ℂ)}
    (hS : IsSpinIntertwiner m m' S) : IsInvariant m (LinearMap.ker S) := by
  intro g v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [hS, hv, mulVec_zero]

lemma isInvariant_range {m m' : ℕ} {S : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m' + 1) → ℂ)}
    (hS : IsSpinIntertwiner m m' S) : IsInvariant m' (LinearMap.range S) := by
  rintro g v ⟨w, rfl⟩
  exact ⟨spinMat m g *ᵥ w, hS g w⟩

/-- **Schur's lemma, first form**: an intertwiner between spin `m/2` and spin `m'/2` with
`m ≠ m'` vanishes. -/
theorem schur_eq_zero {m m' : ℕ} (hm : m ≠ m') {S : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m' + 1) → ℂ)}
    (hS : IsSpinIntertwiner m m' S) : S = 0 := by
  rcases isInvariant_eq_bot_or_eq_top (isInvariant_ker hS) with h | h
  · exfalso
    have hinj : Function.Injective S := LinearMap.ker_eq_bot.mp h
    rcases isInvariant_eq_bot_or_eq_top (isInvariant_range hS) with h' | h'
    · -- the range is zero although `S` is injective on a nonzero space
      have hx : S (Pi.single 0 1) = 0 := by
        have : S (Pi.single 0 1) ∈ LinearMap.range S := ⟨_, rfl⟩
        rw [h'] at this; exact this
      have := hinj (hx.trans (map_zero S).symm)
      have := congrFun this 0
      simp at this
    · have h1 := LinearMap.finrank_range_of_inj hinj
      rw [h', finrank_top] at h1
      simp only [Module.finrank_fin_fun] at h1
      exact hm (by omega)
  · exact LinearMap.ker_eq_top.mp h

/-- **Schur's lemma, second form**: an endomorphism commuting with spin `m/2` is a scalar. -/
theorem schur_eq_smul {m : ℕ} {S : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ)}
    (hS : IsSpinIntertwiner m m S) : ∃ c : ℂ, S = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue S
  refine ⟨c, ?_⟩
  have hT : IsSpinIntertwiner m m (S - c • LinearMap.id) := by
    intro u x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, mulVec_sub,
      mulVec_smul]
    rw [hS]
  rcases isInvariant_eq_bot_or_eq_top (isInvariant_ker hT) with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv0 : v ∈ LinearMap.ker (S - c • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hv.apply_eq_smul, sub_self]
    rw [h, Submodule.mem_bot] at hv0
    exact hv.2 hv0
  · have := LinearMap.ker_eq_top.mp h
    exact sub_eq_zero.mp this

end Lightlike.Lorentz

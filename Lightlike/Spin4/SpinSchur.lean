import Lightlike.SU2.SpinRep

/-!
# Schur's lemma for the spin representations, in matrix form

For the spin representations `SU2.spinMat` of SU(2) (irreducible by
`SU2.isInvariant_eq_bot_or_eq_top`), an intertwiner `T`, i.e. a matrix with
`D^{M/2}(g) T = T D^{N/2}(g)` for all `g ∈ SU(2)`, is

* zero if `N ≠ M` (`spin_intertwiner_eq_zero`), and
* a multiple of the identity if `N = M` (`spin_intertwiner_eq_smul`).

The proof is the usual one: the kernel and the range of `T` are invariant subspaces, and over `ℂ`
every endomorphism has an eigenvalue.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics 129,
  Springer (1991), Lecture 1 (Schur's lemma).
-/

open Matrix

namespace Lightlike.Spin4

open SU2

variable {N M : ℕ}

/-- The kernel of an intertwiner is an invariant subspace. -/
lemma isInvariant_ker {T : Matrix (Fin (M + 1)) (Fin (N + 1)) ℂ}
    (hT : ∀ g : SU2, spinMat M g * T = T * spinMat N g) :
    IsInvariant N (LinearMap.ker (Matrix.toLin' T)) := by
  intro g v hv
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
  rw [mulVec_mulVec, ← hT g, ← mulVec_mulVec, hv, mulVec_zero]

/-- The range of an intertwiner is an invariant subspace. -/
lemma isInvariant_range {T : Matrix (Fin (M + 1)) (Fin (N + 1)) ℂ}
    (hT : ∀ g : SU2, spinMat M g * T = T * spinMat N g) :
    IsInvariant M (LinearMap.range (Matrix.toLin' T)) := by
  rintro g _ ⟨v, rfl⟩
  refine ⟨spinMat N g *ᵥ v, ?_⟩
  simp only [Matrix.toLin'_apply, mulVec_mulVec, hT g]

/-- **Schur's lemma, different spins.** An intertwiner between spin `N/2` and spin `M/2` with
`N ≠ M` vanishes. -/
theorem spin_intertwiner_eq_zero (hNM : N ≠ M) {T : Matrix (Fin (M + 1)) (Fin (N + 1)) ℂ}
    (hT : ∀ g : SU2, spinMat M g * T = T * spinMat N g) : T = 0 := by
  rcases isInvariant_eq_bot_or_eq_top (isInvariant_ker hT) with hk | hk
  · exfalso
    rcases isInvariant_eq_bot_or_eq_top (isInvariant_range hT) with hr | hr
    · -- injective with zero range: impossible on a nonzero space
      have h1 : Matrix.toLin' T (Pi.single 0 1) = 0 := by
        have : Matrix.toLin' T (Pi.single 0 1) ∈ LinearMap.range (Matrix.toLin' T) := ⟨_, rfl⟩
        rw [hr] at this
        exact (Submodule.mem_bot ℂ).mp this
      have h2 : (Pi.single 0 1 : Fin (N + 1) → ℂ) ∈ LinearMap.ker (Matrix.toLin' T) := h1
      rw [hk] at h2
      have := congrFun ((Submodule.mem_bot ℂ).mp h2) 0
      simp at this
    · have hinj : Function.Injective (Matrix.toLin' T) :=
        LinearMap.ker_eq_bot.mp hk
      have hsurj : Function.Surjective (Matrix.toLin' T) :=
        LinearMap.range_eq_top.mp hr
      have e := (LinearEquiv.ofBijective (Matrix.toLin' T) ⟨hinj, hsurj⟩).finrank_eq
      simp only [Module.finrank_fin_fun] at e
      exact hNM (by omega)
  · have : Matrix.toLin' T = 0 := by
      refine LinearMap.ext fun v => ?_
      have : v ∈ LinearMap.ker (Matrix.toLin' T) := by rw [hk]; trivial
      simpa using this
    exact Matrix.toLin'.injective (by rw [this, map_zero])

/-- **Schur's lemma, equal spins.** A self-intertwiner of spin `N/2` is a scalar. -/
theorem spin_intertwiner_eq_smul {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hT : ∀ g : SU2, spinMat N g * T = T * spinMat N g) : ∃ c : ℂ, T = c • 1 := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' T)
  refine ⟨c, ?_⟩
  have hT' : ∀ g : SU2, spinMat N g * (T - c • 1) = (T - c • 1) * spinMat N g := fun g => by
    rw [Matrix.mul_sub, Matrix.sub_mul, hT g, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  rcases isInvariant_eq_bot_or_eq_top (isInvariant_ker hT') with hk | hk
  · exfalso
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hmem : v ∈ LinearMap.ker (Matrix.toLin' (T - c • 1)) := by
      have h1 := Module.End.mem_eigenspace_iff.mp hv.1
      rw [Matrix.toLin'_apply] at h1
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, smul_mulVec, one_mulVec, h1,
        sub_self]
    rw [hk] at hmem
    exact hv.2 ((Submodule.mem_bot ℂ).mp hmem)
  · have h0 : Matrix.toLin' (T - c • 1) = 0 := by
      refine LinearMap.ext fun v => ?_
      have : v ∈ LinearMap.ker (Matrix.toLin' (T - c • 1)) := by rw [hk]; trivial
      simpa using this
    have := Matrix.toLin'.injective (h0.trans (map_zero _).symm)
    exact sub_eq_zero.mp this

end Lightlike.Spin4

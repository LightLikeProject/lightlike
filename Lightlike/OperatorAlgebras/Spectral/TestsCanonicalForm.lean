import Lightlike.OperatorAlgebras.Spectral.CanonicalForm

/-!
# Tests for the canonical form of a compact operator

* `isEmpty_of_canonical_zero`: the zero operator has no singular values (every canonical form of `0` has an empty index
  set, since the `sⱼ` are positive and the `φ'ⱼ` are unit vectors);
* `nonempty_of_canonical_ne_zero`: a nonzero operator has a singular value in every canonical form.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CompactSpectral

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The zero operator has no singular values.** -/
theorem isEmpty_of_canonical_zero {ι : Type*} {φ φ' : ι → E} {s : ι → ℝ} (hφ' : Orthonormal 𝕜 φ')
    (hs : ∀ j, 0 < s j) (h : ∀ j, (0 : E →L[𝕜] E) (φ j) = (s j : 𝕜) • φ' j) : IsEmpty ι := by
  refine ⟨fun j => ?_⟩
  have h1 := h j
  rw [ContinuousLinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact (hs j).ne' (by exact_mod_cast h1)
  · exact hφ'.ne_zero j h1

/-- **A nonzero operator has a singular value** in every canonical form: with no terms the expansion gives `K = 0`. -/
theorem nonempty_of_canonical_ne_zero {ι : Type*} {K : E →L[𝕜] E} {φ φ' : ι → E} {s : ι → ℝ}
    (hKx : ∀ x, HasSum (fun j => ((s j : 𝕜) * ⟪φ j, x⟫_𝕜) • φ' j) (K x)) (hK : K ≠ 0) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  apply hK
  ext x
  rw [ContinuousLinearMap.zero_apply]
  exact (hKx x).unique hasSum_empty

end Lightlike.OperatorAlgebras.CompactSpectral

import Lightlike.OperatorAlgebras.Spectral.Schatten
import Lightlike.OperatorAlgebras.Spectral.HilbertSchmidtCompact

/-!
# `J₂` is the Hilbert–Schmidt class

G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 6.3, Lemma 6.10, (6.14), (6.16)-(6.17), p. 140, and
p. 142 ("`J₂(H)` is the space of Hilbert–Schmidt operators investigated in the previous section"): a compact `K` is
Hilbert–Schmidt iff `∑ⱼ sⱼ(K)² < ∞`, iff `∑ₙ ‖K ψₙ‖² < ∞` for some orthonormal basis, and then `∑ₙ ‖K ψₙ‖² = ‖K‖₂²` for
every orthonormal basis.

* `tsum_norm_sq_apply_eq`: Lemma 6.10, `∑ₙ ‖K ψₙ‖² = ∑ⱼ sⱼ²` for a canonical form and every Hilbert basis;
* `schattenSum_two_eq_tsum_norm_sq`: `‖K‖₂² = ∑ₙ ‖K ψₙ‖²` for a compact `K` and every Hilbert basis;
* `isHilbertSchmidt_iff`: `IsHilbertSchmidt K ↔ K` compact and `‖K‖₂ < ∞` (`J₂` is the repository's Hilbert–Schmidt
  class).
-/

open scoped InnerProductSpace NNReal ENNReal

namespace Lightlike.OperatorAlgebras.CompactSpectral

section General

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Teschl, Lemma 6.10**, (6.16)-(6.17), p. 140: for a canonical form `K x = ∑ⱼ sⱼ ⟪φⱼ, x⟫ φ'ⱼ`,
`∑ₙ ‖K ψₙ‖² = ∑ⱼ sⱼ²` in every Hilbert basis `ψ`. -/
theorem tsum_norm_sq_apply_eq {ι S : Type*} {K : E →L[𝕜] E} {φ φ' : ι → E} {s : ι → ℝ}
    (hφ : Orthonormal 𝕜 φ) (hφ' : Orthonormal 𝕜 φ')
    (hK : ∀ x, HasSum (fun j => ((s j : 𝕜) * ⟪φ j, x⟫_𝕜) • φ' j) (K x)) (b : HilbertBasis S 𝕜 E) :
    ∑' i, ENNReal.ofReal (‖K (b i)‖ ^ 2) = ∑' j, ENNReal.ofReal (s j ^ 2) := by
  have h1 : ∀ i, ENNReal.ofReal (‖K (b i)‖ ^ 2) =
      ∑' j, ENNReal.ofReal (s j ^ 2) * ENNReal.ofReal (‖⟪b i, φ j⟫_𝕜‖ ^ 2) := by
    intro i
    have h := hasSum_norm_sq_of_orthonormal hφ' (hK (b i))
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) h.summable]
    refine tsum_congr fun j => ?_
    rw [← ENNReal.ofReal_mul (by positivity), norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs, norm_inner_symm]
  have hpars : ∀ j, ∑' i, ENNReal.ofReal (‖⟪b i, φ j⟫_𝕜‖ ^ 2) = 1 := by
    intro j
    have h := hasSum_norm_sq_of_orthonormal b.orthonormal (b.hasSum_repr (φ j))
    simp only [HilbertBasis.repr_apply_apply] at h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h.summable, h.tsum_eq, hφ.1 j]
    simp
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun j => ?_
  rw [ENNReal.tsum_mul_left, hpars j, mul_one]

/-- **`‖K‖₂² = ∑ₙ ‖K ψₙ‖²`** for a compact `K` and every Hilbert basis `ψ` (Teschl, (6.17), p. 140, with (6.23)). -/
theorem schattenSum_two_eq_tsum_norm_sq {S : Type*} {K : E →L[𝕜] E} (hK : IsCompactOperator K)
    (b : HilbertBasis S 𝕜 E) : schattenSum 2 K = ∑' i, ENNReal.ofReal (‖K (b i)‖ ^ 2) := by
  obtain ⟨ι, φ, φ', s, hc⟩ := exists_isCanonicalForm hK
  rw [schattenSum_eq_tsum hc one_le_two,
    tsum_norm_sq_apply_eq hc.orthonormal_left hc.orthonormal_right hc.hasSum_apply b]
  refine tsum_congr fun j => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (hc.pos j).le zero_le_two, Real.rpow_two]

end General

section HilbertSchmidt

open TraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`J₂` is the Hilbert–Schmidt class** (Teschl, Lemma 6.10 and p. 142): `K` is Hilbert–Schmidt (the repository's
`IsHilbertSchmidt`) iff `K` is compact and `‖K‖₂ < ∞`. -/
theorem isHilbertSchmidt_iff {K : H →L[ℂ] H} :
    IsHilbertSchmidt K ↔ IsCompactOperator K ∧ schattenSum 2 K < ⊤ := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  constructor
  · intro hHS
    have hK := isCompactOperator_of_isHilbertSchmidt hHS
    refine ⟨hK, ?_⟩
    rw [schattenSum_two_eq_tsum_norm_sq hK b, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_norm_sq_apply_of_hilbertBasis w b hHS)]
    exact ENNReal.ofReal_lt_top
  · rintro ⟨hK, hlt⟩
    rw [schattenSum_two_eq_tsum_norm_sq hK b] at hlt
    refine ⟨w, b, ?_⟩
    have h : (∑' i, ENNReal.ofReal (‖K (b i)‖ ^ 2)) ≠ ⊤ := hlt.ne
    simp_rw [ENNReal.ofReal_eq_coe_nnreal (sq_nonneg _)] at h
    rw [ENNReal.tsum_coe_ne_top_iff_summable] at h
    exact (NNReal.summable_coe.mpr h).congr fun i => rfl

end HilbertSchmidt

end Lightlike.OperatorAlgebras.CompactSpectral

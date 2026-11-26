import Mathlib
import Lightlike.TemperleyLieb.ChannelFusion

/-!
# Completeness of a family of orthogonal idempotents by a rank count

`complete_of_rank`: let `Q` and `E_0, …, E_n` be idempotent endomorphisms of a finite-dimensional vector space over a
field of characteristic zero with `E_i E_j = 0` for `i ≠ j` and `Q E_i = E_i = E_i Q`.  If
`Σ rank E_i ≥ rank Q` then `Q = Σ E_i`.  (`Q - Σ E_i` is an idempotent whose trace is `rank Q - Σ rank E_i ≤ 0`.)
-/

namespace Lightlike.TemperleyLieb

open LinearMap Module

variable {K : Type*} [Field K] [CharZero K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Completeness by rank.** -/
theorem complete_of_rank {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : V →ₗ[K] V) (E : ι → V →ₗ[K] V)
    (hQ : IsIdempotentElem Q) (hE : ∀ i, IsIdempotentElem (E i)) (hEE : ∀ i j, i ≠ j → E i * E j = 0)
    (hQE : ∀ i, Q * E i = E i) (hEQ : ∀ i, E i * Q = E i)
    (hrank : finrank K (range Q) ≤ ∑ i, finrank K (range (E i))) : Q = ∑ i, E i := by
  set S := ∑ i, E i with hS
  have hSS : IsIdempotentElem S := by
    unfold IsIdempotentElem
    rw [hS, Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · exact (hE i).eq
    · intro j _ hj; exact hEE i j (Ne.symm hj)
    · intro h; exact absurd (Finset.mem_univ i) h
  have hQS : Q * S = S := by simp [hS, Finset.mul_sum, hQE]
  have hSQ : S * Q = S := by simp [hS, Finset.sum_mul, hEQ]
  set R := Q - S with hR
  have hRR : IsIdempotentElem R := by
    unfold IsIdempotentElem
    have := hQ.eq; have := hSS.eq
    simp only [hR, mul_sub, sub_mul, hQS, hSQ, hQ.eq, hSS.eq]
    abel
  have tr : ∀ {X : V →ₗ[K] V}, IsIdempotentElem X → trace K V X = (finrank K (range X) : K) :=
    fun hX => hX.isProj_range.trace
  have h1 : trace K V R = trace K V Q - ∑ i, trace K V (E i) := by
    simp only [hR, hS, map_sub, map_sum]
  rw [tr hRR, tr hQ] at h1
  simp only [fun i => tr (hE i)] at h1
  have h2 : (finrank K (range R) : K) + ∑ i, (finrank K (range (E i)) : K) = (finrank K (range Q) : K) := by
    rw [h1]; ring
  have h3 : finrank K (range R) + ∑ i, finrank K (range (E i)) = finrank K (range Q) := by
    exact_mod_cast h2
  have h4 : finrank K (range R) = 0 := by omega
  have h5 : R = 0 := by
    have hb : range R = ⊥ := Submodule.finrank_eq_zero.mp h4
    exact LinearMap.range_eq_bot.mp hb
  rw [hR] at h5
  exact sub_eq_zero.mp h5

end Lightlike.TemperleyLieb

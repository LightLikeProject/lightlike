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

/-- The trace of an idempotent is the rank of its range. -/
theorem trace_idempotent {X : V →ₗ[K] V} (hX : IsIdempotentElem X) :
    trace K V X = (finrank K (range X) : K) := hX.isProj_range.trace

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

/-- **Trace of a conjugated idempotent.** If `W ∘ V = κ P` and `E ∘ P = E`, then `κ⁻¹ V E W` has the trace of `E`. -/
theorem trace_conj {P Q : Type*} [AddCommGroup P] [Module K P] [Module.Free K P] [Module.Finite K P]
    [AddCommGroup Q] [Module K Q] [Module.Free K Q] [Module.Finite K Q]
    (Vw : P →ₗ[K] Q) (Ww : Q →ₗ[K] P) (Ew Pp : P →ₗ[K] P) (κ : K) (hκ : κ ≠ 0)
    (hWV : Ww ∘ₗ Vw = κ • Pp) (hEP : Ew ∘ₗ Pp = Ew) :
    trace K Q (κ⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww)) = trace K P Ew := by
  rw [map_smul, smul_eq_mul]
  have h1 : trace K Q (Vw ∘ₗ (Ew ∘ₗ Ww)) = trace K P ((Ew ∘ₗ Ww) ∘ₗ Vw) := trace_comp_comm' (Ew ∘ₗ Ww) Vw
  have h2 : (Ew ∘ₗ Ww) ∘ₗ Vw = κ • Ew := by
    rw [LinearMap.comp_assoc, hWV, LinearMap.comp_smul, hEP]
  rw [h1, h2, map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]

/-- **Ranks of conjugated idempotents.** -/
theorem finrank_conj {P Q : Type*} [AddCommGroup P] [Module K P] [Module.Free K P] [Module.Finite K P]
    [AddCommGroup Q] [Module K Q] [Module.Free K Q] [Module.Finite K Q]
    (Vw : P →ₗ[K] Q) (Ww : Q →ₗ[K] P) (Ew Pp : P →ₗ[K] P) (κ : K) (hκ : κ ≠ 0)
    (hWV : Ww ∘ₗ Vw = κ • Pp) (hEP : Ew ∘ₗ Pp = Ew) (hPE : Pp ∘ₗ Ew = Ew) (hE : IsIdempotentElem Ew) :
    finrank K (range (κ⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww))) = finrank K (range Ew) := by
  have hT : IsIdempotentElem (κ⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww)) := by
    show (κ⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww)) * (κ⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww)) = κ⁻¹ • (Vw ∘ₗ Ew ∘ₗ Ww)
    have hEE : Ew ∘ₗ Ew = Ew := hE.eq
    have key : (Vw ∘ₗ Ew ∘ₗ Ww) * (Vw ∘ₗ Ew ∘ₗ Ww) = κ • (Vw ∘ₗ Ew ∘ₗ Ww) := by
      show (Vw ∘ₗ Ew ∘ₗ Ww) ∘ₗ (Vw ∘ₗ Ew ∘ₗ Ww) = κ • (Vw ∘ₗ Ew ∘ₗ Ww)
      calc (Vw ∘ₗ Ew ∘ₗ Ww) ∘ₗ (Vw ∘ₗ Ew ∘ₗ Ww)
          = Vw ∘ₗ Ew ∘ₗ (Ww ∘ₗ Vw) ∘ₗ Ew ∘ₗ Ww := by
            simp only [LinearMap.comp_assoc]
        _ = Vw ∘ₗ Ew ∘ₗ (κ • Pp) ∘ₗ Ew ∘ₗ Ww := by rw [hWV]
        _ = κ • (Vw ∘ₗ (Ew ∘ₗ Pp ∘ₗ Ew) ∘ₗ Ww) := by
            simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
        _ = κ • (Vw ∘ₗ Ew ∘ₗ Ww) := by rw [hPE, hEE]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, key, smul_smul, mul_assoc, inv_mul_cancel₀ hκ, mul_one]
  have h := trace_conj Vw Ww Ew Pp κ hκ hWV hEP
  rw [trace_idempotent hT, trace_idempotent hE] at h
  exact_mod_cast h

end Lightlike.TemperleyLieb

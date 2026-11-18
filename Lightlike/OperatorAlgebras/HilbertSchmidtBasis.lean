import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Basis independence of the Hilbert-Schmidt square sum

For a bounded operator `S` of a complex Hilbert space, `∑ᵢ ‖S bᵢ‖²` is the same in every Hilbert basis `b`
(finite or infinite, in particular `∑ᵢ ‖S bᵢ‖²` summable in one basis iff in every basis), and equals
`∑ⱼ ‖S† cⱼ‖²` for any second basis `c`. The proof is the Parseval double-sum argument.

Ported, with the index types generalised from subsets of `H` to arbitrary index types, from Physlib
(`PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/Basic.lean`, `hasSum_norm_sq_inner_basis`, and
the Physlib file `.../TraceClass/HilbertSchmidt`, `hasSum_norm_sq_apply_eq_adjoint`, `hasSum_norm_sq_apply_of_basis`;
Copyright (c) 2026 Tom Ole Diem, Apache 2.0; Physlib commit `cdfa6094`). It is the shared base of the
necessity part of Shale's criterion (`T-OP2-P6`) and of the trace-class and Hilbert-Schmidt layer.
-/

open scoped ComplexOrder InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



/-- **Parseval's identity**: `∑ᵢ |⟪eᵢ, y⟫|² = ‖y‖²` for a Hilbert basis `{eᵢ}`. -/
lemma hasSum_norm_sq_inner_basis {ι : Type*} (b : HilbertBasis ι ℂ H) (y : H) :
    HasSum (fun i : ι => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have hpt : ∀ i : ι, ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ = ((‖⟪b i, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm y (b i), RCLike.conj_mul]
    norm_cast
  have hval : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [hpt] at h
  rw [hval] at h
  exact Complex.hasSum_ofReal.mp h



/-- The Hilbert–Schmidt square sum of `S` in one basis equals the square sum of `S⋆` in a second
basis. This is the nonnegative double-sum identity; the usual basis-independence statement follows
by applying it twice. -/
lemma hasSum_norm_sq_apply_eq_adjoint {S : H →L[ℂ] H}
    {ι ι' : Type*} (b : HilbertBasis ι ℂ H) (c : HilbertBasis ι' ℂ H)
    (hb : Summable (fun i : ι => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : ι' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2)
      (∑' i : ι, ‖S (b i)‖ ^ 2) := by
  classical
  set F : ι → ι' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : ι, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hcol : ∀ j : ι', HasSum (fun i : ι => F i j)
      (‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : ι, ⟪c j, S (b i)⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ := fun i =>
      (ContinuousLinearMap.adjoint_inner_left S (b i) (c j)).symm
    have key : (fun i : ι => F i j) = fun i : ι =>
        ‖⟪b i, (ContinuousLinearMap.adjoint S) (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) ((ContinuousLinearMap.adjoint S) (c j)),
        RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b ((ContinuousLinearMap.adjoint S) (c j))
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : ι => ∑' j : ι', F i j) = fun i : ι => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : ι => ∑' j : ι', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  have hLHS : ∑' j : ι', ∑' i : ι, F i j = ∑' j : ι', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : ι, ∑' j : ι', F i j = ∑' i : ι, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : ι', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 = ∑' i : ι, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]; exact hswap
  set G : ι' → ι → ℝ := fun j i => F i j with hGdef
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘ (Equiv.prodComm ι' ι) := by
      funext p; simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm ι' ι).summable_iff.mpr hjoint
  have hcolSummable : Summable
      (fun j : ι' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : ι' => ∑' i : ι, G j i := hpair.2
    have heq2 : (fun j : ι' => ∑' i : ι, G j i) = fun j : ι' =>
        ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

/-- **Basis independence**: if `∑ᵢ ‖S bᵢ‖²` converges in one Hilbert basis `b`, it converges in every Hilbert
basis `c`, to the same sum. -/
lemma hasSum_norm_sq_apply_of_basis {S : H →L[ℂ] H} {ι ι' : Type*}
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis ι' ℂ H)
    (hb : Summable (fun i : ι => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : ι' => ‖S (c j)‖ ^ 2) (∑' i : ι, ‖S (b i)‖ ^ 2) := by
  have hfirst := hasSum_norm_sq_apply_eq_adjoint b c hb
  have hstarc : Summable (fun j : ι' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) :=
    hfirst.summable
  have hsecond := hasSum_norm_sq_apply_eq_adjoint (S := ContinuousLinearMap.adjoint S) c c hstarc
  have hsecond' : HasSum (fun j : ι' => ‖S (c j)‖ ^ 2)
      (∑' j : ι', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hsecond
  rw [← hfirst.tsum_eq]
  exact hsecond'
end Lightlike.OperatorAlgebras

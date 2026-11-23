import Lightlike.Geometry.HeatKernel.Expansion

/-!
# Heat-trace expansions of products

For a Riemannian product `M × M'` the Laplace-type operator is `D ⊗ 1 + 1 ⊗ D'`, so the heat trace
is the product `K t * L t` of the two heat traces. If `K ∼ Σ a_k t^{k - n/2}` and
`L ∼ Σ b_j t^{j - m/2}`, then `K L ∼ Σ_l c_l t^{l - (n+m)/2}` with `c = a ⋆ b` the Cauchy product.
This is the algebraic form of the additivity of `a₁ = (4π)^{-n/2} ∫ R/6` under products
(`R` and the volume are additive/multiplicative).

## Main definitions

* `Lightlike.HeatKernel.convCoeff a b`: the Cauchy product of two coefficient sequences.

## Main results

* `HasHeatExpansionTo.mul`, `HasHeatExpansion.mul`: expansion of a product of heat traces.
* `HasHeatExpansionTo.isBigO`: a heat trace with expansion is `O(t^{-n/2})`.
-/

open Filter Topology Asymptotics Finset

noncomputable section

namespace Lightlike.HeatKernel

/-- `t ^ x = O(t ^ y)` as `t → 0⁺` when `y ≤ x`. -/
theorem rpow_isBigO_of_le {x y : ℝ} (h : y ≤ x) :
    (fun t : ℝ => t ^ x) =O[𝓝[>] (0 : ℝ)] fun t => t ^ y := by
  refine IsBigO.of_bound' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le h

/-- The truncated series of a heat expansion is `O(t^{-n/2})`. -/
theorem truncated_isBigO (n N : ℕ) (a : ℕ → ℝ) :
    (fun t : ℝ => ∑ k ∈ Finset.range N, a k * t ^ ((k : ℝ) - n / 2)) =O[𝓝[>] (0 : ℝ)]
      fun t => t ^ (-(n : ℝ) / 2) := by
  refine IsBigO.fun_sum (fun k _ => ?_)
  refine (rpow_isBigO_of_le ?_).const_mul_left (a k)
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  linarith

/-- A heat trace with an expansion is `O(t^{-n/2})`. -/
theorem HasHeatExpansionTo.isBigO {n N : ℕ} {K : ℝ → ℝ} {a : ℕ → ℝ}
    (h : HasHeatExpansionTo n N K a) :
    K =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-(n : ℝ) / 2) := by
  have h1 := h.trans (rpow_isBigO_of_le (x := (N : ℝ) - n / 2) (y := -(n : ℝ) / 2)
    (by have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith))
  refine (h1.add (truncated_isBigO n N a)).congr_left ?_
  intro t
  simp

/-- Cauchy product of coefficient sequences. -/
def convCoeff (a b : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal l, a p.1 * b p.2

private theorem rpow_mul_rpow_aux (n m k j : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ ((k : ℝ) - n / 2) * t ^ ((j : ℝ) - m / 2)
      = t ^ (((k + j : ℕ) : ℝ) - ((n + m : ℕ) : ℝ) / 2) := by
  rw [← Real.rpow_add ht]
  congr 1
  push_cast
  ring

/-- **Heat trace of a product.** If `K ∼ Σ a_k t^{k-n/2}` and `L ∼ Σ b_j t^{j-m/2}` up to order `N`,
then `K L ∼ Σ (a ⋆ b)_l t^{l-(n+m)/2}` up to order `N`. -/
theorem HasHeatExpansionTo.mul {n m N : ℕ} {K L : ℝ → ℝ} {a b : ℕ → ℝ}
    (hK : HasHeatExpansionTo n N K a) (hL : HasHeatExpansionTo m N L b) :
    HasHeatExpansionTo (n + m) N (fun t => K t * L t) (convCoeff a b) := by
  set A : ℝ → ℝ := fun t => ∑ k ∈ Finset.range N, a k * t ^ ((k : ℝ) - n / 2) with hA
  set B : ℝ → ℝ := fun t => ∑ k ∈ Finset.range N, b k * t ^ ((k : ℝ) - m / 2) with hB
  let f : ℕ × ℕ → ℝ → ℝ := fun p t =>
    a p.1 * b p.2 * t ^ (((p.1 + p.2 : ℕ) : ℝ) - ((n + m : ℕ) : ℝ) / 2)
  let R : ℝ → ℝ := fun t =>
    ∑ p ∈ Finset.range N ×ˢ Finset.range N, if N ≤ p.1 + p.2 then f p t else 0
  have hE : (fun t => (K t - A t) * L t) =O[𝓝[>] (0 : ℝ)]
      fun t => t ^ (((N : ℝ) - ((n + m : ℕ) : ℝ) / 2)) := by
    refine (IsBigO.mul hK hL.isBigO).congr' EventuallyEq.rfl ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← Real.rpow_add (show (0 : ℝ) < t from ht)]
    congr 1
    push_cast
    ring
  have hF : (fun t => A t * (L t - B t)) =O[𝓝[>] (0 : ℝ)]
      fun t => t ^ (((N : ℝ) - ((n + m : ℕ) : ℝ) / 2)) := by
    refine (IsBigO.mul (truncated_isBigO n N a) hL).congr' EventuallyEq.rfl ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← Real.rpow_add (show (0 : ℝ) < t from ht)]
    congr 1
    push_cast
    ring
  have hR : R =O[𝓝[>] (0 : ℝ)] fun t => t ^ (((N : ℝ) - ((n + m : ℕ) : ℝ) / 2)) := by
    refine IsBigO.fun_sum (fun p hp => ?_)
    by_cases hc : N ≤ p.1 + p.2
    · simp only [hc, ite_true]
      refine (rpow_isBigO_of_le ?_).const_mul_left (a p.1 * b p.2)
      have : (N : ℝ) ≤ ((p.1 + p.2 : ℕ) : ℝ) := by exact_mod_cast hc
      linarith
    · simp only [hc, ite_false]
      exact isBigO_zero _ _
  have hsum := (hE.add hF).add hR
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hAB : A t * B t = ∑ p ∈ Finset.range N ×ˢ Finset.range N, f p t := by
    simp only [hA, hB, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [f]
    rw [← rpow_mul_rpow_aux n m k j ht']
    ring
  have hS : ∑ k ∈ Finset.range N, convCoeff a b k * t ^ ((k : ℝ) - ((n + m : ℕ) : ℝ) / 2)
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N, if p.1 + p.2 < N then f p t else 0 := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.range N ×ˢ Finset.range N).filter
      (fun p => p.1 + p.2 < N)) (t := Finset.range N) (g := fun p => p.1 + p.2)
      (fun p hp => by simp at hp ⊢; exact hp.2)]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hfib : ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)).filter
        (fun p => p.1 + p.2 = l) = Finset.HasAntidiagonal.antidiagonal l := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.HasAntidiagonal.mem_antidiagonal]
      have := Finset.mem_range.mp hl
      omega
    rw [hfib, convCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    simp only [f]
    rw [hp']
  have key : K t * L t - ∑ k ∈ Finset.range N,
      convCoeff a b k * t ^ ((k : ℝ) - ((n + m : ℕ) : ℝ) / 2)
      = (K t - A t) * L t + A t * (L t - B t) + R t := by
    rw [hS]
    have : R t = A t * B t - ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        if p.1 + p.2 < N then f p t else 0 := by
      rw [hAB, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hc : N ≤ p.1 + p.2
      · simp [hc, not_lt.mpr hc]
      · simp [hc, not_le.mp hc]
    rw [this]
    ring
  exact key.symm

/-- **Heat trace of a product, full expansion.** -/
theorem HasHeatExpansion.mul {n m : ℕ} {K L : ℝ → ℝ} {a b : ℕ → ℝ}
    (hK : HasHeatExpansion n K a) (hL : HasHeatExpansion m L b) :
    HasHeatExpansion (n + m) (fun t => K t * L t) (convCoeff a b) :=
  fun N => HasHeatExpansionTo.mul (hK N) (hL N)

theorem convCoeff_zero (a b : ℕ → ℝ) : convCoeff a b 0 = a 0 * b 0 := by
  simp [convCoeff]

theorem convCoeff_one (a b : ℕ → ℝ) : convCoeff a b 1 = a 0 * b 1 + a 1 * b 0 := by
  simp [convCoeff, Finset.Nat.antidiagonal_succ]

theorem convCoeff_two (a b : ℕ → ℝ) :
    convCoeff a b 2 = a 0 * b 2 + a 1 * b 1 + a 2 * b 0 := by
  simp [convCoeff, Finset.Nat.antidiagonal_succ]
  ring

end Lightlike.HeatKernel

import Lightlike.HarmonicAnalysis.SU2Complete

/-!
# The Peter–Weyl basis of `L²(SU(2))`

For the Haar probability measure `μ` of `SU(2)`, the functions `√(n+1) · Dⁿ_{ij}`, with `Dⁿ` the spin-`n/2`
representation (`Lightlike.SU2.spinMat n`), `n : ℕ` and `i, j : Fin (n + 1)`, form a Hilbert basis of
`L²(SU(2), μ)` (`su2_hilbertBasis`). This is the Peter–Weyl theorem (`peterWeyl_hilbertBasis`) for `SU(2)`
with the classes of irreducible representations made explicit by `su2_irreducible_classification`; it is the
basis of spin-network functions on one edge.

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), §1, Propositions 7 and 8 (the general theorem).
* C. Teleman, *Representation Theory* (lecture notes, Cambridge, Lent 2005), Lecture 21, Theorem 21.1 (the
  list of irreducible representations of SU(2)).
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

open UnitaryMatrixRep

variable (μ : Measure SU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- The index of the Peter–Weyl basis of `SU(2)`: a spin `n/2` and a pair of magnetic indices. -/
abbrev SU2CoeffIdx : Type := Σ n : ℕ, Fin (n + 1) × Fin (n + 1)

/-- The matrix element `g ↦ Dⁿ(g)_{ij}` of the spin-`n/2` representation, as a continuous function. -/
def su2Coeff (n : ℕ) (i j : Fin (n + 1)) : C(SU2, ℂ) :=
  ⟨fun g => (su2Spin n).mat g i j, (su2Spin n).continuous_mat_apply i j⟩

/-- The normalised matrix element `√(n+1) · Dⁿ_{ij}` in `L²(SU(2), μ)`. -/
def su2CoeffFamily (a : SU2CoeffIdx) : Lp ℂ 2 μ :=
  ((Real.sqrt ((a.1 : ℝ) + 1) : ℝ) : ℂ) •
    ContinuousMap.toLp (E := ℂ) 2 μ ℂ (su2Coeff a.1 a.2.1 a.2.2)

/-- The functions `√(n+1) · Dⁿ_{ij}` are orthonormal (Schur orthogonality). -/
theorem orthonormal_su2CoeffFamily : Orthonormal ℂ (su2CoeffFamily μ) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨n, i, j⟩ ⟨m, l, k⟩
  simp only [su2CoeffFamily]
  rw [inner_smul_left, inner_smul_right, inner_toLp_toLp]
  by_cases hnm : n = m
  · subst hnm
    have hs : ∫ x, su2Coeff n l k x * starRingEnd ℂ (su2Coeff n i j x) ∂μ =
        if l = i ∧ k = j then 1 / ((Fintype.card (Fin (n + 1)) : ℕ) : ℂ) else 0 :=
      schur_orthogonality_eq μ (su2Spin_isIrreducible n) l k j i
    rw [hs]
    have hsq : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) =
        (n : ℂ) + 1 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      simp
    have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    by_cases h : i = l ∧ j = k
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
      simp only [Complex.conj_ofReal, Fintype.card_fin]
      rw [← mul_assoc, hsq]
      push_cast
      rw [mul_one_div, div_self hn]
    · rw [if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩, if_neg]
      · simp
      · intro h'
        exact h (Prod.mk.inj (eq_of_heq (Sigma.mk.inj_iff.1 h').2))
  · rw [if_neg fun h' => hnm (congrArg Sigma.fst h')]
    have h0 : ∫ x, su2Coeff m l k x * starRingEnd ℂ (su2Coeff n i j x) ∂μ = 0 :=
      schur_orthogonality_ne μ (su2Spin_isIrreducible m) (su2Spin_isIrreducible n)
        (su2Spin_not_equivalent (Ne.symm hnm)) l k j i
    rw [h0]
    simp

/-- **Completeness.** A function orthogonal to all `Dⁿ_{ij}` is zero. -/
theorem eq_zero_of_orthogonal_su2CoeffFamily {v : Lp ℂ 2 μ}
    (hv : ∀ a, inner ℂ v (su2CoeffFamily μ a) = 0) : v = 0 := by
  have hbase : ∀ (n : ℕ) (i j : Fin (n + 1)),
      inner ℂ v (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (su2Coeff n i j)) = 0 := by
    intro n i j
    have h := hv ⟨n, (i, j)⟩
    simp only [su2CoeffFamily, inner_smul_right] at h
    have hne : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      exact_mod_cast hpos.ne'
    exact (mul_eq_zero.1 h).resolve_left hne
  refine eq_zero_of_orthogonal_coeffFamily μ fun a => ?_
  obtain ⟨π, i, j⟩ := a
  obtain ⟨n, hn, -⟩ := su2_irreducible_classification (Quotient.out π : IrrRep SU2).irr
  obtain ⟨c, hc⟩ := UnitaryMatrixRep.entry_eq_sum_of_equivalent hn i j
  have hfun : coeffFun (Quotient.out π : IrrRep SU2) i j = ∑ a, ∑ b, c a b • su2Coeff n a b := by
    ext g
    simp only [coeffFun, su2Coeff, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    exact hc g
  simp only [coeffFamily, inner_smul_right]
  rw [hfun]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, hbase, mul_zero, Finset.sum_const_zero]

/-- **The Peter–Weyl basis of `L²(SU(2))`.** The functions `√(n+1) · Dⁿ_{ij}` form a Hilbert basis of
`L²(SU(2), μ)`. -/
theorem su2_hilbertBasis :
    ∃ b : HilbertBasis SU2CoeffIdx ℂ (Lp ℂ 2 μ), ∀ a, b a = su2CoeffFamily μ a := by
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range (su2CoeffFamily μ))).topologicalClosure := by
    rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff]
    refine (Submodule.eq_bot_iff _).2 fun χ hχ => ?_
    refine eq_zero_of_orthogonal_su2CoeffFamily μ fun a => ?_
    have h1 : inner ℂ (su2CoeffFamily μ a) χ = 0 :=
      (Submodule.mem_orthogonal _ _).1 hχ _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [← inner_conj_symm, h1]
    simp
  exact ⟨HilbertBasis.mk (orthonormal_su2CoeffFamily μ) hsp, fun a => by simp⟩

end

end Lightlike.HarmonicAnalysis

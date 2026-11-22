import Lightlike.Rows.G2_010.Maschke

/-!
# Spin networks, step C2a: products of spin coefficients are combinations of the `phi n i j`

Row G2-010 (milestone OP, task T-CA2). If every factor `f e` lies in `spinSpan`, then the product function
`h ↦ ∏_e f e (h e)` on `SU(2)^E` lies in the span of the normalised coefficients `phi n i j`
(`prod_mem_phiSpan`, multilinear expansion with `Finset.prod_univ_sum`).

Supporting lemmas for the spin-network basis theorem; no catalogue entry.
-/

namespace Lightlike.Rows.G2_010

open Lightlike Lightlike.Spin4 Lightlike.HarmonicAnalysis

noncomputable section

variable {E : Type} [Fintype E]

/-- The span of the product coefficients `phi n i j` inside all functions on `SU(2)^E`. -/
def phiSpan (E : Type) [Fintype E] : Submodule ℂ ((E → SU2) → ℂ) :=
  Submodule.span ℂ {F | ∃ (n : E → ℕ) (i j : Idx n), F = phi n i j}

lemma phi_mem_phiSpan (n : E → ℕ) (i j : Idx n) : phi n i j ∈ phiSpan E :=
  Submodule.subset_span ⟨n, i, j, rfl⟩

lemma spinMat_eq_phiEdge (n : ℕ) (i j : Fin (n + 1)) (g : SU2) :
    SU2.spinMat n g i j = (((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) * phiEdge n i j g := by
  have hs : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  simp only [phiEdge, Complex.ofReal_inv]
  field_simp

/-- **Multilinear expansion.** A product of spin coefficients, one on each edge, is a linear combination
of the `phi n i j`. -/
lemma prod_mem_phiSpan (f : E → SU2 → ℂ) (hf : ∀ e, f e ∈ spinSpan) :
    (fun h : E → SU2 => ∏ e, f e (h e)) ∈ phiSpan E := by
  classical
  let v : (Σ n : ℕ, Fin (n + 1) × Fin (n + 1)) → (SU2 → ℂ) :=
    fun a g => SU2.spinMat a.1 g a.2.1 a.2.2
  have hset : {f : SU2 → ℂ | ∃ (n : ℕ) (i j : Fin (n + 1)), f = fun g : SU2 => SU2.spinMat n g i j} =
      Set.range v := by
    ext F
    constructor
    · rintro ⟨n, i, j, rfl⟩
      exact ⟨⟨n, i, j⟩, rfl⟩
    · rintro ⟨⟨n, i, j⟩, rfl⟩
      exact ⟨n, i, j, rfl⟩
  have hf' : ∀ e, ∃ c : (Σ n : ℕ, Fin (n + 1) × Fin (n + 1)) →₀ ℂ,
      (c.sum fun a x => x • v a) = f e := by
    intro e
    have := hf e
    unfold spinSpan at this
    rw [hset] at this
    exact Finsupp.mem_span_range_iff_exists_finsupp.1 this
  choose c hc using hf'
  have hfe : ∀ e g, f e g = ∑ a ∈ (c e).support, c e a * v a g := by
    intro e g
    rw [← hc e]
    simp [Finsupp.sum, Finset.sum_apply]
  have key : (fun h : E → SU2 => ∏ e, f e (h e)) =
      ∑ p ∈ Fintype.piFinset fun e => (c e).support,
        (∏ e, (c e (p e) * (((Real.sqrt (((p e).1 : ℝ) + 1))⁻¹ : ℝ) : ℂ))) •
          phi (fun e => (p e).1) (fun e => (p e).2.1) (fun e => (p e).2.2) := by
    funext h
    simp_rw [hfe]
    rw [Finset.prod_univ_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, phi]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    simp only [v]
    rw [spinMat_eq_phiEdge]
    ring
  rw [key]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (phi_mem_phiSpan _ _ _)

end

end Lightlike.Rows.G2_010

import Lightlike.HarmonicAnalysis.WeylIntegrationSU2
import Lightlike.HarmonicAnalysis.PeterWeylTests

/-!
# The spin representations are all the irreducible representations of SU(2)

`su2_irreducible_classification`: every irreducible continuous unitary matrix representation of `SU(2)` is
equivalent to a spin representation `su2Spin n` (`Lightlike.SU2.spinRep n`, of dimension `n + 1`).

Proof: an irreducible `σ` inequivalent to all `su2Spin n` has a character orthogonal to every `χ_n`, hence to
every polynomial in the half-trace (`χ_n = U_n(½ tr)`, and the `U_n` span the polynomials). Its character is
a continuous function of the half-trace, so by the Weierstrass theorem it is orthogonal to itself, against
`∫ |χ_σ|² = 1`.

## References

* C. Teleman, *Representation Theory* (lecture notes, Cambridge, Lent 2005), Lecture 21, Theorem 21.1
  ("this is the complete list of irreducibles").
-/

open MeasureTheory Polynomial TopologicalSpace

namespace Lightlike.HarmonicAnalysis

noncomputable section

open UnitaryMatrixRep

variable {κ : Type} [Fintype κ] [DecidableEq κ] (μ : Measure SU2) [μ.IsHaarMeasure]
  [IsProbabilityMeasure μ]

/-- The character of an irreducible representation inequivalent to all spin representations is orthogonal
to every polynomial in the half-trace. -/
theorem integral_eval_mul_conj_character_eq_zero {σ : UnitaryMatrixRep SU2 κ} (hσ : σ.IsIrreducible)
    (hne : ∀ n : ℕ, ¬ Equivalent (su2Spin n) σ) (p : ℝ[X]) :
    ∫ g, ((p.eval (su2HalfTr g) : ℝ) : ℂ) * starRingEnd ℂ (σ.character g) ∂μ = 0 := by
  have hspan : p ∈ Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) := by
    rw [span_chebyshevU_eq_top]
    exact Submodule.mem_top
  have hint : ∀ q : ℝ[X], Integrable
      (fun g => ((q.eval (su2HalfTr g) : ℝ) : ℂ) * starRingEnd ℂ (σ.character g)) μ := fun q =>
    ((Complex.continuous_ofReal.comp ((Polynomial.continuous q).comp continuous_su2HalfTr)).mul
      (Complex.continuous_conj.comp σ.continuous_character)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine Submodule.span_induction (p := fun q _ =>
    ∫ g, ((q.eval (su2HalfTr g) : ℝ) : ℂ) * starRingEnd ℂ (σ.character g) ∂μ = 0) ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨n, rfl⟩
    show ∫ g, (((Chebyshev.U ℝ n).eval (su2HalfTr g) : ℝ) : ℂ) * starRingEnd ℂ (σ.character g) ∂μ = 0
    have h := character_orthogonality_ne μ (su2Spin_isIrreducible n) hσ (hne n)
    simp_rw [su2Spin_character_eq_U] at h
    exact h
  · simp
  · intro q r _ _ hq hr
    simp only [Polynomial.eval_add, Complex.ofReal_add, add_mul]
    rw [integral_add (hint q) (hint r), hq, hr, add_zero]
  · intro c q _ hq
    simp only [Polynomial.eval_smul, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
    rw [integral_const_mul, hq, mul_zero]

include μ in
/-- Completeness of the spin representations, with a Haar probability measure as a parameter. -/
lemma su2_irreducible_equivalent_spin_aux {σ : UnitaryMatrixRep SU2 κ} (hσ : σ.IsIrreducible) :
    ∃ n : ℕ, Equivalent (su2Spin n) σ := by
  by_contra hno
  push_neg at hno
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℂ, ∀ x, Φ x = σ.character (Spin4.torusExp (Real.arccos x)) :=
    ⟨_, fun _ => rfl⟩
  have hΦc : Continuous Φ := by
    have h : Φ = fun x => σ.character (Spin4.torusExp (Real.arccos x)) := funext hΦ
    rw [h]
    exact σ.continuous_character.comp (continuous_torusExp.comp Real.continuous_arccos)
  have hχ : ∀ g, σ.character g = Φ (su2HalfTr g) := fun g => by
    rw [hΦ]
    exact su2_eq_of_isClassFunction _ σ.character_conj g
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn σ.continuous_character.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 (Set.mem_univ _))
  have hone : ∫ g, σ.character g * starRingEnd ℂ (σ.character g) ∂μ = 1 :=
    character_orthogonality_eq μ hσ
  have hI : ∀ F : SU2 → ℂ, Continuous F → Integrable F μ := fun F hF =>
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcχ : Continuous σ.character := σ.continuous_character
  have hcc : Continuous fun g => starRingEnd ℂ (σ.character g) := Complex.continuous_conj.comp hcχ
  have key : ∀ ε : ℝ, 0 < ε → (1 : ℝ) ≤ 2 * ε * M := by
    intro ε hε
    obtain ⟨pr, hpr⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => (Φ x).re)
      (Complex.continuous_re.comp hΦc).continuousOn ε hε
    obtain ⟨pi, hpi⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => (Φ x).im)
      (Complex.continuous_im.comp hΦc).continuousOn ε hε
    have h0r := integral_eval_mul_conj_character_eq_zero μ hσ hno pr
    have h0i := integral_eval_mul_conj_character_eq_zero μ hσ hno pi
    have hcr : Continuous fun g : SU2 => ((pr.eval (su2HalfTr g) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((Polynomial.continuous pr).comp continuous_su2HalfTr)
    have hci : Continuous fun g : SU2 => ((pi.eval (su2HalfTr g) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((Polynomial.continuous pi).comp continuous_su2HalfTr)
    have hP : ∫ g, (((pr.eval (su2HalfTr g) : ℝ) : ℂ) + ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I) *
        starRingEnd ℂ (σ.character g) ∂μ = 0 := by
      have e : ∀ g : SU2, (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
          ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I) * starRingEnd ℂ (σ.character g) =
          ((pr.eval (su2HalfTr g) : ℝ) : ℂ) * starRingEnd ℂ (σ.character g) +
          Complex.I * (((pi.eval (su2HalfTr g) : ℝ) : ℂ) * starRingEnd ℂ (σ.character g)) :=
        fun g => by ring
      simp_rw [e]
      have hir : Integrable (fun g : SU2 => ((pr.eval (su2HalfTr g) : ℝ) : ℂ) *
          starRingEnd ℂ (σ.character g)) μ := hI _ (hcr.mul hcc)
      have hii : Integrable (fun g : SU2 => Complex.I * (((pi.eval (su2HalfTr g) : ℝ) : ℂ) *
          starRingEnd ℂ (σ.character g))) μ := (hI _ (hci.mul hcc)).const_mul _
      rw [integral_add hir hii, integral_const_mul, h0r, h0i]
      simp
    have hdiff : ∫ g, (σ.character g - (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
        ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I)) * starRingEnd ℂ (σ.character g) ∂μ = 1 := by
      have e : ∀ g : SU2, (σ.character g - (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
          ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I)) * starRingEnd ℂ (σ.character g) =
          σ.character g * starRingEnd ℂ (σ.character g) -
          (((pr.eval (su2HalfTr g) : ℝ) : ℂ) + ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I) *
            starRingEnd ℂ (σ.character g) := fun g => by ring
      simp_rw [e]
      have hi1 : Integrable (fun g : SU2 => σ.character g * starRingEnd ℂ (σ.character g)) μ :=
        hI _ (hcχ.mul hcc)
      have hiP : Integrable (fun g : SU2 => (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
          ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I) * starRingEnd ℂ (σ.character g)) μ :=
        hI _ ((hcr.add (hci.mul continuous_const)).mul hcc)
      rw [integral_sub hi1 hiP, hone, hP, sub_zero]
    have hbound : ‖∫ g, (σ.character g - (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
        ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I)) * starRingEnd ℂ (σ.character g) ∂μ‖ ≤
        2 * ε * M := by
      have h := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun g => (σ.character g - (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
          ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I)) * starRingEnd ℂ (σ.character g))
        (C := 2 * ε * M) (Filter.Eventually.of_forall fun g => by
          have hx := su2HalfTr_mem_Icc g
          have hr : |pr.eval (su2HalfTr g) - (Φ (su2HalfTr g)).re| ≤ ε := (hpr _ hx).le
          have hi : |pi.eval (su2HalfTr g) - (Φ (su2HalfTr g)).im| ≤ ε := (hpi _ hx).le
          have a1 : |(Φ (su2HalfTr g)).re - pr.eval (su2HalfTr g)| ≤ ε := by
            rw [abs_sub_comm]; exact hr
          have a2 : |(Φ (su2HalfTr g)).im - pi.eval (su2HalfTr g)| ≤ ε := by
            rw [abs_sub_comm]; exact hi
          have h1 : ‖σ.character g - (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
              ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * ε := by
            rw [hχ g]
            refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
            have e1 : (Φ (su2HalfTr g) - (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
                ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I)).re =
                (Φ (su2HalfTr g)).re - pr.eval (su2HalfTr g) := by simp
            have e2 : (Φ (su2HalfTr g) - (((pr.eval (su2HalfTr g) : ℝ) : ℂ) +
                ((pi.eval (su2HalfTr g) : ℝ) : ℂ) * Complex.I)).im =
                (Φ (su2HalfTr g)).im - pi.eval (su2HalfTr g) := by simp
            rw [e1, e2]
            linarith
          rw [norm_mul, RCLike.norm_conj]
          exact mul_le_mul h1 (hM g (Set.mem_univ _)) (norm_nonneg _) (by positivity))
      simpa using h
    rw [hdiff, norm_one] at hbound
    exact hbound
  have h := key (1 / (4 * (M + 1))) (by positivity)
  have e : 2 * (1 / (4 * (M + 1))) * M = M / (2 * (M + 1)) := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity)] at h
  linarith

/-- **The spin representations are all the irreducible unitary representations of SU(2).** Every irreducible
continuous unitary matrix representation of `SU(2)` is equivalent to `su2Spin n` for some `n`, and then has
dimension `n + 1`. -/
theorem su2_irreducible_classification {σ : UnitaryMatrixRep SU2 κ} (hσ : σ.IsIrreducible) :
    ∃ n : ℕ, Equivalent (su2Spin n) σ ∧ Fintype.card κ = n + 1 := by
  have hp := isProbabilityMeasure_haarMeasure_top SU2
  obtain ⟨n, hn⟩ := su2_irreducible_equivalent_spin_aux (Measure.haarMeasure ⊤) hσ
  refine ⟨n, hn, ?_⟩
  obtain ⟨e, -⟩ := hn
  have h1 := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  exact h1

end

end Lightlike.HarmonicAnalysis

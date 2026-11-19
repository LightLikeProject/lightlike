import Lightlike.Spin4.Rep

/-!
# Conjugacy classes of SU(2): every element is conjugate to a diagonal one

`exists_conj_torus`, `exists_conj_torusExp`: every `g ∈ SU(2)` is `h · diag(e^{iθ}, e^{-iθ}) · h⁻¹` for some
`h ∈ SU(2)` and `θ : ℝ`. The proof takes a unit eigenvector `(a, b)` of `g` and conjugates by the matrix
`[[a, -b̄], [b, ā]]` of SU(2) with that first column.

Supporting lemmas for the Weyl integration formula; no catalogue entry.

## References

* C. Teleman, *Representation Theory* (lecture notes, Cambridge, Lent 2005), Lecture 20, §(20.3) and
  Proposition 20.4.
-/

open Matrix

namespace Lightlike.HarmonicAnalysis

noncomputable section

/-- For `g ∈ SU(2)` the conjugate transpose is the adjugate. -/
lemma su2_star_eq_adjugate (g : SU2) :
    star (g : Matrix (Fin 2) (Fin 2) ℂ) = adjugate (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp g.2
  have hstar : star (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    mem_unitaryGroup_iff'.mp hU
  calc star (g : Matrix (Fin 2) (Fin 2) ℂ)
      = star (g : Matrix (Fin 2) (Fin 2) ℂ) *
          ((g : Matrix (Fin 2) (Fin 2) ℂ) * adjugate (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
        rw [mul_adjugate, hdet, one_smul, mul_one]
    _ = adjugate (g : Matrix (Fin 2) (Fin 2) ℂ) := by rw [← Matrix.mul_assoc, hstar, Matrix.one_mul]

/-- The lower right entry of `g ∈ SU(2)` is the conjugate of the upper left one. -/
lemma su2_apply_one_one (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  have e00 := congrFun (congrFun (su2_star_eq_adjugate g) 0) 0
  simp only [adjugate_fin_two, star_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at e00
  exact e00.symm

/-- The lower left entry of `g ∈ SU(2)` is minus the conjugate of the upper right one. -/
lemma su2_apply_one_zero (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  have e01 := congrFun (congrFun (su2_star_eq_adjugate g) 0) 1
  simp only [adjugate_fin_two, star_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at e01
  have h : starRingEnd ℂ (starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) =
      starRingEnd ℂ (-(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := congrArg (starRingEnd ℂ) e01
  rw [Complex.conj_conj, map_neg] at h
  exact h

/-- The element `[[a, -b̄], [b, ā]]` of SU(2) with first column the unit vector `(a, b)`. -/
def su2OfColumn (a b : ℂ) (h : a * starRingEnd ℂ a + b * starRingEnd ℂ b = 1) : SU2 :=
  ⟨!![a, -starRingEnd ℂ b; b, starRingEnd ℂ a], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · have hs : star (!![a, -starRingEnd ℂ b; b, starRingEnd ℂ a] : Matrix (Fin 2) (Fin 2) ℂ) =
          !![starRingEnd ℂ a, starRingEnd ℂ b; -b, a] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
      rw [hs, Matrix.mul_fin_two, Matrix.one_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;>
        first
          | linear_combination h
          | ring
    · rw [det_fin_two_of]
      linear_combination h⟩

lemma su2OfColumn_coe (a b : ℂ) (h : a * starRingEnd ℂ a + b * starRingEnd ℂ b = 1) :
    (su2OfColumn a b h : Matrix (Fin 2) (Fin 2) ℂ) = !![a, -starRingEnd ℂ b; b, starRingEnd ℂ a] := rfl

/-- **Every element of SU(2) is conjugate to a diagonal element.** -/
theorem exists_conj_torus (g : SU2) :
    ∃ (h : SU2) (z : ℂ) (hz : z * star z = 1), g = h * SU2.torus z hz * h⁻¹ := by
  -- an eigenvector
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue
    (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℂ))
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  have hGv : (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = lam • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have e0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * v 0 + (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * v 1 =
      lam * v 0 := by
    have h := congrFun hGv 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have e1 : -starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * v 0 +
      starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * v 1 = lam * v 1 := by
    have h := congrFun hGv 1
    rw [← su2_apply_one_zero g, ← su2_apply_one_one g]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  -- normalise it
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = Complex.normSq (v 0) + Complex.normSq (v 1) := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv0 (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
    have h0 := Complex.normSq_nonneg (v 0)
    have h1 := Complex.normSq_nonneg (v 1)
    rcases hne with h | h
    · have := Complex.normSq_pos.2 h
      linarith
    · have := Complex.normSq_pos.2 h
      linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt N := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hNpos
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hr2 : (r : ℂ) * (r : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, hr, Real.mul_self_sqrt hNpos.le]
  have hsum : v 0 * starRingEnd ℂ (v 0) + v 1 * starRingEnd ℂ (v 1) = (N : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, hN, Complex.ofReal_add]
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = v 0 / r := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = v 1 / r := ⟨_, rfl⟩
  have hab : a * starRingEnd ℂ a + b * starRingEnd ℂ b = 1 := by
    have h1 : a * starRingEnd ℂ a + b * starRingEnd ℂ b =
        (v 0 * starRingEnd ℂ (v 0) + v 1 * starRingEnd ℂ (v 1)) / ((r : ℂ) * (r : ℂ)) := by
      rw [ha, hb]
      simp only [map_div₀, Complex.conj_ofReal]
      field_simp
    rw [h1, hsum, hr2, div_self]
    exact_mod_cast hNpos.ne'
  have ea0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * a + (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * b =
      lam * a := by
    rw [ha, hb]
    linear_combination e0 / (r : ℂ)
  have ea1 : -starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * a +
      starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * b = lam * b := by
    rw [ha, hb]
    linear_combination e1 / (r : ℂ)
  have c0 : starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * starRingEnd ℂ a +
      starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * starRingEnd ℂ b =
      starRingEnd ℂ lam * starRingEnd ℂ a := by
    have h := congrArg (starRingEnd ℂ) ea0
    simpa only [map_add, map_mul] using h
  have c1 : -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * starRingEnd ℂ a +
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * starRingEnd ℂ b = starRingEnd ℂ lam * starRingEnd ℂ b := by
    have h := congrArg (starRingEnd ℂ) ea1
    simpa only [map_add, map_mul, map_neg, Complex.conj_conj] using h
  -- the conjugating element
  have hg : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1;
        -starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1),
        starRingEnd ℂ ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su2_apply_one_zero g, su2_apply_one_one g]
  have hdiag : (diagonal ![lam, star lam] : Matrix (Fin 2) (Fin 2) ℂ) =
      !![lam, 0; 0, starRingEnd ℂ lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hprod : (g : Matrix (Fin 2) (Fin 2) ℂ) * (su2OfColumn a b hab : Matrix (Fin 2) (Fin 2) ℂ) =
      (su2OfColumn a b hab : Matrix (Fin 2) (Fin 2) ℂ) * diagonal ![lam, star lam] := by
    rw [hdiag, su2OfColumn_coe]
    nth_rewrite 1 [hg]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first
        | linear_combination ea0
        | linear_combination ea1
        | linear_combination c0
        | linear_combination (-1 : ℂ) * c1
  have hk : ((su2OfColumn a b hab)⁻¹ * g * su2OfColumn a b hab : SU2).1 = diagonal ![lam, star lam] := by
    show ((su2OfColumn a b hab)⁻¹ : SU2).1 * (g : Matrix (Fin 2) (Fin 2) ℂ) *
      (su2OfColumn a b hab : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [Matrix.mul_assoc, hprod, ← Matrix.mul_assoc]
    have hinv : ((su2OfColumn a b hab)⁻¹ : SU2).1 * (su2OfColumn a b hab : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel (su2OfColumn a b hab))
    rw [hinv, Matrix.one_mul]
  have hz : lam * star lam = 1 := by
    have hU := mem_unitaryGroup_iff.1
      (mem_specialUnitaryGroup_iff.1 ((su2OfColumn a b hab)⁻¹ * g * su2OfColumn a b hab : SU2).2).1
    rw [hk] at hU
    have h00 := congrFun (congrFun hU 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.diagonal_apply] using h00
  refine ⟨su2OfColumn a b hab, lam, hz, ?_⟩
  have hkt : (su2OfColumn a b hab)⁻¹ * g * su2OfColumn a b hab = SU2.torus lam hz := Subtype.ext hk
  rw [← hkt]
  group

/-- **Every element of SU(2) is conjugate to `diag(e^{iθ}, e^{-iθ})`** for some real `θ`. -/
theorem exists_conj_torusExp (g : SU2) : ∃ (h : SU2) (θ : ℝ), g = h * Spin4.torusExp θ * h⁻¹ := by
  obtain ⟨h, z, hz, hg⟩ := exists_conj_torus g
  have hn : Complex.normSq z = 1 := by
    have h1 := hz
    rw [Complex.star_def, Complex.mul_conj] at h1
    exact_mod_cast h1
  have hnorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hn
    rw [← Real.sqrt_sq (norm_nonneg z), h2, Real.sqrt_one]
  have hzeq : z = Complex.exp ((Complex.arg z : ℝ) * Complex.I) := by
    have h3 := Complex.norm_mul_exp_arg_mul_I z
    rw [hnorm, Complex.ofReal_one, one_mul] at h3
    exact h3.symm
  refine ⟨h, Complex.arg z, ?_⟩
  rw [hg]
  congr 2
  apply Subtype.ext
  show diagonal ![z, star z] = diagonal ![Complex.exp ((Complex.arg z : ℝ) * Complex.I),
    star (Complex.exp ((Complex.arg z : ℝ) * Complex.I))]
  rw [← hzeq]

end

end Lightlike.HarmonicAnalysis

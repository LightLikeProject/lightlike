import Lightlike.HarmonicAnalysis.SU2Conjugacy
import Lightlike.HarmonicAnalysis.PeterWeylSU2

/-!
# The Weyl integration formula and the character formula for SU(2)

For the normalised Haar measure `μ` of `SU(2)`:

* `su2Spin_character_eq_U`: the character of the spin-`n/2` representation is the Chebyshev polynomial of the
  second kind in the half-trace, `χ_n(g) = U_n(½ tr g)`; on the diagonal torus,
  `χ_n(diag(e^{iθ}, e^{-iθ})) · sin θ = sin((n+1)θ)` (`su2Spin_character_torusExp_mul_sin`).
* `su2_eq_of_isClassFunction`: a class function is a function of the half-trace (conjugacy classes of SU(2)).
* `weyl_integration_formula_su2`: for a continuous class function `f` on `SU(2)`,
  `∫ f dμ = (1/π) ∫₀^{2π} f(diag(e^{iθ}, e^{-iθ})) sin² θ dθ`.

The proof is not the geometric one of the source: both sides are bounded by the supremum of `f` on the torus,
they agree on the characters `χ_n` (Schur orthogonality on the left, a trigonometric integral on the right),
the characters are the Chebyshev polynomials `U_n` of the half-trace, which span all polynomials, and
polynomials are dense by the Weierstrass theorem.

## References

* C. Teleman, *Representation Theory* (lecture notes, Cambridge, Lent 2005), Lecture 20, Proposition 20.4 and
  Theorem 20.9 (Weyl integration formula), and Lecture 21, Theorem 21.1 (the character formula).
-/

open MeasureTheory Matrix Polynomial

namespace Lightlike.HarmonicAnalysis

noncomputable section

open UnitaryMatrixRep

/-! ### The half-trace -/

/-- The half-trace `½ tr g = Re g₀₀` of `g ∈ SU(2)`. -/
def su2HalfTr (g : SU2) : ℝ := ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re

lemma su2_trace (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ).trace = ((2 * su2HalfTr g : ℝ) : ℂ) := by
  rw [Matrix.trace_fin_two, su2_apply_one_one g, Complex.add_conj]
  rfl

lemma su2HalfTr_conj (h g : SU2) : su2HalfTr (h * g * h⁻¹) = su2HalfTr g := by
  have h1 : ((h * g * h⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ).trace =
      (g : Matrix (Fin 2) (Fin 2) ℂ).trace := by
    show ((h : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) *
      ((h⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)).trace = _
    rw [Matrix.trace_mul_cycle]
    have hinv : ((h⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel h)
    rw [hinv, Matrix.one_mul]
  rw [su2_trace, su2_trace] at h1
  have h2 : (2 * su2HalfTr (h * g * h⁻¹) : ℝ) = 2 * su2HalfTr g := by exact_mod_cast h1
  linarith

lemma su2HalfTr_torusExp (θ : ℝ) : su2HalfTr (Spin4.torusExp θ) = Real.cos θ := by
  show ((diagonal ![Complex.exp (θ * Complex.I), star (Complex.exp (θ * Complex.I))] :
    Matrix (Fin 2) (Fin 2) ℂ) 0 0).re = _
  simp [Complex.exp_ofReal_mul_I_re]

lemma continuous_su2HalfTr : Continuous su2HalfTr :=
  Complex.continuous_re.comp
    ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val))

lemma continuous_torusExp : Continuous Spin4.torusExp := by
  refine continuous_induced_rng.2 ?_
  show Continuous fun θ : ℝ => (diagonal ![Complex.exp (θ * Complex.I),
    star (Complex.exp (θ * Complex.I))] : Matrix (Fin 2) (Fin 2) ℂ)
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  fin_cases i
  · show Continuous fun θ : ℝ => Complex.exp (θ * Complex.I)
    fun_prop
  · show Continuous fun θ : ℝ => star (Complex.exp (θ * Complex.I))
    exact continuous_star.comp (by fun_prop)

/-! ### Conjugacy classes: angles in `[0, π]` -/

lemma torus_eq_torusExp_arg (z : ℂ) (hz : z * star z = 1) :
    SU2.torus z hz = Spin4.torusExp (Complex.arg z) := by
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
  apply Subtype.ext
  show diagonal ![z, star z] = diagonal ![Complex.exp ((Complex.arg z : ℝ) * Complex.I),
    star (Complex.exp ((Complex.arg z : ℝ) * Complex.I))]
  rw [← hzeq]

lemma torus_swap (z : ℂ) (hz : z * star z = 1) (hz' : star z * star (star z) = 1) :
    SU2.torus z hz =
      su2OfColumn 0 1 (by simp) * SU2.torus (star z) hz' * (su2OfColumn 0 1 (by simp))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  show (diagonal ![z, star z] : Matrix (Fin 2) (Fin 2) ℂ) *
      !![(0 : ℂ), -starRingEnd ℂ 1; 1, starRingEnd ℂ 0] =
    !![(0 : ℂ), -starRingEnd ℂ 1; 1, starRingEnd ℂ 0] * diagonal ![star z, star (star z)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

/-- Every element of SU(2) is conjugate to `diag(e^{iθ}, e^{-iθ})` with `θ ∈ [0, π]`. -/
theorem exists_conj_torusExp_Icc (g : SU2) :
    ∃ (h : SU2) (θ : ℝ), 0 ≤ θ ∧ θ ≤ Real.pi ∧ g = h * Spin4.torusExp θ * h⁻¹ := by
  obtain ⟨h, z, hz, hg⟩ := exists_conj_torus g
  by_cases him : 0 ≤ z.im
  · exact ⟨h, Complex.arg z, Complex.arg_nonneg_iff.2 him, Complex.arg_le_pi z, by
      rw [hg, torus_eq_torusExp_arg]⟩
  · have hz' : star z * star (star z) = 1 := by rw [star_star, mul_comm]; exact hz
    have him' : 0 ≤ (star z).im := by
      rw [Complex.star_def, Complex.conj_im]
      linarith [not_le.1 him]
    refine ⟨h * su2OfColumn 0 1 (by simp), Complex.arg (star z), Complex.arg_nonneg_iff.2 him',
      Complex.arg_le_pi _, ?_⟩
    rw [hg, torus_swap z hz hz', torus_eq_torusExp_arg]
    group

lemma su2HalfTr_mem_Icc (g : SU2) : su2HalfTr g ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨h, θ, -, -, rfl⟩ := exists_conj_torusExp_Icc g
  rw [su2HalfTr_conj, su2HalfTr_torusExp]
  exact ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

/-- **A class function on SU(2) is a function of the half-trace.** -/
theorem su2_eq_of_isClassFunction {α : Type*} (f : SU2 → α) (hcl : ∀ h g : SU2, f (h * g * h⁻¹) = f g)
    (g : SU2) : f g = f (Spin4.torusExp (Real.arccos (su2HalfTr g))) := by
  obtain ⟨h, θ, h0, hπ, rfl⟩ := exists_conj_torusExp_Icc g
  rw [hcl, su2HalfTr_conj, su2HalfTr_torusExp, Real.arccos_cos h0 hπ]

/-! ### The character formula -/

lemma UnitaryMatrixRep.continuous_character {G : Type*} [Group G] [TopologicalSpace G] {ι : Type}
    [Fintype ι] [DecidableEq ι] (ρ : UnitaryMatrixRep G ι) : Continuous ρ.character := by
  show Continuous fun g => ∑ i, ρ.mat g i i
  exact continuous_finsetSum _ fun i _ => ρ.continuous_mat_apply i i

lemma UnitaryMatrixRep.character_conj {G : Type*} [Group G] [TopologicalSpace G] {ι : Type}
    [Fintype ι] [DecidableEq ι] (ρ : UnitaryMatrixRep G ι) (h g : G) :
    ρ.character (h * g * h⁻¹) = ρ.character g := by
  show (ρ.mat (h * g * h⁻¹)).trace = (ρ.mat g).trace
  rw [ρ.mat_mul, ρ.mat_mul, Matrix.trace_mul_cycle, ← ρ.mat_mul, inv_mul_cancel, ρ.mat_one,
    Matrix.one_mul]

/-- The character of the spin-`n/2` representation on the torus: the sum of the weights. -/
lemma su2Spin_character_torusExp (n : ℕ) (θ : ℝ) :
    (su2Spin n).character (Spin4.torusExp θ) =
      ∑ k : Fin (n + 1), Complex.exp ((((n : ℝ) - 2 * (k : ℕ)) * θ : ℝ) * Complex.I) := by
  have h : (su2Spin n).mat (Spin4.torusExp θ) = diagonal fun k : Fin (n + 1) =>
      Complex.exp ((((n : ℝ) - 2 * (k : ℕ)) * θ : ℝ) * Complex.I) := SU2.spinMat_torus_exp θ
  show ((su2Spin n).mat (Spin4.torusExp θ)).trace = _
  rw [h, Matrix.trace_diagonal]

/-- **The character formula for SU(2)**: `χ_n(diag(e^{iθ}, e^{-iθ})) · sin θ = sin((n+1)θ)`. -/
theorem su2Spin_character_torusExp_mul_sin (n : ℕ) (θ : ℝ) :
    (su2Spin n).character (Spin4.torusExp θ) * Complex.sin θ =
      Complex.sin ((((n : ℝ) + 1) * θ : ℝ)) := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℂ,
      ∀ j : ℕ, F j = Complex.exp ((((n : ℝ) + 1 - 2 * (j : ℕ)) * θ : ℝ) * Complex.I) :=
    ⟨_, fun _ => rfl⟩
  have hterm : ∀ k : ℕ, Complex.exp ((((n : ℝ) - 2 * (k : ℕ)) * θ : ℝ) * Complex.I) * Complex.sin θ =
      (F (k + 1) - F k) * Complex.I / 2 := by
    intro k
    have h1 : Complex.exp ((((n : ℝ) - 2 * (k : ℕ)) * θ : ℝ) * Complex.I) *
        Complex.exp (-(θ : ℂ) * Complex.I) = F (k + 1) := by
      rw [hF, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h2 : Complex.exp ((((n : ℝ) - 2 * (k : ℕ)) * θ : ℝ) * Complex.I) *
        Complex.exp ((θ : ℂ) * Complex.I) = F k := by
      rw [hF, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← h1, ← h2, Complex.sin]
    ring
  rw [su2Spin_character_torusExp, Finset.sum_mul]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun k => F (k + 1) - F k) (n + 1),
    Finset.sum_range_sub]
  have e1 : F (n + 1) = Complex.exp (-((((n : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [hF]
    congr 1
    push_cast
    ring
  have e2 : F 0 = Complex.exp (((((n : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [hF]
    congr 1
    push_cast
    ring
  rw [e1, e2, Complex.sin]

/-- The set where `sin` does not vanish is dense. -/
lemma dense_sin_ne_zero : Dense {θ : ℝ | Real.sin θ ≠ 0} := by
  have hc : {θ : ℝ | Real.sin θ = 0}.Countable := by
    have h : {θ : ℝ | Real.sin θ = 0} = Set.range fun k : ℤ => (k : ℝ) * Real.pi := by
      ext θ
      simp [Real.sin_eq_zero_iff]
    rw [h]
    exact Set.countable_range _
  exact hc.dense_compl ℝ

/-- On the torus the character of the spin-`n/2` representation is `U_n(cos θ)`. -/
theorem su2Spin_character_torusExp_eq_U (n : ℕ) (θ : ℝ) :
    (su2Spin n).character (Spin4.torusExp θ) = (((Chebyshev.U ℝ n).eval (Real.cos θ) : ℝ) : ℂ) := by
  have hc1 : Continuous fun θ : ℝ => (su2Spin n).character (Spin4.torusExp θ) :=
    (su2Spin n).continuous_character.comp continuous_torusExp
  have hc2 : Continuous fun θ : ℝ => (((Chebyshev.U ℝ n).eval (Real.cos θ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((Polynomial.continuous _).comp Real.continuous_cos)
  have hpt : ∀ θ ∈ {θ : ℝ | Real.sin θ ≠ 0},
      (su2Spin n).character (Spin4.torusExp θ) = (((Chebyshev.U ℝ n).eval (Real.cos θ) : ℝ) : ℂ) := by
    intro θ hθ
    have hs : Complex.sin (θ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sin]
      exact_mod_cast hθ
    apply mul_right_cancel₀ hs
    rw [su2Spin_character_torusExp_mul_sin, ← Complex.ofReal_sin θ, ← Complex.ofReal_mul,
      Chebyshev.U_real_cos, Complex.ofReal_sin]
    simp
  exact congrFun (Continuous.ext_on dense_sin_ne_zero hc1 hc2 hpt) θ

/-- **The character of the spin-`n/2` representation is `U_n` of the half-trace.** -/
theorem su2Spin_character_eq_U (n : ℕ) (g : SU2) :
    (su2Spin n).character g = (((Chebyshev.U ℝ n).eval (su2HalfTr g) : ℝ) : ℂ) := by
  obtain ⟨h, θ, -, -, rfl⟩ := exists_conj_torusExp_Icc g
  rw [character_conj, su2HalfTr_conj, su2HalfTr_torusExp, su2Spin_character_torusExp_eq_U]

/-! ### Polynomials: the Chebyshev polynomials of the second kind span -/

theorem span_chebyshevU_eq_top :
    Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) = ⊤ := by
  have hU : ∀ n : ℕ, Chebyshev.U ℝ (n : ℤ) ∈
      Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) :=
    fun n => Submodule.subset_span ⟨n, rfl⟩
  have hUm : ∀ n : ℕ, Chebyshev.U ℝ ((n : ℤ) - 1) ∈
      Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) := by
    intro n
    cases n with
    | zero => simp [Chebyshev.U_neg_one]
    | succ k =>
      have h : (((k + 1 : ℕ) : ℤ)) - 1 = (k : ℤ) := by push_cast; ring
      rw [h]
      exact hU k
  have hX : ∀ q ∈ Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)),
      (X : ℝ[X]) * q ∈ Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) := by
    intro q hq
    refine Submodule.span_induction (p := fun q _ => (X : ℝ[X]) * q ∈
      Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ))) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨n, rfl⟩
      have h2 : (2 : ℝ) • ((X : ℝ[X]) * Chebyshev.U ℝ (n : ℤ)) =
          Chebyshev.U ℝ ((n : ℤ) + 1) + Chebyshev.U ℝ ((n : ℤ) - 1) := by
        rw [Chebyshev.U_add_one ℝ (n : ℤ), sub_add_cancel, two_smul, two_mul, add_mul]
      have key : (X : ℝ[X]) * Chebyshev.U ℝ (n : ℤ) =
          (2 : ℝ)⁻¹ • (Chebyshev.U ℝ ((n : ℤ) + 1) + Chebyshev.U ℝ ((n : ℤ) - 1)) := by
        rw [← h2, inv_smul_smul₀ two_ne_zero]
      have h1 : Chebyshev.U ℝ ((n : ℤ) + 1) ∈
          Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) := by
        have h : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h]
        exact hU (n + 1)
      show (X : ℝ[X]) * Chebyshev.U ℝ (n : ℤ) ∈ _
      rw [key]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (hUm n))
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hx
  have hpow : ∀ n : ℕ, (X : ℝ[X]) ^ n ∈
      Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) := by
    intro n
    induction n with
    | zero =>
      have h := hU 0
      simpa [Chebyshev.U_zero] using h
    | succ k ih =>
      rw [pow_succ']
      exact hX _ ih
  rw [eq_top_iff]
  rintro p -
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | monomial n a =>
    rw [← Polynomial.smul_X_eq_monomial]
    exact Submodule.smul_mem _ _ (hpow n)

/-! ### The two sides on polynomials -/

lemma integral_cos_nat_mul (m : ℕ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos ((m : ℝ) * θ) = if m = 0 then 2 * Real.pi else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [if_neg hm]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hs : Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
      rw [show (m : ℝ) * (2 * Real.pi) = ((2 * m : ℕ) : ℝ) * Real.pi by push_cast; ring]
      exact Real.sin_nat_mul_pi _
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos]
    simp [hs]

/-- The right side of the Weyl integration formula on `U_n`. -/
theorem integral_U_cos_mul_sin_sq (n : ℕ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, (Chebyshev.U ℝ n).eval (Real.cos θ) * Real.sin θ ^ 2 =
      if n = 0 then Real.pi else 0 := by
  have h1 : ∀ θ : ℝ, (Chebyshev.U ℝ n).eval (Real.cos θ) * Real.sin θ ^ 2 =
      (Real.cos ((n : ℝ) * θ) - Real.cos (((n + 2 : ℕ) : ℝ) * θ)) / 2 := by
    intro θ
    have e1 : ((n : ℝ) * θ + ((n + 2 : ℕ) : ℝ) * θ) / 2 = ((n : ℝ) + 1) * θ := by push_cast; ring
    have e2 : ((n : ℝ) * θ - ((n + 2 : ℕ) : ℝ) * θ) / 2 = -θ := by push_cast; ring
    rw [pow_two, ← mul_assoc, Chebyshev.U_real_cos, Real.cos_sub_cos, e1, e2, Real.sin_neg,
      Int.cast_natCast]
    ring
  simp_rw [h1]
  have hi1 : IntervalIntegrable (fun θ : ℝ => Real.cos ((n : ℝ) * θ)) volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.cos ((n : ℝ) * θ)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ => Real.cos (((n + 2 : ℕ) : ℝ) * θ)) volume 0
      (2 * Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.cos (((n + 2 : ℕ) : ℝ) * θ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hi1 hi2,
    integral_cos_nat_mul, integral_cos_nat_mul]
  by_cases hn : n = 0
  · subst hn
    simp
  · simp [hn]

variable (μ : Measure SU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- The left side of the Weyl integration formula on `U_n`: Schur orthogonality with the trivial
representation. -/
theorem integral_U_halfTr (n : ℕ) :
    ∫ g, (Chebyshev.U ℝ n).eval (su2HalfTr g) ∂μ = if n = 0 then 1 else 0 := by
  have h := su2_character_orthogonality μ n 0
  simp_rw [su2Spin_character_eq_U] at h
  simp only [Nat.cast_zero, Chebyshev.U_zero, Polynomial.eval_one, Complex.ofReal_one, map_one,
    mul_one] at h
  rw [integral_complex_ofReal] at h
  have h2 : ((∫ g, (Chebyshev.U ℝ n).eval (su2HalfTr g) ∂μ : ℝ) : ℂ) =
      (((if n = 0 then 1 else 0 : ℝ)) : ℂ) := by
    rw [h]
    split_ifs <;> simp
  exact_mod_cast h2

/-- **The Weyl integration formula for polynomials in the half-trace.** -/
theorem integral_eval_su2HalfTr (p : ℝ[X]) :
    ∫ g, p.eval (su2HalfTr g) ∂μ =
      (1 / Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, p.eval (Real.cos θ) * Real.sin θ ^ 2 := by
  have hspan : p ∈ Submodule.span ℝ (Set.range fun n : ℕ => Chebyshev.U ℝ (n : ℤ)) := by
    rw [span_chebyshevU_eq_top]
    exact Submodule.mem_top
  have hint : ∀ q : ℝ[X], Integrable (fun g => q.eval (su2HalfTr g)) μ := fun q =>
    ((Polynomial.continuous q).comp continuous_su2HalfTr).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hii : ∀ q : ℝ[X], IntervalIntegrable (fun θ => q.eval (Real.cos θ) * Real.sin θ ^ 2) volume 0
      (2 * Real.pi) := fun q =>
    (((Polynomial.continuous q).comp Real.continuous_cos).mul
      (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  refine Submodule.span_induction (p := fun q _ => ∫ g, q.eval (su2HalfTr g) ∂μ =
    (1 / Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, q.eval (Real.cos θ) * Real.sin θ ^ 2) ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨n, rfl⟩
    show ∫ g, (Chebyshev.U ℝ n).eval (su2HalfTr g) ∂μ = (1 / Real.pi) *
      ∫ θ in (0 : ℝ)..2 * Real.pi, (Chebyshev.U ℝ n).eval (Real.cos θ) * Real.sin θ ^ 2
    rw [integral_U_halfTr, integral_U_cos_mul_sin_sq]
    split_ifs <;> simp [Real.pi_ne_zero]
  · simp
  · intro q r _ _ hq hr
    simp only [Polynomial.eval_add, add_mul]
    rw [integral_add (hint q) (hint r), intervalIntegral.integral_add (hii q) (hii r), hq, hr]
    ring
  · intro c q _ hq
    simp only [Polynomial.eval_smul, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, intervalIntegral.integral_const_mul, hq]
    ring

/-! ### The Weyl integration formula -/

/-- The Weyl integration formula for real continuous functions of the half-trace. -/
theorem integral_comp_su2HalfTr (G : ℝ → ℝ) (hG : Continuous G) :
    ∫ g, G (su2HalfTr g) ∂μ =
      (1 / Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, G (Real.cos θ) * Real.sin θ ^ 2 := by
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 G hG.continuousOn (ε / 3)
    (by positivity)
  have hLp := integral_eval_su2HalfTr μ p
  have hpt : ∀ g : SU2, |p.eval (su2HalfTr g) - G (su2HalfTr g)| ≤ ε / 3 := fun g =>
    (hp _ (su2HalfTr_mem_Icc g)).le
  have hptθ : ∀ θ : ℝ, |p.eval (Real.cos θ) - G (Real.cos θ)| ≤ ε / 3 := fun θ =>
    (hp _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).le
  have hG1 : Integrable (fun g => G (su2HalfTr g)) μ :=
    (hG.comp continuous_su2HalfTr).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp1 : Integrable (fun g => p.eval (su2HalfTr g)) μ :=
    ((Polynomial.continuous p).comp continuous_su2HalfTr).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hL : |∫ g, G (su2HalfTr g) ∂μ - ∫ g, p.eval (su2HalfTr g) ∂μ| ≤ ε / 3 := by
    rw [← integral_sub hG1 hp1]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun g => G (su2HalfTr g) - p.eval (su2HalfTr g)) (C := ε / 3)
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact hpt g)
    simpa using h
  have hG2 : IntervalIntegrable (fun θ => G (Real.cos θ) * Real.sin θ ^ 2) volume 0 (2 * Real.pi) :=
    ((hG.comp Real.continuous_cos).mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hp2 : IntervalIntegrable (fun θ => p.eval (Real.cos θ) * Real.sin θ ^ 2) volume 0
      (2 * Real.pi) :=
    (((Polynomial.continuous p).comp Real.continuous_cos).mul
      (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hR : |(1 / Real.pi) * (∫ θ in (0 : ℝ)..2 * Real.pi, G (Real.cos θ) * Real.sin θ ^ 2) -
      (1 / Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, p.eval (Real.cos θ) * Real.sin θ ^ 2| ≤
      2 * (ε / 3) := by
    rw [← mul_sub, ← intervalIntegral.integral_sub hG2 hp2, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := fun θ => G (Real.cos θ) * Real.sin θ ^ 2 - p.eval (Real.cos θ) * Real.sin θ ^ 2)
      (C := ε / 3) (fun θ _ => by
        rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
        have h1 := hptθ θ
        have h2 : |Real.sin θ ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact Real.sin_sq_le_one θ
        calc |p.eval (Real.cos θ) - G (Real.cos θ)| * |Real.sin θ ^ 2| ≤ ε / 3 * 1 :=
              mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ = ε / 3 := mul_one _)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
    refine h3.trans (le_of_eq ?_)
    field_simp
  have hsplit : ∫ g, G (su2HalfTr g) ∂μ -
      (1 / Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, G (Real.cos θ) * Real.sin θ ^ 2 =
      (∫ g, G (su2HalfTr g) ∂μ - ∫ g, p.eval (su2HalfTr g) ∂μ) -
      ((1 / Real.pi) * (∫ θ in (0 : ℝ)..2 * Real.pi, G (Real.cos θ) * Real.sin θ ^ 2) -
        (1 / Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, p.eval (Real.cos θ) * Real.sin θ ^ 2) := by
    rw [hLp]
    ring
  rw [hsplit]
  calc |_ - _| ≤ |∫ g, G (su2HalfTr g) ∂μ - ∫ g, p.eval (su2HalfTr g) ∂μ| +
        |(1 / Real.pi) * (∫ θ in (0 : ℝ)..2 * Real.pi, G (Real.cos θ) * Real.sin θ ^ 2) -
          (1 / Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, p.eval (Real.cos θ) * Real.sin θ ^ 2| :=
        abs_sub _ _
    _ ≤ ε / 3 + 2 * (ε / 3) := add_le_add hL hR
    _ = ε := by ring

/-- **The Weyl integration formula for SU(2).** For a continuous class function `f` on `SU(2)` and the
normalised Haar measure `μ`,
`∫ f dμ = (1/π) ∫₀^{2π} f(diag(e^{iθ}, e^{-iθ})) sin² θ dθ`. -/
theorem weyl_integration_formula_su2 (f : SU2 → ℂ) (hf : Continuous f)
    (hcl : ∀ h g : SU2, f (h * g * h⁻¹) = f g) :
    ∫ g, f g ∂μ = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ θ in (0 : ℝ)..2 * Real.pi, f (Spin4.torusExp θ) * ((Real.sin θ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℂ, ∀ x, F x = f (Spin4.torusExp (Real.arccos x)) :=
    ⟨_, fun _ => rfl⟩
  have hF : Continuous F := by
    have h : F = fun x => f (Spin4.torusExp (Real.arccos x)) := funext hFdef
    rw [h]
    exact hf.comp (continuous_torusExp.comp Real.continuous_arccos)
  have hfF : ∀ g, f g = F (su2HalfTr g) := fun g => by
    rw [hFdef]
    exact su2_eq_of_isClassFunction f hcl g
  have hfθ : ∀ θ : ℝ, f (Spin4.torusExp θ) = F (Real.cos θ) := fun θ => by
    rw [hfF, su2HalfTr_torusExp]
  have hre := integral_comp_su2HalfTr μ (fun x => (F x).re) (Complex.continuous_re.comp hF)
  have him := integral_comp_su2HalfTr μ (fun x => (F x).im) (Complex.continuous_im.comp hF)
  have hintL : Integrable (fun g => f g) μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintR : IntervalIntegrable
      (fun θ : ℝ => f (Spin4.torusExp θ) * ((Real.sin θ ^ 2 : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    ((hf.comp continuous_torusExp).mul
      (Complex.continuous_ofReal.comp (Real.continuous_sin.pow 2))).intervalIntegrable _ _
  apply Complex.ext
  · have h1 : (∫ g, f g ∂μ).re = ∫ g, (F (su2HalfTr g)).re ∂μ := by
      have h := Complex.reCLM.integral_comp_comm hintL
      rw [← Complex.reCLM_apply, ← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show Complex.reCLM (f g) = (F (su2HalfTr g)).re
      rw [hfF g]
      rfl
    have h2 : (∫ θ in (0 : ℝ)..2 * Real.pi, f (Spin4.torusExp θ) * ((Real.sin θ ^ 2 : ℝ) : ℂ)).re =
        ∫ θ in (0 : ℝ)..2 * Real.pi, (F (Real.cos θ)).re * Real.sin θ ^ 2 := by
      have h := Complex.reCLM.intervalIntegral_comp_comm hintR
      rw [← Complex.reCLM_apply, ← h]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      show Complex.reCLM (f (Spin4.torusExp θ) * ((Real.sin θ ^ 2 : ℝ) : ℂ)) = _
      rw [Complex.reCLM_apply, hfθ θ, Complex.re_mul_ofReal]
    rw [Complex.re_ofReal_mul, h1, h2, hre]
  · have h1 : (∫ g, f g ∂μ).im = ∫ g, (F (su2HalfTr g)).im ∂μ := by
      have h := Complex.imCLM.integral_comp_comm hintL
      rw [← Complex.imCLM_apply, ← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show Complex.imCLM (f g) = (F (su2HalfTr g)).im
      rw [hfF g]
      rfl
    have h2 : (∫ θ in (0 : ℝ)..2 * Real.pi, f (Spin4.torusExp θ) * ((Real.sin θ ^ 2 : ℝ) : ℂ)).im =
        ∫ θ in (0 : ℝ)..2 * Real.pi, (F (Real.cos θ)).im * Real.sin θ ^ 2 := by
      have h := Complex.imCLM.intervalIntegral_comp_comm hintR
      rw [← Complex.imCLM_apply, ← h]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      show Complex.imCLM (f (Spin4.torusExp θ) * ((Real.sin θ ^ 2 : ℝ) : ℂ)) = _
      rw [Complex.imCLM_apply, hfθ θ, Complex.im_mul_ofReal]
    rw [Complex.im_ofReal_mul, h1, h2, him]

end

end Lightlike.HarmonicAnalysis

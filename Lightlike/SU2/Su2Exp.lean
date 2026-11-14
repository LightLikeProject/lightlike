module

public import Lightlike.SU2.LieProduct
public import Lightlike.SU2.LieBridge

/-!
# The exponential map of SU(2)

Stage C, part 1, of group-level completeness (`Completeness.lean`). The Lie algebra `su(2)`:
traceless anti-Hermitian `2 × 2` complex matrices (`IsSu2`).

* `IsSu2.mul_self`: `X² = -det X`, and `det X = sqNorm X ≥ 0` is real.
* `exp_smul_of_pos`: `exp(tX) = cos(tω) + (sin(tω)/ω) X` with `ω = √det X > 0`, by ODE uniqueness
  (`eq_exp_of_hasDerivAt`), not power series.
* `combo_mem`: `α + βX ∈ SU(2)` whenever `α² + β² det X = 1`.
* `Γ X hX : ℝ → SU2`: the one-parameter subgroup `t ↦ exp(tX)` (`Γ_add`, `continuous_Γ`). It lies
  in SU(2) without using `det exp = exp tr`, which is still a Mathlib TODO.
* `exists_exp_eq`: **every `g ∈ SU(2)` is `exp X` for some `X ∈ su(2)`**.

Matrices carry the operator norm (local instances). Its topology is definitionally the product
one, so `NormedSpace.exp` is the usual matrix exponential.

**References.** B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (Springer, 2015), ch. 2 (the matrix exponential). For SU(2) surjectivity is elementary: every element is unitarily diagonalizable with eigenvalues e^{±iθ}.
-/

@[expose] public section

open Matrix Real Filter Topology

namespace Lightlike.SU2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `su(2)`: traceless anti-Hermitian `2 × 2` matrices. -/
def IsSu2 (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Xᴴ = -X ∧ X.trace = 0

/-- `det X` as a real number (it is `|X₀₀|² + |X₀₁|² ≥ 0` on `su(2)`). -/
noncomputable def sqNorm (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := X.det.re

variable {X : Matrix (Fin 2) (Fin 2) ℂ}

lemma IsSu2.entry (hX : IsSu2 X) (i j : Fin 2) : star (X j i) = -X i j := by
  have := congrFun (congrFun hX.1 i) j
  simpa [conjTranspose_apply] using this

lemma IsSu2.trace_eq (hX : IsSu2 X) : X 1 1 = -X 0 0 := by
  have := hX.2
  simp [trace, Fin.sum_univ_two] at this
  linear_combination this

lemma IsSu2.entry10 (hX : IsSu2 X) : X 1 0 = -star (X 0 1) := by
  rw [hX.entry 1 0, neg_neg]

lemma IsSu2.re00 (hX : IsSu2 X) : (X 0 0).re = 0 := by
  have := congrArg Complex.re (hX.entry 0 0)
  simp at this
  linarith

lemma IsSu2.det_eq (hX : IsSu2 X) : X.det = (sqNorm X : ℂ) ∧ sqNorm X =
    Complex.normSq (X 0 0) + Complex.normSq (X 0 1) := by
  have hd : X.det = ((Complex.normSq (X 0 0) + Complex.normSq (X 0 1) : ℝ) : ℂ) := by
    rw [det_fin_two, hX.trace_eq, hX.entry10]
    apply Complex.ext <;>
      simp [Complex.normSq_apply, hX.re00, Complex.mul_re, Complex.mul_im]; ring
  refine ⟨?_, ?_⟩
  · rw [sqNorm, hd, Complex.ofReal_re]
  · rw [sqNorm, hd, Complex.ofReal_re]

lemma IsSu2.sqNorm_nonneg (hX : IsSu2 X) : 0 ≤ sqNorm X := by
  rw [hX.det_eq.2]
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

lemma IsSu2.eq_zero_of_sqNorm (hX : IsSu2 X) (h : sqNorm X = 0) : X = 0 := by
  rw [hX.det_eq.2] at h
  have p0 := Complex.normSq_nonneg (X 0 0)
  have p1 := Complex.normSq_nonneg (X 0 1)
  have h0 : X 0 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have h1 : X 0 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  ext i j
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h1
  · simp only [Fin.mk_one, Fin.zero_eta, Matrix.zero_apply]
    rw [hX.entry10, h1, star_zero, neg_zero]
  · simp only [Fin.mk_one, Matrix.zero_apply]
    rw [hX.trace_eq, h0, neg_zero]

/-- **Cayley–Hamilton on su(2)**: `X² = -det X`. -/
lemma IsSu2.mul_self (hX : IsSu2 X) : X * X = (-sqNorm X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h11 := hX.trace_eq
  have hd := hX.det_eq.1
  rw [det_fin_two, h11] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, h11, Complex.real_smul] <;>
    first
      | linear_combination -hd
      | ring

/-- The determinant of `α + βX` on `su(2)`. -/
lemma IsSu2.det_combo (hX : IsSu2 X) (α β : ℝ) :
    (α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • X).det = ((α ^ 2 + β ^ 2 * sqNorm X : ℝ) : ℂ) := by
  have h11 := hX.trace_eq
  have hd := hX.det_eq.1
  rw [det_fin_two] at hd ⊢
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, one_apply_eq,
    one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    mul_one, mul_zero, zero_add, h11] at hd ⊢
  push_cast
  linear_combination (β : ℂ) ^ 2 * hd

/-- **`α + βX ∈ SU(2)`** when `α² + β² det X = 1`. -/
lemma combo_mem (hX : IsSu2 X) {α β : ℝ} (h : α ^ 2 + β ^ 2 * sqNorm X = 1) :
    α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • X ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, hX.det_combo, h]
  refine ⟨?_, by simp⟩
  have hstar : star (α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • X) = α • 1 - β • X := by
    rw [star_eq_conjTranspose, conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
      conjTranspose_one, hX.1, star_trivial, star_trivial, smul_neg, sub_eq_add_neg]
  have key : (α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • X) * (α • 1 - β • X) =
      (α ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (β ^ 2) • (X * X) := by
    simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul]
    rw [mul_comm β α]
    module
  rw [hstar, key, hX.mul_self, smul_smul, ← sub_smul,
    show α ^ 2 - β ^ 2 * -sqNorm X = 1 by linarith, one_smul]

/-- **The exponential on `su(2)`**: `exp(tX) = cos(tω) + (sin(tω)/ω) X`, `ω = √det X > 0`. -/
theorem exp_smul_of_pos (hX : IsSu2 X) (hω : 0 < sqNorm X) (t : ℝ) :
    NormedSpace.exp (t • X) = cos (t * √(sqNorm X)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (sin (t * √(sqNorm X)) / √(sqNorm X)) • X := by
  have hω0 : 0 < √(sqNorm X) := Real.sqrt_pos.mpr hω
  have hω2 : √(sqNorm X) ^ 2 = sqNorm X := Real.sq_sqrt hω.le
  generalize √(sqNorm X) = ω at hω0 hω2 ⊢
  have hval : ∀ t : ℝ, (cos (t * ω) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (sin (t * ω) / ω) • X) * X =
      (-sin (t * ω) * ω) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + cos (t * ω) • X := by
    intro t
    rw [add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hX.mul_self, smul_smul,
      ← hω2, show sin (t * ω) / ω * -ω ^ 2 = -sin (t * ω) * ω by field_simp]
    abel
  have hcd : ∀ t : ℝ, HasDerivAt
      (fun t => cos (t * ω) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (sin (t * ω) / ω) • X)
      ((cos (t * ω) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (sin (t * ω) / ω) • X) * X) t := by
    intro t
    have h1 : HasDerivAt (fun t => cos (t * ω)) (-sin (t * ω) * ω) t := by
      have := ((hasDerivAt_id t).mul_const ω).cos
      simpa only [id, one_mul] using this
    have h2 : HasDerivAt (fun t => sin (t * ω) / ω) (cos (t * ω)) t := by
      have := (((hasDerivAt_id t).mul_const ω).sin).div_const ω
      simp only [id, one_mul] at this
      convert this using 1
      field_simp
    rw [hval]
    exact (h1.smul_const (1 : Matrix (Fin 2) (Fin 2) ℂ)).add (h2.smul_const X)
  exact (eq_exp_of_hasDerivAt _ X (by simp) hcd t).symm

/-- `exp(tX) ∈ SU(2)` for `X ∈ su(2)`. -/
theorem exp_smul_mem (hX : IsSu2 X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rcases hX.sqNorm_nonneg.lt_or_eq with hω | hω
  · rw [exp_smul_of_pos hX hω]
    refine combo_mem hX ?_
    have hs : 0 < √(sqNorm X) := Real.sqrt_pos.mpr hω
    have := Real.sq_sqrt hω.le
    field_simp
    rw [this]
    nlinarith [sin_sq_add_cos_sq (t * √(sqNorm X))]
  · rw [hX.eq_zero_of_sqNorm hω.symm, smul_zero, NormedSpace.exp_zero]
    exact one_mem _

/-- The one-parameter subgroup `t ↦ exp(tX)` of SU(2). -/
noncomputable def Γ (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : IsSu2 X) (t : ℝ) : SU2 :=
  ⟨NormedSpace.exp (t • X), exp_smul_mem hX t⟩

lemma Γ_coe (hX : IsSu2 X) (t : ℝ) :
    (Γ X hX t : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (t • X) := rfl

/-- `Γ X` is a one-parameter subgroup: `exp((s + t) X) = exp(sX) exp(tX)`. -/
lemma Γ_add (hX : IsSu2 X) (s t : ℝ) : Γ X hX (s + t) = Γ X hX s * Γ X hX t := by
  apply Subtype.ext
  simp only [Γ_coe, Submonoid.coe_mul]
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl X).smul_left s |>.smul_right t)

lemma Γ_zero (hX : IsSu2 X) : Γ X hX 0 = 1 := by
  apply Subtype.ext; simp [Γ_coe]

/-- The one-parameter subgroup `t ↦ exp(tX)` is continuous. -/
lemma continuous_Γ (hX : IsSu2 X) : Continuous (Γ X hX) :=
  Continuous.subtype_mk (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)) _

/-! ## Every element of SU(2) is an exponential -/

/-- The entries of an SU(2) matrix: `g = [[a, -b̄], [b, ā]]` with `|a|² + |b|² = 1`. -/
lemma su2_entries (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∧
    (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∧
    Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 1 := by
  obtain ⟨hu, hdet⟩ := mem_specialUnitaryGroup_iff.mp g.2
  set G := (g : Matrix (Fin 2) (Fin 2) ℂ)
  have hinv : star G = G.adjugate := by
    have h1 : star G * G = 1 := (mem_unitaryGroup_iff').mp hu
    have h2 : G.adjugate * G = 1 := by rw [adjugate_mul, hdet, one_smul]
    calc star G = star G * (G * G.adjugate) := by rw [mul_adjugate, hdet, one_smul, mul_one]
      _ = (star G * G) * G.adjugate := by rw [mul_assoc]
      _ = G.adjugate := by rw [h1, one_mul]
  rw [adjugate_fin_two] at hinv
  have e00 := congrFun (congrFun hinv 0) 0
  have e01 := congrFun (congrFun hinv 0) 1
  simp only [star_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one] at e00 e01
  have h11 : G 1 1 = star (G 0 0) := e00.symm
  have h01 : G 0 1 = -star (G 1 0) := by rw [e01, neg_neg]
  refine ⟨h11, h01, ?_⟩
  have hd := hdet
  rw [det_fin_two, h11, h01] at hd
  have := congrArg Complex.re hd
  simp [Complex.normSq_apply, Complex.mul_re] at this ⊢
  linarith

/-- **Every `g ∈ SU(2)` is `exp X` for some `X ∈ su(2)`.** -/
theorem exists_exp_eq (g : SU2) :
    ∃ X, IsSu2 X ∧ NormedSpace.exp X = (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨h11, h01, hn⟩ := su2_entries g
  set G := (g : Matrix (Fin 2) (Fin 2) ℂ)
  set a := G 0 0
  set b := G 1 0
  set p := a.re
  have hna : Complex.normSq a = p ^ 2 + a.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hp2 : p ^ 2 ≤ 1 := by nlinarith [Complex.normSq_nonneg b, sq_nonneg a.im]
  have hp1 : -1 ≤ p := by nlinarith
  have hp1' : p ≤ 1 := by nlinarith
  -- `N = G - p` is in su(2), with `det N = 1 - p²`
  set N := G - p • (1 : Matrix (Fin 2) (Fin 2) ℂ) with hNdef
  have hN : IsSu2 N := by
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [N, conjTranspose_apply, h11, h01, Complex.real_smul, Complex.ext_iff, p, a, b]
    · simp [N, trace, Fin.sum_univ_two, h11, Complex.real_smul, Complex.ext_iff, p, a]
      ring
  have hNsq : sqNorm N = 1 - p ^ 2 := by
    rw [hN.det_eq.2]
    have e0 : N 0 0 = a - p := by simp [N, a, Complex.real_smul]
    have e1 : N 0 1 = -star b := by simp [N, h01, b]
    rw [e0, e1, Complex.normSq_neg, Complex.star_def, Complex.normSq_conj]
    have : Complex.normSq (a - p) = a.im ^ 2 := by
      rw [Complex.normSq_apply]; simp [p]; ring
    rw [this]
    linarith
  have hG : G = p • (1 : Matrix (Fin 2) (Fin 2) ℂ) + N := by rw [hNdef]; abel
  by_cases hs : p ^ 2 < 1
  · -- generic case: `X = (θ / sin θ) • N`, `θ = arccos p ∈ (0, π)`
    set θ := Real.arccos p
    have hcos : Real.cos θ = p := Real.cos_arccos hp1 hp1'
    have hsin : Real.sin θ = √(1 - p ^ 2) := Real.sin_arccos p
    have hsin0 : 0 < Real.sin θ := by rw [hsin]; exact Real.sqrt_pos.mpr (by linarith)
    have hθ0 : 0 < θ := Real.arccos_pos.mpr (by nlinarith)
    have hsin2 : Real.sin θ ^ 2 = 1 - p ^ 2 := by rw [hsin, Real.sq_sqrt (by linarith)]
    set X := (θ / Real.sin θ) • N with hXdef
    have hX : IsSu2 X := by
      refine ⟨?_, ?_⟩
      · rw [hXdef, conjTranspose_smul, star_trivial, hN.1, smul_neg]
      · rw [hXdef, trace_smul, hN.2, smul_zero]
    have hXsq : sqNorm X = θ ^ 2 := by
      have : X.det = ((θ / Real.sin θ) ^ 2 * sqNorm N : ℝ) := by
        rw [hXdef, show (θ / Real.sin θ) • N = ((θ / Real.sin θ : ℝ) : ℂ) • N from
          (Complex.coe_smul _ _).symm, det_smul, hN.det_eq.1]
        simp
      rw [sqNorm, this, Complex.ofReal_re, hNsq, ← hsin2]
      field_simp
    refine ⟨X, hX, ?_⟩
    have hpos : 0 < sqNorm X := by rw [hXsq]; positivity
    have := exp_smul_of_pos hX hpos 1
    rw [one_smul, one_mul, hXsq, Real.sqrt_sq hθ0.le, hcos] at this
    rw [this, hG, hXdef, smul_smul, div_mul_div_comm, mul_comm θ, div_self (by positivity), one_smul]
  · -- `p = ±1`, so `g = ±1`
    have hp : p ^ 2 = 1 := le_antisymm hp2 (not_lt.mp hs)
    have hN0 : N = 0 := hN.eq_zero_of_sqNorm (by rw [hNsq, hp]; ring)
    rw [hN0, add_zero] at hG
    obtain h | h : p = 1 ∨ p = -1 := by
      have : (p - 1) * (p + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · refine ⟨0, ⟨by simp, by simp⟩, ?_⟩
      rw [NormedSpace.exp_zero, hG, h, one_smul]
    · set Zm : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I] with hZm
      have hZ : IsSu2 Zm := by
        refine ⟨?_, by simp [Zm, trace, Fin.sum_univ_two]⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Zm, conjTranspose_apply]
      have hZsq : sqNorm Zm = 1 := by simp [sqNorm, Zm, det_fin_two]
      refine ⟨π • Zm, ⟨by rw [conjTranspose_smul, star_trivial, hZ.1, smul_neg],
        by rw [trace_smul, hZ.2, smul_zero]⟩, ?_⟩
      have := exp_smul_of_pos hZ (by rw [hZsq]; norm_num) π
      rw [this, hZsq, Real.sqrt_one, mul_one, Real.cos_pi, Real.sin_pi, zero_div, zero_smul,
        add_zero, hG, h]

end Lightlike.SU2

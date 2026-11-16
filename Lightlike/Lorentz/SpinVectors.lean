module

public import Lightlike.Lorentz.Homogeneous
public import Lightlike.Lorentz.Schur

/-!
# The SU(2)-finite vectors of the principal series

For `p, q ∈ ℕ` with `p - q = n = 2k` and `x ∈ ℂ^{p+q+1}` we build an explicit function
`hvec p q ρ x` on `ℂ²`, homogeneous of degree `(-1+iρ+k, -1+iρ-k)`, such that

  `hvec p q ρ x (uᵀ ζ) = hvec p q ρ (spinMat (p+q) u x) ζ`   for `u ∈ SU(2)`

(`hvec_transpose`): `x ↦ hvec p q ρ x` intertwines the spin-`j` representation of
`Lightlike/SU2/SpinRep.lean`, `j = (p+q)/2`, with the principal series. Its chart lies in `L²(ℂ)`,
so `tlin p q ρ : ℂ^{2j+1} →ₗ L²(ℂ)` is an intertwiner into the principal series restricted to
`SU(2)` (`principalSeries_tlin`), and it is nonzero (`tlin_ne_zero`).

## Implementation notes

`Lightlike/SU2/SpinRep.lean` realises spin `j` as the symmetric part of `(ℂ²)^{⊗ 2j}`. Contract the
`2j` tensor factors with `p` copies of `ζ` and `q` copies of `εζ̄ = (ζ̄₁, -ζ̄₀)`:

  `Λ(v)(ζ) = Σ_t v_t ∏_i η_i(ζ)_{t_i}`,   `η_i = ζ` for `i < p`, `η_i = εζ̄` for `i ≥ p`.

For `u ∈ SU(2)` both `ζ` and `εζ̄` transform by `uᵀ` (`epsConj_transpose`, since `ū = ε u ε⁻¹`),
so `Λ(v)(uᵀ ζ) = Λ(u^{⊗2j} v)(ζ)` (`lam_transpose`). `Λ(v)` is a polynomial of bidegree `(p, q)` in
`(ζ, ζ̄)`, and `hvec = N^{iρ-1} N^{-j} Λ(emb x)` with `N = |ζ₀|² + |ζ₁|²` has the right
homogeneity (`isHomog_hvec`). In the chart `ζ = (z, 1)` it is a combination of the functions
`(1+|z|²)^{iρ-1-j} z^a z̄^b`, `a ≤ p`, `b ≤ q` (`chart_hvec_mem_levelSpace`).

References: I. M. Gelfand, R. A. Minlos, Z. Ya. Shapiro, *Representations of the Rotation and
Lorentz Groups and their Applications* (Pergamon, 1963); W. Rühl, *The Lorentz Group and Harmonic
Analysis* (Benjamin, 1970); A. W. Knapp, *Representation Theory of Semisimple Groups* (Princeton,
1986), Chapter II.
-/

@[expose] public section

open Matrix Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Lightlike.Lorentz

open Lightlike.SU2

/-! ## SU(2) matrices -/

lemma su2_star_eq_adjugate (u : SU2) :
    star (u : Matrix (Fin 2) (Fin 2) ℂ) = adjugate (u : Matrix (Fin 2) (Fin 2) ℂ) := by
  set U : Matrix (Fin 2) (Fin 2) ℂ := u.1
  have h1 : star U * U = 1 := mem_unitaryGroup_iff'.mp (specialUnitaryGroup_le_unitaryGroup u.2)
  have hdet : det U = 1 := (mem_specialUnitaryGroup_iff.mp u.2).2
  calc star U = star U * (U * adjugate U) := by rw [mul_adjugate, hdet, one_smul, Matrix.mul_one]
    _ = adjugate U := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- An `SU(2)` matrix is `[[a, b], [-b̄, ā]]`. -/
lemma su2_11 (u : SU2) :
    (u : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = conj ((u : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  have := congrFun (congrFun (su2_star_eq_adjugate u) 0) 0
  simp [adjugate_fin_two] at this
  exact this.symm

lemma su2_10 (u : SU2) :
    (u : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -conj ((u : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  have := congrFun (congrFun (su2_star_eq_adjugate u) 0) 1
  simp [adjugate_fin_two] at this
  have h := congrArg conj this
  simpa using h

lemma su2_normSq (u : SU2) :
    Complex.normSq ((u : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
      Complex.normSq ((u : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 1 := by
  have hdet : det (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 := (mem_specialUnitaryGroup_iff.mp u.2).2
  rw [det_fin_two, su2_11, su2_10] at hdet
  have := congrArg Complex.re hdet
  simp [Complex.mul_re] at this
  simp only [Complex.normSq_apply]
  linarith

/-! ## The linear forms `ζ` and `εζ̄` -/

/-- `εζ̄ = (ζ̄₁, -ζ̄₀)`: for `u ∈ SU(2)` it transforms like `ζ`. -/
def epsConj (ζ : C2) : C2 := ![conj (ζ 1), -conj (ζ 0)]

lemma epsConj_transpose (u : SU2) (ζ : C2) :
    epsConj ((u : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ) =
      (u : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ epsConj ζ := by
  have h11 := su2_11 u
  have h10 := su2_10 u
  ext i; fin_cases i <;>
    simp [epsConj, mulVec, dotProduct, Fin.sum_univ_two, h11, h10]
  ring

lemma epsConj_smul (w : ℂ) (ζ : C2) : epsConj (w • ζ) = conj w • epsConj ζ := by
  ext i; fin_cases i <;> simp [epsConj]

/-- The `i`-th linear form: `ζ` for `i < p`, `εζ̄` for `i ≥ p`. -/
def lform (p q : ℕ) (i : Fin (p + q)) (ζ : C2) : C2 :=
  Fin.addCases (fun _ => ζ) (fun _ => epsConj ζ) i

/-- **The contraction** `Λ(v)(ζ) = Σ_t v_t ∏_i η_i(ζ)_{t_i}` of a tensor `v ∈ (ℂ²)^{⊗(p+q)}`. -/
def lam (p q : ℕ) (v : Str (p + q) → ℂ) (ζ : C2) : ℂ :=
  ∑ t : Str (p + q), v t * ∏ i, lform p q i ζ (t i)

lemma lform_transpose (p q : ℕ) (u : SU2) (i : Fin (p + q)) (ζ : C2) :
    lform p q i ((u : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ) =
      (u : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ lform p q i ζ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [lform]
  · simp only [lform, Fin.addCases_right]; exact epsConj_transpose u ζ

/-- **Equivariance of the contraction**: `Λ(v)(uᵀ ζ) = Λ(u^{⊗(p+q)} v)(ζ)`. -/
theorem lam_transpose (p q : ℕ) (u : SU2) (v : Str (p + q) → ℂ) (ζ : C2) :
    lam p q v ((u : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ) =
      lam p q (kron (p + q) (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) ζ := by
  simp only [lam, lform_transpose, mulVec, dotProduct, transpose_apply, kron_apply]
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]; ring

/-- The product of the scalars picked up by the `p + q` forms under `ζ ↦ w ζ`. -/
lemma prod_addCases_const (p q : ℕ) (w : ℂ) :
    ∏ i : Fin (p + q), (Fin.addCases (fun _ => w) (fun _ => conj w) i : ℂ) =
      w ^ p * conj w ^ q := by
  rw [Fin.prod_univ_add]; simp

/-- **Homogeneity of the contraction**: `Λ(v)(w ζ) = w^p w̄^q Λ(v)(ζ)`. -/
theorem lam_smul (p q : ℕ) (v : Str (p + q) → ℂ) (w : ℂ) (ζ : C2) :
    lam p q v (w • ζ) = w ^ p * conj w ^ q * lam p q v ζ := by
  have he : ∀ i : Fin (p + q), lform p q i (w • ζ) =
      (Fin.addCases (fun _ => w) (fun _ => conj w) i : ℂ) • lform p q i ζ := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [lform]
    · simp [lform, epsConj_smul]
  simp only [lam, he, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, prod_addCases_const,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

lemma lam_add (p q : ℕ) (v v' : Str (p + q) → ℂ) (ζ : C2) :
    lam p q (v + v') ζ = lam p q v ζ + lam p q v' ζ := by
  simp only [lam, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma lam_smul_left (p q : ℕ) (c : ℂ) (v : Str (p + q) → ℂ) (ζ : C2) :
    lam p q (c • v) ζ = c * lam p q v ζ := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- `N(ζ) = |ζ₀|² + |ζ₁|²`. -/
noncomputable def nsq (ζ : C2) : ℝ := ‖ζ 0‖ ^ 2 + ‖ζ 1‖ ^ 2

lemma nsq_nonneg (ζ : C2) : 0 ≤ nsq ζ := by unfold nsq; positivity

lemma nsq_smul (w : ℂ) (ζ : C2) : nsq (w • ζ) = ‖w‖ ^ 2 * nsq ζ := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul]; ring

lemma nsq_transpose (u : SU2) (ζ : C2) : nsq ((u : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ) = nsq ζ := by
  have h11 := su2_11 u
  have h10 := su2_10 u
  have hn := su2_normSq u
  simp only [nsq, mulVec, dotProduct, Fin.sum_univ_two, transpose_apply, h11, h10]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hn ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.conj_re, Complex.conj_im] at hn ⊢
  linear_combination ((ζ 0).re ^ 2 + (ζ 0).im ^ 2 + (ζ 1).re ^ 2 + (ζ 1).im ^ 2) * hn

lemma nsq_chart (z : ℂ) : nsq ![z, 1] = 1 + ‖z‖ ^ 2 := by simp [nsq]; ring

lemma norm_le_sqrt_nsq (ζ : C2) (c : Fin 2) : ‖ζ c‖ ≤ Real.sqrt (nsq ζ) := by
  apply Real.le_sqrt_of_sq_le
  fin_cases c <;> simp [nsq]

lemma norm_lform_le (p q : ℕ) (i : Fin (p + q)) (ζ : C2) (c : Fin 2) :
    ‖lform p q i ζ c‖ ≤ Real.sqrt (nsq ζ) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [lform] using norm_le_sqrt_nsq ζ c
  · have : nsq (epsConj ζ) = nsq ζ := by simp [nsq, epsConj]; ring
    simpa [lform, this] using norm_le_sqrt_nsq (epsConj ζ) c

/-- **Bound** `|Λ(v)(ζ)| ≤ (Σ_t |v_t|) N(ζ)^{(p+q)/2}`. -/
lemma norm_lam_le (p q : ℕ) (v : Str (p + q) → ℂ) (ζ : C2) :
    ‖lam p q v ζ‖ ≤ (∑ t, ‖v t‖) * Real.sqrt (nsq ζ) ^ (p + q) := by
  unfold lam
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [norm_mul, norm_prod]
  gcongr
  calc ∏ i, ‖lform p q i ζ (t i)‖ ≤ ∏ _i : Fin (p + q), Real.sqrt (nsq ζ) := by
        gcongr with i; exact norm_lform_le p q i ζ (t i)
    _ = Real.sqrt (nsq ζ) ^ (p + q) := by simp

/-! ## The homogeneous vectors -/

lemma ofReal_sq_cpow {r : ℝ} (hr : 0 < r) (c : ℂ) :
    (((r ^ 2 : ℝ)) : ℂ) ^ c = ((r : ℝ) : ℂ) ^ (2 * c) := by
  have h1 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hr 2).ne'
  have h2 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2,
    ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log hr.le, Real.log_pow]
  push_cast; ring_nf

/-- `|w|^{-(p+q)} w^p w̄^q = (w / |w|)^{p - q}`. -/
lemma phase_pow {w : ℂ} (hw : w ≠ 0) (p q : ℕ) :
    (((‖w‖⁻¹ ^ (p + q) : ℝ)) : ℂ) * w ^ p * conj w ^ q = (w / ((‖w‖ : ℝ) : ℂ)) ^ ((p : ℤ) - q) := by
  set r : ℂ := ((‖w‖ : ℝ) : ℂ)
  have hr : r ≠ 0 := by simp [r, hw]
  set u : ℂ := w / r
  have hu0 : u ≠ 0 := div_ne_zero hw hr
  have hwu : w = r * u := by simp [u]; field_simp
  have hconj : conj u = u⁻¹ := by
    have h1 : ‖u‖ = 1 := norm_phase hw
    have : conj u * u = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
    exact eq_inv_of_mul_eq_one_left this
  have hcw : conj w = r * u⁻¹ := by
    rw [hwu, map_mul, hconj]; simp [r]
  have e1 : (((‖w‖⁻¹ ^ (p + q) : ℝ)) : ℂ) = r⁻¹ ^ (p + q) := by simp [r]
  rw [e1, show w ^ p = (r * u) ^ p by rw [← hwu], hcw, zpow_sub₀ hu0, zpow_natCast, zpow_natCast]
  rw [div_eq_mul_inv, ← inv_pow]
  calc r⁻¹ ^ (p + q) * (r * u) ^ p * (r * u⁻¹) ^ q = (r * r⁻¹) ^ (p + q) * (u ^ p * u⁻¹ ^ q) := by
        ring
    _ = u ^ p * u⁻¹ ^ q := by rw [mul_inv_cancel₀ hr, one_pow, one_mul]

/-- **The SU(2)-finite vector** `hvec p q ρ x = N^{iρ-1} N^{-(p+q)/2} Λ(emb x)` on `ℂ²`. -/
noncomputable def hvec (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) (ζ : C2) : ℂ :=
  ((nsq ζ : ℝ) : ℂ) ^ (I * ρ - 1) * (((Real.sqrt (nsq ζ))⁻¹ ^ (p + q) : ℝ) : ℂ) *
    lam p q (emb (p + q) *ᵥ x) ζ

/-- **`hvec` is homogeneous of degree `(-1+iρ+k, -1+iρ-k)`** when `p - q = 2k`. -/
theorem isHomog_hvec {n : ℤ} {p q : ℕ} (hpq : (p : ℤ) - q = n) (ρ : ℝ)
    (x : Fin (p + q + 1) → ℂ) : IsHomog n ρ (hvec p q ρ x) := by
  intro w ζ hw _
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hmult : mult n ρ w = ((‖w‖ : ℝ) : ℂ) ^ (2 * (I * ρ - 1)) *
      ((((‖w‖⁻¹ ^ (p + q) : ℝ)) : ℂ) * w ^ p * conj w ^ q) := by
    rw [phase_pow hw, hpq, mult]; ring_nf
  simp only [hvec, nsq_smul, lam_smul]
  rw [hmult, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (nsq_nonneg ζ),
    ofReal_sq_cpow hwpos, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), mul_inv,
    mul_pow]
  push_cast
  ring

/-- **`hvec` intertwines spin `(p+q)/2` with the principal series**:
`hvec x (uᵀ ζ) = hvec (spinMat u x) ζ` for `u ∈ SU(2)`. -/
theorem hvec_transpose (p q : ℕ) (ρ : ℝ) (u : SU2) (x : Fin (p + q + 1) → ℂ) (ζ : C2) :
    hvec p q ρ x ((u : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ) =
      hvec p q ρ (spinMat (p + q) (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) ζ := by
  simp only [hvec, nsq_transpose, lam_transpose, mulVec_mulVec, kron_mul_emb]

/-! ## The chart and L² -/

/-- The weight `W(z) = (1+|z|²)^{iρ-1} (1+|z|²)^{-(p+q)/2}` of the level `(p, q)`. -/
noncomputable def wgt (p q : ℕ) (ρ : ℝ) (z : ℂ) : ℂ :=
  (((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) ^ (I * ρ - 1) * (((Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p + q) : ℝ) : ℂ)

lemma chart_hvec (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) (z : ℂ) :
    chart (hvec p q ρ x) z = wgt p q ρ z * lam p q (emb (p + q) *ᵥ x) ![z, 1] := by
  simp only [chart, hvec, nsq_chart, wgt]

lemma one_add_pos (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity

lemma one_le_sqrt (z : ℂ) : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2) :=
  Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖z‖])

lemma norm_wgt (p q : ℕ) (ρ : ℝ) (z : ℂ) :
    ‖wgt p q ρ z‖ = (1 + ‖z‖ ^ 2)⁻¹ * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p + q) := by
  have h := one_add_pos z
  rw [wgt, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  congr 1
  simp [Real.rpow_neg_one]

lemma continuous_wgt (p q : ℕ) (ρ : ℝ) : Continuous (wgt p q ρ) := by
  have h1 : Continuous fun z : ℂ => ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by fun_prop
  refine (h1.cpow continuous_const fun z => ?_).mul ?_
  · exact Complex.ofReal_mem_slitPlane.mpr (one_add_pos z)
  · refine Complex.continuous_ofReal.comp ((Continuous.inv₀ (by fun_prop) fun z => ?_).pow _)
    exact (Real.sqrt_pos.mpr (one_add_pos z)).ne'

lemma continuous_lform (p q : ℕ) (i : Fin (p + q)) (c : Fin 2) :
    Continuous fun ζ : C2 => lform p q i ζ c := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [lform] using continuous_apply c
  · simp only [lform, Fin.addCases_right]
    fin_cases c <;> simp [epsConj] <;> fun_prop

lemma continuous_lam (p q : ℕ) (v : Str (p + q) → ℂ) : Continuous (lam p q v) := by
  unfold lam
  exact continuous_finsetSum _ fun t _ =>
    continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_lform p q i (t i))

lemma continuous_chartVec : Continuous fun z : ℂ => (![z, 1] : C2) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

/-- A continuous function bounded by `C (1+|z|²)⁻¹` lies in `L²(ℂ)`. -/
lemma memLp_of_bound {f : ℂ → ℂ} (hf : Continuous f) (C : ℝ)
    (h : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) : MemLp f 2 volume := by
  have hg : MemLp (fun z : ℂ => C * (1 + ‖z‖ ^ 2)⁻¹) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
    have hi := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)
    refine (hi.const_mul (C ^ 2)).congr (Eventually.of_forall fun z => ?_)
    have hpos := one_add_pos z
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    rw [show (-4 / 2 : ℝ) = -2 by norm_num, Real.rpow_neg hpos.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine hg.of_le hf.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  refine (h z).trans (le_trans (le_abs_self _) ?_)
  rw [Real.norm_eq_abs]

/-- The chart of `hvec`, the function on `ℂ` that represents it in `L²(ℂ)`. -/
noncomputable def tfun (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) : ℂ → ℂ :=
  chart (hvec p q ρ x)

lemma continuous_tfun (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) :
    Continuous (tfun p q ρ x) := by
  have : tfun p q ρ x = fun z => wgt p q ρ z * lam p q (emb (p + q) *ᵥ x) ![z, 1] :=
    funext (chart_hvec p q ρ x)
  rw [this]
  exact (continuous_wgt p q ρ).mul ((continuous_lam p q _).comp continuous_chartVec)

lemma norm_tfun_le (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) (z : ℂ) :
    ‖tfun p q ρ x z‖ ≤ (∑ t, ‖(emb (p + q) *ᵥ x) t‖) * (1 + ‖z‖ ^ 2)⁻¹ := by
  rw [tfun, chart_hvec, norm_mul, norm_wgt]
  have hl := norm_lam_le p q (emb (p + q) *ᵥ x) ![z, 1]
  rw [nsq_chart] at hl
  have hs : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.mpr (one_add_pos z)
  have hC : 0 ≤ ∑ t, ‖(emb (p + q) *ᵥ x) t‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc (1 + ‖z‖ ^ 2)⁻¹ * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p + q) *
        ‖lam p q (emb (p + q) *ᵥ x) ![z, 1]‖
      ≤ (1 + ‖z‖ ^ 2)⁻¹ * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p + q) *
          ((∑ t, ‖(emb (p + q) *ᵥ x) t‖) * Real.sqrt (1 + ‖z‖ ^ 2) ^ (p + q)) := by
        gcongr
    _ = (∑ t, ‖(emb (p + q) *ᵥ x) t‖) * (1 + ‖z‖ ^ 2)⁻¹ := by
        rw [inv_pow]; field_simp

lemma memLp_tfun (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) :
    MemLp (tfun p q ρ x) 2 volume :=
  memLp_of_bound (continuous_tfun p q ρ x) _ (norm_tfun_le p q ρ x)

lemma tfun_add (p q : ℕ) (ρ : ℝ) (x y : Fin (p + q + 1) → ℂ) :
    tfun p q ρ (x + y) = tfun p q ρ x + tfun p q ρ y := by
  funext z; simp only [tfun, chart_hvec, Pi.add_apply, mulVec_add, lam_add]; ring

lemma tfun_smul (p q : ℕ) (ρ : ℝ) (c : ℂ) (x : Fin (p + q + 1) → ℂ) :
    tfun p q ρ (c • x) = c • tfun p q ρ x := by
  funext z; simp only [tfun, chart_hvec, Pi.smul_apply, mulVec_smul, lam_smul_left, smul_eq_mul]
  ring

/-- **The intertwiner** `ℂ^{p+q+1} → L²(ℂ)`, `x ↦ hvec x (·, 1)`. -/
noncomputable def tlin (p q : ℕ) (ρ : ℝ) : (Fin (p + q + 1) → ℂ) →ₗ[ℂ] L2C where
  toFun x := (memLp_tfun p q ρ x).toLp _
  map_add' x y := by
    simp only [tfun_add]
    exact MemLp.toLp_add _ _
  map_smul' c x := by
    simp only [tfun_smul, RingHom.id_apply]
    exact MemLp.toLp_const_smul _ _

lemma coeFn_tlin (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) :
    tlin p q ρ x =ᵐ[volume] tfun p q ρ x :=
  MemLp.coeFn_toLp (memLp_tfun p q ρ x)

/-- **`tlin` intertwines** spin `(p+q)/2` with the principal series restricted to `SU(2)`. -/
theorem principalSeries_tlin {n : ℤ} {p q : ℕ} (hpq : (p : ℤ) - q = n) (ρ : ℝ) (u : SU2)
    (x : Fin (p + q + 1) → ℂ) :
    principalSeries n ρ (SL2C.ofSU2 u) (tlin p q ρ x) =
      tlin p q ρ (spinMat (p + q) (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) := by
  rw [Lp.ext_iff]
  have h1 := coeFn_principalSeries n ρ (SL2C.ofSU2 u) (tlin p q ρ x)
  have h2 := ae_eq_comp_mob (SL2C.ofSU2 u) (coeFn_tlin p q ρ x)
  have h3 := coeFn_tlin p q ρ (spinMat (p + q) (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x)
  filter_upwards [h1, h2, h3, ae_den_ne_zero (SL2C.ofSU2 u)] with z hz1 hz2 hz3 hden
  rw [hz1, hz3]
  simp only [Function.comp_apply] at hz2
  rw [hz2]
  have := chart_actH (isHomog_hvec hpq ρ x) (SL2C.ofSU2 u) hden
  simp only [act] at this
  rw [tfun, ← this, chart, actH, SL2C.coe_ofSU2, hvec_transpose]
  rfl

/-! ## The intertwiner is nonzero -/

/-- The string `1 … 1 0 … 0` (`p` ones, then `q` zeros). -/
def tstar (p q : ℕ) : Str (p + q) := Fin.addCases (fun _ => 1) (fun _ => 0)

lemma downs_tstar (p q : ℕ) : downs (tstar p q) = p := by
  unfold downs
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp [tstar]

lemma lform_chart_zero (p q : ℕ) (i : Fin (p + q)) (c : Fin 2) :
    lform p q i ![0, 1] c = if c = tstar p q i then 1 else 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> fin_cases c <;> simp [lform, epsConj, tstar]

lemma lam_chart_zero (p q : ℕ) (v : Str (p + q) → ℂ) : lam p q v ![0, 1] = v (tstar p q) := by
  classical
  simp only [lam, lform_chart_zero, Finset.prod_boole, Finset.mem_univ, true_implies]
  have : ∀ t : Str (p + q), (∀ i, t i = tstar p q i) ↔ t = tstar p q := fun t => funext_iff.symm
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The vector picking out the weight `p`. -/
def xstar (p q : ℕ) : Fin (p + q + 1) → ℂ := Pi.single ⟨p, by omega⟩ 1

lemma tfun_xstar_zero (p q : ℕ) (ρ : ℝ) : tfun p q ρ (xstar p q) 0 = nrm (p + q) p := by
  rw [tfun, chart_hvec, lam_chart_zero, xstar, mulVec_single_one]
  simp [wgt, emb_apply, downs_tstar]

/-- **The intertwiner is nonzero.** -/
theorem tlin_ne_zero (p q : ℕ) (ρ : ℝ) : tlin p q ρ ≠ 0 := by
  intro h
  have h0 : tlin p q ρ (xstar p q) = 0 := by rw [h]; rfl
  have hae : tfun p q ρ (xstar p q) =ᵐ[volume] (0 : ℂ → ℂ) := by
    have := coeFn_tlin p q ρ (xstar p q)
    rw [h0] at this
    exact this.symm.trans (Lp.coeFn_zero _ _ _)
  have hfun := (Continuous.ae_eq_iff_eq volume (continuous_tfun p q ρ (xstar p q))
    continuous_zero).mp hae
  have := congrFun hfun 0
  rw [tfun_xstar_zero] at this
  exact nrm_ne_zero (by omega : p ≤ p + q) this

end Lightlike.Lorentz

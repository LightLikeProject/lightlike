module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteSchurOrth
public import Lightlike.Lorentz.SL2RPlancherel.OrthSumL2

/-!
# Schur orthogonality for all vectors of `D_n⁺`: the finite combinations of `K`-weight vectors

For finite combinations `v = Σ_{j ∈ s} a_j e_j`, `w = Σ_{l ∈ t} b_l e_l` of the `K`-weight vectors,
`∫ |⟨v, D_n(g) w⟩|² dg = d_n⁻¹ ‖v‖² ‖w‖²` with `d_n⁻¹ = 2π|c₀|² / ‖e₀‖²` (`lintegral_norm_sq_mcoef_finite`): the
terms `⟨e_j, D_n(g) e_l⟩` are mutually orthogonal in `L²` with the norms of `lintegral_norm_sq_mcoef_kvec`.
-/

@[expose] public section

open MeasureTheory Set Finset Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The Schur ratio** `2π |c₀|² / ‖e₀‖²`, the inverse of the formal degree of `D_n⁺` for the normalisation of `haarR`. -/
def schurRatio {n : ℕ} (hn : 2 ≤ n) : ℝ := schurConst n / ‖kClass hn 0‖ ^ 2

lemma schurRatio_pos {n : ℕ} (hn : 2 ≤ n) : 0 < schurRatio hn :=
  div_pos (schurConst_pos hn) (pow_pos (norm_kClass_pos hn 0) 2)

/-- A continuous function with finite `L²`-norm is in `L²`. -/
lemma memLp_two_of_lintegral_lt_top {F : SL2R → ℂ} (hF : Continuous F)
    (h : ∫⁻ g, ENNReal.ofReal (‖F g‖ ^ 2) ∂haarR < ⊤) : MemLp F 2 haarR := by
  have hI : Integrable (fun g => ‖F g‖ ^ 2) haarR :=
    ⟨(hF.norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun g => by positivity))).2 h⟩
  exact (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).2 hI

lemma memLp_two_mcoef_kvec {n : ℕ} (hn : 2 ≤ n) (j l : ℕ) :
    MemLp (mcoef n (kClass hn j) (kClass hn l)) 2 haarR := by
  refine memLp_two_of_lintegral_lt_top (continuous_mcoef n _ _) ?_
  rw [lintegral_norm_sq_mcoef_kvec hn j l]
  exact ENNReal.ofReal_lt_top

lemma mcoef_sum {n : ℕ} (hn : 2 ≤ n) (s t : Finset ℕ) (a b : ℕ → ℂ) (g : SL2R) :
    mcoef n (∑ j ∈ s, a j • kClass hn j) (∑ l ∈ t, b l • kClass hn l) g =
      ∑ p ∈ s ×ˢ t, ((starRingEnd ℂ) (a p.1) * b p.2) * mcoef n (kClass hn p.1) (kClass hn p.2) g := by
  unfold mcoef
  have h2 : discreteAction n g (∑ l ∈ t, b l • kClass hn l) = ∑ l ∈ t, b l • discreteAction n g (kClass hn l) := by
    rw [map_sum]; simp only [map_smul]
  rw [h2, sum_inner, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [inner_smul_right]
  ring

lemma norm_sq_sum_kClass {n : ℕ} (hn : 2 ≤ n) (s : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ j ∈ s, a j • kClass hn j‖ ^ 2 = ∑ j ∈ s, ‖a j‖ ^ 2 * ‖kClass hn j‖ ^ 2 := by
  have h : ⟪∑ j ∈ s, a j • kClass hn j, ∑ j ∈ s, a j • kClass hn j⟫_ℂ =
      ((∑ j ∈ s, ‖a j‖ ^ 2 * ‖kClass hn j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    push_cast
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.sum_eq_single j]
    · rw [inner_self_eq_norm_sq_to_K]
      have : a j * (starRingEnd ℂ) (a j) = ((‖a j‖ : ℝ) : ℂ) ^ 2 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [← mul_assoc, this]
      rfl
    · intro k _ hkj
      rw [kClass_orthogonal hn hkj]; simp
    · intro hjs; exact absurd hj hjs
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖∑ j ∈ s, a j • kClass hn j‖ ^ 2 : ℝ) : ℂ) = ((∑ j ∈ s, ‖a j‖ ^ 2 * ‖kClass hn j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast at h ⊢
    exact h
  exact Complex.ofReal_injective h'

lemma sum_prod_mul (s t : Finset ℕ) (A B : ℕ → ℝ) (d : ℝ) :
    ∑ p ∈ s ×ˢ t, d * A p.1 * B p.2 = d * (∑ j ∈ s, A j) * (∑ l ∈ t, B l) := by
  rw [Finset.sum_product]
  calc ∑ x ∈ s, ∑ y ∈ t, d * A x * B y = (∑ x ∈ s, d * A x) * (∑ y ∈ t, B y) :=
        (Finset.sum_mul_sum _ _ _ _).symm
    _ = d * (∑ j ∈ s, A j) * (∑ l ∈ t, B l) := by rw [← Finset.mul_sum]

/-- **Schur orthogonality for finite combinations of `K`-weight vectors.** -/
theorem lintegral_norm_sq_mcoef_finite {n : ℕ} (hn : 2 ≤ n) (s t : Finset ℕ) (a b : ℕ → ℂ) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n (∑ j ∈ s, a j • kClass hn j) (∑ l ∈ t, b l • kClass hn l) g‖ ^ 2) ∂haarR =
      ENNReal.ofReal (schurRatio hn * ‖∑ j ∈ s, a j • kClass hn j‖ ^ 2 *
        ‖∑ l ∈ t, b l • kClass hn l‖ ^ 2) := by
  classical
  have hdpos := schurRatio_pos hn
  set F : ℕ × ℕ → SL2R → ℂ := fun p g =>
    ((starRingEnd ℂ) (a p.1) * b p.2) * mcoef n (kClass hn p.1) (kClass hn p.2) g with hF
  have hFmem : ∀ p, MemLp (F p) 2 haarR := fun p => (memLp_two_mcoef_kvec hn p.1 p.2).const_mul _
  have horth : ∀ p ∈ s ×ˢ t, ∀ p' ∈ s ×ˢ t, p ≠ p' →
      ∫ g, F p g * (starRingEnd ℂ) (F p' g) ∂haarR = 0 := by
    intro p _ p' _ hpp
    have h1 : ∀ g, F p g * (starRingEnd ℂ) (F p' g) =
        (((starRingEnd ℂ) (a p.1) * b p.2) * (starRingEnd ℂ) ((starRingEnd ℂ) (a p'.1) * b p'.2)) *
          (mcoef n (kClass hn p.1) (kClass hn p.2) g *
            (starRingEnd ℂ) (mcoef n (kClass hn p'.1) (kClass hn p'.2) g)) := by
      intro g
      simp only [hF, map_mul]
      ring
    simp_rw [h1]
    rw [integral_const_mul]
    have hor : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
      by_contra hcon
      have hc := not_or.1 hcon
      exact hpp (Prod.ext (not_not.1 hc.1) (not_not.1 hc.2))
    rw [integral_mcoef_orth hn hor, mul_zero]
  have hpyth := lintegral_norm_sq_sum_of_orth (s ×ˢ t) F hFmem horth
  have hsumeq : ∀ g, mcoef n (∑ j ∈ s, a j • kClass hn j) (∑ l ∈ t, b l • kClass hn l) g =
      ∑ p ∈ s ×ˢ t, F p g := fun g => mcoef_sum hn s t a b g
  simp_rw [hsumeq]
  rw [hpyth]
  have hterm : ∀ p : ℕ × ℕ, ∫⁻ g, ENNReal.ofReal (‖F p g‖ ^ 2) ∂haarR =
      ENNReal.ofReal (schurRatio hn * (‖a p.1‖ ^ 2 * ‖kClass hn p.1‖ ^ 2) *
        (‖b p.2‖ ^ 2 * ‖kClass hn p.2‖ ^ 2)) := by
    intro p
    have h2 : ∀ g, ENNReal.ofReal (‖F p g‖ ^ 2) = ENNReal.ofReal (‖(starRingEnd ℂ) (a p.1) * b p.2‖ ^ 2) *
        ENNReal.ofReal (‖mcoef n (kClass hn p.1) (kClass hn p.2) g‖ ^ 2) := by
      intro g
      rw [← ENNReal.ofReal_mul (sq_nonneg _), hF]
      simp only [norm_mul, mul_pow]
    simp_rw [h2]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_norm_sq_mcoef_kvec hn p.1 p.2,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    simp only [norm_mul, mul_pow, Complex.norm_conj, schurRatio]
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  congr 1
  rw [norm_sq_sum_kClass hn s a, norm_sq_sum_kClass hn t b]
  exact sum_prod_mul s t (fun j => ‖a j‖ ^ 2 * ‖kClass hn j‖ ^ 2) (fun l => ‖b l‖ ^ 2 * ‖kClass hn l‖ ^ 2)
    (schurRatio hn)

/-- **The `N`-th partial sum of the `K`-weight expansion** `Σ_{j<N} (⟨e_j, v⟩ / ‖e_j‖²) e_j` of a vector `v`. -/
def kTrunc {n : ℕ} (hn : 2 ≤ n) (v : Hn n) (N : ℕ) : Hn n :=
  ∑ j ∈ Finset.range N, (⟪kClass hn j, v⟫_ℂ / ((‖kClass hn j‖ ^ 2 : ℝ) : ℂ)) • kClass hn j

lemma kBasis_apply {n : ℕ} (hn : 2 ≤ n) (l : ℕ) : (kBasis hn) l = kUnit hn l :=
  congrFun (HilbertBasis.coe_mk (kUnit_orthonormal hn) (kUnit_span_top hn)) l

lemma repr_smul_kBasis {n : ℕ} (hn : 2 ≤ n) (x : holoSubmodule n) (i : ℕ) :
    (((kBasis hn).repr x i • (kBasis hn i) : holoSubmodule n) : Hn n) =
      (⟪kClass hn i, (x : Hn n)⟫_ℂ / ((‖kClass hn i‖ ^ 2 : ℝ) : ℂ)) • kClass hn i := by
  rw [HilbertBasis.repr_apply_apply, kBasis_apply]
  have hne : ((‖kClass hn i‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_kClass_pos hn i).ne'
  simp only [Submodule.coe_smul, kUnit, Submodule.coe_inner, inner_smul_left, Complex.conj_ofReal, smul_smul]
  congr 1
  push_cast
  field_simp

/-- **The partial sums converge**: `kTrunc v N → v` for `v ∈ A²_n`. -/
theorem tendsto_kTrunc {n : ℕ} (hn : 2 ≤ n) {v : Hn n} (hv : v ∈ holoSubmodule n) :
    Filter.Tendsto (fun N => kTrunc hn v N) Filter.atTop (nhds v) := by
  set x : holoSubmodule n := ⟨v, hv⟩ with hx
  have hS := ((kBasis hn).hasSum_repr x).tendsto_sum_nat
  have hc := (continuous_subtype_val (p := fun z : Hn n => z ∈ holoSubmodule n)).tendsto x
  have := hc.comp hS
  refine this.congr (fun N => ?_)
  simp only [Function.comp_apply, kTrunc]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact repr_smul_kBasis hn x i

/-- Bessel's inequality for the partial sums. -/
lemma norm_sq_kTrunc_le {n : ℕ} (hn : 2 ≤ n) {v : Hn n} (hv : v ∈ holoSubmodule n) (N : ℕ) :
    ‖kTrunc hn v N‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  set x : holoSubmodule n := ⟨v, hv⟩ with hx
  have hB := (kUnit_orthonormal hn).sum_inner_products_le x (s := Finset.range N)
  have h1 : ‖kTrunc hn v N‖ ^ 2 = ∑ j ∈ Finset.range N, ‖⟪kUnit hn j, x⟫_ℂ‖ ^ 2 := by
    unfold kTrunc
    rw [norm_sq_sum_kClass hn]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hne : ‖kClass hn j‖ ≠ 0 := (norm_kClass_pos hn j).ne'
    have hu : ⟪kUnit hn j, x⟫_ℂ = ((‖kClass hn j‖⁻¹ : ℝ) : ℂ) * ⟪kClass hn j, v⟫_ℂ := by
      simp only [kUnit, Submodule.coe_inner, inner_smul_left, Complex.conj_ofReal]
      rfl
    rw [hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    field_simp
  rw [h1]
  exact hB

/-- **The upper bound in Schur orthogonality for all vectors** (Fatou along the partial sums). -/
theorem lintegral_norm_sq_mcoef_le {n : ℕ} (hn : 2 ≤ n) {v w : Hn n} (hv : v ∈ holoSubmodule n)
    (hw : w ∈ holoSubmodule n) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n v w g‖ ^ 2) ∂haarR ≤
      ENNReal.ofReal (schurRatio hn * ‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  set f : ℕ → SL2R → ℝ≥0∞ := fun N g =>
    ENNReal.ofReal (‖mcoef n (kTrunc hn v N) (kTrunc hn w N) g‖ ^ 2) with hf
  have hmeas : ∀ N, Measurable (f N) := fun N =>
    ENNReal.measurable_ofReal.comp ((continuous_mcoef n _ _).norm.pow 2).measurable
  have hlim : ∀ g, Filter.Tendsto (fun N => f N g) Filter.atTop
      (nhds (ENNReal.ofReal (‖mcoef n v w g‖ ^ 2))) := by
    intro g
    have h1 := tendsto_kTrunc hn hv
    have h2 : Filter.Tendsto (fun N => discreteAction n g (kTrunc hn w N)) Filter.atTop
        (nhds (discreteAction n g w)) :=
      ((discreteAction n g).continuous.tendsto _).comp (tendsto_kTrunc hn hw)
    have h3 : Filter.Tendsto (fun N => mcoef n (kTrunc hn v N) (kTrunc hn w N) g) Filter.atTop
        (nhds (mcoef n v w g)) := h1.inner h2
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((h3.norm).pow 2)
  have hint : ∀ N, ∫⁻ g, f N g ∂haarR ≤ ENNReal.ofReal (schurRatio hn * ‖v‖ ^ 2 * ‖w‖ ^ 2) := by
    intro N
    have := lintegral_norm_sq_mcoef_finite hn (Finset.range N) (Finset.range N)
      (fun j => ⟪kClass hn j, v⟫_ℂ / ((‖kClass hn j‖ ^ 2 : ℝ) : ℂ))
      (fun j => ⟪kClass hn j, w⟫_ℂ / ((‖kClass hn j‖ ^ 2 : ℝ) : ℂ))
    simp only [hf]
    refine this.le.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hd := schurRatio_pos hn
    have hv' := norm_sq_kTrunc_le hn hv N
    have hw' := norm_sq_kTrunc_le hn hw N
    show schurRatio hn * ‖kTrunc hn v N‖ ^ 2 * ‖kTrunc hn w N‖ ^ 2 ≤ _
    gcongr
  calc ∫⁻ g, ENNReal.ofReal (‖mcoef n v w g‖ ^ 2) ∂haarR
      = ∫⁻ g, Filter.liminf (fun N => f N g) Filter.atTop ∂haarR :=
        lintegral_congr (fun g => (hlim g).liminf_eq.symm)
    _ ≤ Filter.liminf (fun N => ∫⁻ g, f N g ∂haarR) Filter.atTop := lintegral_liminf_le hmeas
    _ ≤ ENNReal.ofReal (schurRatio hn * ‖v‖ ^ 2 * ‖w‖ ^ 2) :=
        Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently (Filter.Eventually.of_forall hint))

lemma kTrunc_mem {n : ℕ} (hn : 2 ≤ n) (v : Hn n) (N : ℕ) : kTrunc hn v N ∈ holoSubmodule n :=
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (kClass_mem hn j))

lemma mcoef_sub_left (n : ℕ) (v v' w : Hn n) (g : SL2R) :
    mcoef n (v - v') w g = mcoef n v w g - mcoef n v' w g := by
  unfold mcoef; rw [inner_sub_left]

lemma mcoef_sub_right (n : ℕ) (v w w' : Hn n) (g : SL2R) :
    mcoef n v (w - w') g = mcoef n v w g - mcoef n v w' g := by
  unfold mcoef; rw [map_sub, inner_sub_right]

lemma memLp_two_mcoef {n : ℕ} (hn : 2 ≤ n) {v w : Hn n} (hv : v ∈ holoSubmodule n) (hw : w ∈ holoSubmodule n) :
    MemLp (mcoef n v w) 2 haarR :=
  memLp_two_of_lintegral_lt_top (continuous_mcoef n v w)
    (lt_of_le_of_lt (lintegral_norm_sq_mcoef_le hn hv hw) ENNReal.ofReal_lt_top)

lemma integral_norm_sq_mcoef_le {n : ℕ} (hn : 2 ≤ n) {v w : Hn n} (hv : v ∈ holoSubmodule n)
    (hw : w ∈ holoSubmodule n) :
    ∫ g, ‖mcoef n v w g‖ ^ 2 ∂haarR ≤ schurRatio hn * ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
  have h := lintegral_norm_sq_mcoef_le hn hv hw
  rw [lintegral_ofReal_norm_sq_eq (memLp_two_mcoef hn hv hw)] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (schurRatio_pos hn).le (sq_nonneg _)) (sq_nonneg _))).1 h

lemma integral_norm_sq_mcoef_kTrunc {n : ℕ} (hn : 2 ≤ n) (v w : Hn n) (N : ℕ) :
    ∫ g, ‖mcoef n (kTrunc hn v N) (kTrunc hn w N) g‖ ^ 2 ∂haarR =
      schurRatio hn * ‖kTrunc hn v N‖ ^ 2 * ‖kTrunc hn w N‖ ^ 2 := by
  have h := lintegral_norm_sq_mcoef_finite hn (Finset.range N) (Finset.range N)
    (fun j => ⟪kClass hn j, v⟫_ℂ / ((‖kClass hn j‖ ^ 2 : ℝ) : ℂ))
    (fun j => ⟪kClass hn j, w⟫_ℂ / ((‖kClass hn j‖ ^ 2 : ℝ) : ℂ))
  have hmem := memLp_two_mcoef hn (kTrunc_mem hn v N) (kTrunc_mem hn w N)
  change ∫⁻ g, ENNReal.ofReal (‖mcoef n (kTrunc hn v N) (kTrunc hn w N) g‖ ^ 2) ∂haarR = _ at h
  rw [lintegral_ofReal_norm_sq_eq hmem] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun g => by positivity))
    (mul_nonneg (mul_nonneg (schurRatio_pos hn).le (sq_nonneg _)) (sq_nonneg _))).1 h

/-- **Schur orthogonality for all vectors of `D_n⁺`**: for `v, w ∈ A²_n`,
`∫ |⟨v, D_n(g) w⟩|² dg = (2π |c₀|² / ‖e₀‖²) ‖v‖² ‖w‖²`. -/
theorem lintegral_norm_sq_mcoef_eq {n : ℕ} (hn : 2 ≤ n) {v w : Hn n} (hv : v ∈ holoSubmodule n)
    (hw : w ∈ holoSubmodule n) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n v w g‖ ^ 2) ∂haarR =
      ENNReal.ofReal (schurRatio hn * ‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  set d := schurRatio hn with hd
  have hdpos : 0 < d := schurRatio_pos hn
  set Q : ℝ := ∫ g, ‖mcoef n v w g‖ ^ 2 ∂haarR with hQ
  have hQle : Q ≤ d * ‖v‖ ^ 2 * ‖w‖ ^ 2 := integral_norm_sq_mcoef_le hn hv hw
  have hFmem := memLp_two_mcoef hn hv hw
  have key : ∀ ε : ℝ, 0 < ε → d * ‖v‖ ^ 2 * ‖w‖ ^ 2 ≤ (1 + ε) * Q := by
    intro ε hε
    have hbound : ∀ N : ℕ, d * ‖kTrunc hn v N‖ ^ 2 * ‖kTrunc hn w N‖ ^ 2 ≤
        (1 + ε) * Q + (1 + ε⁻¹) * (2 * (d * ‖v - kTrunc hn v N‖ ^ 2 * ‖w‖ ^ 2) +
          2 * (d * ‖v‖ ^ 2 * ‖w - kTrunc hn w N‖ ^ 2)) := by
      intro N
      set vN := kTrunc hn v N with hvN
      set wN := kTrunc hn w N with hwN
      have hvNm : vN ∈ holoSubmodule n := kTrunc_mem hn v N
      have hwNm : wN ∈ holoSubmodule n := kTrunc_mem hn w N
      have hsubv : v - vN ∈ holoSubmodule n := Submodule.sub_mem _ hv hvNm
      have hsubw : w - wN ∈ holoSubmodule n := Submodule.sub_mem _ hw hwNm
      have hA := memLp_two_mcoef hn hsubv hw
      have hB := memLp_two_mcoef hn hvNm hsubw
      have hFN := memLp_two_mcoef hn hvNm hwNm
      set H : SL2R → ℂ := fun g => mcoef n vN wN g - mcoef n v w g with hH
      have hHmem : MemLp H 2 haarR := hFN.sub hFmem
      have hFN_eq : ∀ g, mcoef n vN wN g = mcoef n v w g + H g := fun g => by simp [hH]
      have h1 : ∫ g, ‖mcoef n vN wN g‖ ^ 2 ∂haarR ≤ (1 + ε) * Q + (1 + ε⁻¹) * ∫ g, ‖H g‖ ^ 2 ∂haarR := by
        have := integral_norm_sq_add_le hFmem hHmem hε
        simp_rw [← hFN_eq] at this
        exact this
      have hHAB : ∀ g, H g = -(mcoef n (v - vN) w g + mcoef n vN (w - wN) g) := by
        intro g
        simp only [hH, mcoef_sub_left, mcoef_sub_right]
        ring
      have h2 : ∫ g, ‖H g‖ ^ 2 ∂haarR ≤ 2 * ∫ g, ‖mcoef n (v - vN) w g‖ ^ 2 ∂haarR +
          2 * ∫ g, ‖mcoef n vN (w - wN) g‖ ^ 2 ∂haarR := by
        have := integral_norm_sq_add_le hA hB (one_pos : (0 : ℝ) < 1)
        simp only [inv_one] at this
        have e : ∀ g, ‖H g‖ ^ 2 = ‖mcoef n (v - vN) w g + mcoef n vN (w - wN) g‖ ^ 2 := by
          intro g; rw [hHAB g, norm_neg]
        simp_rw [e]
        linarith
      have h3 := integral_norm_sq_mcoef_le hn hsubv hw
      have h4 := integral_norm_sq_mcoef_le hn hvNm hsubw
      have h5 : ‖vN‖ ^ 2 ≤ ‖v‖ ^ 2 := norm_sq_kTrunc_le hn hv N
      have h6 : d * ‖vN‖ ^ 2 * ‖w - wN‖ ^ 2 ≤ d * ‖v‖ ^ 2 * ‖w - wN‖ ^ 2 := by gcongr
      have hq := integral_norm_sq_mcoef_kTrunc hn v w N
      have hpos : 0 < 1 + ε⁻¹ := by positivity
      rw [← hq]
      calc ∫ g, ‖mcoef n vN wN g‖ ^ 2 ∂haarR
          ≤ (1 + ε) * Q + (1 + ε⁻¹) * ∫ g, ‖H g‖ ^ 2 ∂haarR := h1
        _ ≤ (1 + ε) * Q + (1 + ε⁻¹) * (2 * (d * ‖v - vN‖ ^ 2 * ‖w‖ ^ 2) +
              2 * (d * ‖v‖ ^ 2 * ‖w - wN‖ ^ 2)) := by
            gcongr
            linarith
        _ = _ := by ring
    -- let `N → ∞`
    have hv1 := tendsto_kTrunc hn hv
    have hw1 := tendsto_kTrunc hn hw
    have hL : Filter.Tendsto (fun N => d * ‖kTrunc hn v N‖ ^ 2 * ‖kTrunc hn w N‖ ^ 2) Filter.atTop
        (nhds (d * ‖v‖ ^ 2 * ‖w‖ ^ 2)) :=
      (((hv1.norm.pow 2).const_mul d).mul (hw1.norm.pow 2))
    have hvs : Filter.Tendsto (fun N => ‖v - kTrunc hn v N‖) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := v)).sub hv1
      simpa using this.norm
    have hws : Filter.Tendsto (fun N => ‖w - kTrunc hn w N‖) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := w)).sub hw1
      simpa using this.norm
    have hR : Filter.Tendsto (fun N => (1 + ε) * Q + (1 + ε⁻¹) * (2 * (d * ‖v - kTrunc hn v N‖ ^ 2 * ‖w‖ ^ 2) +
        2 * (d * ‖v‖ ^ 2 * ‖w - kTrunc hn w N‖ ^ 2))) Filter.atTop (nhds ((1 + ε) * Q + (1 + ε⁻¹) *
        (2 * (d * 0 ^ 2 * ‖w‖ ^ 2) + 2 * (d * ‖v‖ ^ 2 * 0 ^ 2)))) := by
      refine tendsto_const_nhds.add (Filter.Tendsto.const_mul _ ?_)
      refine Filter.Tendsto.add (Filter.Tendsto.const_mul _ ?_) (Filter.Tendsto.const_mul _ ?_)
      · exact (((hvs.pow 2).const_mul d).mul_const _)
      · exact ((hws.pow 2).const_mul _)
    have := le_of_tendsto_of_tendsto' hL hR hbound
    simpa using this
  have hQge : d * ‖v‖ ^ 2 * ‖w‖ ^ 2 ≤ Q := by
    by_contra hlt
    have hlt := not_le.1 hlt
    set R := d * ‖v‖ ^ 2 * ‖w‖ ^ 2 with hR
    have hQnn : 0 ≤ Q := integral_nonneg (fun g => by positivity)
    have hε : 0 < (R - Q) / (2 * (Q + 1)) := div_pos (by linarith) (by positivity)
    have h := key _ hε
    have h2 : (1 + (R - Q) / (2 * (Q + 1))) * Q < R := by
      have : (R - Q) / (2 * (Q + 1)) * Q ≤ (R - Q) / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith
    linarith
  rw [lintegral_ofReal_norm_sq_eq hFmem]
  congr 1
  exact le_antisymm hQle hQge

end Lightlike.Lorentz.SL2RPlancherel

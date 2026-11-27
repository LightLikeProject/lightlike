module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteSchurAll

/-!
# The orthonormal system of the matrix coefficients of `D_n⁺` and the discrete part of `L²(SL(2,ℝ))`

The functions `u_{jl} = ⟨e_j, D_n(g) e_l⟩ / (√d ‖e_j‖ ‖e_l‖)`, `d = 2π|c₀|²/‖e₀‖²`, form an orthonormal system
`discreteONS` of `L²(SL(2,ℝ), haarR)` (Schur orthogonality, `lintegral_norm_sq_mcoef_kvec`, and the orthogonality of
distinct `K`-weight pairs, `integral_mcoef_orth`). Its closed span `discreteSpace` is the isotypic subspace of `D_n⁺`;
for `f ∈ L²` the squared norm of the projection `discreteProj` is `Σ_{j,l} |⟨u_{jl}, f⟩|²`
(`norm_sq_discreteProj`), and `⟨u_{jl}, f⟩ = d^{-1/2} ∫ f conj(⟨e_j, D_n(g) e_l⟩)/(‖e_j‖ ‖e_l‖)` is a matrix entry of
`D_n(f)`.
-/

@[expose] public section

open MeasureTheory Set Finset Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The normalising constant `1 / (√d ‖e_j‖ ‖e_l‖)` of the coefficient `⟨e_j, D_n(g) e_l⟩`. -/
def uConst {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : ℝ :=
  (Real.sqrt (schurRatio hn) * ‖kClass hn p.1‖ * ‖kClass hn p.2‖)⁻¹

/-- **The normalised matrix coefficients** `u_{jl}(g) = ⟨e_j, D_n(g) e_l⟩ / (√d ‖e_j‖ ‖e_l‖)`. -/
def uFun {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : SL2R → ℂ :=
  fun g => (uConst hn p : ℂ) * mcoef n (kClass hn p.1) (kClass hn p.2) g

lemma uConst_pos {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : 0 < uConst hn p := by
  unfold uConst
  have := schurRatio_pos hn
  have h1 := norm_kClass_pos hn p.1
  have h2 := norm_kClass_pos hn p.2
  positivity

lemma continuous_uFun {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : Continuous (uFun hn p) := by
  unfold uFun
  exact continuous_const.mul (continuous_mcoef n _ _)

lemma memLp_uFun {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : MemLp (uFun hn p) 2 haarR :=
  (memLp_two_mcoef_kvec hn p.1 p.2).const_mul _

/-- **The normalisation**: `∫ |u_{jl}|² = 1`. -/
theorem integral_norm_sq_uFun {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) :
    ∫ g, ‖uFun hn p g‖ ^ 2 ∂haarR = 1 := by
  have h := lintegral_norm_sq_mcoef_kvec hn p.1 p.2
  have hmem := memLp_two_mcoef_kvec hn p.1 p.2
  rw [lintegral_ofReal_norm_sq_eq hmem] at h
  have hnn : 0 ≤ schurConst n * ‖kClass hn p.1‖ ^ 2 * ‖kClass hn p.2‖ ^ 2 / ‖kClass hn 0‖ ^ 2 := by
    have := schurConst_pos hn
    positivity
  have h2 := (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun g => by positivity)) hnn).1 h
  have h3 : ∫ g, ‖uFun hn p g‖ ^ 2 ∂haarR = uConst hn p ^ 2 * ∫ g, ‖mcoef n (kClass hn p.1) (kClass hn p.2) g‖ ^ 2 ∂haarR := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
    simp only [uFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h3, h2]
  have h1 := norm_kClass_pos hn p.1
  have h4 := norm_kClass_pos hn p.2
  have h5 := norm_kClass_pos hn 0
  have hd := schurRatio_pos hn
  unfold uConst schurRatio
  have hsq : Real.sqrt (schurConst n / ‖kClass hn 0‖ ^ 2) ^ 2 = schurConst n / ‖kClass hn 0‖ ^ 2 :=
    Real.sq_sqrt (div_nonneg (schurConst_pos hn).le (sq_nonneg _))
  rw [inv_pow, mul_pow, mul_pow, hsq]
  have hs := schurConst_pos hn
  field_simp

/-- **Orthogonality of the normalised matrix coefficients.** -/
theorem integral_uFun_orth {n : ℕ} (hn : 2 ≤ n) {p p' : ℕ × ℕ} (h : p ≠ p') :
    ∫ g, uFun hn p g * (starRingEnd ℂ) (uFun hn p' g) ∂haarR = 0 := by
  have hor : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
    by_contra hcon
    have hc := not_or.1 hcon
    exact h (Prod.ext (not_not.1 hc.1) (not_not.1 hc.2))
  have e : ∀ g, uFun hn p g * (starRingEnd ℂ) (uFun hn p' g) =
      ((uConst hn p : ℂ) * (uConst hn p' : ℂ)) * (mcoef n (kClass hn p.1) (kClass hn p.2) g *
        (starRingEnd ℂ) (mcoef n (kClass hn p'.1) (kClass hn p'.2) g)) := by
    intro g
    simp only [uFun, map_mul, Complex.conj_ofReal]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_mcoef_orth hn hor, mul_zero]

/-- **The orthonormal system of `D_n⁺`-matrix coefficients in `L²(SL(2,ℝ))`.** -/
def uLp {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : Lp ℂ 2 (haarR : Measure SL2R) :=
  (memLp_uFun hn p).toLp (uFun hn p)

/-- **The matrix coefficients `u_{jl}` of `D_n⁺` are an orthonormal system of `L²(SL(2,ℝ))`.** -/
theorem uLp_orthonormal {n : ℕ} (hn : 2 ≤ n) : Orthonormal ℂ (uLp hn) := by
  rw [orthonormal_iff_ite]
  intro p p'
  have hae : ∀ᵐ g ∂haarR, ⟪(uLp hn p : SL2R → ℂ) g, (uLp hn p' : SL2R → ℂ) g⟫_ℂ =
      ⟪uFun hn p g, uFun hn p' g⟫_ℂ := by
    filter_upwards [(memLp_uFun hn p).coeFn_toLp, (memLp_uFun hn p').coeFn_toLp] with g h1 h2
    simp only [uLp]
    rw [h1, h2]
  rw [L2.inner_def, integral_congr_ae hae]
  by_cases h : p = p'
  · subst h
    simp only [↓reduceIte]
    have h1 : ∀ g, ⟪uFun hn p g, uFun hn p g⟫_ℂ = ((‖uFun hn p g‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    simp_rw [h1]
    rw [integral_complex_ofReal, integral_norm_sq_uFun hn p]
    simp
  · simp only [h, ↓reduceIte]
    have h1 : ∀ g, ⟪uFun hn p g, uFun hn p' g⟫_ℂ = (starRingEnd ℂ) (uFun hn p g * (starRingEnd ℂ) (uFun hn p' g)) := by
      intro g
      simp [RCLike.inner_apply, mul_comm]
    simp_rw [h1]
    rw [integral_conj, integral_uFun_orth hn h]
    simp

/-- **The isotypic subspace of `D_n⁺`** in `L²(SL(2,ℝ))`: the closed span of the matrix coefficients. -/
def discreteSpace {n : ℕ} (hn : 2 ≤ n) : Submodule ℂ (Lp ℂ 2 (haarR : Measure SL2R)) :=
  (Submodule.span ℂ (Set.range (uLp hn))).topologicalClosure

lemma uLp_mem_discreteSpace {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : uLp hn p ∈ discreteSpace hn :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨p, rfl⟩)

instance discreteSpace_hasOrthogonalProjection {n : ℕ} (hn : 2 ≤ n) : (discreteSpace hn).HasOrthogonalProjection := by
  have : CompleteSpace (discreteSpace hn) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **The `ℓ²`-expansion of the discrete part**: for `f ∈ L²(SL(2,ℝ))` the squared norm of its projection onto
the isotypic subspace of `D_n⁺` is `Σ_{j,l} |⟨u_{jl}, f⟩|²`. -/
theorem norm_sq_starProjection_discrete {n : ℕ} (hn : 2 ≤ n) (f : Lp ℂ 2 (haarR : Measure SL2R)) :
    ‖(discreteSpace hn).starProjection f‖ ^ 2 = ∑' p : ℕ × ℕ, ‖⟪uLp hn p, f⟫_ℂ‖ ^ 2 := by
  have hcomplete : CompleteSpace (discreteSpace hn) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set M := discreteSpace hn with hM
  set v : ℕ × ℕ → M := fun p => ⟨uLp hn p, uLp_mem_discreteSpace hn p⟩ with hv
  have hon : Orthonormal ℂ v := by
    have := uLp_orthonormal hn
    rw [orthonormal_iff_ite] at this ⊢
    intro p p'
    have h := this p p'
    simpa [hv, Submodule.coe_inner] using h
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    have h0 : ∀ p, ⟪uLp hn p, (x : Lp ℂ 2 (haarR : Measure SL2R))⟫_ℂ = 0 := fun p => by
      have := hx (v p) (Submodule.subset_span ⟨p, rfl⟩)
      simpa [hv, Submodule.coe_inner] using this
    -- `x ∈ M` is orthogonal to the span of the `uLp`, hence to its closure `M ∋ x`
    have hx2 : ⟪(x : Lp ℂ 2 (haarR : Measure SL2R)), (x : Lp ℂ 2 (haarR : Measure SL2R))⟫_ℂ = 0 := by
      have hxM : (x : Lp ℂ 2 (haarR : Measure SL2R)) ∈ (Submodule.span ℂ (Set.range (uLp hn))).topologicalClosure :=
        x.2
      have hcl : (x : Lp ℂ 2 (haarR : Measure SL2R)) ∈
          ((Submodule.span ℂ (Set.range (uLp hn))).topologicalClosure) := hxM
      have horth : (Submodule.span ℂ (Set.range (uLp hn))).topologicalClosure ≤
          (ℂ ∙ (x : Lp ℂ 2 (haarR : Measure SL2R)))ᗮ := by
        refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
        rw [Submodule.span_le]
        rintro _ ⟨p, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
        rw [← inner_conj_symm, h0 p]; simp
      have := horth hcl
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      exact this
    exact Subtype.ext (inner_self_eq_zero.1 hx2)
  let b : HilbertBasis (ℕ × ℕ) ℂ M := HilbertBasis.mkOfOrthogonalEqBot hon hsp
  have hb : ∀ p, b p = v p := fun p => congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp) p
  set g : M := ⟨M.starProjection f, Submodule.starProjection_apply_mem M f⟩ with hg
  have hpar := b.hasSum_inner_mul_inner g g
  have hterm : ∀ p, ⟪g, b p⟫_ℂ * ⟪b p, g⟫_ℂ = ((‖⟪uLp hn p, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro p
    have hin : ⟪b p, g⟫_ℂ = ⟪uLp hn p, f⟫_ℂ := by
      rw [hb p]
      show ⟪uLp hn p, M.starProjection f⟫_ℂ = _
      have h1 := Submodule.starProjection_inner_eq_zero (K := M) f (uLp hn p) (uLp_mem_discreteSpace hn p)
      rw [inner_sub_left] at h1
      have h2 : ⟪f, uLp hn p⟫_ℂ = ⟪M.starProjection f, uLp hn p⟫_ℂ := sub_eq_zero.1 h1
      rw [← inner_conj_symm (uLp hn p) (M.starProjection f), ← h2, inner_conj_symm]
    have : ⟪g, b p⟫_ℂ = (starRingEnd ℂ) ⟪b p, g⟫_ℂ := by
      simp only [Submodule.coe_inner]; exact (inner_conj_symm _ _).symm
    rw [this, hin, Complex.conj_mul']
    push_cast; ring
  have hnorm : ⟪g, g⟫_ℂ = ((‖M.starProjection f‖ ^ 2 : ℝ) : ℂ) := by
    have h0 : ⟪g, g⟫_ℂ = ⟪M.starProjection f, M.starProjection f⟫_ℂ := rfl
    rw [h0, inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [hterm, hnorm] at hpar
  have hpar' : HasSum (fun p : ℕ × ℕ => ‖⟪uLp hn p, f⟫_ℂ‖ ^ 2) (‖M.starProjection f‖ ^ 2) := by
    exact_mod_cast hpar
  exact hpar'.tsum_eq.symm

end Lightlike.Lorentz.SL2RPlancherel

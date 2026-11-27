module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteInnerOrth

/-!
# Orthogonality of the isotypic subspaces of distinct holomorphic discrete series

For `n ≠ n'` the normalised matrix coefficients `u^n_{jl}` and `u^{n'}_{j'l'}` of `D_n⁺` and `D_{n'}⁺` are orthogonal
in `L²(SL(2,ℝ))` (`inner_uLp_uLp_ne`): with different `K × K`-weights by rotation invariance
(`integral_mcoef_orth_gen`); with equal `K × K`-weights because the radial profiles are orthogonal in
`L²((0,∞), sinh ξ dξ)` (`profPair_eq_zero_of_ne`, from the ladder equations) and the Plancherel identity in the
`K × K`-components (`integral_norm_sq_block`) turns the Pythagoras identity of the profiles into that of
`u + t u'`, `t ∈ {1, i}`.
-/

@[expose] public section

open MeasureTheory Set Complex Real Filter Topology UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The radial profile of the normalised coefficient `u_p`: `ξ ↦ u_p(a(ξ))`. -/
def phiRad {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (ξ : ℝ) : ℂ :=
  (uConst hn p : ℂ) * mcoef n (kClass hn p.1) (kClass hn p.2) (aR ξ)

lemma phiRad_eq {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (ξ : ℝ) :
    phiRad hn p ξ = (uConst hn p : ℂ) * profileFun n p.2 p.1 ((‖kClass hn p.1‖ ^ 2 : ℝ) : ℂ) ξ := by
  unfold phiRad
  rw [profile_eq_mcoef hn p.1 p.2 ξ]

lemma continuous_phiRad {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) : Continuous (phiRad hn p) := by
  have : phiRad hn p = fun ξ => (uConst hn p : ℂ) * profileFun n p.2 p.1 ((‖kClass hn p.1‖ ^ 2 : ℝ) : ℂ) ξ := by
    funext ξ; exact phiRad_eq hn p ξ
  rw [this]
  exact continuous_const.mul (continuous_profileFun n p.2 p.1 (by omega) _)

lemma norm_phiRad_le {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ‖phiRad hn p ξ‖ ≤ (uConst hn p * profConst n p.2 p.1 ((‖kClass hn p.1‖ ^ 2 : ℝ) : ℂ)) *
      Real.exp (-((n : ℝ) * ξ / 2)) := by
  rw [phiRad_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (uConst_pos hn p), mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_profileFun_le n p.2 p.1 _ hξ) (uConst_pos hn p).le

lemma kkProfile_uFun {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (ξ : ℝ) (x : Fin 2 → ℝ) :
    kkProfile (uFun hn p) ξ x =
      Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n p.1 p.2) i : ℂ) * (x i : ℂ))) * phiRad hn p ξ := by
  unfold kkProfile
  have h := kkProfile_mcoef hn p.1 p.2 ξ x
  unfold kkProfile at h
  simp only [uFun, phiRad, h]
  ring

/-- The pairing of two radial profiles, in the form used by the Pythagoras identity. -/
lemma integrableOn_phiRad_prod {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (p : ℕ × ℕ) (p' : ℕ × ℕ) :
    IntegrableOn (fun ξ : ℝ => ((Real.sinh ξ : ℝ) : ℂ) * (phiRad hn p ξ * (starRingEnd ℂ) (phiRad hn' p' ξ))) (Ioi 0) := by
  have hf : Continuous fun ξ : ℝ => phiRad hn p ξ * (starRingEnd ℂ) (phiRad hn' p' ξ) * ((Real.sinh ξ : ℝ) : ℂ) :=
    ((continuous_phiRad hn p).mul (Complex.continuous_conj.comp (continuous_phiRad hn' p'))).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh)
  have := integrableOn_of_decay hf _
    (fun ξ hξ => decay_prod (a := n) (b := n') (by omega) (fun ξ hξ => norm_phiRad_le hn p hξ)
      (fun ξ hξ => norm_phiRad_le hn' p' hξ) hξ)
  refine this.congr_fun (fun ξ _ => by ring) measurableSet_Ioi

/-- The radial pairing of the normalised coefficients of two series with equal `K × K`-weights vanishes. -/
lemma radial_cross_eq_zero {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (hne : n ≠ n') (p p' : ℕ × ℕ)
    (hw1 : n + 2 * p.1 = n' + 2 * p'.1) (hw2 : n + 2 * p.2 = n' + 2 * p'.2) :
    ∫ ξ in Ioi (0 : ℝ), ((Real.sinh ξ : ℝ) : ℂ) * (phiRad hn p ξ * (starRingEnd ℂ) (phiRad hn' p' ξ)) = 0 := by
  have h := profPair_eq_zero_of_ne n p.2 p.1 ((‖kClass hn p.1‖ ^ 2 : ℝ) : ℂ) n' p'.2 p'.1
    ((‖kClass hn' p'.1‖ ^ 2 : ℝ) : ℂ) (by omega) (by omega) (by omega) hne hw2 hw1
  unfold profPair at h
  have e : ∀ ξ : ℝ, ((Real.sinh ξ : ℝ) : ℂ) * (phiRad hn p ξ * (starRingEnd ℂ) (phiRad hn' p' ξ)) =
      ((uConst hn p * uConst hn' p' : ℝ) : ℂ) *
        (profileFun n p.2 p.1 ((‖kClass hn p.1‖ ^ 2 : ℝ) : ℂ) ξ *
          (starRingEnd ℂ) (profileFun n' p'.2 p'.1 ((‖kClass hn' p'.1‖ ^ 2 : ℝ) : ℂ) ξ) *
            ((Real.sinh ξ : ℝ) : ℂ)) := by
    intro ξ
    rw [phiRad_eq, phiRad_eq]
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [e]
  rw [integral_const_mul, h, mul_zero]

lemma norm_sinh_mul_conj {z : ℂ} {ξ : ℝ} (hξ : 0 < ξ) :
    ‖((Real.sinh ξ : ℝ) : ℂ) * (z * (starRingEnd ℂ) z)‖ = Real.sinh ξ * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sinh_pos_iff.2 hξ), norm_mul,
    RCLike.norm_conj]
  ring

lemma ofReal_sinh_mul_norm_sq (z : ℂ) (ξ : ℝ) :
    (((Real.sinh ξ * ‖z‖ ^ 2 : ℝ)) : ℂ) = ((Real.sinh ξ : ℝ) : ℂ) * (z * (starRingEnd ℂ) z) := by
  rw [Complex.mul_conj, Complex.sq_norm, Complex.ofReal_mul]

/-- **The expansion of `sinh ‖φ₁ + t φ₂‖²`** in the four complex pairings. -/
lemma ofReal_sinh_norm_add_sq (φ₁ φ₂ : ℂ) (t : ℂ) (ξ : ℝ) :
    (((Real.sinh ξ * ‖φ₁ + t * φ₂‖ ^ 2 : ℝ)) : ℂ) =
      ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ * (starRingEnd ℂ) φ₁) +
        (starRingEnd ℂ) t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₁ * (starRingEnd ℂ) φ₂)) +
        t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₂ * (starRingEnd ℂ) φ₁)) +
        t * (starRingEnd ℂ) t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₂ * (starRingEnd ℂ) φ₂)) := by
  rw [ofReal_sinh_mul_norm_sq]
  simp only [map_add, map_mul]
  ring

lemma integral_add4 {a b c d : ℝ → ℂ} {μ : Measure ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hd : Integrable d μ) :
    ∫ x, (a x + b x + c x + d x) ∂μ = (∫ x, a x ∂μ) + (∫ x, b x ∂μ) + (∫ x, c x ∂μ) + ∫ x, d x ∂μ := by
  have h1 : Integrable (fun x => a x + b x) μ := ha.add hb
  have h2 : Integrable (fun x => a x + b x + c x) μ := h1.add hc
  rw [integral_add h2 hd, integral_add h1 hc, integral_add ha hb]

/-- **Radial Pythagoras**: with orthogonal profiles and `|t| = 1`,
`∫ sinh ‖φ₁ + t φ₂‖² = ∫ sinh ‖φ₁‖² + ∫ sinh ‖φ₂‖²`. -/
theorem radial_pythag {φ₁ φ₂ : ℝ → ℂ}
    (h11 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₁ ξ))) (Ioi 0))
    (h12 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₂ ξ))) (Ioi 0))
    (h21 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₁ ξ))) (Ioi 0))
    (h22 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₂ ξ))) (Ioi 0))
    (hcross : ∫ ξ in Ioi (0 : ℝ), ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₂ ξ)) = 0)
    {t : ℂ} (ht : ‖t‖ = 1) :
    ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖φ₁ ξ + t * φ₂ ξ‖ ^ 2 =
      (∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖φ₁ ξ‖ ^ 2) + ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖φ₂ ξ‖ ^ 2 := by
  have h21z : ∫ ξ in Ioi (0 : ℝ), ((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₁ ξ)) = 0 := by
    have : ∫ ξ in Ioi (0 : ℝ), ((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₁ ξ)) =
        (starRingEnd ℂ) (∫ ξ in Ioi (0 : ℝ), ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₂ ξ))) := by
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [this, hcross]; simp
  have htt : t * (starRingEnd ℂ) t = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ht]; simp
  have e1 : ∀ ξ : ℝ, (((Real.sinh ξ * ‖φ₁ ξ + t * φ₂ ξ‖ ^ 2 : ℝ)) : ℂ) =
      ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₁ ξ)) +
        (starRingEnd ℂ) t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₂ ξ))) +
        t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₁ ξ))) +
        t * (starRingEnd ℂ) t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₂ ξ))) :=
    fun ξ => ofReal_sinh_norm_add_sq _ _ _ _
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [e1]
  have i1 : Integrable (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₁ ξ)))
      (volume.restrict (Ioi (0 : ℝ))) := h11
  have i2 : Integrable (fun ξ => (starRingEnd ℂ) t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₂ ξ))))
      (volume.restrict (Ioi (0 : ℝ))) := h12.const_mul _
  have i3 : Integrable (fun ξ => t * (((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₁ ξ))))
      (volume.restrict (Ioi (0 : ℝ))) := h21.const_mul _
  have i4 : Integrable (fun ξ => t * (starRingEnd ℂ) t * (((Real.sinh ξ : ℝ) : ℂ) *
      (φ₂ ξ * (starRingEnd ℂ) (φ₂ ξ)))) (volume.restrict (Ioi (0 : ℝ))) := h22.const_mul _
  rw [integral_add4 i1 i2 i3 i4, integral_const_mul, integral_const_mul, integral_const_mul, hcross, h21z, htt]
  have f1 : ((∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖φ₁ ξ‖ ^ 2 : ℝ) : ℂ) =
      ∫ ξ in Ioi (0 : ℝ), ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₁ ξ)) := by
    rw [← integral_complex_ofReal]; simp_rw [ofReal_sinh_mul_norm_sq]
  have f2 : ((∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖φ₂ ξ‖ ^ 2 : ℝ) : ℂ) =
      ∫ ξ in Ioi (0 : ℝ), ((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₂ ξ)) := by
    rw [← integral_complex_ofReal]; simp_rw [ofReal_sinh_mul_norm_sq]
  rw [Complex.ofReal_add, f1, f2]
  ring

lemma integrableOn_sinh_norm_sq {φ : ℝ → ℂ}
    (h : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ ξ * (starRingEnd ℂ) (φ ξ))) (Ioi 0)) :
    IntegrableOn (fun ξ => Real.sinh ξ * ‖φ ξ‖ ^ 2) (Ioi 0) := by
  have hn : IntegrableOn (fun ξ => ‖((Real.sinh ξ : ℝ) : ℂ) * (φ ξ * (starRingEnd ℂ) (φ ξ))‖) (Ioi 0) := h.norm
  exact hn.congr_fun (fun ξ hξ => norm_sinh_mul_conj hξ) measurableSet_Ioi

lemma integrableOn_sinh_norm_add_sq {φ₁ φ₂ : ℝ → ℂ} (t : ℂ)
    (h11 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₁ ξ))) (Ioi 0))
    (h12 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₁ ξ * (starRingEnd ℂ) (φ₂ ξ))) (Ioi 0))
    (h21 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₁ ξ))) (Ioi 0))
    (h22 : IntegrableOn (fun ξ => ((Real.sinh ξ : ℝ) : ℂ) * (φ₂ ξ * (starRingEnd ℂ) (φ₂ ξ))) (Ioi 0)) :
    IntegrableOn (fun ξ => Real.sinh ξ * ‖φ₁ ξ + t * φ₂ ξ‖ ^ 2) (Ioi 0) := by
  have hc : IntegrableOn (fun ξ => (((Real.sinh ξ * ‖φ₁ ξ + t * φ₂ ξ‖ ^ 2 : ℝ)) : ℂ)) (Ioi 0) := by
    have := ((h11.add (h12.const_mul ((starRingEnd ℂ) t))).add (h21.const_mul t)).add
      (h22.const_mul (t * (starRingEnd ℂ) t))
    refine this.congr_fun (fun ξ _ => ?_) measurableSet_Ioi
    exact (ofReal_sinh_norm_add_sq _ _ _ _).symm
  have hre : IntegrableOn (fun ξ => ((((Real.sinh ξ * ‖φ₁ ξ + t * φ₂ ξ‖ ^ 2 : ℝ)) : ℂ)).re) (Ioi 0) := hc.re
  exact hre.congr_fun (fun ξ _ => Complex.ofReal_re _) measurableSet_Ioi

/-- **The Pythagoras identity** `∫|u + t u'|² = ∫|u|² + ∫|t u'|²` for coefficients of two series with
equal `K × K`-weights and `n ≠ n'`, `|t| = 1`; hence `Re ∫ u conj(t u') = 0`. -/
theorem re_integral_uFun_conj_zero {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (hne : n ≠ n') (p p' : ℕ × ℕ)
    (hw1 : n + 2 * p.1 = n' + 2 * p'.1) (hw2 : n + 2 * p.2 = n' + 2 * p'.2) {t : ℂ} (ht : ‖t‖ = 1) :
    (∫ g, uFun hn p g * (starRingEnd ℂ) (t * uFun hn' p' g) ∂haarR).re = 0 := by
  have hw : kkWeight n p.1 p.2 = kkWeight n' p'.1 p'.2 := by
    unfold kkWeight; rw [hw1, hw2]
  have h11 := integrableOn_phiRad_prod hn hn p p
  have h12 := integrableOn_phiRad_prod hn hn' p p'
  have h21 := integrableOn_phiRad_prod hn' hn p' p
  have h22 := integrableOn_phiRad_prod hn' hn' p' p'
  have hcross := radial_cross_eq_zero hn hn' hne p p' hw1 hw2
  have hrad := radial_pythag h11 h12 h21 h22 hcross ht
  have hFt : Continuous fun g => uFun hn p g + t * uFun hn' p' g :=
    (continuous_uFun hn p).add (continuous_const.mul (continuous_uFun hn' p'))
  have hprof : ∀ (ξ : ℝ) (x : Fin 2 → ℝ), kkProfile (fun g => uFun hn p g + t * uFun hn' p' g) ξ x =
      Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n p.1 p.2) i : ℂ) * (x i : ℂ))) *
        (phiRad hn p ξ + t * phiRad hn' p' ξ) := by
    intro ξ x
    have e1 := kkProfile_uFun hn p ξ x
    have e2 := kkProfile_uFun hn' p' ξ x
    rw [← hw] at e2
    unfold kkProfile at e1 e2 ⊢
    simp only [e1, e2]
    ring
  have hA := integral_norm_sq_block hFt (kkWeight n p.1 p.2) _ hprof
    (integrableOn_sinh_norm_add_sq t h11 h12 h21 h22)
  have hB := integral_norm_sq_block (continuous_uFun hn p) (kkWeight n p.1 p.2) (phiRad hn p)
    (kkProfile_uFun hn p) (integrableOn_sinh_norm_sq h11)
  have hC := integral_norm_sq_block (continuous_uFun hn' p') (kkWeight n p.1 p.2) (phiRad hn' p')
    (fun ξ x => by rw [hw]; exact kkProfile_uFun hn' p' ξ x) (integrableOn_sinh_norm_sq h22)
  refine integral_re_eq_zero_of_pythag (memLp_uFun hn p) ((memLp_uFun hn' p').const_mul t) ?_
  have hnt : ∀ g, ‖t * uFun hn' p' g‖ ^ 2 = ‖uFun hn' p' g‖ ^ 2 := by
    intro g; rw [norm_mul, ht, one_mul]
  simp_rw [hnt]
  rw [hA, hB, hC, hrad]
  ring

/-- **The normalised matrix coefficients of `D_n⁺` and `D_{n'}⁺` are orthogonal for `n ≠ n'`.** -/
theorem inner_uLp_uLp_ne {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (hne : n ≠ n') (p p' : ℕ × ℕ) :
    ⟪uLp hn p, uLp hn' p'⟫_ℂ = 0 := by
  have hae : ∀ᵐ g ∂haarR, ⟪(uLp hn p : SL2R → ℂ) g, (uLp hn' p' : SL2R → ℂ) g⟫_ℂ =
      (starRingEnd ℂ) (uFun hn p g * (starRingEnd ℂ) (uFun hn' p' g)) := by
    filter_upwards [(memLp_uFun hn p).coeFn_toLp, (memLp_uFun hn' p').coeFn_toLp] with g h1 h2
    simp only [uLp]
    rw [h1, h2]
    simp [RCLike.inner_apply]
    ring
  rw [L2.inner_def, integral_congr_ae hae, integral_conj]
  suffices hZ : ∫ g, uFun hn p g * (starRingEnd ℂ) (uFun hn' p' g) ∂haarR = 0 by
    rw [hZ]; simp
  by_cases hblock : n + 2 * p.1 = n' + 2 * p'.1 ∧ n + 2 * p.2 = n' + 2 * p'.2
  · have h1 := re_integral_uFun_conj_zero hn hn' hne p p' hblock.1 hblock.2 (t := 1) (by simp)
    have h2 := re_integral_uFun_conj_zero hn hn' hne p p' hblock.1 hblock.2 (t := Complex.I) (by simp)
    simp only [one_mul] at h1
    have e : ∫ g, uFun hn p g * (starRingEnd ℂ) (Complex.I * uFun hn' p' g) ∂haarR =
        -Complex.I * ∫ g, uFun hn p g * (starRingEnd ℂ) (uFun hn' p' g) ∂haarR := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [map_mul, Complex.conj_I]
      ring
    rw [e] at h2
    apply Complex.ext
    · simpa using h1
    · simpa using h2
  · have h := not_and_or.1 hblock
    have := integral_mcoef_orth_gen hn hn' (j := p.1) (l := p.2) (j' := p'.1) (l' := p'.2) (by tauto)
    have e : ∀ g, uFun hn p g * (starRingEnd ℂ) (uFun hn' p' g) =
        ((uConst hn p * uConst hn' p' : ℝ) : ℂ) *
          (mcoef n (kClass hn p.1) (kClass hn p.2) g *
            (starRingEnd ℂ) (mcoef n' (kClass hn' p'.1) (kClass hn' p'.2) g)) := by
      intro g
      simp only [uFun, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    simp_rw [e]
    rw [integral_const_mul, this, mul_zero]

/-- **The radial norm of the normalised coefficient**: `∫_0^∞ sinh ξ |u_p(a(ξ))|² dξ = 1/(2π)²`. -/
theorem integral_sinh_norm_sq_phiRad {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) :
    ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖phiRad hn p ξ‖ ^ 2 = 1 / (2 * π) ^ 2 := by
  have h := integral_norm_sq_block (continuous_uFun hn p) (kkWeight n p.1 p.2) (phiRad hn p)
    (kkProfile_uFun hn p) (integrableOn_sinh_norm_sq (integrableOn_phiRad_prod hn hn p p))
  rw [integral_norm_sq_uFun hn p] at h
  have hpi : (2 * π) ^ 2 ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

/-- **The `L²((0,∞), sinh)`-norm of the radial matrix coefficient of the discrete series**:
`∫_0^∞ sinh ξ |⟨e_j, D_n(a(ξ)) e_l⟩|² dξ = 2 ‖e_j‖² ‖e_l‖² / (n - 1)`. -/
theorem integral_sinh_norm_sq_mcoef_aR {n : ℕ} (hn : 2 ≤ n) (j l : ℕ) :
    ∫ ξ in Ioi (0 : ℝ), Real.sinh ξ * ‖mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2 =
      2 * ‖kClass hn j‖ ^ 2 * ‖kClass hn l‖ ^ 2 / ((n : ℝ) - 1) := by
  have h := integral_sinh_norm_sq_phiRad hn (j, l)
  have hu : 0 < uConst hn (j, l) := uConst_pos hn (j, l)
  have e : ∀ ξ : ℝ, Real.sinh ξ * ‖phiRad hn (j, l) ξ‖ ^ 2 =
      uConst hn (j, l) ^ 2 * (Real.sinh ξ * ‖mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2) := by
    intro ξ
    unfold phiRad
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    ring
  simp_rw [e] at h
  rw [integral_const_mul] at h
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hej := norm_kClass_pos hn j
  have hel := norm_kClass_pos hn l
  have hsr := schurRatio_eq hn
  have hsq : uConst hn (j, l) ^ 2 = (schurRatio hn * ‖kClass hn j‖ ^ 2 * ‖kClass hn l‖ ^ 2)⁻¹ := by
    unfold uConst
    simp only
    rw [inv_pow, mul_pow, mul_pow, Real.sq_sqrt (schurRatio_pos hn).le]
  rw [hsq] at h
  have hpi : 0 < π := Real.pi_pos
  rw [hsr] at h
  have hd : (8 * π ^ 2 / ((n : ℝ) - 1)) * ‖kClass hn j‖ ^ 2 * ‖kClass hn l‖ ^ 2 ≠ 0 := by positivity
  field_simp at h ⊢
  nlinarith [h]

end Lightlike.Lorentz.SL2RPlancherel

import Lightlike.Asymptotics.Valley
import Lightlike.Asymptotics.Landing
import Lightlike.Oscillatory.LaplaceRay

/-!
# Descent paths from opposite valleys land at different points

Let `ψ` be the continued phase of Racah's sum (`phaseC`), `s` the saddle point of a Euclidean
tetrahedron and `D = Re ψ s`. The valley step (`exists_valley`) gives two valleys at `s`: rays
`t ↦ s + t v` with `v = valleyDir u₀ ε τ`, `ε = ±1`, along which `Re ψ` falls like `‖b‖ t² / 4`
and `ψ` follows `ψ s + b v² t²` up to `K t³`. The descent step (`exists_descent`) continues the
end point `s + r v` of a valley ray by a descent path, which lands on the real axis.

**Main theorem (`IsEuclid.not_landing_eq`).** A descent path from the end point of a ray in the
valley `ε = 1` and one from the end point of a ray in the valley `ε = −1` never land at the same
point.

## Proof

Suppose both land at `p`. Cut the two descent paths shortly before `p`, at points `w₁`, `w₂`
within `ρ` of `p`, where `Re ψ ≤ D − δ/2` by continuity (`δ = ‖b‖ r² / 4`). The two valley
rays, the two cut paths and the segment `[w₁, w₂]` lie in a disc inside the open upper
half-plane, on which `e^{Nψ}` has a primitive `F` (Morera, `DifferentiableOn.isExactOn_ball`).
Then `F z₁ − F z₂` (with `z₁`, `z₂` the ends of the rays) can be computed in two ways:

* through `s`, it is `e^{Nψ s}` times the difference of two Laplace integrals along the rays.
  By Laplace's method on a ray (`Lightlike.Oscillatory.laplace_ray_uniform`), each is `±u₀ √(π/(N‖b‖)) / 2` up to
  `C/N`. The two half-Gaussians add rather than cancel, because `v / √(−b v²) = ε u₀ / √‖b‖`
  changes sign between the valleys. So `‖F z₁ − F z₂‖ ≥ e^{ND} (√(π/(N‖b‖)) − 2C/N)`;
* through `w₁` and `w₂`, the descent paths and the segment run where `Re ψ ≤ D − δ/2`, so
  `‖F z₁ − F z₂‖ ≤ e^{N(D − δ/2)} Q` with `Q` independent of `N`.

For large `N` the first bound, of order `e^{ND} N^{−1/2}`, exceeds the second, which is
exponentially smaller. This is the closing argument of the steepest-descent proof of the
Ponzano–Regge formula; no winding numbers or Jordan curve theorem are needed, only a primitive
on a disc.

## Laplace's method

The uniform Laplace bound on a ray is `Lightlike.Oscillatory.laplace_ray_uniform`
(`Lightlike/Oscillatory/LaplaceRay.lean`): for `Re a ≥ α > 0` and the bounds
`‖φ t + a t²/2‖ ≤ M t³`, `Re φ t ≤ −c t²`, the error of the half-Gaussian leading term is at most
`C / N` with `C` depending only on `r, α, M, c, K, G`. That uniformity is what lets one constant
serve every tilt `τ` of the valley rays.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace Lightlike.Asymptotics

/-! ## A disc in the upper half-plane -/

/-- Every compact subset of the open upper half-plane lies in an open disc inside it. For
`‖z‖ ≤ R` and `Im z ≥ m > 0` on the set, the disc of centre `iY`, `Y = (R² + m²)/m`, and radius
`Y − m/2` works. -/
lemma exists_ball_superset_of_isCompact {S : Set ℂ} (hS : IsCompact S)
    (hH : ∀ z ∈ S, 0 < z.im) :
    ∃ (c : ℂ) (R : ℝ), Metric.ball c R ⊆ {z : ℂ | 0 < z.im} ∧ S ⊆ Metric.ball c R := by
  obtain ⟨R, m, hR, hm, hRm⟩ : ∃ R m : ℝ, 0 ≤ R ∧ 0 < m ∧ ∀ z ∈ S, ‖z‖ ≤ R ∧ m ≤ z.im := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 1, le_rfl, one_pos, fun z hz => hz.elim⟩
    obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨z₀, hz₀, hmin⟩ := hS.exists_isMinOn hne continuous_im.continuousOn
    obtain ⟨z, hz⟩ := hne
    exact ⟨R, z₀.im, (norm_nonneg _).trans (hR z hz), hH z₀ hz₀,
      fun w hw => ⟨hR w hw, hmin hw⟩⟩
  set Y : ℝ := (R ^ 2 + m ^ 2) / m with hY
  have hYm : Y * m = R ^ 2 + m ^ 2 := by rw [hY]; field_simp
  have hY0 : m ≤ Y := by
    rw [hY, le_div_iff₀ hm]; nlinarith
  refine ⟨Y * I, Y - m / 2, fun w hw => ?_, fun z hz => ?_⟩
  · have h1 := abs_im_le_norm (w - Y * I)
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h2 : (w - Y * I).im = w.im - Y := by simp
    rw [h2] at h1
    show 0 < w.im
    have := neg_abs_le (w.im - Y)
    linarith
  · obtain ⟨hzR, hzm⟩ := hRm z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hsq : ‖z - Y * I‖ ^ 2 = ‖z‖ ^ 2 - 2 * Y * z.im + Y ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
      simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        sub_im, mul_im, add_zero]
      ring
    have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR 2
    have hlt : ‖z - Y * I‖ ^ 2 < (Y - m / 2) ^ 2 := by
      rw [hsq]; nlinarith
    by_contra hc
    have hc' := not_lt.1 hc
    have hpos : 0 ≤ Y - m / 2 := by linarith
    nlinarith [mul_le_mul hc' hc' hpos (norm_nonneg _)]

/-! ## Integrals of a primitive along a ray and along a descent path -/

/-- **A primitive along a ray.** If `F' = f` on `U` and the ray `t ↦ s + t v`, `t ∈ [0, r]`,
lies in `U`, then `F (s + r v) − F s = ∫₀ʳ f (s + t v) v dt`. -/
lemma primitive_sub_eq_integral {f F : ℂ → ℂ} {U : Set ℂ}
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) {s v : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hU : ∀ t ∈ Icc (0 : ℝ) r, s + t * v ∈ U)
    (hf : ContinuousOn (fun t : ℝ => f (s + t * v)) (Icc 0 r)) :
    F (s + r * v) - F s = ∫ t in (0 : ℝ)..r, f (s + t * v) * v := by
  have hd : ∀ t ∈ uIcc 0 r, HasDerivAt (fun t : ℝ => F (s + t * v)) (f (s + t * v) * v) t := by
    intro t ht
    rw [uIcc_of_le hr] at ht
    have h1 : HasDerivAt (fun t : ℝ => s + (t : ℂ) * v) v t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const v).const_add s
    exact (hF _ (hU t ht)).comp t h1
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hf.mul continuousOn_const).intervalIntegrable_of_Icc hr)
  simp only [ofReal_zero, zero_mul, add_zero] at this
  exact this.symm

/-- **A primitive of `e^{Nψ}` along a descent path.** Let `α` be a descent path from `z₀` on
`[0, T)`, `t₁ ∈ [0, T)`, and `F' = e^{Nψ}` (`N ≥ 0`) on a set containing `α [0, t₁]`. If the
speed `‖−1/ψ'‖` is at most `S` on `α [0, t₁]`, then
`‖F (α t₁) − F z₀‖ ≤ e^{N Re ψ z₀} S t₁`, since `Re ψ` falls along the path. -/
theorem IsEuclid.norm_primitive_lift_sub_le {l : Fin 6 → ℝ} (h : IsEuclid l) {F : ℂ → ℂ}
    {U : Set ℂ} {N : ℝ} (hN : 0 ≤ N)
    (hF : ∀ z ∈ U, HasDerivAt F (cexp (N * phaseC (faceSum l) (quadSum l) z)) z)
    {z₀ : ℂ} {T t₁ S : ℝ} {α : ℝ → ℂ}
    (hα : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α)
    (ht₁ : t₁ ∈ Ico 0 T) (hU : ∀ t ∈ Icc 0 t₁, α t ∈ U)
    (hS : ∀ t ∈ Icc 0 t₁, ‖descentField (faceSum l) (quadSum l) (α t)‖ ≤ S) :
    ‖F (α t₁) - F z₀‖ ≤ Real.exp (N * (phaseC (faceSum l) (quadSum l) z₀).re) * S * t₁ := by
  have hsub : ∀ t ∈ Icc 0 t₁, t ∈ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt ht₁.2⟩
  have hαc : ContinuousOn α (Icc 0 t₁) := fun t ht =>
    ((hα.deriv t (hsub t ht)).continuousWithinAt).mono (fun u hu => hsub u hu)
  have hψ := h.phaseC_lift hα
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun t => F (α t))
    (f' := fun t => cexp (N * phaseC (faceSum l) (quadSum l) (α t)) *
      descentField (faceSum l) (quadSum l) (α t)) (C := Real.exp (N *
        (phaseC (faceSum l) (quadSum l) z₀).re) * S)
    (fun t ht => (hF _ (hU t ht)).continuousAt.comp_continuousWithinAt (hαc t ht))
    (fun t ht => by
      have ht' : t ∈ Ico 0 T := hsub t (Ico_subset_Icc_self ht)
      exact (hF _ (hU t (Ico_subset_Icc_self ht))).comp_hasDerivWithinAt t
        ((hα.deriv t ht').mono_of_mem_nhdsWithin (Ico_mem_nhdsGE_of_mem' ht')))
    (fun t ht => by
      have ht' : t ∈ Ico 0 T := hsub t (Ico_subset_Icc_self ht)
      rw [norm_mul, norm_exp, re_ofReal_mul, hψ t ht', sub_re, ofReal_re]
      have hS0 : 0 ≤ ‖descentField (faceSum l) (quadSum l) (α t)‖ := norm_nonneg _
      refine mul_le_mul (Real.exp_le_exp.2 ?_) (hS t (Ico_subset_Icc_self ht)) hS0
        (Real.exp_pos _).le
      nlinarith [ht.1])
    t₁ ⟨ht₁.1, le_rfl⟩
  simpa [hα.start] using key

/-! ## Laplace's method along the valley rays -/

/-- **Laplace's method along the valley rays** (from `Lightlike.Oscillatory.laplace_ray_uniform`). Along every
valley ray `t ↦ s + t v`, `v = valleyDir u₀ ε τ`, with the bounds of `exists_valley`,
`‖∫₀ʳ v e^{N(ψ(s + t v) − ψ s)} dt − ε u₀ √(π/(N‖b‖)) / 2‖ ≤ C / N` for all `N > 0`, with one
`C` for all `ε = ±1` and `|τ| ≤ 1/2`. The leading term does not depend on the tilt `τ`:
`N b v² = −N‖b‖ (1 + iτ)²`, so `(π / (−N b v²))^{1/2} = √(π/(N‖b‖)) / (1 + iτ)`. -/
theorem laplace_valley (A : Fin 4 → ℝ) (B : Fin 3 → ℝ)
    {s b u₀ : ℂ} {K r : ℝ} (hb0 : b ≠ 0) (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖)
    (hr : 0 < r)
    (hray : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (s + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
          b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
      (phaseC A B (s + t * valleyDir u₀ ε τ)).re ≤ (phaseC A B s).re - ‖b‖ / 4 * t ^ 2) :
    ∃ C : ℝ, ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ N : ℝ, 0 < N →
      ‖(∫ t in (0 : ℝ)..r, valleyDir u₀ ε τ *
          cexp (N * (phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s))) -
        ε * u₀ * (Real.sqrt (π / (N * ‖b‖)) : ℂ) / 2‖ ≤ C / N := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  obtain ⟨C, hC⟩ :=
    Lightlike.Oscillatory.laplace_ray_uniform r ‖b‖ K (‖b‖ / 4) 0 (3 / 2) hr hbn (by positivity)
  refine ⟨C, fun ε hε τ hτ N hN => ?_⟩
  have hv2 := mul_valleyDir_sq hbu hε τ
  have hτ2 : τ ^ 2 ≤ 1 / 4 := by
    have := sq_abs τ
    nlinarith [abs_nonneg τ]
  have ha : -2 * b * valleyDir u₀ ε τ ^ 2 =
      ((2 * ‖b‖ * (1 - τ ^ 2) : ℝ) : ℂ) + ((4 * ‖b‖ * τ : ℝ) : ℂ) * I := by
    push_cast; linear_combination (-2 : ℂ) * hv2
  have key := hC (-2 * b * valleyDir u₀ ε τ ^ 2)
    (fun t => phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s) (fun _ => valleyDir u₀ ε τ)
    (by rw [ha, add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]; nlinarith)
    (((continuousOn_phaseC A B).comp (by fun_prop : Continuous fun t : ℝ =>
      s + t * valleyDir u₀ ε τ).continuousOn
        (fun t ht => (hray ε hε τ hτ t ht).1.le)).sub continuousOn_const)
    continuousOn_const
    (fun t ht => by
      have := (hray ε hε τ hτ t ht).2.1
      convert this using 2; ring)
    (fun t ht => by
      have := (hray ε hε τ hτ t ht).2.2
      rw [sub_re]; linarith)
    (fun t _ => by simp)
    (norm_valleyDir_le hu hε hτ) N hN
  -- the leading term
  have hx : 0 < π / (N * ‖b‖) := by positivity
  set q : ℝ := Real.sqrt (π / (N * ‖b‖)) with hqdef
  have hq2 : (q : ℂ) ^ 2 = (π : ℂ) / (N * ‖b‖) := by
    rw [← ofReal_pow, hqdef, Real.sq_sqrt hx.le]; push_cast; ring
  have h1τ : (1 + (τ : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg re h0
    simp at this
  set w : ℂ := (q : ℂ) / (1 + τ * I) with hwdef
  have hw : w = ((q / (1 + τ ^ 2) : ℝ) : ℂ) * (1 - τ * I) := by
    have e : (1 - (τ : ℂ) * I) * (1 + τ * I) = 1 + (τ : ℂ) ^ 2 := by
      linear_combination (-(τ : ℂ) ^ 2) * I_sq
    have h2 : (1 + (τ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity : (1 + τ ^ 2 : ℝ) ≠ 0)
    rw [hwdef, div_eq_iff h1τ, mul_assoc, e]
    push_cast
    field_simp
  have hwre : 0 < w.re := by
    rw [hw, re_ofReal_mul]
    simp only [sub_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, sub_zero]
    positivity
  have harg := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hwre))
  have e1 : (N : ℂ) * (-2 * b * valleyDir u₀ ε τ ^ 2) / 2 = N * ‖b‖ * (1 + τ * I) ^ 2 := by
    linear_combination (-(N : ℂ)) * hv2 - ((N : ℂ) * ‖b‖ * τ ^ 2) * I_sq
  have hsq : (π : ℂ) / (N * (-2 * b * valleyDir u₀ ε τ ^ 2) / 2) = w ^ 2 := by
    rw [e1, hwdef, div_pow, hq2, div_div]
  have hhalf : (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ := by norm_num
  have hroot : ((π : ℂ) / (N * (-2 * b * valleyDir u₀ ε τ ^ 2) / 2)) ^ (1 / 2 : ℂ) = w := by
    rw [hsq, hhalf]
    exact pow_cpow_nat_inv two_ne_zero (by push_cast; linarith) (by push_cast; linarith)
  have hlead : valleyDir u₀ ε τ * (w / 2) = ε * u₀ * (q : ℂ) / 2 := by
    rw [hwdef, valleyDir]
    field_simp
  simp only [hroot, hlead] at key
  exact key

/-! ## Opposite valleys land at different points -/

/-- **Descent paths from opposite valleys land at different points.** Let `l` be a
Euclidean tetrahedron with saddle `s`, and let `b, u₀, K, r`
satisfy the valley bounds of `IsEuclid.exists_valley`. Let `α₁` be a descent path from the end
point `s + r v₁` of a ray in the valley `ε = 1`, and `α₂` one from the end point `s + r v₂` of
a ray in the valley `ε = −1` (any tilts `|τ₁|, |τ₂| ≤ 1/2`). Then `α₁` and `α₂` do not
converge to the same real point.

The proof compares two evaluations of `F z₁ − F z₂` for a primitive `F` of `e^{Nψ}` on a disc
inside the upper half-plane (see the module docstring). -/
theorem IsEuclid.not_landing_eq {l : Fin 6 → ℝ} (h : IsEuclid l)
    {b u₀ : ℂ} {K r : ℝ} (hb0 : b ≠ 0) (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖)
    (hr : 0 < r)
    (hray : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (saddle l + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ) -
          phaseC (faceSum l) (quadSum l) (saddle l) - b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤
        K * t ^ 3 ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖b‖ / 4 * t ^ 2)
    {τ₁ τ₂ T₁ T₂ : ℝ} (hτ₁ : |τ₁| ≤ 1 / 2) (hτ₂ : |τ₂| ≤ 1 / 2) {α₁ α₂ : ℝ → ℂ} {p : ℝ}
    (hα₁ : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
      (saddle l + r * valleyDir u₀ 1 τ₁) T₁ α₁)
    (hα₂ : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
      (saddle l + r * valleyDir u₀ (-1) τ₂) T₂ α₂)
    (h₁ : Tendsto α₁ (𝓝[<] T₁) (𝓝 (p : ℂ))) (h₂ : Tendsto α₂ (𝓝[<] T₂) (𝓝 (p : ℂ))) :
    False := by
  set ψ := phaseC (faceSum l) (quadSum l) with hψdef
  set s := saddle l with hsdef
  set D := (ψ s).re with hD
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  set δ : ℝ := ‖b‖ / 4 * r ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hε₁ : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hε₂ : (-1 : ℝ) ^ 2 = 1 := by norm_num
  have hrI : r ∈ Icc (0 : ℝ) r := ⟨hr.le, le_rfl⟩
  have hz₁ : (ψ (s + r * valleyDir u₀ 1 τ₁)).re ≤ D - δ := (hray 1 hε₁ τ₁ hτ₁ r hrI).2.2
  have hz₂ : (ψ (s + r * valleyDir u₀ (-1) τ₂)).re ≤ D - δ := (hray (-1) hε₂ τ₂ hτ₂ r hrI).2.2
  have hψ₁ : ∀ t ∈ Ico 0 T₁, ψ (α₁ t) = ψ (s + r * valleyDir u₀ 1 τ₁) - t := h.phaseC_lift hα₁
  -- the landing point lies below the level `D − δ`
  have hcont : ContinuousWithinAt ψ {z : ℂ | 0 ≤ z.im} (p : ℂ) :=
    continuousOn_phaseC _ _ _ (by simp)
  have hp : (ψ p).re ≤ D - δ := by
    have hin : ∀ᶠ t in 𝓝[<] T₁, α₁ t ∈ {z : ℂ | 0 ≤ z.im} := by
      filter_upwards [Ico_mem_nhdsLT hα₁.pos] with t ht using (hα₁.mem t ht).1.le
    have ht : Tendsto (fun t => (ψ (α₁ t)).re) (𝓝[<] T₁) (𝓝 (ψ p).re) :=
      (continuous_re.tendsto _).comp (hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h₁, hin⟩))
    refine le_of_tendsto ht ?_
    filter_upwards [Ico_mem_nhdsLT hα₁.pos] with t ht
    rw [hψ₁ t ht, sub_re, ofReal_re]
    linarith [ht.1]
  -- a half-disc around `p` below the level `D − δ/2`
  obtain ⟨ρ, hρ, hρψ⟩ : ∃ ρ > 0, ∀ z : ℂ, 0 ≤ z.im → dist z p < ρ → (ψ z).re < D - δ / 2 := by
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousWithinAt_iff.1 hcont (δ / 2) (by positivity)
    refine ⟨ρ, hρ, fun z hz hzp => ?_⟩
    have h1 := hρ' (x := z) hz hzp
    rw [dist_eq_norm] at h1
    have h2 := abs_re_le_norm (ψ z - ψ p)
    rw [sub_re] at h2
    linarith [le_abs_self ((ψ z).re - (ψ p).re)]
  -- cut the descent paths inside that half-disc
  obtain ⟨t₁, ht₁, hw₁⟩ := Filter.nonempty_of_mem
    (Filter.inter_mem (Ico_mem_nhdsLT hα₁.pos) (h₁ (Metric.ball_mem_nhds _ hρ)))
  obtain ⟨t₂, ht₂, hw₂⟩ := Filter.nonempty_of_mem
    (Filter.inter_mem (Ico_mem_nhdsLT hα₂.pos) (h₂ (Metric.ball_mem_nhds _ hρ)))
  have hw₁' : dist (α₁ t₁) p < ρ := hw₁
  have hw₂' : dist (α₂ t₂) p < ρ := hw₂
  -- the compact set of all pieces and a disc around it
  have hsub₁ : ∀ t ∈ Icc 0 t₁, t ∈ Ico 0 T₁ := fun t ht => ⟨ht.1, ht.2.trans_lt ht₁.2⟩
  have hsub₂ : ∀ t ∈ Icc 0 t₂, t ∈ Ico 0 T₂ := fun t ht => ⟨ht.1, ht.2.trans_lt ht₂.2⟩
  have hαc₁ : ContinuousOn α₁ (Icc 0 t₁) := fun t ht =>
    ((hα₁.deriv t (hsub₁ t ht)).continuousWithinAt).mono (fun u hu => hsub₁ u hu)
  have hαc₂ : ContinuousOn α₂ (Icc 0 t₂) := fun t ht =>
    ((hα₂.deriv t (hsub₂ t ht)).continuousWithinAt).mono (fun u hu => hsub₂ u hu)
  set S : Set ℂ := (fun t : ℝ => s + t * valleyDir u₀ 1 τ₁) '' Icc 0 r ∪
    (fun t : ℝ => s + t * valleyDir u₀ (-1) τ₂) '' Icc 0 r ∪ α₁ '' Icc 0 t₁ ∪ α₂ '' Icc 0 t₂
  have hSc : IsCompact S :=
    (((isCompact_Icc.image (by fun_prop)).union (isCompact_Icc.image (by fun_prop))).union
      (isCompact_Icc.image_of_continuousOn hαc₁)).union (isCompact_Icc.image_of_continuousOn hαc₂)
  have hSH : ∀ z ∈ S, 0 < z.im := by
    rintro z (((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact (hray 1 hε₁ τ₁ hτ₁ t ht).1
    · exact (hray (-1) hε₂ τ₂ hτ₂ t ht).1
    · exact (hα₁.mem t (hsub₁ t ht)).1
    · exact (hα₂.mem t (hsub₂ t ht)).1
  obtain ⟨c, R, hBH, hSB⟩ := exists_ball_superset_of_isCompact hSc hSH
  -- speed bounds along the cut descent paths
  have hspeed : ∀ {z₀ : ℂ} {T t₁ : ℝ} {α : ℝ → ℂ},
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α → t₁ ∈ Ico 0 T →
      ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Icc 0 t₁, ‖descentField (faceSum l) (quadSum l) (α t)‖ ≤ S := by
    intro z₀ T t₁ α hα ht₁
    have hsub : ∀ t ∈ Icc 0 t₁, t ∈ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt ht₁.2⟩
    have hαc : ContinuousOn α (Icc 0 t₁) := fun t ht =>
      ((hα.deriv t (hsub t ht)).continuousWithinAt).mono (fun u hu => hsub u hu)
    obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun t =>
      descentField (faceSum l) (quadSum l) (α t)) (fun t ht =>
        ((h.contDiffAt_descentField (hα.mem t (hsub t ht))).continuousAt).comp_continuousWithinAt
          (hαc t ht))
    exact ⟨S, (norm_nonneg _).trans (hS 0 ⟨le_rfl, ht₁.1⟩), hS⟩
  obtain ⟨S₁, hS₁0, hS₁⟩ := hspeed hα₁ ht₁
  obtain ⟨S₂, hS₂0, hS₂⟩ := hspeed hα₂ ht₂
  -- Laplace along the two valley rays
  obtain ⟨C, hC⟩ := laplace_valley (faceSum l) (quadSum l) hb0 hu hbu hr hray
  set Q : ℝ := S₁ * t₁ + S₂ * t₂ + 2 * ρ with hQ
  -- the inequality for each `N`
  have main : ∀ N : ℝ, 0 < N →
      Real.sqrt (π / (N * ‖b‖)) - 2 * C / N ≤ Real.exp (-(δ / 2) * N) * Q := by
    intro N hN
    have hdiff : DifferentiableOn ℂ (fun z => cexp (N * ψ z)) (Metric.ball c R) := fun z hz =>
      (((hasDerivAt_phaseC _ _ (hBH hz)).differentiableAt.const_mul (N : ℂ)).cexp)
        |>.differentiableWithinAt
    obtain ⟨F, hF⟩ := hdiff.isExactOn_ball
    -- the two valley rays
    have hrayF : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 →
        (∀ t ∈ Icc (0 : ℝ) r, s + t * valleyDir u₀ ε τ ∈ Metric.ball c R) →
        F (s + r * valleyDir u₀ ε τ) - F s = cexp (N * ψ s) *
          ∫ t in (0 : ℝ)..r, valleyDir u₀ ε τ *
            cexp (N * (ψ (s + t * valleyDir u₀ ε τ) - ψ s)) := by
      intro ε hε τ hτ hin
      rw [primitive_sub_eq_integral hF hr.le hin
        (((continuous_exp.comp_continuousOn ((continuousOn_phaseC _ _).comp
          (by fun_prop : Continuous fun t : ℝ => s + t * valleyDir u₀ ε τ).continuousOn
          (fun t ht => (hray ε hε τ hτ t ht).1.le) |>.const_smul (N : ℂ)))))]
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      have : cexp (N * ψ (s + t * valleyDir u₀ ε τ)) =
          cexp (N * ψ s) * cexp (N * (ψ (s + t * valleyDir u₀ ε τ) - ψ s)) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [this]; ring
    have e₁ := hrayF 1 hε₁ τ₁ hτ₁ fun t ht => hSB (Or.inl (Or.inl (Or.inl ⟨t, ht, rfl⟩)))
    have e₂ := hrayF (-1) hε₂ τ₂ hτ₂ fun t ht => hSB (Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩)))
    -- the lower bound through the saddle
    set q : ℝ := Real.sqrt (π / (N * ‖b‖)) with hq
    have hL₁ := hC 1 hε₁ τ₁ hτ₁ N hN
    have hL₂ := hC (-1) hε₂ τ₂ hτ₂ N hN
    set I₁ := ∫ t in (0 : ℝ)..r, valleyDir u₀ 1 τ₁ *
      cexp (N * (ψ (s + t * valleyDir u₀ 1 τ₁) - ψ s))
    set I₂ := ∫ t in (0 : ℝ)..r, valleyDir u₀ (-1) τ₂ *
      cexp (N * (ψ (s + t * valleyDir u₀ (-1) τ₂) - ψ s))
    have hlow : q - 2 * C / N ≤ ‖I₁ - I₂‖ := by
      set E₁ := I₁ - ((1 : ℝ) : ℂ) * u₀ * q / 2 with hE₁
      set E₂ := I₂ - ((-1 : ℝ) : ℂ) * u₀ * q / 2 with hE₂
      have hsplit : I₁ - I₂ = u₀ * q + (E₁ - E₂) := by rw [hE₁, hE₂]; push_cast; ring
      have hq0 : ‖u₀ * (q : ℂ)‖ = q := by
        rw [norm_mul, hu, one_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      have h3 := norm_sub_norm_le (u₀ * (q : ℂ)) (-(E₁ - E₂))
      rw [sub_neg_eq_add, norm_neg] at h3
      have h4 := norm_sub_le E₁ E₂
      rw [hsplit]
      have : 2 * C / N = C / N + C / N := by ring
      linarith
    have hX : ‖F (s + r * valleyDir u₀ 1 τ₁) - F (s + r * valleyDir u₀ (-1) τ₂)‖ =
        Real.exp (N * D) * ‖I₁ - I₂‖ := by
      rw [show F (s + r * valleyDir u₀ 1 τ₁) - F (s + r * valleyDir u₀ (-1) τ₂) =
        (F (s + r * valleyDir u₀ 1 τ₁) - F s) - (F (s + r * valleyDir u₀ (-1) τ₂) - F s) by ring,
        e₁, e₂, ← mul_sub, norm_mul, norm_exp, re_ofReal_mul]
    -- the upper bound through the descent paths and the connecting segment
    have hmemB₁ : ∀ t ∈ Icc 0 t₁, α₁ t ∈ Metric.ball c R := fun t ht =>
      hSB (Or.inl (Or.inr ⟨t, ht, rfl⟩))
    have hmemB₂ : ∀ t ∈ Icc 0 t₂, α₂ t ∈ Metric.ball c R := fun t ht =>
      hSB (Or.inr ⟨t, ht, rfl⟩)
    have hlift₁ := h.norm_primitive_lift_sub_le hN.le hF hα₁ ht₁ hmemB₁ hS₁
    have hlift₂ := h.norm_primitive_lift_sub_le hN.le hF hα₂ ht₂ hmemB₂ hS₂
    have hconn : ‖F (α₂ t₂) - F (α₁ t₁)‖ ≤ Real.exp (N * (D - δ / 2)) * (2 * ρ) := by
      have hconv : Convex ℝ (Metric.ball (p : ℂ) ρ ∩ Metric.ball c R) :=
        (convex_ball _ _).inter (convex_ball _ _)
      have h1 := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F)
        (f' := fun z => cexp (N * ψ z)) (C := Real.exp (N * (D - δ / 2)))
        (fun z hz => (hF z hz.2).hasDerivWithinAt)
        (fun z hz => by
          rw [norm_exp, re_ofReal_mul]
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
            (hρψ z (hBH hz.2).le hz.1).le hN.le))
        ⟨hw₁', hmemB₁ t₁ ⟨ht₁.1, le_rfl⟩⟩ ⟨hw₂', hmemB₂ t₂ ⟨ht₂.1, le_rfl⟩⟩
      have h2 : ‖α₂ t₂ - α₁ t₁‖ ≤ 2 * ρ := by
        have := dist_triangle (α₂ t₂) p (α₁ t₁)
        rw [dist_comm (p : ℂ)] at this
        rw [← dist_eq_norm]; linarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
    have hup : ‖F (s + r * valleyDir u₀ 1 τ₁) - F (s + r * valleyDir u₀ (-1) τ₂)‖ ≤
        Real.exp (N * (D - δ / 2)) * Q := by
      have hsplit : F (s + r * valleyDir u₀ 1 τ₁) - F (s + r * valleyDir u₀ (-1) τ₂) =
          -(F (α₁ t₁) - F (s + r * valleyDir u₀ 1 τ₁)) - (F (α₂ t₂) - F (α₁ t₁)) +
            (F (α₂ t₂) - F (s + r * valleyDir u₀ (-1) τ₂)) := by ring
      have hE : ∀ x : ℝ, x ≤ D - δ → Real.exp (N * x) ≤ Real.exp (N * (D - δ / 2)) := fun x hx =>
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hN.le)
      have hl₁ : ‖F (α₁ t₁) - F (s + r * valleyDir u₀ 1 τ₁)‖ ≤
          Real.exp (N * (D - δ / 2)) * (S₁ * t₁) := by
        refine hlift₁.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (hE _ hz₁) (mul_nonneg hS₁0 ht₁.1)
      have hl₂ : ‖F (α₂ t₂) - F (s + r * valleyDir u₀ (-1) τ₂)‖ ≤
          Real.exp (N * (D - δ / 2)) * (S₂ * t₂) := by
        refine hlift₂.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (hE _ hz₂) (mul_nonneg hS₂0 ht₂.1)
      rw [hsplit]
      calc _ ≤ ‖-(F (α₁ t₁) - F (s + r * valleyDir u₀ 1 τ₁)) - (F (α₂ t₂) - F (α₁ t₁))‖ +
            ‖F (α₂ t₂) - F (s + r * valleyDir u₀ (-1) τ₂)‖ := norm_add_le _ _
        _ ≤ ‖F (α₁ t₁) - F (s + r * valleyDir u₀ 1 τ₁)‖ + ‖F (α₂ t₂) - F (α₁ t₁)‖ +
            ‖F (α₂ t₂) - F (s + r * valleyDir u₀ (-1) τ₂)‖ := by
          gcongr
          exact (norm_sub_le _ _).trans (by rw [norm_neg])
        _ ≤ _ := by rw [hQ]; nlinarith [hl₁, hl₂, hconn]
    -- divide by `e^{ND}`
    have hcomb := (mul_le_mul_of_nonneg_left hlow (Real.exp_pos (N * D)).le).trans
      (hX ▸ hup)
    have hsplitE : Real.exp (N * (D - δ / 2)) = Real.exp (N * D) * Real.exp (-(δ / 2) * N) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplitE, mul_assoc] at hcomb
    exact le_of_mul_le_mul_left hcomb (Real.exp_pos _)
  -- let `N → ∞`
  have hlim : Tendsto (fun N : ℝ => 2 * C / Real.sqrt N +
      Real.sqrt N * Real.exp (-(δ / 2) * N) * Q) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℝ => 2 * C / Real.sqrt N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    have h2 : Tendsto (fun N : ℝ => Real.sqrt N * Real.exp (-(δ / 2) * N) * Q) atTop (𝓝 0) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (δ / 2)
        (by positivity)).mul_const Q
      rw [zero_mul] at this
      refine this.congr fun N => ?_
      rw [Real.sqrt_eq_rpow]
    simpa using h1.add h2
  have hpos : 0 < Real.sqrt (π / ‖b‖) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨N, hN1, hN0⟩ := ((hlim.eventually (gt_mem_nhds hpos)).and
    (eventually_gt_atTop 0)).exists
  have hm := main N hN0
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hq : Real.sqrt (π / (N * ‖b‖)) * Real.sqrt N = Real.sqrt (π / ‖b‖) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hNs : 2 * C / N * Real.sqrt N = 2 * C / Real.sqrt N := by
    field_simp
    rw [Real.sq_sqrt hN0.le]
  have := mul_le_mul_of_nonneg_right hm hsN.le
  rw [sub_mul, hq, hNs] at this
  nlinarith [this, hN1]

/-- **Two descent paths from opposite valleys land at two different real points.** With the
valley data of `IsEuclid.exists_valley` and any tilts `|τ₁|, |τ₂| ≤ 1/2`, the end points
`s + r v₁` (valley `ε = 1`) and `s + r v₂` (valley `ε = −1`) lie below the saddle level, so
descent paths `α₁`, `α₂` from them exist and land at real points `x₁`, `x₂`
(`IsEuclid.exists_descent`), on the level of their start points (`bdry xⱼ = Im ψ zⱼ`) and outside
the middle interval (`IsEuclid.exists_descent_outside`). By `IsEuclid.not_landing_eq`,
`x₁ ≠ x₂`. -/
theorem IsEuclid.exists_landing_ne {l : Fin 6 → ℝ} (h : IsEuclid l)
    {b u₀ : ℂ} {K r : ℝ} (hb0 : b ≠ 0) (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖)
    (hr : 0 < r)
    (hray : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (saddle l + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ) -
          phaseC (faceSum l) (quadSum l) (saddle l) - b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤
        K * t ^ 3 ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖b‖ / 4 * t ^ 2)
    {τ₁ τ₂ : ℝ} (hτ₁ : |τ₁| ≤ 1 / 2) (hτ₂ : |τ₂| ≤ 1 / 2) :
    ∃ (T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (x₁ x₂ : ℝ),
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir u₀ 1 τ₁) T₁ α₁ ∧ Tendsto α₁ (𝓝[<] T₁) (𝓝 (x₁ : ℂ)) ∧
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir u₀ (-1) τ₂) T₂ α₂ ∧ Tendsto α₂ (𝓝[<] T₂) (𝓝 (x₂ : ℂ)) ∧
      bdry (faceSum l) (quadSum l) x₁ =
        (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ 1 τ₁)).im ∧
      bdry (faceSum l) (quadSum l) x₂ =
        (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ (-1) τ₂)).im ∧
      ((∃ i, x₁ ≤ faceSum l i) ∨ ∃ k, quadSum l k ≤ x₁) ∧
      ((∃ i, x₂ ≤ faceSum l i) ∨ ∃ k, quadSum l k ≤ x₂) ∧ x₁ ≠ x₂ := by
  have hrI : r ∈ Icc (0 : ℝ) r := ⟨hr.le, le_rfl⟩
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  have hlt : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 →
      (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ ε τ)).re <
        (phaseC (faceSum l) (quadSum l) (saddle l)).re := fun ε hε τ hτ => by
    have h1 := (hray ε hε τ hτ r hrI).2.2
    have h2 : 0 < ‖b‖ / 4 * r ^ 2 := by positivity
    linarith
  have hε₁ : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hε₂ : (-1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨T₁, α₁, x₁, hα₁, hx₁, -, hb₁, -, ho₁⟩ :=
    h.exists_descent_outside (hray 1 hε₁ τ₁ hτ₁ r hrI).1 (hlt 1 hε₁ τ₁ hτ₁)
  obtain ⟨T₂, α₂, x₂, hα₂, hx₂, -, hb₂, -, ho₂⟩ :=
    h.exists_descent_outside (hray (-1) hε₂ τ₂ hτ₂ r hrI).1 (hlt (-1) hε₂ τ₂ hτ₂)
  refine ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, hb₁, hb₂, ho₁, ho₂, ?_⟩
  rintro rfl
  exact h.not_landing_eq hb0 hu hbu hr hray hτ₁ hτ₂ hα₁ hα₂ hx₁ hx₂

end Lightlike.Asymptotics

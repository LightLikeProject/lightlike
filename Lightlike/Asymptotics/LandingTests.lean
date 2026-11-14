import Lightlike.Asymptotics.Landing
import Lightlike.Asymptotics.DescentTests

/-!
# Trust checks for the landing points

* **Known values.** For the regular unit tetrahedron (`Aᵢ = 3`, `Bₖ = 4`) at the middle point
  `p = 7/2`, `dphaseM p = log 7 + iπ` (`dphaseM_regular`), and the imaginary part of `phaseM p`,
  computed from its own formula, is the boundary value `bdry (7/2) = 7π/2` that `Contour.lean`
  computes from the piecewise-linear formula (`im_phaseM_regular`).
* **Wrong input fails.** To the right of every `Aᵢ` and `Bₖ` the continued phase is holomorphic
  across the real axis with `Im ψ' = −2π < 0` (`im_dphaseC_ofReal_right`), and there the
  conclusion of `eventually_phaseC_ne_add_pos` is false: arbitrarily close to such a point `p`
  the upper half-plane contains points `z` with `ψ z = ψ p + ε`, `ε > 0`
  (`not_eventually_phaseC_ne_add_pos_right`), found with the local inverse of `ψ`. For the
  regular tetrahedron this happens at `p = 5` (`not_eventually_regular_five`). So the hypothesis
  that `p` lies left of every `Bₖ` is needed, and the sign `Im ψₘ' = +π` is what blocks landing.
* **Non-vacuity.** The hypotheses of `eventually_phaseC_ne_add_pos` hold at `p = 7/2` for the
  regular tetrahedron (`eventually_regular_mid`), and the descent of the regular tetrahedron
  from a point below the saddle level lands at or left of `3` or at or right of `4`
  (`exists_descent_outside_regular`).
* **Junk values.** `phaseM` and `dphaseM` are used only where all their logarithms have arguments
  with positive real part, so `log 0 = 0` never enters; the value `phaseC p` at a real point is
  the genuine boundary value of the continuous function `phaseC` on the closed upper half-plane
  (`continuousOn_phaseC`), with `log x = log |x| + iπ` for `x < 0`.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: `dphaseM (7/2) = log 7 + iπ` for the regular unit tetrahedron:
`log (7/2) − 4 log (1/2) + 3 log (1/2) + iπ`. -/
theorem dphaseM_regular :
    dphaseM (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) ((7 / 2 : ℝ) : ℂ) =
      (Real.log 7 : ℂ) + π * I := by
  have e1 : log ((7 / 2 : ℝ) : ℂ) = ((Real.log 7 - Real.log 2 : ℝ) : ℂ) := by
    rw [← Real.log_div (by norm_num) (by norm_num), ofReal_log (by norm_num)]
  have e2 : log (((7 / 2 : ℝ) : ℂ) - ((3 : ℝ) : ℂ)) = ((-Real.log 2 : ℝ) : ℂ) := by
    rw [← ofReal_sub, ← Real.log_inv, ofReal_log (by norm_num)]; norm_num
  have e3 : log (((4 : ℝ) : ℂ) - ((7 / 2 : ℝ) : ℂ)) = ((-Real.log 2 : ℝ) : ℂ) := by
    rw [← ofReal_sub, ← Real.log_inv, ofReal_log (by norm_num)]; norm_num
  rw [faceSum_regular, quadSum_regular]
  simp only [dphaseM, Fin.sum_univ_four, Fin.sum_univ_three, e1, e2, e3]
  push_cast; ring

/-- **Known value**: `Im phaseM (7/2) = bdry (7/2) = 7π/2` for the regular unit tetrahedron; the
left side is computed from the formula for `phaseM`, the right side from the piecewise-linear
boundary formula (`bdry_regular_mid`). -/
theorem im_phaseM_regular :
    (phaseM (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) ((7 / 2 : ℝ) : ℂ)).im =
      bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (7 / 2) := by
  have hx : ∀ x : ℝ, 0 ≤ x → (xlog (x : ℂ)).im = 0 := fun x hx => by
    rw [im_xlog_ofReal, min_eq_right hx, mul_zero]
  have h1 : (xlog ((7 / 2 : ℝ) : ℂ)).im = 0 := hx _ (by norm_num)
  have h2 : (xlog (((7 / 2 : ℝ) : ℂ) - ((3 : ℝ) : ℂ))).im = 0 := by
    rw [← ofReal_sub]; exact hx _ (by norm_num)
  have h3 : (xlog (((4 : ℝ) : ℂ) - ((7 / 2 : ℝ) : ℂ))).im = 0 := by
    rw [← ofReal_sub]; exact hx _ (by norm_num)
  rw [bdry_regular_mid, faceSum_regular, quadSum_regular]
  simp only [phaseM, Fin.sum_univ_four, Fin.sum_univ_three, add_im, sub_im, h1, h2, h3, mul_im,
    ofReal_re, ofReal_im, I_re, I_im]
  ring

/-- `phaseC` is holomorphic at every point whose real part lies to the right of `0` and of all
the `Aᵢ` and `Bₖ` (there every logarithm is off its cut), with derivative `dphaseC`. -/
lemma hasDerivAt_phaseC_of_re (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (h0 : 0 < z.re)
    (hA : ∀ i, A i < z.re) (hB : ∀ k, B k < z.re) :
    HasDerivAt (phaseC A B) (dphaseC A B z) z := by
  have hsh : ∀ c : ℝ, c < z.re →
      HasDerivAt (fun z : ℂ => xlog (z - c)) (log (z - c) + 1) z := fun c hc =>
    (hasDerivAt_xlog (mem_slitPlane_iff.2 (Or.inl (by simpa using hc)))).comp_sub_const z (c : ℂ)
  have h := ((((hasDerivAt_xlog (mem_slitPlane_iff.2 (Or.inl h0))).sub
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hsh (A i) (hA i))).add
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hsh (B k) (hB k))).sub
    ((hasDerivAt_id z).const_mul (2 * π * I))).add_const (π * I * ∑ k, (B k : ℂ))
  convert h using 1
  · ext w; simp [phaseC]
  · simp only [dphaseC, Fin.sum_univ_four, Fin.sum_univ_three]; ring

/-- To the right of `0` and of all the `Aᵢ` and `Bₖ`, the derivative of the continued phase has
imaginary part `−2π`. -/
theorem im_dphaseC_ofReal_right (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {p : ℝ} (hp : 0 < p)
    (hA : ∀ i, A i < p) (hB : ∀ k, B k < p) : (dphaseC A B p).im = -(2 * π) := by
  have h0 : ∀ x : ℝ, 0 < x → (log (x : ℂ)).im = 0 := fun x hx => by
    rw [log_im, arg_ofReal_of_nonneg hx.le]
  have hA' : ∀ i, (log ((p : ℂ) - A i)).im = 0 := fun i => by
    rw [← ofReal_sub]; exact h0 _ (by linarith [hA i])
  have hB' : ∀ k, (log ((p : ℂ) - B k)).im = 0 := fun k => by
    rw [← ofReal_sub]; exact h0 _ (by linarith [hB k])
  simp [dphaseC, Complex.im_sum, hA', hB', h0 p hp]

/-- **Wrong input**: to the right of `0` and of all the `Aᵢ` and `Bₖ`, the conclusion of
`eventually_phaseC_ne_add_pos` fails: every neighbourhood of `p` contains a point `z` of the
upper half-plane with `phaseC z = phaseC p + ε` for some `ε > 0`. -/
theorem not_eventually_phaseC_ne_add_pos_right (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {p : ℝ}
    (hp : 0 < p) (hA : ∀ i, A i < p) (hB : ∀ k, B k < p) :
    ¬ ∀ᶠ z in 𝓝 (p : ℂ), 0 ≤ z.im → ∀ ε : ℝ, 0 < ε → phaseC A B z ≠ phaseC A B p + ε := by
  intro hP
  set f := phaseC A B
  set d := dphaseC A B p
  have hdev : ∀ᶠ z in 𝓝 (p : ℂ), HasDerivAt f (dphaseC A B z) z := by
    have h0 : ∀ᶠ z in 𝓝 (p : ℂ), 0 < z.re :=
      (continuous_re.tendsto (p : ℂ)).eventually (eventually_gt_nhds (by simpa using hp))
    have hA0 : ∀ᶠ z in 𝓝 (p : ℂ), ∀ i, A i < z.re := eventually_all.2 fun i =>
      (continuous_re.tendsto (p : ℂ)).eventually (eventually_gt_nhds (by simpa using hA i))
    have hB0 : ∀ᶠ z in 𝓝 (p : ℂ), ∀ k, B k < z.re := eventually_all.2 fun k =>
      (continuous_re.tendsto (p : ℂ)).eventually (eventually_gt_nhds (by simpa using hB k))
    filter_upwards [h0, hA0, hB0] with z h1 h2 h3 using hasDerivAt_phaseC_of_re A B h1 h2 h3
  have han : AnalyticAt ℂ f p :=
    analyticAt_iff_eventually_differentiableAt.2 (hdev.mono fun z hz => hz.differentiableAt)
  have hs : HasStrictDerivAt f d p := by
    have := han.hasStrictDerivAt
    rwa [hdev.self_of_nhds.deriv] at this
  have hdim : d.im = -(2 * π) := im_dphaseC_ofReal_right A B hp hA hB
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_im] at hdim; linarith [Real.pi_pos]
  set g := hs.localInverse f d p hd0
  have hg : HasDerivAt g d⁻¹ (f p) := (hs.to_localInverse hd0).hasDerivAt
  have hgp : g (f p) = p := (hs.eventually_left_inverse hd0).self_of_nhds
  have hc : 0 < (d⁻¹).im := by
    rw [inv_im, hdim, neg_neg]; exact div_pos (by positivity) (normSq_pos.2 hd0)
  have ho := (hasDerivAt_iff_isLittleO.1 hg).def (half_pos hc)
  have hφ : Tendsto (fun ε : ℝ => f p + ε) (𝓝[>] 0) (𝓝 (f p)) := by
    have : Tendsto (fun ε : ℝ => f p + ε) (𝓝 0) (𝓝 (f p + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add continuous_ofReal).tendsto 0
    rw [ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hgφ : Tendsto (fun ε : ℝ => g (f p + ε)) (𝓝[>] 0) (𝓝 (p : ℂ)) := by
    have := hg.continuousAt.tendsto.comp hφ
    rwa [hgp] at this
  obtain ⟨ε, hPε, hinv, hle, hε⟩ := ((hgφ.eventually hP).and
    ((hφ.eventually (hs.eventually_right_inverse hd0)).and
      ((hφ.eventually ho).and self_mem_nhdsWithin))).exists
  have hε0 : 0 < ε := hε
  rw [show f p + (ε : ℂ) - f p = (ε : ℂ) by ring, hgp, smul_eq_mul, norm_real,
    Real.norm_of_nonneg hε0.le] at hle
  have him : 0 ≤ (g (f p + ε)).im := by
    have h1 := abs_im_le_norm (g (f p + ε) - p - ε * d⁻¹)
    have h2 : (g (f p + ε) - p - ε * d⁻¹).im = (g (f p + ε)).im - ε * (d⁻¹).im := by
      simp [mul_im]
    rw [h2] at h1
    have h3 := (abs_le.1 (h1.trans hle)).1
    nlinarith [mul_pos hε0 hc]
  exact hPε him ε hε0 hinv

/-- **Wrong input** for the regular tetrahedron: at `p = 5`, right of `Bₖ = 4`, points of the
upper half-plane with `ψ z = ψ 5 + ε`, `ε > 0`, come arbitrarily close to `5`. -/
theorem not_eventually_regular_five :
    ¬ ∀ᶠ z in 𝓝 ((5 : ℝ) : ℂ), 0 ≤ z.im → ∀ ε : ℝ, 0 < ε →
      phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) z ≠
        phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (5 : ℝ) + ε :=
  not_eventually_phaseC_ne_add_pos_right _ _ (by norm_num)
    (fun i => by rw [faceSum_regular]; norm_num) (fun k => by rw [quadSum_regular]; norm_num)

/-- **Non-vacuity**: the hypotheses of `eventually_phaseC_ne_add_pos` hold at the middle point
`7/2` of the regular tetrahedron. -/
theorem eventually_regular_mid :
    ∀ᶠ z in 𝓝 ((7 / 2 : ℝ) : ℂ), 0 ≤ z.im → ∀ ε : ℝ, 0 < ε →
      phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) z ≠
        phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (7 / 2 : ℝ) + ε :=
  eventually_phaseC_ne_add_pos _ _ (by norm_num) (fun i => by rw [faceSum_regular]; norm_num)
    (fun k => by rw [quadSum_regular]; norm_num)

/-- **Non-vacuity**: for the regular unit tetrahedron, a descent from below the saddle level
lands at a real point `x ≤ 3` or `x ≥ 4`, outside the middle interval `(3, 4)`. -/
theorem exists_descent_outside_regular : ∃ z₀ : ℂ, 0 < z₀.im ∧ ∃ T α, ∃ x : ℝ,
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₀ T α ∧ Tendsto α (𝓝[<] T) (𝓝 (x : ℂ)) ∧
    (x ≤ 3 ∨ 4 ≤ x) := by
  obtain ⟨z₀, hz₀, hD⟩ := exists_below_saddle_regular
  obtain ⟨T, α, x, hα, hx, -, -, -, hout⟩ := isEuclid_regular.exists_descent_outside hz₀ hD
  refine ⟨z₀, hz₀, T, α, x, hα, hx, ?_⟩
  rw [faceSum_regular, quadSum_regular] at hout
  rcases hout with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

end Lightlike.Asymptotics

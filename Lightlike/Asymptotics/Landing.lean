import Lightlike.Asymptotics.Descent

/-!
# No landing in the middle of the real axis

Between the largest face sum `A_max` and the smallest quadrilateral sum `B_min`, the continued
phase `ψ = phaseC A B` continues holomorphically across the real axis as
`ψₘ z = g z − Σᵢ g (z − Aᵢ) − Σₖ g (Bₖ − z) + iπ z` (`phaseM`), with `g w = w log w`: the two
agree on the closed upper half-plane left of every `Bₖ` (`phaseC_eq_phaseM`), because crossing
the cut of the logarithm from above adds `iπ` (`log_eq_log_neg_add`). The derivative `dphaseM` of
`ψₘ` is the boundary value of `dphaseC` (`dphaseC_eq_dphaseM`), and at every real point of
`(A_max, B_min)` its imaginary part is `π` (`im_dphaseM_ofReal`).

So near such a point `p`, `ψ z − ψ p ≈ ψₘ'(p) (z − p)` takes positive real values only below the
real axis: no point `z` of the closed upper half-plane near `p` has `ψ z = ψ p + ε` with `ε > 0`
(`eventually_phaseC_ne_add_pos`). A curve in the closed upper half-plane along which `ψ` falls
at unit rate, such as a descent lift, therefore never lands in `(A_max, B_min)`
(`not_tendsto_middle`); for a Euclidean tetrahedron every descent from below the saddle level
lands at or left of a face sum or at or right of a quadrilateral sum
(`IsEuclid.exists_descent_outside`).

This is the step of the steepest-descent proof of the Ponzano–Regge asymptotics that rules out
landing in the middle interval.
-/

open Complex Set Filter Topology
open scoped Real ComplexConjugate

namespace Lightlike.Asymptotics

/-! ## The continuation across the middle interval -/

/-- Crossing the cut from above: `log w = log (−w) + iπ` for `w` in the closed upper half-plane
with negative real part. -/
lemma log_eq_log_neg_add {w : ℂ} (him : 0 ≤ w.im) (hre : w.re < 0) :
    log w = log (-w) + π * I := by
  rcases him.lt_or_eq with h | h
  · rw [log_neg_of_im_pos h]; ring
  · apply Complex.ext
    · simp [log_re]
    · simp only [log_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
      rw [arg_eq_pi_iff.2 ⟨hre, h.symm⟩,
        arg_eq_zero_iff.2 ⟨by simp only [neg_re]; linarith, by simp only [neg_im, ← h, neg_zero]⟩]
      ring

/-- `g w = iπ w − g (−w)` for `w` in the closed upper half-plane with negative real part,
where `g w = w log w`. -/
lemma xlog_eq_of_re_neg {w : ℂ} (him : 0 ≤ w.im) (hre : w.re < 0) :
    xlog w = π * I * w - xlog (-w) := by
  rw [xlog, xlog, log_eq_log_neg_add him hre]; ring

/-- The continuation of `phaseC` across the real interval between the face sums and the
quadrilateral sums: `g z − Σᵢ g (z − Aᵢ) − Σₖ g (Bₖ − z) + iπ z`, with `g w = w log w`. -/
noncomputable def phaseM (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  xlog z - ∑ i, xlog (z - A i) - ∑ k, xlog (B k - z) + π * I * z

/-- The derivative of `phaseM`: `log z − Σᵢ log (z − Aᵢ) + Σₖ log (Bₖ − z) + iπ`. -/
noncomputable def dphaseM (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  log z - ∑ i, log (z - A i) + ∑ k, log (B k - z) + π * I

/-- On the closed upper half-plane left of every `Bₖ`, the continued phase is `phaseM`. -/
theorem phaseC_eq_phaseM (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (him : 0 ≤ z.im)
    (hB : ∀ k, z.re < B k) : phaseC A B z = phaseM A B z := by
  have h : ∀ k, xlog (z - B k) = π * I * (z - B k) - xlog ((B k : ℂ) - z) := fun k => by
    rw [xlog_eq_of_re_neg (by simpa using him) (by simpa using hB k), neg_sub]
  simp only [phaseC, phaseM, h, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- On the closed upper half-plane left of every `Bₖ`, `dphaseC` is `dphaseM`; so `dphaseM` is
the boundary value of the derivative of the continued phase. -/
theorem dphaseC_eq_dphaseM (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (him : 0 ≤ z.im)
    (hB : ∀ k, z.re < B k) : dphaseC A B z = dphaseM A B z := by
  have h : ∀ k, log (z - B k) = log ((B k : ℂ) - z) + π * I := fun k => by
    rw [log_eq_log_neg_add (by simpa using him) (by simpa using hB k), neg_sub]
  simp only [dphaseC, dphaseM, h, Fin.sum_univ_three]
  ring

/-- `phaseM` is holomorphic at every point whose real part lies to the right of `0` and of every
`Aᵢ` and to the left of every `Bₖ`, with derivative `dphaseM`. -/
theorem hasDerivAt_phaseM (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (h0 : 0 < z.re)
    (hA : ∀ i, A i < z.re) (hB : ∀ k, z.re < B k) :
    HasDerivAt (phaseM A B) (dphaseM A B z) z := by
  have hsA : ∀ i, HasDerivAt (fun z : ℂ => xlog (z - A i)) (log (z - A i) + 1) z := fun i =>
    (hasDerivAt_xlog (mem_slitPlane_iff.2 (Or.inl (by simpa using hA i)))).comp_sub_const z _
  have hsB : ∀ k, HasDerivAt (fun z : ℂ => xlog (B k - z)) (-(log (B k - z) + 1)) z := fun k =>
    (hasDerivAt_xlog (mem_slitPlane_iff.2 (Or.inl (by simpa using hB k)))).comp_const_sub _ z
  have h := (((hasDerivAt_xlog (mem_slitPlane_iff.2 (Or.inl h0))).sub
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hsA i)).sub
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hsB k)).add
    ((hasDerivAt_id z).const_mul (π * I))
  convert h using 1
  · ext w; simp [phaseM]
  · simp only [dphaseM, Fin.sum_univ_four, Fin.sum_univ_three]; ring

/-- At every real point of the middle interval, to the right of `0` and of every `Aᵢ` and to the
left of every `Bₖ`, the derivative `dphaseM` has imaginary part `π`. -/
theorem im_dphaseM_ofReal (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {p : ℝ} (hp : 0 < p)
    (hA : ∀ i, A i < p) (hB : ∀ k, p < B k) : (dphaseM A B p).im = π := by
  have h0 : ∀ x : ℝ, 0 < x → (log (x : ℂ)).im = 0 := fun x hx => by
    rw [log_im, arg_ofReal_of_nonneg hx.le]
  have hA' : ∀ i, (log ((p : ℂ) - A i)).im = 0 := fun i => by
    rw [← ofReal_sub]; exact h0 _ (by linarith [hA i])
  have hB' : ∀ k, (log ((B k : ℂ) - p)).im = 0 := fun k => by
    rw [← ofReal_sub]; exact h0 _ (by linarith [hB k])
  simp [dphaseM, Complex.im_sum, hA', hB', h0 p hp]

/-! ## No landing in the middle -/

/-- The first-order obstruction: if `Im d = π`, `w` lies in the closed upper half-plane and
`ε > 0`, then `ε` differs from `d w` by more than `‖w‖`. -/
lemma lt_norm_sub_mul {d w : ℂ} (hd : d.im = π) (hw : 0 ≤ w.im) {ε : ℝ} (hε : 0 < ε) :
    ‖w‖ < ‖(ε : ℂ) - d * w‖ := by
  rw [← not_le]
  intro hle
  have hdn : π ≤ ‖d‖ := hd ▸ (le_abs_self _).trans (abs_im_le_norm d)
  have key : -(conj d * ((ε : ℂ) - d * w)).im = (d.re ^ 2 + d.im ^ 2) * w.im + d.im * ε := by
    simp only [mul_im, conj_re, conj_im, sub_im, sub_re, mul_re, ofReal_re, ofReal_im]; ring
  have h1 : π * ε ≤ ‖d‖ * ‖w‖ := by
    have ha := neg_le_abs ((conj d * ((ε : ℂ) - d * w)).im)
    have hb := abs_im_le_norm (conj d * ((ε : ℂ) - d * w))
    rw [norm_mul, norm_conj] at hb
    have hc : 0 ≤ (d.re ^ 2 + d.im ^ 2) * w.im := by positivity
    have hm := mul_le_mul_of_nonneg_left hle (norm_nonneg d)
    rw [hd] at key hc
    linarith
  have h2 : ‖d‖ * ‖w‖ ≤ ε + ‖w‖ := by
    calc ‖d‖ * ‖w‖ = ‖(ε : ℂ) - ((ε : ℂ) - d * w)‖ := by rw [← norm_mul]; ring_nf
      _ ≤ ‖(ε : ℂ)‖ + ‖(ε : ℂ) - d * w‖ := norm_sub_le _ _
      _ ≤ ε + ‖w‖ := by rw [norm_real, Real.norm_of_nonneg hε.le]; linarith
  have h3 := mul_le_mul_of_nonneg_right hdn (norm_nonneg w)
  have hπ := Real.pi_gt_three
  have h4 := mul_pos (sub_pos.2 hπ) hε
  have h5 := mul_nonneg (sub_pos.2 hπ).le (norm_nonneg w)
  nlinarith

/-- **No positive real increments above the middle.** Let `p` be a real point to the right of
`0` and of every face sum `Aᵢ` and to the left of every quadrilateral sum `Bₖ`. Near `p`, no point
`z` of the closed upper half-plane has `phaseC z = phaseC p + ε` with `ε > 0`. -/
theorem eventually_phaseC_ne_add_pos (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {p : ℝ} (hp : 0 < p)
    (hA : ∀ i, A i < p) (hB : ∀ k, p < B k) :
    ∀ᶠ z in 𝓝 (p : ℂ), 0 ≤ z.im → ∀ ε : ℝ, 0 < ε → phaseC A B z ≠ phaseC A B p + ε := by
  have hd := hasDerivAt_phaseM A B (z := (p : ℂ)) (by simpa using hp) (fun i => by simpa using hA i)
    (fun k => by simpa using hB k)
  have ho := (hasDerivAt_iff_isLittleO.1 hd).def one_pos
  have hre : ∀ᶠ z in 𝓝 (p : ℂ), ∀ k, z.re < B k := eventually_all.2 fun k =>
    (continuous_re.tendsto (p : ℂ)).eventually (eventually_lt_nhds (by simpa using hB k))
  filter_upwards [ho, hre] with z hz hzB him ε hε heq
  rw [← phaseC_eq_phaseM A B him hzB,
    ← phaseC_eq_phaseM A B (z := (p : ℂ)) (by simp) (fun k => by simpa using hB k), heq,
    show phaseC A B p + ε - phaseC A B p - (z - p) • dphaseM A B p =
      (ε : ℂ) - dphaseM A B p * (z - p) by rw [smul_eq_mul]; ring, one_mul] at hz
  have h := lt_norm_sub_mul (im_dphaseM_ofReal A B hp hA hB) (w := z - p) (by simpa using him) hε
  linarith

/-- **No landing in the middle.** A curve `α` in the closed upper half-plane along which
the continued phase falls at unit rate, `phaseC (α t) = w₀ − t` on `[0, T)`, does not converge,
as `t → T⁻`, to a real point `p` to the right of `0` and of every face sum and to the left of
every quadrilateral sum. -/
theorem not_tendsto_middle (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {p : ℝ} (hp : 0 < p)
    (hA : ∀ i, A i < p) (hB : ∀ k, p < B k) {w₀ : ℂ} {T : ℝ} (hT : 0 < T) {α : ℝ → ℂ}
    (hα : ∀ t ∈ Ico 0 T, 0 ≤ (α t).im ∧ phaseC A B (α t) = w₀ - t) :
    ¬ Tendsto α (𝓝[<] T) (𝓝 (p : ℂ)) := by
  intro hlim
  have hev : ∀ᶠ t in 𝓝[<] T, t ∈ Ico 0 T := Ico_mem_nhdsLT hT
  have hψ : phaseC A B p = w₀ - T := by
    have h1 : Tendsto (fun t => phaseC A B (α t)) (𝓝[<] T) (𝓝 (phaseC A B p)) :=
      ((continuousOn_phaseC A B) p (by simp)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hlim, hev.mono fun t ht => (hα t ht).1⟩)
    have h2 : Tendsto (fun t => phaseC A B (α t)) (𝓝[<] T) (𝓝 (w₀ - T)) := by
      have : Tendsto (fun t : ℝ => w₀ - (t : ℂ)) (𝓝[<] T) (𝓝 (w₀ - T)) :=
        ((continuous_const.sub continuous_ofReal).tendsto T).mono_left nhdsWithin_le_nhds
      exact this.congr' (hev.mono fun t ht => ((hα t ht).2).symm)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨t, ht, hne⟩ := (hev.and (hlim.eventually (eventually_phaseC_ne_add_pos A B hp hA hB))).exists
  exact hne (hα t ht).1 (T - t) (by linarith [ht.2])
    (by rw [(hα t ht).2, hψ]; push_cast; ring)

/-- **No landing in the middle, for a Euclidean tetrahedron.** From every point of the upper
half-plane below the saddle level, the descent lands at a real point `x`, as in
`IsEuclid.exists_descent`, and `x` lies at or to the left of some face sum or at or to the right of
some quadrilateral sum. -/
theorem IsEuclid.exists_descent_outside {l : Fin 6 → ℝ} (h : IsEuclid l) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im)
    (hD : (phaseC (faceSum l) (quadSum l) z₀).re <
      (phaseC (faceSum l) (quadSum l) (saddle l)).re) :
    ∃ T α, ∃ x : ℝ,
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α ∧
      Tendsto α (𝓝[<] T) (𝓝 (x : ℂ)) ∧
      phaseC (faceSum l) (quadSum l) x = phaseC (faceSum l) (quadSum l) z₀ - T ∧
      bdry (faceSum l) (quadSum l) x = (phaseC (faceSum l) (quadSum l) z₀).im ∧
      (phaseC (faceSum l) (quadSum l) x).re < (phaseC (faceSum l) (quadSum l) z₀).re ∧
      ((∃ i, x ≤ faceSum l i) ∨ ∃ k, quadSum l k ≤ x) := by
  obtain ⟨T, α, x, hα, hlim, h1, h2, h3⟩ := h.exists_descent hz₀ hD
  refine ⟨T, α, x, hα, hlim, h1, h2, h3, ?_⟩
  by_contra hc
  rw [not_or, not_exists, not_exists] at hc
  have hA : ∀ i, faceSum l i < x := fun i => not_le.1 (hc.1 i)
  have hB : ∀ k, x < quadSum l k := fun k => not_le.1 (hc.2 k)
  exact not_tendsto_middle _ _ ((h.faceSum_pos 0).trans (hA 0)) hA hB hα.pos
    (fun t ht => ⟨(hα.mem t ht).1.le, h.phaseC_lift hα t ht⟩) hlim

end Lightlike.Asymptotics

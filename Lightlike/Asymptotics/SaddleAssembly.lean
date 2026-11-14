import Lightlike.Asymptotics.SaddleRay
import Lightlike.Asymptotics.Racah

/-!
# Assembly of the saddle-point asymptotics of Racah's sum

For Euclidean integer spins `j` and lengths `ℓ = λj + ½ = λ m_λ` with `m_λ = j + 1/(2λ)`, Racah's
sum is `−Im(Φ(x₂) − Φ(x₁))/π` for a primitive `Φ` of Racah's kernel, and after the substitution
`z = λw − 3/2` the primitive `F(w) = Φ(λw − 3/2)` has derivative `λ K(λw − 3/2)`. The contour from
`x₁` to `x₂` is cut into:

* the two rays of length `r` from the saddle `s_λ` of `m_λ` along `±v`, each contributing half of
  the Gaussian term (`ray_estimate`);
* two outer pieces from the ends of the rays to points on the real axis near the landing points
  of the steepest-descent lines, on which the kernel is smaller than at the saddle by a factor
  `e^{−λδ}` (`IsEuclid.outer_side`).

The result is `racahSumAsymptotics`, and with it the Ponzano–Regge formula
`ponzanoReggeFormula` without hypotheses.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-! ## Scaling of the integer face and quadrilateral sums -/

/-- The face sums of the spins `λj` are `λ` times those of `j`. -/
lemma faceN_mul (j : Fin 6 → ℕ) (lam : ℕ) (i : Fin 4) :
    faceN (fun e => lam * j e) i = lam * faceN j i := by
  fin_cases i <;> simp [faceN] <;> ring

/-- The quadrilateral sums of the spins `λj` are `λ` times those of `j`. -/
lemma quadN_mul (j : Fin 6 → ℕ) (lam : ℕ) (k : Fin 3) :
    quadN (fun e => lam * j e) k = lam * quadN j k := by
  fin_cases k <;> simp [quadN] <;> ring

/-- The real face sums of integer lengths are the integer face sums. -/
lemma faceSum_natCast (j : Fin 6 → ℕ) (i : Fin 4) :
    faceSum (fun e => (j e : ℝ)) i = faceN j i := by
  fin_cases i <;> simp [faceSum, faceN]

/-- The real quadrilateral sums of integer lengths are the integer quadrilateral sums. -/
lemma quadSum_natCast (j : Fin 6 → ℕ) (k : Fin 3) :
    quadSum (fun e => (j e : ℝ)) k = quadN j k := by
  fin_cases k <;> simp [quadSum, quadN]

/-- The Ponzano–Regge lengths are the spins `λj` shifted by `½`. -/
lemma lengths_eq_add_half (j : Fin 6 → ℕ) (lam : ℕ) :
    PR.lengths j lam = fun e => ((lam * j e : ℕ) : ℝ) + 1 / 2 := by
  funext e
  simp [PR.lengths]

/-! ## Racah's kernel in the rescaled variable -/

/-- The part of the real axis, in the rescaled variable `w = (z + 3/2)/λ`, on which the kernel
bound of `exists_norm_racahKernel_le` holds: `0 ≤ q ≤ (face sum of j)` or
`q ≥ (quadrilateral sum of j) + 2/λ`. -/
def kernelRegion (j : Fin 6 → ℕ) (lam : ℕ) (q : ℝ) : Prop :=
  (0 ≤ q ∧ ∃ i, q ≤ (faceN j i : ℝ)) ∨ ∃ k, (quadN j k : ℝ) + 2 / lam ≤ q

/-- The derivative `λ K(λw − 3/2)` of `w ↦ Φ(λw − 3/2)`, where `K` is Racah's kernel of the
spins `λj`. -/
noncomputable def scaledKernel (j : Fin 6 → ℕ) (lam : ℕ) (w : ℂ) : ℂ :=
  ((lam : ℝ) : ℂ) * racahKernel (faceN fun e => lam * j e) (quadN fun e => lam * j e)
    (((lam : ℝ) : ℂ) * w - 3 / 2)

/-- **Kernel bound in the rescaled variable**: off a strip along the real axis, and on the parts
of the real axis given by `kernelRegion`, `|λ K(λw − 3/2)| ≤ λ C e^{λ Re ψ_{m_λ}(w)}` with `C`
independent of `λ`. -/
theorem exists_norm_scaledKernel_le (j : Fin 6 → ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℕ, lam ≠ 0 → ∀ w : ℂ, 0 < w.im →
      (c ≤ w.im ∨ kernelRegion j lam w.re) →
      ‖scaledKernel j lam w‖ ≤ lam * C *
        Real.exp (lam * (phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam)) w).re) := by
  obtain ⟨C, hC, hK⟩ := exists_norm_racahKernel_le hc
  refine ⟨C, hC, fun lam hlam w hw hreg => ?_⟩
  have hN : (0 : ℝ) < lam := Nat.cast_pos.2 (Nat.pos_of_ne_zero hlam)
  have hN1 : (1 : ℝ) ≤ lam := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hlam)
  have hzim : (((lam : ℝ) : ℂ) * w - 3 / 2).im = lam * w.im := im_rescale _ _
  have hzre : (((lam : ℝ) : ℂ) * w - 3 / 2).re = lam * w.re - 3 / 2 := by simp
  have hzpos : 0 < (((lam : ℝ) : ℂ) * w - 3 / 2).im := by rw [hzim]; exact mul_pos hN hw
  have hreg' : c ≤ (((lam : ℝ) : ℂ) * w - 3 / 2).im ∨
      (-3 / 2 ≤ (((lam : ℝ) : ℂ) * w - 3 / 2).re ∧
        ∃ i, (((lam : ℝ) : ℂ) * w - 3 / 2).re ≤ (faceN (fun e => lam * j e) i : ℝ) - 1 / 2) ∨
      ∃ k, (quadN (fun e => lam * j e) k : ℝ) + 1 / 2 ≤ (((lam : ℝ) : ℂ) * w - 3 / 2).re := by
    rw [hzim, hzre]
    rcases hreg with h | ⟨h0, i, hi⟩ | ⟨k, hk⟩
    · exact Or.inl (h.trans (le_mul_of_one_le_left hw.le hN1))
    · refine Or.inr (Or.inl ⟨by nlinarith [mul_nonneg hN.le h0], i, ?_⟩)
      rw [faceN_mul]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hi hN.le]
    · refine Or.inr (Or.inr ⟨k, ?_⟩)
      rw [quadN_mul]
      push_cast
      have h2 : (lam : ℝ) * (2 / lam) = 2 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hk hN.le]
  have hb : ‖racahKernel (faceN fun e => lam * j e) (quadN fun e => lam * j e)
      (((lam : ℝ) : ℂ) * w - 3 / 2)‖ ≤ C * Real.exp (phaseC (faceSum (PR.lengths j lam))
        (quadSum (PR.lengths j lam)) (((lam : ℝ) : ℂ) * w - 3 / 2 + 3 / 2)).re := by
    rw [lengths_eq_add_half]
    exact hK _ _ hzpos hreg'
  rw [lengths_eq_smul j hlam, sub_add_cancel, phaseC_faceSum_smul _ hN, re_ofReal_mul] at hb
  unfold scaledKernel
  rw [norm_mul, norm_real, Real.norm_of_nonneg hN.le, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb hN.le

/-! ## Scaling of the prefactor and of the action -/

/-- `√√V(cl) = c √c √√V(l)` for the squared volume `V`, which has degree six. -/
lemma sqrt_sqrt_vol2l_smul {c : ℝ} (hc : 0 < c) (l : Fin 6 → ℝ) :
    √(√(vol2l (c • l))) = c * √c * √(√(vol2l l)) := by
  have hc3 : 0 ≤ c ^ 2 * c := (mul_pos (pow_pos hc 2) hc).le
  have h6 : √(c ^ 6) = c ^ 2 * c := by
    rw [show c ^ 6 = (c ^ 2 * c) ^ 2 by ring]
    exact Real.sqrt_sq hc3
  have h3 : √(c ^ 2 * c) = c * √c := by
    rw [Real.sqrt_mul (pow_nonneg hc.le 2) c, Real.sqrt_sq hc.le]
  rw [vol2l_smul, Real.sqrt_mul (pow_nonneg hc.le 6) (vol2l l), h6,
    Real.sqrt_mul hc3 (√(vol2l l)), h3]

/-- The exponential rate of the prefactor has degree one: `prefactorRate (cl) = c Re ψ_l(s_l)`. -/
theorem IsEuclid.prefactorRate_smul {l : Fin 6 → ℝ} (h : IsEuclid l) {c : ℝ} (hc : 0 < c) :
    prefactorRate (c • l) = c * (phaseC (faceSum l) (quadSum l) (saddle l)).re := by
  have hc' : IsEuclid (c • l) := (isEuclid_smul_iff l hc).2 h
  rw [← hc'.re_phase_saddle, phase_eq_phaseC _ hc'.saddle_im_pos, saddle_smul l hc,
    phaseC_faceSum_smul l hc, re_ofReal_mul]

/-- The Regge action has degree one: `S(cl) = c Im ψ_l(s_l)`. -/
theorem IsEuclid.reggeAction_smul {l : Fin 6 → ℝ} (h : IsEuclid l) {c : ℝ} (hc : 0 < c) :
    PR.reggeAction (c • l) = c * (phaseC (faceSum l) (quadSum l) (saddle l)).im := by
  have hc' : IsEuclid (c • l) := (isEuclid_smul_iff l hc).2 h
  rw [← hc'.im_phase_saddle, phase_eq_phaseC _ hc'.saddle_im_pos, saddle_smul l hc,
    phaseC_faceSum_smul l hc, im_ofReal_mul]

/-! ## Elementary estimates -/

/-- The normalized Racah sum minus the cosine term is bounded by the error of the complex
leading form: with `E = (2π)² N √N e^{−Nψ}`,
`|N √N q e^{−N Re ψ} (−Im ΔF/π) + (q/(π(2π)²)) Im(e^{iN Im ψ} M)| ≤ q/(π(2π)²) |E ΔF − M|`. -/
lemma abs_lead_sub_le {N q : ℝ} (hq : 0 ≤ q) (Ψ ΔF M : ℂ) :
    |N * √N * q * Real.exp (-(N * Ψ.re)) * (-ΔF.im / π) -
        -(q / (π * (2 * π) ^ 2)) * (cexp ((N * Ψ.im : ℝ) * I) * M).im| ≤
      q / (π * (2 * π) ^ 2) *
        ‖(((2 * π) ^ 2 * N * √N : ℝ) : ℂ) * cexp (-(N * Ψ)) * ΔF - M‖ := by
  have hw : ‖cexp ((N * Ψ.im : ℝ) * I)‖ = 1 := norm_exp_ofReal_mul_I _
  have hE : cexp ((N * Ψ.im : ℝ) * I) * cexp (-(N * Ψ)) = (Real.exp (-(N * Ψ.re)) : ℂ) := by
    rw [← Complex.exp_add, ofReal_exp]
    congr 1
    apply Complex.ext <;> simp
  have hprod : cexp ((N * Ψ.im : ℝ) * I) *
      ((((2 * π) ^ 2 * N * √N : ℝ) : ℂ) * cexp (-(N * Ψ)) * ΔF - M) =
      (((2 * π) ^ 2 * N * √N * Real.exp (-(N * Ψ.re)) : ℝ) : ℂ) * ΔF -
        cexp ((N * Ψ.im : ℝ) * I) * M := by
    rw [mul_sub, ofReal_mul ((2 * π) ^ 2 * N * √N) (Real.exp (-(N * Ψ.re))), ← hE]
    ring
  have key : N * √N * q * Real.exp (-(N * Ψ.re)) * (-ΔF.im / π) -
        -(q / (π * (2 * π) ^ 2)) * (cexp ((N * Ψ.im : ℝ) * I) * M).im =
      -(q / (π * (2 * π) ^ 2)) * (cexp ((N * Ψ.im : ℝ) * I) *
        ((((2 * π) ^ 2 * N * √N : ℝ) : ℂ) * cexp (-(N * Ψ)) * ΔF - M)).im := by
    rw [hprod, sub_im, im_ofReal_mul]
    field_simp
    ring
  have hpos : 0 ≤ q / (π * (2 * π) ^ 2) := div_nonneg hq (by positivity)
  rw [key, abs_mul, abs_neg, abs_of_nonneg hpos]
  refine mul_le_mul_of_nonneg_left ((abs_im_le_norm _).trans ?_) hpos
  rw [norm_mul, hw, one_mul]

/-- Near a point of the closed upper half-plane the real part of the phase is at most its value
there plus `δ`, on a closed disc of radius `η < η₀`. -/
lemma exists_ball_re_phaseC_le (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z₀ : ℂ} (hz₀ : 0 ≤ z₀.im)
    {δ : ℝ} (hδ : 0 < δ) {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ η, 0 < η ∧ η < η₀ ∧ ∀ z : ℂ, 0 ≤ z.im → ‖z - z₀‖ ≤ η →
      (phaseC A B z).re ≤ (phaseC A B z₀).re + δ := by
  obtain ⟨η', hη', hball⟩ :=
    Metric.continuousWithinAt_iff.1 (continuousOn_phaseC A B z₀ hz₀) δ hδ
  refine ⟨min (η' / 2) (η₀ / 2), lt_min (half_pos hη') (half_pos hη₀),
    (min_le_right _ _).trans_lt (half_lt_self hη₀), fun z hz hzz => ?_⟩
  have hd : dist z z₀ < η' := by
    rw [dist_eq_norm]
    exact hzz.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hη'))
  have h1 := hball hz hd
  rw [dist_eq_norm] at h1
  have h3 := (le_abs_self _).trans (abs_re_le_norm (phaseC A B z - phaseC A B z₀))
  rw [sub_re] at h3
  linarith

/-- The fundamental estimate along a segment `t ↦ z + t v`, `t ∈ [a, b]`. -/
lemma norm_sub_le_of_line {F f : ℂ → ℂ} {z v : ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Ico a b, HasDerivAt F (f (z + t * v)) (z + t * v))
    (hM : ∀ t ∈ Ico a b, ‖f (z + t * v)‖ ≤ M)
    (hFb : ContinuousAt F (z + b * v)) :
    ‖F (z + b * v) - F (z + a * v)‖ ≤ M * ‖v‖ * (b - a) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + (t : ℂ) * v) v t := fun t => by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const v).const_add z
  exact norm_sub_le_of_path (γ := fun t : ℝ => z + (t : ℂ) * v) (γ' := fun _ => v) hab
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt)
    (fun _ _ => le_rfl) hF hM hFb

/-- Combination of the two rays and the two outer pieces: if `E(b − c)` and `E(d − c)` are
`±M/2` up to `ρ`, then `E(a − e)` is `M` up to `2ρ + |E|(o₁ + o₂)`. -/
lemma norm_four_le {E M a b c d e : ℂ} {ρ o₁ o₂ : ℝ}
    (h₁ : ‖E * (b - c) - M / 2‖ ≤ ρ) (h₂ : ‖E * (d - c) + M / 2‖ ≤ ρ)
    (h₃ : ‖a - b‖ ≤ o₁) (h₄ : ‖e - d‖ ≤ o₂) :
    ‖E * (a - e) - M‖ ≤ 2 * ρ + ‖E‖ * (o₁ + o₂) := by
  have hid : E * (a - e) - M = (E * (b - c) - M / 2) - (E * (d - c) + M / 2) +
      (E * (a - b) - E * (e - d)) := by ring
  rw [hid]
  have h5 : ‖E * (a - b) - E * (e - d)‖ ≤ ‖E‖ * (o₁ + o₂) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left h₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left h₄ (norm_nonneg _))
  have h6 := norm_sub_le (E * (b - c) - M / 2) (E * (d - c) + M / 2)
  have h7 := norm_add_le ((E * (b - c) - M / 2) - (E * (d - c) + M / 2))
    (E * (a - b) - E * (e - d))
  linarith

/-- `C λ² √λ e^{−λδ} → 0` for `δ > 0`. -/
lemma tendsto_pow_sqrt_mul_exp_neg {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    Tendsto (fun lam : ℕ => C * ((lam : ℝ) ^ 2 * √(lam : ℝ) * Real.exp (-(lam * δ)))) atTop
      (𝓝 0) := by
  have hsq : ∀ lam : ℕ, √(lam : ℝ) ≤ lam := fun lam => by
    rcases Nat.eq_zero_or_pos lam with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ lam := Nat.one_le_cast.2 h
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
  have h3 : Tendsto (fun lam : ℕ => ((lam : ℝ) * δ) ^ 3 * Real.exp (-((lam : ℝ) * δ))) atTop
      (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hδ)
  have h4 := h3.div_const (δ ^ 3)
  rw [zero_div] at h4
  have hmain : Tendsto (fun lam : ℕ => (lam : ℝ) ^ 2 * √(lam : ℝ) * Real.exp (-(lam * δ)))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun lam => by positivity) (fun lam => ?_) h4
    have he : ((lam : ℝ) * δ) ^ 3 * Real.exp (-((lam : ℝ) * δ)) / δ ^ 3 =
        (lam : ℝ) ^ 3 * Real.exp (-((lam : ℝ) * δ)) := by
      rw [div_eq_iff (pow_ne_zero 3 hδ.ne')]
      ring
    rw [he]
    have hl : 0 ≤ (lam : ℝ) ^ 2 * Real.exp (-((lam : ℝ) * δ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (hsq lam) hl]
  have := hmain.const_mul C
  rwa [mul_zero] at this

/-! ## The outer pieces of the contour -/

/-- **The outer pieces are exponentially small.** Let `α` be the steepest-descent line of the
phase `ψ` of `l` from the point `s₀ + r_c v` of a descent ray, landing at the real point `x`,
and let `ψ_λ → ψ` uniformly on compact subsets of the closed upper half-plane, `D_λ → Re ψ(s₀)`
and `Q_λ → s₀ + r v` with `0 < r ≤ r_c`. If the derivatives `G_λ` obey
`|G_λ(w)| ≤ λ C e^{λ Re ψ_λ(w)}` off a strip along the real axis and on the real points `reg_λ`,
and these contain the real points within `η₀` of `x`, then there are a real point `p` within `η₀`
of `x` and `C, δ > 0` with `|F(p) − F(Q_λ)| ≤ C λ e^{λ(D_λ − δ)}` for every primitive `F` of
`G_λ` continuous at `p`. The path is the segment from `Q_λ` to `s₀ + r v`, the ray to
`s₀ + r_c v`, the descent line up to a point `α(T')` close to `x`, and the vertical segment down
to `p = Re α(T')`. -/
theorem IsEuclid.outer_side {l : Fin 6 → ℝ} (h : IsEuclid l) {ψ : ℕ → ℂ → ℂ}
    (hU : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | 0 ≤ z.im} → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ lam in atTop, ∀ z ∈ K, ‖ψ lam z - phaseC (faceSum l) (quadSum l) z‖ < δ)
    {s₀ v : ℂ} {β : ℝ} (hβ : 0 < β) {D : ℕ → ℝ}
    (hD : Tendsto D atTop (𝓝 (phaseC (faceSum l) (quadSum l) s₀).re))
    {G : ℕ → ℂ → ℂ} {reg : ℕ → ℝ → Prop}
    (hG : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ᶠ lam : ℕ in atTop, ∀ w : ℂ, 0 < w.im →
      (c ≤ w.im ∨ reg lam w.re) → ‖G lam w‖ ≤ lam * C * Real.exp (lam * (ψ lam w).re))
    {r rc T x η₀ : ℝ} {α : ℝ → ℂ} (hr : 0 < r) (hrc : r ≤ rc)
    (hray : ∀ t ∈ Icc (0 : ℝ) rc, 0 < (s₀ + t * v).im ∧
      (phaseC (faceSum l) (quadSum l) (s₀ + t * v)).re ≤
        (phaseC (faceSum l) (quadSum l) s₀).re - β / 4 * t ^ 2)
    (hα : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) (s₀ + rc * v) T α)
    (hx : Tendsto α (𝓝[<] T) (𝓝 (x : ℂ))) (hη₀ : 0 < η₀)
    (hcond : ∀ᶠ lam : ℕ in atTop, ∀ q : ℝ, |q - x| < η₀ → reg lam q)
    {Q : ℕ → ℂ} (hQ : Tendsto Q atTop (𝓝 (s₀ + r * v))) :
    ∃ p : ℝ, |p - x| < η₀ ∧ ∃ C δ : ℝ, 0 < δ ∧ ∀ᶠ lam : ℕ in atTop, ∀ F : ℂ → ℂ,
      (∀ w : ℂ, 0 < w.im → HasDerivAt F (G lam w) w) → ContinuousAt F p →
      ‖F p - F (Q lam)‖ ≤ C * lam * Real.exp (lam * (D lam - δ)) := by
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = β * r ^ 2 / 16 := ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; exact div_pos (mul_pos hβ (pow_pos hr 2)) (by norm_num)
  -- the ray beyond `r`
  have hA : ∀ t ∈ Icc r rc, 0 < (s₀ + t * v).im ∧
      (phaseC (faceSum l) (quadSum l) (s₀ + t * v)).re ≤
        (phaseC (faceSum l) (quadSum l) s₀).re - 4 * δ₀ := fun t ht => by
    obtain ⟨h1, h2⟩ := hray t ⟨hr.le.trans ht.1, ht.2⟩
    refine ⟨h1, h2.trans ?_⟩
    have hrt : r ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
    have := mul_le_mul_of_nonneg_left hrt (div_nonneg hβ.le (by norm_num : (0 : ℝ) ≤ 4))
    rw [hδ₀]
    linarith
  -- the descent line
  have hB : ∀ t ∈ Ico 0 T, (phaseC (faceSum l) (quadSum l) (α t)).re ≤
      (phaseC (faceSum l) (quadSum l) s₀).re - 4 * δ₀ := fun t ht => by
    rw [h.phaseC_lift hα t ht, sub_re, ofReal_re]
    linarith [ht.1, (hA rc ⟨hrc, le_rfl⟩).2]
  -- the landing point
  have hxH : (0 : ℝ) ≤ (x : ℂ).im := by simp
  have hlim : Tendsto (fun t => (phaseC (faceSum l) (quadSum l) (α t)).re) (𝓝[<] T)
      (𝓝 (phaseC (faceSum l) (quadSum l) x).re) := by
    have hα' : Tendsto α (𝓝[<] T) (𝓝[{z : ℂ | 0 ≤ z.im}] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hx, by
        filter_upwards [Ico_mem_nhdsLT hα.pos] with t ht using (hα.mem t ht).1.le⟩
    exact (continuous_re.tendsto _).comp (((continuousOn_phaseC _ _) x hxH).tendsto.comp hα')
  have hC : (phaseC (faceSum l) (quadSum l) x).re ≤
      (phaseC (faceSum l) (quadSum l) s₀).re - 4 * δ₀ :=
    le_of_tendsto hlim (by filter_upwards [Ico_mem_nhdsLT hα.pos] with t ht using hB t ht)
  obtain ⟨η, hη, hηη₀, hball⟩ :=
    exists_ball_re_phaseC_le (faceSum l) (quadSum l) hxH hδ₀pos hη₀
  -- a point `α T'` of the descent line close to `x`
  obtain ⟨T', hT'x, hT'⟩ :=
    ((hx.eventually (Metric.ball_mem_nhds _ hη)).and (Ico_mem_nhdsLT hα.pos)).exists
  have hT'x' : ‖α T' - x‖ < η := by rw [← dist_eq_norm]; exact hT'x
  have hpx : |(α T').re - x| < η₀ := by
    have := abs_re_le_norm (α T' - x)
    rw [sub_re, ofReal_re] at this
    linarith
  have hpcim : 0 < (α T').im := (hα.mem T' hT').1
  have hsub : ∀ t ∈ Icc 0 T', t ∈ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hT'.2⟩
  have hαc : ContinuousOn α (Icc 0 T') := fun t ht =>
    ((hα.deriv t (hsub t ht)).continuousWithinAt).mono (fun u hu => hsub u hu)
  obtain ⟨S, hS0, hS⟩ : ∃ S : ℝ, 0 ≤ S ∧
      ∀ t ∈ Icc 0 T', ‖descentField (faceSum l) (quadSum l) (α t)‖ ≤ S := by
    obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun t =>
      descentField (faceSum l) (quadSum l) (α t)) (fun t ht =>
        ((h.contDiffAt_descentField (hα.mem t (hsub t ht))).continuousAt).comp_continuousWithinAt
          (hαc t ht))
    exact ⟨S, (norm_nonneg _).trans (hS 0 ⟨le_rfl, hT'.1⟩), hS⟩
  -- a disc around the end `s₀ + r v` of the ray
  have hQ₀ := hA r ⟨le_rfl, hrc⟩
  obtain ⟨η₁, hη₁, hη₁Q, hball₁⟩ :=
    exists_ball_re_phaseC_le (faceSum l) (quadSum l) hQ₀.1.le hδ₀pos (half_pos hQ₀.1)
  -- a lower bound `c` for the imaginary part along the path
  have hrayc : Continuous fun t : ℝ => (s₀ + t * v).im :=
    continuous_im.comp (continuous_const.add (continuous_ofReal.mul continuous_const))
  obtain ⟨t₁, ht₁, hmin₁⟩ := isCompact_Icc.exists_isMinOn
    (f := fun t : ℝ => (s₀ + t * v).im) (nonempty_Icc.2 hrc) hrayc.continuousOn
  obtain ⟨t₂, ht₂, hmin₂⟩ := isCompact_Icc.exists_isMinOn (f := fun t : ℝ => (α t).im)
    (nonempty_Icc.2 hT'.1) (continuous_im.comp_continuousOn hαc)
  have hm1 : ∀ t ∈ Icc r rc, (s₀ + t₁ * v).im ≤ (s₀ + t * v).im := fun t ht =>
    isMinOn_iff.1 hmin₁ t ht
  have hm2 : ∀ t ∈ Icc 0 T', (α t₂).im ≤ (α t).im := fun t ht => isMinOn_iff.1 hmin₂ t ht
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min ((s₀ + r * v).im / 2) (min (s₀ + t₁ * v).im (α t₂).im) :=
    ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]
    exact lt_min (half_pos hQ₀.1) (lt_min (hA t₁ ht₁).1 (hα.mem t₂ (hsub t₂ ht₂)).1)
  have hc1 : c ≤ (s₀ + r * v).im / 2 := by rw [hc]; exact min_le_left _ _
  have hc2 : ∀ t ∈ Icc r rc, c ≤ (s₀ + t * v).im := fun t ht => by
    rw [hc]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (hm1 t ht))
  have hc3 : ∀ t ∈ Icc 0 T', c ≤ (α t).im := fun t ht => by
    rw [hc]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (hm2 t ht))
  have hK₁ : ∀ z : ℂ, ‖z - (s₀ + r * v)‖ ≤ η₁ → c ≤ z.im ∧ 0 < z.im ∧
      (phaseC (faceSum l) (quadSum l) z).re ≤ (phaseC (faceSum l) (quadSum l) s₀).re - 3 * δ₀ :=
    fun z hz => by
    have h1 := abs_im_le_norm (z - (s₀ + r * v))
    rw [sub_im] at h1
    have h2 := (abs_le.1 (h1.trans hz)).1
    have hzc : c ≤ z.im := by linarith
    exact ⟨hzc, hcpos.trans_le hzc,
      (hball₁ z (hcpos.trans_le hzc).le hz).trans (by linarith [hQ₀.2])⟩
  -- four compact sets on which `ψ_λ` is close to `ψ`
  have hU₁ := hU (Metric.closedBall (s₀ + r * v) η₁) (isCompact_closedBall _ _)
    (fun z hz => (hK₁ z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.1.le) δ₀ hδ₀pos
  have hU₂ := hU ((fun t : ℝ => s₀ + t * v) '' Icc r rc)
    (isCompact_Icc.image (continuous_const.add (continuous_ofReal.mul continuous_const)))
    (by rintro _ ⟨t, ht, rfl⟩; exact (hA t ht).1.le) δ₀ hδ₀pos
  have hU₃ := hU (α '' Icc 0 T') (isCompact_Icc.image_of_continuousOn hαc)
    (by rintro _ ⟨t, ht, rfl⟩; exact (hα.mem t (hsub t ht)).1.le) δ₀ hδ₀pos
  have hU₄ := hU (Metric.closedBall (x : ℂ) η ∩ {z : ℂ | 0 ≤ z.im})
    ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_im))
    inter_subset_right δ₀ hδ₀pos
  have hDev : ∀ᶠ lam in atTop, (phaseC (faceSum l) (quadSum l) s₀).re - δ₀ < D lam :=
    hD.eventually (lt_mem_nhds (by linarith))
  have hQev := hQ.eventually (Metric.ball_mem_nhds _ hη₁)
  obtain ⟨Ck, hCk, hGev⟩ := hG c hcpos
  refine ⟨(α T').re, hpx, Ck * (‖((α T').re : ℂ) - α T'‖ + S * T' + ‖v‖ * (rc - r) + η₁), δ₀,
    hδ₀pos, ?_⟩
  filter_upwards [hU₁, hU₂, hU₃, hU₄, hDev, hQev, hGev, hcond] with
    lam hu₁ hu₂ hu₃ hu₄ hDl hQl hGl hcl
  intro F hFd hFp
  have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg lam
  have hM0 : 0 ≤ (lam : ℝ) * Ck * Real.exp (lam * (D lam - δ₀)) :=
    mul_nonneg (mul_nonneg hl hCk.le) (Real.exp_pos _).le
  have hMb : ∀ w : ℂ, 0 < w.im → (c ≤ w.im ∨ reg lam w.re) →
      (phaseC (faceSum l) (quadSum l) w).re ≤ (phaseC (faceSum l) (quadSum l) s₀).re - 3 * δ₀ →
      ‖ψ lam w - phaseC (faceSum l) (quadSum l) w‖ < δ₀ →
      ‖G lam w‖ ≤ lam * Ck * Real.exp (lam * (D lam - δ₀)) := fun w hw hcw hre hclose => by
    refine (hGl w hw hcw).trans ?_
    have h1 := (le_abs_self _).trans
      (abs_re_le_norm (ψ lam w - phaseC (faceSum l) (quadSum l) w))
    rw [sub_re] at h1
    have h2 : (ψ lam w).re ≤ D lam - δ₀ := by linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hl))
      (mul_nonneg hl hCk.le)
  -- the segment from `Q_λ` to `s₀ + r v`
  have hQd : ‖Q lam - (s₀ + r * v)‖ < η₁ := by rw [← dist_eq_norm]; exact hQl
  have hseg : ‖F (s₀ + r * v) - F (Q lam)‖ ≤
      lam * Ck * Real.exp (lam * (D lam - δ₀)) * η₁ := by
    have hpt : ∀ t ∈ Ico (0 : ℝ) 1, ‖Q lam + t * (s₀ + r * v - Q lam) - (s₀ + r * v)‖ ≤ η₁ :=
      fun t ht => by
      have := (convex_closedBall (s₀ + r * v) η₁).add_smul_sub_mem
        (Metric.mem_closedBall.2 (by rw [dist_eq_norm]; exact hQd.le))
        (Metric.mem_closedBall_self hη₁.le) (Ico_subset_Icc_self ht)
      rwa [Complex.real_smul, Metric.mem_closedBall, dist_eq_norm] at this
    have h0 : Q lam + ((0 : ℝ) : ℂ) * (s₀ + r * v - Q lam) = Q lam := by simp
    have h1 : Q lam + ((1 : ℝ) : ℂ) * (s₀ + r * v - Q lam) = s₀ + r * v := by simp
    have := norm_sub_le_of_line (F := F) (f := G lam) (z := Q lam) (v := s₀ + r * v - Q lam)
      (a := 0) (b := 1) zero_le_one
      (fun t ht => hFd _ (hK₁ _ (hpt t ht)).2.1)
      (fun t ht => hMb _ (hK₁ _ (hpt t ht)).2.1 (Or.inl (hK₁ _ (hpt t ht)).1)
        (hK₁ _ (hpt t ht)).2.2
        (hu₁ _ (Metric.mem_closedBall.2 (by rw [dist_eq_norm]; exact hpt t ht))))
      (by rw [h1]; exact (hFd _ hQ₀.1).continuousAt)
    rw [h0, h1, sub_zero, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact hQd.le) hM0)
  -- the ray from `s₀ + r v` to `s₀ + r_c v`
  have hrayb : ‖F (s₀ + rc * v) - F (s₀ + r * v)‖ ≤
      lam * Ck * Real.exp (lam * (D lam - δ₀)) * ‖v‖ * (rc - r) :=
    norm_sub_le_of_line hrc (fun t ht => hFd _ (hA t (Ico_subset_Icc_self ht)).1)
      (fun t ht => hMb _ (hA t (Ico_subset_Icc_self ht)).1
        (Or.inl (hc2 t (Ico_subset_Icc_self ht)))
        ((hA t (Ico_subset_Icc_self ht)).2.trans (by linarith))
        (hu₂ _ (mem_image_of_mem _ (Ico_subset_Icc_self ht))))
      (hFd _ (hA rc ⟨hrc, le_rfl⟩).1).continuousAt
  -- the descent line from `s₀ + r_c v` to `α T'`
  have hliftb : ‖F (α T') - F (s₀ + rc * v)‖ ≤
      lam * Ck * Real.exp (lam * (D lam - δ₀)) * S * (T' - 0) := by
    rw [← hα.start]
    exact norm_sub_le_of_path (γ' := fun t => descentField (faceSum l) (quadSum l) (α t))
      hT'.1 hαc
      (fun t ht => (hα.deriv t (hsub t (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Ico_mem_nhdsGE_of_mem' (hsub t (Ico_subset_Icc_self ht))))
      (fun t ht => hS t (Ico_subset_Icc_self ht))
      (fun t ht => hFd _ (hα.mem t (hsub t (Ico_subset_Icc_self ht))).1)
      (fun t ht => hMb _ (hα.mem t (hsub t (Ico_subset_Icc_self ht))).1
        (Or.inl (hc3 t (Ico_subset_Icc_self ht)))
        ((hB t (hsub t (Ico_subset_Icc_self ht))).trans (by linarith))
        (hu₃ _ (mem_image_of_mem _ (Ico_subset_Icc_self ht))))
      (hFd _ hpcim).continuousAt
  -- the vertical segment from `α T'` down to the real point `Re α(T')`
  have hdrop : ‖F ((α T').re : ℂ) - F (α T')‖ ≤
      lam * Ck * Real.exp (lam * (D lam - δ₀)) * ‖((α T').re : ℂ) - α T'‖ * (1 - 0) := by
    have hx1 : α T' ∈ Metric.closedBall (x : ℂ) ‖α T' - x‖ :=
      Metric.mem_closedBall.2 (le_of_eq (dist_eq_norm _ _))
    have hx2 : ((α T').re : ℂ) ∈ Metric.closedBall (x : ℂ) ‖α T' - x‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      have := abs_re_le_norm (α T' - x)
      rwa [sub_re, ofReal_re] at this
    have hpt : ∀ t ∈ Ico (0 : ℝ) 1, 0 < (α T' + t * (((α T').re : ℂ) - α T')).im ∧
        (α T' + t * (((α T').re : ℂ) - α T')).re = (α T').re ∧
        ‖α T' + t * (((α T').re : ℂ) - α T') - x‖ ≤ η := fun t ht => by
      refine ⟨?_, ?_, ?_⟩
      · rw [show (α T' + t * (((α T').re : ℂ) - α T')).im = (1 - t) * (α T').im by
          simp only [add_im, mul_im, ofReal_re, ofReal_im, sub_im]; ring]
        exact mul_pos (by linarith [ht.2]) hpcim
      · simp only [add_re, mul_re, ofReal_re, ofReal_im, sub_re]; ring
      · have := (convex_closedBall (x : ℂ) ‖α T' - x‖).add_smul_sub_mem hx1 hx2
          (Ico_subset_Icc_self ht)
        rw [Complex.real_smul, Metric.mem_closedBall, dist_eq_norm] at this
        exact this.trans hT'x'.le
    have h0 : α T' + ((0 : ℝ) : ℂ) * (((α T').re : ℂ) - α T') = α T' := by simp
    have h1 : α T' + ((1 : ℝ) : ℂ) * (((α T').re : ℂ) - α T') = ((α T').re : ℂ) := by simp
    have := norm_sub_le_of_line (F := F) (f := G lam) (z := α T') (v := ((α T').re : ℂ) - α T')
      (a := 0) (b := 1) zero_le_one
      (fun t ht => hFd _ (hpt t ht).1)
      (fun t ht => hMb _ (hpt t ht).1 (Or.inr (by rw [(hpt t ht).2.1]; exact hcl _ hpx))
        ((hball _ (hpt t ht).1.le (hpt t ht).2.2).trans (by linarith))
        (hu₄ _ ⟨Metric.mem_closedBall.2 (by rw [dist_eq_norm]; exact (hpt t ht).2.2),
          (hpt t ht).1.le⟩))
      (by rw [h1]; exact hFp)
    rwa [h0, h1] at this
  have h_a := norm_sub_le_norm_sub_add_norm_sub (F ((α T').re : ℂ)) (F (α T')) (F (Q lam))
  have h_b := norm_sub_le_norm_sub_add_norm_sub (F (α T')) (F (s₀ + rc * v)) (F (Q lam))
  have h_c := norm_sub_le_norm_sub_add_norm_sub (F (s₀ + rc * v)) (F (s₀ + r * v)) (F (Q lam))
  linarith

/-! ## The asymptotic formula -/

set_option maxHeartbeats 1600000 in
/-- **Ponzano–Regge asymptotics of Racah's sum.** For spins `j` whose lengths form a Euclidean
tetrahedron, `√√V²(ℓ) e^{−Re ψ(s)} {λj} − cos(S_R(ℓ) + π/4)/(√(12π)(2π)²) → 0` with
`ℓ = λj + ½`. Racah's sum is `−Im(F(p_R) − F(p_L))/π` for a primitive `F` of the rescaled
kernel; the path from `p_L` to `p_R` runs along the two descent rays of the saddle, whose
contributions are given by `ray_estimate`, and two outer pieces, which `IsEuclid.outer_side`
shows to be exponentially smaller. -/
theorem racahSumAsymptotics : RacahSumAsymptotics := by
  intro j hj
  obtain ⟨l, hl⟩ : ∃ l : Fin 6 → ℝ, l = fun e => (j e : ℝ) := ⟨_, rfl⟩
  have h : IsEuclid l := by rw [hl]; exact hj
  have hlim : Tendsto (lengthsDir j) atTop (𝓝 l) := by rw [hl]; exact tendsto_lengthsDir j
  have hsad : Tendsto (fun lam : ℕ => saddle (lengthsDir j lam)) atTop (𝓝 (saddle l)) := by
    rw [hl]; exact tendsto_saddle_lengthsDir hj
  have hphs : Tendsto (fun lam : ℕ => phaseC (faceSum (lengthsDir j lam))
      (quadSum (lengthsDir j lam)) (saddle (lengthsDir j lam))) atTop
      (𝓝 (phaseC (faceSum l) (quadSum l) (saddle l))) := by
    rw [hl]; exact tendsto_phaseC_saddle_lengthsDir hj
  have hdir : Tendsto (fun lam : ℕ => saddleDir (lengthsDir j lam)) atTop
      (𝓝 (saddleDir l)) := by
    rw [hl]; exact tendsto_saddleDir_lengthsDir hj
  have hU : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | 0 ≤ z.im} → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ lam : ℕ in atTop, ∀ z ∈ K, ‖phaseC (faceSum (lengthsDir j lam))
        (quadSum (lengthsDir j lam)) z - phaseC (faceSum l) (quadSum l) z‖ < δ :=
    fun K hK hKH δ hδ => by rw [hl]; exact eventually_norm_phaseC_lengthsDir_sub_lt j hK hKH hδ
  have hfN : ∀ i, faceSum l i = faceN j i := fun i => by rw [hl]; exact faceSum_natCast j i
  have hqN : ∀ k, quadSum l k = quadN j k := fun k => by rw [hl]; exact quadSum_natCast j k
  -- the contour of the limit tetrahedron
  obtain ⟨K₀, rc, τ₁, τ₂, T₁, T₂, α₁, α₂, x₁, x₂, hrc, -, hτ₁, hτ₂, hray₀, -, -, hα₁, hx₁, hα₂,
    hx₂, -, -, ⟨k₀, hk₀⟩, hx₂pos, ⟨i₀, hi₀⟩⟩ := h.exists_contour
  obtain ⟨ru, Ku, β, hru, hβ, hev⟩ := h.eventually_valley_bounds
  have hevm := hlim.eventually hev
  have hs₀ : 0 < (saddle l).im := h.saddle_im_pos
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (min rc ru) (2 * (saddle l).im / 9) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]; exact lt_min (lt_min hrc hru) (div_pos (mul_pos two_pos hs₀) (by norm_num))
  have hrrc : r ≤ rc := by rw [hr]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrru : r ≤ ru := by rw [hr]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrs : r ≤ 2 * (saddle l).im / 9 := by rw [hr]; exact min_le_right _ _
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (saddle l).im / 3 := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; exact div_pos hs₀ (by norm_num)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = ∑ i, |faceSum l i| + ∑ k, |quadSum l k| := ⟨_, rfl⟩
  have hΛA : ∀ i, |faceSum l i| ≤ Λ := fun i => by
    rw [hΛ]
    linarith [Finset.single_le_sum (f := fun i => |faceSum l i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i), Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
        abs_nonneg (quadSum l k))]
  have hΛB : ∀ k, |quadSum l k| ≤ Λ := fun k => by
    rw [hΛ]
    linarith [Finset.single_le_sum (f := fun k => |quadSum l k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k), Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
        abs_nonneg (faceSum l i))]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛA 0)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖saddle l‖ + 2 + 2 * r + Λ := ⟨_, rfl⟩
  obtain ⟨Cr, hCr⟩ := ray_estimate (K := Ku) (R := R) hr0 hβ hy0
  -- the two outer pieces
  have hβl : 0 < ‖saddleCoeff l‖ := norm_pos_iff.2 h.saddleCoeff_ne_zero
  have hvc : ∀ ε τ : ℝ, Continuous fun u : ℂ => valleyDir u ε τ := fun ε τ => by
    unfold valleyDir; fun_prop
  have hD : Tendsto (fun lam : ℕ => (phaseC (faceSum (lengthsDir j lam))
      (quadSum (lengthsDir j lam)) (saddle (lengthsDir j lam))).re) atTop
      (𝓝 (phaseC (faceSum l) (quadSum l) (saddle l)).re) := (continuous_re.tendsto _).comp hphs
  have hG : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ᶠ lam : ℕ in atTop, ∀ w : ℂ, 0 < w.im →
      (c ≤ w.im ∨ kernelRegion j lam w.re) → ‖scaledKernel j lam w‖ ≤ lam * C *
        Real.exp (lam * (phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam)) w).re) :=
    fun c hc => by
    obtain ⟨C, hC, hb⟩ := exists_norm_scaledKernel_le j hc
    exact ⟨C, hC, (eventually_ne_atTop 0).mono fun lam hlam => hb lam hlam⟩
  have hQ : ∀ ε τ : ℝ, Tendsto (fun lam : ℕ => saddle (lengthsDir j lam) +
      r * valleyDir (saddleDir (lengthsDir j lam)) ε τ) atTop
      (𝓝 (saddle l + r * valleyDir (saddleDir l) ε τ)) := fun ε τ =>
    hsad.add (tendsto_const_nhds.mul (((hvc ε τ).tendsto _).comp hdir))
  have hrayR : ∀ t ∈ Icc (0 : ℝ) rc, 0 < (saddle l + t * valleyDir (saddleDir l) 1 τ₁).im ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir (saddleDir l) 1 τ₁)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖saddleCoeff l‖ / 4 * t ^ 2 :=
    fun t ht => ⟨(hray₀ 1 (by norm_num) τ₁ hτ₁ t ht).1, (hray₀ 1 (by norm_num) τ₁ hτ₁ t ht).2.2⟩
  have hrayL : ∀ t ∈ Icc (0 : ℝ) rc, 0 < (saddle l + t * valleyDir (saddleDir l) (-1) τ₂).im ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir (saddleDir l) (-1) τ₂)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖saddleCoeff l‖ / 4 * t ^ 2 :=
    fun t ht => ⟨(hray₀ (-1) (by norm_num) τ₂ hτ₂ t ht).1,
      (hray₀ (-1) (by norm_num) τ₂ hτ₂ t ht).2.2⟩
  rw [hqN] at hk₀
  rw [hfN] at hi₀
  obtain ⟨ηR, hηR⟩ : ∃ ηR : ℝ, ηR = (x₁ - quadN j k₀) / 2 := ⟨_, rfl⟩
  have hηR0 : 0 < ηR := by rw [hηR]; linarith
  have hcondR : ∀ᶠ lam : ℕ in atTop, ∀ q : ℝ, |q - x₁| < ηR → kernelRegion j lam q := by
    filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat 2).eventually (gt_mem_nhds hηR0)]
      with lam hlam q hq
    have := (abs_lt.1 hq).1
    exact Or.inr ⟨k₀, by linarith⟩
  obtain ⟨ηL, hηL⟩ : ∃ ηL : ℝ, ηL = min (x₂ / 2) ((faceN j i₀ - x₂) / 2) := ⟨_, rfl⟩
  have hηL1 : ηL ≤ x₂ / 2 := by rw [hηL]; exact min_le_left _ _
  have hηL2 : ηL ≤ (faceN j i₀ - x₂) / 2 := by rw [hηL]; exact min_le_right _ _
  have hηL0 : 0 < ηL := by rw [hηL]; exact lt_min (by linarith) (by linarith)
  have hcondL : ∀ᶠ lam : ℕ in atTop, ∀ q : ℝ, |q - x₂| < ηL → kernelRegion j lam q :=
    Eventually.of_forall fun lam q hq => by
      have h1 := (abs_lt.1 hq).1
      have h2 := (abs_lt.1 hq).2
      exact Or.inl ⟨by linarith, i₀, by linarith⟩
  obtain ⟨pR, hpR, CR, δR, hδR, hRev⟩ := h.outer_side
    (ψ := fun lam => phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))) hU hβl hD
    (G := scaledKernel j) (reg := kernelRegion j) hG hr0 hrrc hrayR hα₁ hx₁ hηR0 hcondR (hQ 1 τ₁)
  obtain ⟨pL, hpL, CL, δL, hδL, hLev⟩ := h.outer_side
    (ψ := fun lam => phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))) hU hβl hD
    (G := scaledKernel j) (reg := kernelRegion j) hG hr0 hrrc hrayL hα₂ hx₂ hηL0 hcondL
    (hQ (-1) τ₂)
  have hpRq : (quadN j k₀ : ℝ) + ηR < pR := by
    have := (abs_lt.1 hpR).1; rw [hηR] at this ⊢; linarith
  have hpLf : pL < faceN j i₀ := by have := (abs_lt.1 hpL).2; linarith
  -- eventual facts along the sequence `λ`
  have hsc : ∀ᶠ lam : ℕ in atTop, ‖saddle (lengthsDir j lam) - saddle l‖ <
      min 1 ((saddle l).im / 3) :=
    (Metric.tendsto_nhds.1 hsad _ (lt_min one_pos (div_pos hs₀ (by norm_num : (0 : ℝ) < 3)))).mono
      fun lam h => by rwa [dist_eq_norm] at h
  have hAc : ∀ᶠ lam : ℕ in atTop, ∀ i, |faceSum (lengthsDir j lam) i - faceSum l i| < 1 :=
    Filter.eventually_all.2 fun i =>
      (Metric.tendsto_nhds.1 (((continuous_faceSum i).tendsto l).comp hlim) 1 one_pos).mono
        fun lam h => by rw [Real.dist_eq] at h; exact h
  have hBc : ∀ᶠ lam : ℕ in atTop, ∀ k, |quadSum (lengthsDir j lam) k - quadSum l k| < 1 :=
    Filter.eventually_all.2 fun k =>
      (Metric.tendsto_nhds.1 (((continuous_quadSum k).tendsto l).comp hlim) 1 one_pos).mono
        fun lam h => by rw [Real.dist_eq] at h; exact h
  have hl1 : ∀ᶠ lam : ℕ in atTop, (1 : ℝ) ≤ lam := tendsto_natCast_atTop_atTop.eventually_ge_atTop 1
  have hlR : ∀ᶠ lam : ℕ in atTop, 2 * (R + 1) ≤ (lam : ℝ) * y ^ 2 :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * (R + 1) / y ^ 2)).mono
      fun lam h => (div_le_iff₀ (pow_pos hy0 2)).1 h
  have hlY : ∀ᶠ lam : ℕ in atTop, 12 * ((R + 1) / y) ^ 2 + 4 ≤ (lam : ℝ) * y :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ((12 * ((R + 1) / y) ^ 2 + 4) / y)).mono
      fun lam h => (div_le_iff₀ hy0).1 h
  have hlη : ∀ᶠ lam : ℕ in atTop, 2 ≤ (lam : ℝ) * ηR :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / ηR)).mono
      fun lam h => (div_le_iff₀ hηR0).1 h
  -- the bound and its limit
  refine squeeze_zero_norm' (a := fun lam : ℕ => √(√(vol2l (lengthsDir j lam))) /
      (π * (2 * π) ^ 2) * (2 * (Cr / √(lam : ℝ)) +
        (2 * π) ^ 2 * (CR * ((lam : ℝ) ^ 2 * √(lam : ℝ) * Real.exp (-(lam * δR)))) +
        (2 * π) ^ 2 * (CL * ((lam : ℝ) ^ 2 * √(lam : ℝ) * Real.exp (-(lam * δL)))))) ?_ ?_
  swap
  · have hq : Tendsto (fun lam : ℕ => √(√(vol2l (lengthsDir j lam))) / (π * (2 * π) ^ 2)) atTop
        (𝓝 (√(√(vol2l l)) / (π * (2 * π) ^ 2))) :=
      ((continuous_vol2l.sqrt.sqrt.tendsto l).comp hlim).div_const _
    have h1 : Tendsto (fun lam : ℕ => Cr / √(lam : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h4 := ((h1.const_mul 2).add ((tendsto_pow_sqrt_mul_exp_neg hδR CR).const_mul
      ((2 * π) ^ 2))).add ((tendsto_pow_sqrt_mul_exp_neg hδL CL).const_mul ((2 * π) ^ 2))
    simp only [mul_zero, add_zero] at h4
    have h5 := hq.mul h4
    rw [mul_zero] at h5
    exact h5
  filter_upwards [hevm, hsc, hAc, hBc, hl1, hlR, hlY, hlη, eventually_ne_atTop 0, hRev, hLev]
    with lam hm hscl hAcl hBcl hl1l hlRl hlYl hlηl hl0 hRl hLl
  obtain ⟨hmE, hmβ, hmray⟩ := hm
  have hN : (0 : ℝ) < lam := Nat.cast_pos.2 (Nat.pos_of_ne_zero hl0)
  -- the primitive of the rescaled kernel
  have hxL : (lam * pL - 3 / 2 : ℝ) < faceN (fun e => lam * j e) i₀ := by
    rw [faceN_mul]; push_cast
    nlinarith [mul_le_mul_of_nonneg_left hpLf.le hN.le]
  have hxR : (quadN (fun e => lam * j e) k₀ : ℝ) < lam * pR - 3 / 2 := by
    rw [quadN_mul]; push_cast
    have := mul_lt_mul_of_pos_left hpRq hN
    rw [mul_add] at this
    linarith
  obtain ⟨Φ, hΦd, hΦ1, hΦ2, hΦs⟩ :=
    racahSum_eq_im_primitive (fun e => lam * j e) ⟨i₀, hxL⟩ ⟨k₀, hxR⟩
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun w => Φ (((lam : ℝ) : ℂ) * w - 3 / 2) := ⟨_, rfl⟩
  have hFd : ∀ w : ℂ, 0 < w.im → HasDerivAt F (scaledKernel j lam w) w := fun w hw => by
    rw [hF]; unfold scaledKernel
    exact hasDerivAt_rescale (f := racahKernel (faceN fun e => lam * j e)
      (quadN fun e => lam * j e)) hN hΦd hw
  have hcast : ∀ p : ℝ, (((lam : ℝ) * p - 3 / 2 : ℝ) : ℂ) = ((lam : ℝ) : ℂ) * (p : ℂ) - 3 / 2 :=
    fun p => by push_cast; ring
  have hFc : ∀ p : ℝ, ContinuousAt Φ (((lam : ℝ) * p - 3 / 2 : ℝ) : ℂ) →
      ContinuousAt F (p : ℂ) := fun p hp => by
    rw [hF]
    exact ContinuousAt.comp_of_eq (f := fun w : ℂ => ((lam : ℝ) : ℂ) * w - 3 / 2) hp
      (by fun_prop) (hcast p).symm
  have hsum : racahSum (fun e => lam * j e) = -(F pR - F pL).im / π := by
    rw [hΦs, hcast, hcast, hF]
  -- the two rays
  have hA : ∀ i, (lam : ℝ) * faceSum (lengthsDir j lam) i = faceN (fun e => lam * j e) i + 3 / 2 :=
    fun i => by
    rw [← faceSum_smul, ← lengths_eq_smul j hl0, lengths_eq_add_half, faceSum_add_half]
  have hB : ∀ k, (lam : ℝ) * quadSum (lengthsDir j lam) k = quadN (fun e => lam * j e) k + 2 :=
    fun k => by
    rw [← quadSum_smul, ← lengths_eq_smul j hl0, lengths_eq_add_half, quadSum_add_half]
  have hbox : ∀ ε τ : ℝ, ε ^ 2 = 1 → |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      y ≤ (saddle (lengthsDir j lam) + t * valleyDir (saddleDir (lengthsDir j lam)) ε τ).im ∧
      ‖saddle (lengthsDir j lam) + t * valleyDir (saddleDir (lengthsDir j lam)) ε τ‖ ≤ R ∧
      (∀ i, ‖saddle (lengthsDir j lam) + t * valleyDir (saddleDir (lengthsDir j lam)) ε τ -
        faceSum (lengthsDir j lam) i‖ ≤ R) ∧
      ∀ k, ‖saddle (lengthsDir j lam) + t * valleyDir (saddleDir (lengthsDir j lam)) ε τ -
        quadSum (lengthsDir j lam) k‖ ≤ R := fun ε τ hε hτ t ht => by
    have hv := norm_valleyDir_le (norm_saddleDir (lengthsDir j lam)) hε hτ
    have htv : ‖(t : ℂ) * valleyDir (saddleDir (lengthsDir j lam)) ε τ‖ ≤ 3 / 2 * r := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg ht.1]
      linarith [mul_le_mul ht.2 hv (norm_nonneg _) hr0.le]
    have hs1 : ‖saddle (lengthsDir j lam) - saddle l‖ < 1 := hscl.trans_le (min_le_left _ _)
    have hs2 : ‖saddle (lengthsDir j lam) - saddle l‖ < (saddle l).im / 3 :=
      hscl.trans_le (min_le_right _ _)
    have hz : ‖saddle (lengthsDir j lam) + t * valleyDir (saddleDir (lengthsDir j lam)) ε τ‖ ≤
        ‖saddle l‖ + 1 + 3 / 2 * r := by
      have := norm_sub_norm_le (saddle (lengthsDir j lam)) (saddle l)
      have := norm_add_le (saddle (lengthsDir j lam))
        ((t : ℂ) * valleyDir (saddleDir (lengthsDir j lam)) ε τ)
      linarith
    have hi1 := (abs_im_le_norm (saddle (lengthsDir j lam) - saddle l)).trans hs2.le
    have hi2 := (abs_im_le_norm ((t : ℂ) * valleyDir (saddleDir (lengthsDir j lam)) ε τ)).trans htv
    rw [sub_im] at hi1
    have hi1' := neg_abs_le ((saddle (lengthsDir j lam)).im - (saddle l).im)
    have hi2' := neg_abs_le (((t : ℂ) * valleyDir (saddleDir (lengthsDir j lam)) ε τ).im)
    refine ⟨?_, hz.trans (by linarith), fun i => ?_, fun k => ?_⟩
    · rw [add_im, hy]; linarith
    · have h1 := norm_sub_le (saddle (lengthsDir j lam) +
        t * valleyDir (saddleDir (lengthsDir j lam)) ε τ) ((faceSum (lengthsDir j lam) i : ℝ) : ℂ)
      rw [norm_real, Real.norm_eq_abs] at h1
      have h2 := abs_sub_abs_le_abs_sub (faceSum (lengthsDir j lam) i) (faceSum l i)
      linarith [hAcl i, hΛA i]
    · have h1 := norm_sub_le (saddle (lengthsDir j lam) +
        t * valleyDir (saddleDir (lengthsDir j lam)) ε τ) ((quadSum (lengthsDir j lam) k : ℝ) : ℂ)
      rw [norm_real, Real.norm_eq_abs] at h1
      have h2 := abs_sub_abs_le_abs_sub (quadSum (lengthsDir j lam) k) (quadSum l k)
      linarith [hBcl k, hΛB k]
  have hr1 := hCr (faceN fun e => lam * j e) (quadN fun e => lam * j e)
    (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam)) (saddle (lengthsDir j lam))
    (saddleCoeff (lengthsDir j lam)) (saddleDir (lengthsDir j lam)) 1 τ₁ lam F
    (norm_saddleDir _) hmE.mul_saddleDir_sq hmβ (by norm_num) hτ₁
    (fun t ht => hmray 1 (by norm_num) τ₁ hτ₁ t ⟨ht.1, ht.2.trans hrru⟩)
    (hbox 1 τ₁ (by norm_num) hτ₁) hA hB (sum_faceSum_eq_sum_quadSum _) hl1l hlRl hlYl hFd
  have hr2 := hCr (faceN fun e => lam * j e) (quadN fun e => lam * j e)
    (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam)) (saddle (lengthsDir j lam))
    (saddleCoeff (lengthsDir j lam)) (saddleDir (lengthsDir j lam)) (-1) τ₂ lam F
    (norm_saddleDir _) hmE.mul_saddleDir_sq hmβ (by norm_num) hτ₂
    (fun t ht => hmray (-1) (by norm_num) τ₂ hτ₂ t ⟨ht.1, ht.2.trans hrru⟩)
    (hbox (-1) τ₂ (by norm_num) hτ₂) hA hB (sum_faceSum_eq_sum_quadSum _) hl1l hlRl hlYl hFd
  rw [ofReal_one, one_mul] at hr1
  rw [ofReal_neg, ofReal_one, neg_one_mul, neg_div, sub_neg_eq_add] at hr2
  have h3 := hRl F hFd (hFc pR hΦ2)
  have h4 := hLl F hFd (hFc pL hΦ1)
  have key := norm_four_le hr1 hr2 h3 h4
  -- the norm of the normalising factor
  have hEn : ‖(((2 * π) ^ 2 * (lam : ℝ) * √(lam : ℝ) : ℝ) : ℂ) * cexp (-(((lam : ℝ) : ℂ) *
      phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))
        (saddle (lengthsDir j lam))))‖ = (2 * π) ^ 2 * lam * √(lam : ℝ) * Real.exp (-(lam *
      (phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))
        (saddle (lengthsDir j lam))).re)) := by
    rw [norm_mul, norm_real, Real.norm_of_nonneg (by positivity), norm_exp, neg_re, re_ofReal_mul]
  have hEo : ∀ C δ : ℝ, ‖(((2 * π) ^ 2 * (lam : ℝ) * √(lam : ℝ) : ℝ) : ℂ) * cexp (-(((lam : ℝ) : ℂ) *
      phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))
        (saddle (lengthsDir j lam))))‖ * (C * lam * Real.exp (lam *
      ((phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))
        (saddle (lengthsDir j lam))).re - δ))) =
      (2 * π) ^ 2 * (C * ((lam : ℝ) ^ 2 * √(lam : ℝ) * Real.exp (-(lam * δ)))) := fun C δ => by
    rw [hEn]
    have hx : Real.exp (-(lam * (phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))
        (saddle (lengthsDir j lam))).re)) * Real.exp (lam *
        ((phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))
          (saddle (lengthsDir j lam))).re - δ)) = Real.exp (-(lam * δ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← hx]; ring
  rw [mul_add, hEo CR δR, hEo CL δL] at key
  -- the target
  rw [Real.norm_eq_abs, lengths_eq_smul j hl0, sqrt_sqrt_vol2l_smul hN,
    hmE.prefactorRate_smul hN, hmE.reggeAction_smul hN, hsum, ← hmE.im_lead_main]
  refine (abs_lead_sub_le (N := lam) (Real.sqrt_nonneg _) _ _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Real.sqrt_nonneg _) (by positivity))
  linarith

/-- **The Ponzano–Regge formula** for the 6j symbol, without hypotheses: for integer spins `j`
with triangular faces and `V²(j) > 0`, `√(12π √V²(ℓ)) {λj} − cos(S_R(ℓ) + π/4) → 0` as
`λ → ∞`, with `ℓ = λj + ½`. -/
theorem ponzanoReggeFormula : PR.PonzanoReggeFormula :=
  ponzanoReggeFormula_of_racahSumAsymptotics racahSumAsymptotics

end Lightlike.Asymptotics

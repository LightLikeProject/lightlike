import Lightlike.Asymptotics.KernelBound
import Lightlike.Asymptotics.Homogeneity

/-!
# The leading form of Racah's kernel

On the open upper half-plane Racah's kernel `f(z) = π T(z)/sin(π z)` (`racahKernel`) is a
quotient of Gamma functions (`racahT_eq_Gamma`). In the variable `Z = z + 3/2`, with
`Aᵢ = aᵢ + 3/2`, `Bₖ = bₖ + 2` and `Σᵢ Aᵢ = Σₖ Bₖ`, Stirling's formula with exact remainder
(`Gamma_half_add`) turns it into the exact identity (`racahKernel_eq_lead`)

  `f(Z − 3/2) = e^{ψ(Z)} P_A(Z) e^{E(Z)} / ((2π)² (1 + e^{2πiZ}))`,

where `ψ = phaseC A B` is the continued phase, `P_A(w) = ∏ᵢ (w − Aᵢ)^{−1/2}` (`leadP`) is the
amplitude, and `E` (`kernelErr`) collects the Stirling remainders `μ` and the half-shift defects
`ρ(X) = f(X + ½) − f(X) − ½ log X` (`stirRho`), `f(w) = w log w − w`. The factor
`1/(1 + e^{2πiZ})` comes from `π/sin(π(Z − 3/2)) = π/cos(πZ) = 2π e^{iπZ}/(1 + e^{2πiZ})`.

Under the rescaling `A ↦ NA`, `B ↦ NB`, `Z = Nx`, the phase is homogeneous (`phaseC_smul`), the
amplitude scales as `P_{NA}(Nx) = P_A(x)/N²` (`leadP_smul`), and the error is `O(1/N)` uniformly
on sets `Im x ≥ y > 0` of bounded size: `‖ρ(X)‖ ≤ 1/‖X‖` (`norm_stirRho_le`), the sector bound
for `μ` (`norm_stirMu_le_of_im`), `‖e^{2πiNx}‖ = e^{−2πN Im x}`. The result
(`norm_racahKernel_sub_lead_le`) is

  `‖(2π)² N² f(Nx − 3/2) − e^{Nψ(x)} P_A(x)‖ ≤ (C/N) ‖e^{Nψ(x)} P_A(x)‖`

with `C` depending only on `y` and the size bound, the leading term of the saddle-point
estimate of Racah's sum. The amplitude is bounded and Lipschitz on `Im w ≥ y`
(`norm_leadP_le`, `norm_leadP_sub_le`), as Laplace's method needs.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-! ## Definitions -/

/-- The half-shift defect of Stirling's exponent, `ρ(X) = f(X + ½) − f(X) − ½ log X` with
`f(w) = w log w − w` (`stirF`). It is `O(1/‖X‖)` on the slit plane (`norm_stirRho_le`). -/
noncomputable def stirRho (X : ℂ) : ℂ := stirF (X + 1 / 2) - stirF X - log X / 2

/-- The amplitude of Racah's kernel, `P_A(w) = exp(−½ Σᵢ log(w − Aᵢ))`, the product of the
principal square roots `(w − Aᵢ)^{−1/2}`. -/
noncomputable def leadP (A : Fin 4 → ℝ) (w : ℂ) : ℂ := cexp (-(∑ i, log (w - A i)) / 2)

/-- The Stirling error of Racah's kernel,
`E(Z) = μ(Z) − Σᵢ μ(Z − Aᵢ + ½) − Σₖ μ(Bₖ − Z) − Σᵢ ρ(Z − Aᵢ)`, with `μ` the remainder of
Stirling's formula (`stirMu`) and `ρ` the half-shift defect (`stirRho`). -/
noncomputable def kernelErr (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (Z : ℂ) : ℂ :=
  stirMu Z - ∑ i, stirMu (Z - A i + 1 / 2) - ∑ k, stirMu (B k - Z) - ∑ i, stirRho (Z - A i)

/-! ## The exact identity -/

/-- The Stirling exponents of the seven Gamma factors of Racah's kernel combine to the continued
phase, the logarithm of the amplitude, the error `E` and `−iπZ`, when `Σᵢ Aᵢ = Σₖ Bₖ`. -/
lemma stir_exponent_eq {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hAB : ∑ i, A i = ∑ k, B k) {Z : ℂ}
    (hZ : 0 < Z.im) :
    (stirF Z + stirMu Z) - ∑ i, (stirF (Z - A i + 1 / 2) + stirMu (Z - A i + 1 / 2)) -
        ∑ k, (stirF (B k - Z) + stirMu (B k - Z)) =
      phaseC A B Z + -(∑ i, log (Z - A i)) / 2 + kernelErr A B Z - π * I * Z := by
  have hB : ∀ k, stirF ((B k : ℂ) - Z) =
      -xlog (Z - B k) - π * I * ((B k : ℂ) - Z) - ((B k : ℂ) - Z) := by
    intro k
    have h := log_neg_of_im_pos (w := Z - B k) (by simpa using hZ)
    rw [show -(Z - (B k : ℂ)) = (B k : ℂ) - Z by ring] at h
    simp only [stirF, xlog, h]
    ring
  have hA : ∀ i, stirF (Z - A i + 1 / 2) =
      xlog (Z - A i) - (Z - A i) + log (Z - A i) / 2 + stirRho (Z - A i) := by
    intro i
    simp only [stirRho, stirF, xlog]
    ring
  have hbal : (∑ i, (A i : ℂ)) = ∑ k, (B k : ℂ) := by exact_mod_cast hAB
  simp only [hA, hB]
  simp only [phaseC, kernelErr, stirF, xlog, Fin.sum_univ_four, Fin.sum_univ_three] at hbal ⊢
  linear_combination (-1 : ℂ) * hbal

/-- `π/sin(π(Z − 3/2)) = 2π e^{iπZ}/(1 + e^{2πiZ})`, as `sin(π(Z − 3/2)) = cos(πZ)`. -/
lemma sin_pi_mul_sub_three_halves (Z : ℂ) :
    Complex.sin (π * (Z - 3 / 2)) =
      (1 + cexp (π * I * Z) ^ 2) / (2 * cexp (π * I * Z)) := by
  have h1 : (π : ℂ) * (Z - 3 / 2) = (π * Z - π) - π / 2 := by ring
  rw [h1, Complex.sin_sub_pi_div_two, Complex.cos_sub_pi, neg_neg]
  have h2 := Complex.two_cos (π * Z)
  have hu : cexp (π * I * Z) ≠ 0 := Complex.exp_ne_zero _
  have h3 : cexp (-(π * Z) * I) = (cexp (π * I * Z))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; ring
  have h4 : cexp (π * Z * I) = cexp (π * I * Z) := by congr 1; ring
  rw [h3, h4] at h2
  have h5 : 2 * Complex.cos (π * Z) * cexp (π * I * Z) = cexp (π * I * Z) ^ 2 + 1 := by
    rw [h2, add_mul, inv_mul_cancel₀ hu]; ring
  rw [eq_div_iff (mul_ne_zero two_ne_zero hu)]
  linear_combination h5

/-- **The exact leading form of Racah's kernel.** For `Aᵢ = aᵢ + 3/2`, `Bₖ = bₖ + 2` with
`Σᵢ Aᵢ = Σₖ Bₖ` and `Im Z > 0`,
`f(Z − 3/2) = e^{ψ(Z)} P_A(Z) e^{E(Z)} / ((2π)² (1 + e^{2πiZ}))`. -/
theorem racahKernel_eq_lead (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) {A : Fin 4 → ℝ} {B : Fin 3 → ℝ}
    (hA : ∀ i, A i = a i + 3 / 2) (hB : ∀ k, B k = b k + 2) (hAB : ∑ i, A i = ∑ k, B k)
    {Z : ℂ} (hZ : 0 < Z.im) :
    racahKernel a b (Z - 3 / 2) = cexp (phaseC A B Z) * leadP A Z * cexp (kernelErr A B Z) /
      ((2 * π) ^ 2 * (1 + cexp (2 * π * I * Z))) := by
  set c : ℂ := ((√(2 * π) : ℝ) : ℂ) with hc
  have hc2 : c ^ 2 = 2 * π := by
    rw [hc, ← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc2; simp at hc2
  have hz : 0 < (Z - 3 / 2).im := by simpa using hZ
  have hslit : ∀ w : ℂ, w.im ≠ 0 → w ∈ slitPlane := fun w hw => mem_slitPlane_iff.2 (Or.inr hw)
  have hG0 : Complex.Gamma (Z - 3 / 2 + 2) = c * cexp (stirF Z + stirMu Z) := by
    rw [show Z - 3 / 2 + 2 = Z + 1 / 2 by ring]; exact Gamma_half_add (hslit Z hZ.ne')
  have hGA : ∀ i, Complex.Gamma (Z - 3 / 2 - (a i : ℂ) + 1) =
      c * cexp (stirF (Z - A i + 1 / 2) + stirMu (Z - A i + 1 / 2)) := by
    intro i
    rw [show Z - 3 / 2 - (a i : ℂ) + 1 = (Z - A i + 1 / 2) + 1 / 2 by rw [hA i]; push_cast; ring]
    refine Gamma_half_add (hslit _ ?_)
    rw [show (Z - (A i : ℂ) + 1 / 2).im = Z.im by simp]; exact hZ.ne'
  have hGB : ∀ k, Complex.Gamma ((b k : ℂ) - (Z - 3 / 2) + 1) =
      c * cexp (stirF (B k - Z) + stirMu (B k - Z)) := by
    intro k
    rw [show (b k : ℂ) - (Z - 3 / 2) + 1 = ((B k : ℂ) - Z) + 1 / 2 by rw [hB k]; push_cast; ring]
    refine Gamma_half_add (hslit _ ?_)
    rw [show ((B k : ℂ) - Z).im = -Z.im by simp]; exact neg_ne_zero.2 hZ.ne'
  have hT : racahT a b (Z - 3 / 2) =
      cexp (phaseC A B Z + -(∑ i, log (Z - A i)) / 2 + kernelErr A B Z - π * I * Z) / c ^ 6 := by
    rw [racahT_eq_Gamma a b hz, hG0]
    simp only [hGA, hGB]
    rw [← stir_exponent_eq hAB hZ, Finset.prod_inv_distrib, Finset.prod_inv_distrib,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      ← Complex.exp_sum, ← Complex.exp_sum, Complex.exp_sub, Complex.exp_sub]
    simp only [Finset.card_univ, Fintype.card_fin]
    have key : ∀ e0 e1 e2 : ℂ, e1 ≠ 0 → e2 ≠ 0 →
        c * e0 * (c ^ 4 * e1)⁻¹ * (c ^ 3 * e2)⁻¹ = e0 / e1 / e2 / c ^ 6 := by
      intro e0 e1 e2 h1 h2; field_simp
    exact key _ _ _ (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  set u := cexp (π * I * Z) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hun : ‖u‖ < 1 := by
    rw [hu, Complex.norm_exp]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have h1u : 1 + u ^ 2 ≠ 0 := by
    intro h
    have : ‖u ^ 2‖ = 1 := by rw [show u ^ 2 = -1 by linear_combination h, norm_neg, norm_one]
    rw [norm_pow] at this
    nlinarith [norm_nonneg u]
  have hq : cexp (2 * π * I * Z) = u ^ 2 := by
    rw [hu, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hE : cexp (phaseC A B Z + -(∑ i, log (Z - A i)) / 2 + kernelErr A B Z - π * I * Z) =
      cexp (phaseC A B Z) * leadP A Z * cexp (kernelErr A B Z) / u := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_add, leadP]
  rw [racahKernel, hT, hE, sin_pi_mul_sub_three_halves, ← hu, hq]
  have hc6 : c ^ 6 = (2 * π) ^ 3 := by rw [show c ^ 6 = (c ^ 2) ^ 3 by ring, hc2]
  rw [hc6]
  field_simp

/-! ## The amplitude -/

/-- `‖P_A(w)‖ = exp(−½ Σᵢ log ‖w − Aᵢ‖)`. -/
lemma norm_leadP (A : Fin 4 → ℝ) (w : ℂ) :
    ‖leadP A w‖ = Real.exp (-(∑ i, Real.log ‖w - A i‖) / 2) := by
  rw [leadP, Complex.norm_exp]
  congr 1
  simp [log_re, Complex.re_sum]

/-- **The amplitude is bounded** on `Im w ≥ y > 0`: `‖P_A(w)‖ ≤ 1/y²`. -/
theorem norm_leadP_le (A : Fin 4 → ℝ) {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : y ≤ w.im) :
    ‖leadP A w‖ ≤ 1 / y ^ 2 := by
  rw [norm_leadP]
  have hl : ∀ i, Real.log y ≤ Real.log ‖w - A i‖ := fun i => by
    refine Real.log_le_log hy (hw.trans ?_)
    have := Complex.abs_im_le_norm (w - A i)
    simp only [sub_im, ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have hs : 4 * Real.log y ≤ ∑ i, Real.log ‖w - A i‖ := by
    simpa [Fin.sum_univ_four] using
      (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hl i).trans_eq' (by simp)
  calc Real.exp (-(∑ i, Real.log ‖w - A i‖) / 2) ≤ Real.exp (-(2 * Real.log y)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = 1 / y ^ 2 := by
        rw [Real.exp_neg, show 2 * Real.log y = Real.log (y ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]

/-- **Scaling of the amplitude**: `P_{cA}(cw) = P_A(w)/c²` for real `c > 0` and `Im w > 0`. -/
theorem leadP_smul (A : Fin 4 → ℝ) {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.im) :
    leadP (c • A) (c * w) = leadP A w / c ^ 2 := by
  have h : ∀ i, log ((c : ℂ) * w - (((c • A) i : ℝ) : ℂ)) = Real.log c + log (w - A i) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, ofReal_mul, ← mul_sub]
    refine log_ofReal_mul hc fun h0 => ?_
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hs : -(∑ i, log ((c : ℂ) * w - (((c • A) i : ℝ) : ℂ))) / 2 =
      -(∑ i, log (w - A i)) / 2 + ((-2 * Real.log c : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
    simp
    ring
  have hr : Real.exp (-2 * Real.log c) = (c ^ 2)⁻¹ := by
    rw [show -2 * Real.log c = -Real.log (c ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_neg, Real.exp_log (by positivity)]
  rw [leadP, leadP, hs, Complex.exp_add, ← ofReal_exp, hr]
  push_cast
  ring

/-- The derivative of the amplitude, `P_A' = −½ P_A Σᵢ 1/(w − Aᵢ)`, on the open upper
half-plane. -/
theorem hasDerivAt_leadP (A : Fin 4 → ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (leadP A) (leadP A w * (-(∑ i, (w - A i)⁻¹) / 2)) w := by
  have hlog : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      HasDerivAt (fun w : ℂ => log (w - A i)) ((w - A i)⁻¹) w := fun i _ => by
    have hs : w - (A i : ℂ) ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by simp; exact hw.ne'))
    simpa using ((hasDerivAt_id w).sub_const (A i : ℂ)).clog hs
  exact ((HasDerivAt.fun_sum hlog).neg.div_const 2).cexp

/-- **The amplitude is Lipschitz** on `Im w ≥ y > 0`, with constant `2/y³`. -/
theorem norm_leadP_sub_le (A : Fin 4 → ℝ) {y : ℝ} (hy : 0 < y) {w₁ w₂ : ℂ} (h₁ : y ≤ w₁.im)
    (h₂ : y ≤ w₂.im) : ‖leadP A w₂ - leadP A w₁‖ ≤ 2 / y ^ 3 * ‖w₂ - w₁‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := {w : ℂ | y ≤ w.im}) (f' := fun w => leadP A w * (-(∑ i, (w - A i)⁻¹) / 2))
    (fun w hw => (hasDerivAt_leadP A (hy.trans_le hw)).hasDerivWithinAt) (fun w hw => ?_)
    (convex_halfSpace_im_ge y) h₁ h₂
  have hw : y ≤ w.im := hw
  have hinv : ∀ i, ‖(w - (A i : ℂ))⁻¹‖ ≤ 1 / y := fun i => by
    rw [norm_inv, one_div]
    refine inv_anti₀ hy (hw.trans ?_)
    have := Complex.abs_im_le_norm (w - A i)
    simp only [sub_im, ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have hsum : ‖∑ i, (w - (A i : ℂ))⁻¹‖ ≤ 4 * (1 / y) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hinv i).trans (by simp))
  rw [norm_mul, norm_div, norm_neg, Complex.norm_two]
  calc ‖leadP A w‖ * (‖∑ i, (w - (A i : ℂ))⁻¹‖ / 2) ≤ 1 / y ^ 2 * (4 * (1 / y) / 2) :=
        mul_le_mul (norm_leadP_le A hy hw) (by linarith) (by positivity) (by positivity)
    _ = 2 / y ^ 3 := by field_simp; ring

/-! ## The error terms -/

/-- **The half-shift defect is small**: `‖ρ(X)‖ ≤ 1/‖X‖` on the slit plane for `‖X‖ ≥ 1`.
With `ζ = 1/(2X)`, `ρ(X) = ζ/2 + (X + ½)(log(1 + ζ) − ζ)`. -/
theorem norm_stirRho_le {X : ℂ} (hX : X ∈ slitPlane) (h1 : 1 ≤ ‖X‖) :
    ‖stirRho X‖ ≤ 1 / ‖X‖ := by
  have hX0 : X ≠ 0 := slitPlane_ne_zero hX
  have hn : 0 < ‖X‖ := norm_pos_iff.2 hX0
  have hζX : X * (2 * X)⁻¹ = 1 / 2 := by field_simp
  have hζn : ‖(2 * X)⁻¹‖ = 1 / (2 * ‖X‖) := by
    rw [norm_inv, norm_mul, Complex.norm_two, one_div]
  have hζs : ‖(2 * X)⁻¹‖ ≤ 1 / 2 := by
    rw [hζn, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hR := norm_log_one_add_sub_self_le (z := (2 * X)⁻¹) (by linarith)
  have hR' : ‖log (1 + (2 * X)⁻¹) - (2 * X)⁻¹‖ ≤ ‖(2 * X)⁻¹‖ ^ 2 := by
    refine hR.trans ?_
    have : (1 - ‖(2 * X)⁻¹‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    nlinarith [sq_nonneg ‖(2 * X)⁻¹‖]
  have hform : stirRho X =
      (2 * X)⁻¹ / 2 + (X + 1 / 2) * (log (1 + (2 * X)⁻¹) - (2 * X)⁻¹) := by
    simp only [stirRho, stirF]
    rw [log_add_half hX]
    linear_combination hζX
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [one_div, norm_inv, Complex.norm_two, one_div]
  rw [hform]
  calc ‖(2 * X)⁻¹ / 2 + (X + 1 / 2) * (log (1 + (2 * X)⁻¹) - (2 * X)⁻¹)‖
      ≤ ‖(2 * X)⁻¹‖ / 2 + (‖X‖ + 1 / 2) * ‖(2 * X)⁻¹‖ ^ 2 := by
        refine (norm_add_le _ _).trans (add_le_add (by rw [norm_div, Complex.norm_two]) ?_)
        rw [norm_mul]
        exact mul_le_mul ((norm_add_le _ _).trans (by rw [hhalf])) hR' (norm_nonneg _)
          (by positivity)
    _ = 1 / ‖X‖ * ((4 * ‖X‖ + 1) / (8 * ‖X‖)) := by rw [hζn]; field_simp; ring
    _ ≤ 1 / ‖X‖ := by
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [div_le_one (by positivity)]; linarith

/-- **Sector bound for Stirling's remainder**: if `|Im w| ≥ δ ‖w‖` with `δ > 0` and
`‖w‖² ≥ 4/δ²`, then `‖μ(w)‖ ≤ 3/(2δ² ‖w‖)`. -/
theorem norm_stirMu_le_of_im {w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hw : δ * ‖w‖ ≤ |w.im|)
    (hR : 4 / δ ^ 2 ≤ ‖w‖ ^ 2) : ‖stirMu w‖ ≤ 3 / (2 * δ ^ 2 * ‖w‖) := by
  have hn : 0 < ‖w‖ := by
    have : 0 < 4 / δ ^ 2 := by positivity
    nlinarith [norm_nonneg w]
  have hδ1 : δ ≤ 1 := by
    have := Complex.abs_im_le_norm w
    nlinarith
  have h1 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have h2 : δ ^ 2 * ‖w‖ ^ 2 ≤ w.im ^ 2 := by
    have := mul_self_le_mul_self (by positivity) hw
    rw [← sq_abs w.im]; nlinarith
  have h3 : w.re ^ 2 ≤ ((1 - δ ^ 2 / 2) * ‖w‖) ^ 2 := by
    nlinarith [sq_nonneg (δ ^ 2 * ‖w‖)]
  have hre : -(1 - δ ^ 2 / 2) * ‖w‖ ≤ w.re := by
    have := (abs_le_of_sq_le_sq' h3 (by nlinarith)).1
    linarith
  have hc0 : 0 ≤ 1 - δ ^ 2 / 2 := by nlinarith
  have hc1 : 1 - δ ^ 2 / 2 < 1 := by nlinarith
  have hR' : 2 / (1 - (1 - δ ^ 2 / 2)) ≤ ‖w‖ ^ 2 := by
    rw [show 2 / (1 - (1 - δ ^ 2 / 2)) = 4 / δ ^ 2 by field_simp; ring]; exact hR
  refine (norm_stirMu_le hc0 hc1 hre hR').2.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The Stirling error is `O(1/N)` under rescaling.** If `Im x ≥ y > 0`, the norms of `x`,
`x − Aᵢ` and `x − Bₖ` are at most `R`, `N ≥ 1` and `N y² ≥ 2(R + 1)`, then
`‖E_{NA, NB}(Nx)‖ ≤ (12 ((R + 1)/y)² + 4)/(N y)`. -/
theorem norm_kernelErr_smul_le {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} {x : ℂ} {y R N : ℝ}
    (hy : 0 < y) (hyx : y ≤ x.im) (hx : ‖x‖ ≤ R) (hA : ∀ i, ‖x - A i‖ ≤ R)
    (hB : ∀ k, ‖x - B k‖ ≤ R) (hN1 : 1 ≤ N) (hN : 2 * (R + 1) ≤ N * y ^ 2) :
    ‖kernelErr (N • A) (N • B) (N * x)‖ ≤ (12 * ((R + 1) / y) ^ 2 + 4) / (N * y) := by
  have hN0 : 0 < N := by linarith
  have hyR : y ≤ R := hyx.trans ((le_abs_self _).trans ((Complex.abs_im_le_norm x).trans hx))
  have hR0 : 0 < R := hy.trans_le hyR
  set δ : ℝ := y / (R + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hNy : 0 < N * y := by positivity
  -- the generic sector estimate
  have hmu : ∀ w : ℂ, N * y ≤ |w.im| → ‖w‖ ≤ N * (R + 1) →
      ‖stirMu w‖ ≤ 3 / (2 * δ ^ 2 * (N * y)) := by
    intro w hwi hwn
    have hwy : N * y ≤ ‖w‖ := hwi.trans (Complex.abs_im_le_norm w)
    have hw1 : δ * ‖w‖ ≤ |w.im| := by
      calc δ * ‖w‖ ≤ δ * (N * (R + 1)) := mul_le_mul_of_nonneg_left hwn hδ0.le
        _ = N * y := by rw [hδ]; field_simp
        _ ≤ |w.im| := hwi
    have hw2 : 4 / δ ^ 2 ≤ ‖w‖ ^ 2 := by
      have h2 : 2 / δ ≤ N * y := by
        rw [hδ, div_div_eq_mul_div, div_le_iff₀ hy]; nlinarith
      calc 4 / δ ^ 2 = (2 / δ) ^ 2 := by ring
        _ ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (by positivity) (h2.trans hwy) 2
    refine (norm_stirMu_le_of_im hδ0 hw1 hw2).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hwy (by positivity))
  have hcast : ∀ r : ℝ, ((N * r : ℝ) : ℂ) = (N : ℂ) * r := fun r => by push_cast; ring
  have himx : (N * x).im = N * x.im := by simp
  -- the four kinds of terms
  have h0 : ‖stirMu ((N : ℂ) * x)‖ ≤ 3 / (2 * δ ^ 2 * (N * y)) := by
    refine hmu _ ?_ ?_
    · rw [himx, abs_of_pos (by nlinarith)]; exact mul_le_mul_of_nonneg_left hyx hN0.le
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN0.le]; nlinarith
  have hAi : ∀ i, ‖stirMu ((N : ℂ) * x - (((N • A) i : ℝ) : ℂ) + 1 / 2)‖ ≤
      3 / (2 * δ ^ 2 * (N * y)) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, hcast, ← mul_sub]
    refine hmu _ ?_ ?_
    · rw [show ((N : ℂ) * (x - A i) + 1 / 2).im = N * x.im by simp,
        abs_of_pos (by nlinarith)]
      exact mul_le_mul_of_nonneg_left hyx hN0.le
    · refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN0.le,
        show ‖(1 / 2 : ℂ)‖ = 1 / 2 by rw [one_div, norm_inv, Complex.norm_two, one_div]]
      nlinarith [hA i]
  have hBk : ∀ k, ‖stirMu ((((N • B) k : ℝ) : ℂ) - (N : ℂ) * x)‖ ≤
      3 / (2 * δ ^ 2 * (N * y)) := by
    intro k
    rw [Pi.smul_apply, smul_eq_mul, hcast, ← mul_sub]
    refine hmu _ ?_ ?_
    · rw [show ((N : ℂ) * ((B k : ℂ) - x)).im = -(N * x.im) by simp, abs_neg,
        abs_of_pos (by nlinarith)]
      exact mul_le_mul_of_nonneg_left hyx hN0.le
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN0.le, norm_sub_rev]
      nlinarith [hB k]
  have hRi : ∀ i, ‖stirRho ((N : ℂ) * x - (((N • A) i : ℝ) : ℂ))‖ ≤ 1 / (N * y) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, hcast, ← mul_sub]
    have hn : N * y ≤ ‖(N : ℂ) * (x - A i)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN0.le]
      refine mul_le_mul_of_nonneg_left (hyx.trans ?_) hN0.le
      have := Complex.abs_im_le_norm (x - A i)
      simp only [sub_im, ofReal_im, sub_zero] at this
      exact (le_abs_self _).trans this
    have hNy1 : 1 ≤ N * y := by
      have : 2 * (R + 1) ≤ N * y * R := by nlinarith
      nlinarith
    have hs : (N : ℂ) * (x - A i) ∈ slitPlane := by
      refine mem_slitPlane_iff.2 (Or.inr ?_)
      rw [show ((N : ℂ) * (x - A i)).im = N * x.im by simp]
      exact (mul_pos hN0 (hy.trans_le hyx)).ne'
    refine (norm_stirRho_le hs (hNy1.trans hn)).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) hNy hn
  -- summing up
  have hsA : ∑ i, ‖stirMu ((N : ℂ) * x - (((N • A) i : ℝ) : ℂ) + 1 / 2)‖ ≤
      4 * (3 / (2 * δ ^ 2 * (N * y))) :=
    (Finset.sum_le_sum fun i _ => hAi i).trans (by simp)
  have hsB : ∑ k, ‖stirMu ((((N • B) k : ℝ) : ℂ) - (N : ℂ) * x)‖ ≤
      3 * (3 / (2 * δ ^ 2 * (N * y))) :=
    (Finset.sum_le_sum fun k _ => hBk k).trans (by simp)
  have hsR : ∑ i, ‖stirRho ((N : ℂ) * x - (((N • A) i : ℝ) : ℂ))‖ ≤ 4 * (1 / (N * y)) :=
    (Finset.sum_le_sum fun i _ => hRi i).trans (by simp)
  unfold kernelErr
  calc _ ≤ ‖stirMu ((N : ℂ) * x)‖ + ∑ i, ‖stirMu ((N : ℂ) * x - (((N • A) i : ℝ) : ℂ) + 1 / 2)‖ +
        ∑ k, ‖stirMu ((((N • B) k : ℝ) : ℂ) - (N : ℂ) * x)‖ +
        ∑ i, ‖stirRho ((N : ℂ) * x - (((N • A) i : ℝ) : ℂ))‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))) (norm_sum_le _ _)))
          (norm_sum_le _ _))
    _ ≤ 3 / (2 * δ ^ 2 * (N * y)) + 4 * (3 / (2 * δ ^ 2 * (N * y))) +
        3 * (3 / (2 * δ ^ 2 * (N * y))) + 4 * (1 / (N * y)) := by gcongr
    _ = (12 * ((R + 1) / y) ^ 2 + 4) / (N * y) := by rw [hδ]; field_simp; ring

/-- `‖e^E/(1 + q) − 1‖ ≤ 2 (2‖E‖ + ‖q‖)` for `‖E‖ ≤ 1` and `‖q‖ ≤ 1/2`. -/
lemma norm_exp_div_one_add_sub_one_le {E q : ℂ} (hE : ‖E‖ ≤ 1) (hq : ‖q‖ ≤ 1 / 2) :
    ‖cexp E / (1 + q) - 1‖ ≤ 2 * (2 * ‖E‖ + ‖q‖) := by
  have h1q : 1 / 2 ≤ ‖1 + q‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-q)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have h0 : (1 : ℂ) + q ≠ 0 := fun h => by rw [h, norm_zero] at h1q; linarith
  rw [div_sub_one h0, norm_div]
  have hnum : ‖cexp E - (1 + q)‖ ≤ 2 * ‖E‖ + ‖q‖ := by
    rw [show cexp E - (1 + q) = (cexp E - 1) - q by ring]
    exact (norm_sub_le _ _).trans (add_le_add (Complex.norm_exp_sub_one_le hE) le_rfl)
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg E, norm_nonneg q]

/-- The constant of the leading-form estimate, `C(y, R) = 2(2(12((R + 1)/y)² + 4) + 1)/y`. -/
noncomputable def kernelLeadC (y R : ℝ) : ℝ := 2 * (2 * (12 * ((R + 1) / y) ^ 2 + 4) + 1) / y

/-- **The leading form of Racah's kernel under rescaling.** Let `N Aᵢ = aᵢ + 3/2`,
`N Bₖ = bₖ + 2`, `Σᵢ Aᵢ = Σₖ Bₖ`, `Im x ≥ y > 0`, and let the norms of `x`, `x − Aᵢ`, `x − Bₖ`
be at most `R`. If `N ≥ 1`, `N y² ≥ 2(R + 1)` and `N y ≥ 12((R + 1)/y)² + 4`, then
`‖(2π)² N² f(Nx − 3/2) − e^{Nψ(x)} P_A(x)‖ ≤ (C(y, R)/N) ‖e^{Nψ(x)} P_A(x)‖`. -/
theorem norm_racahKernel_sub_lead_le (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) {A : Fin 4 → ℝ}
    {B : Fin 3 → ℝ} {N : ℝ} (hA : ∀ i, N * A i = a i + 3 / 2) (hB : ∀ k, N * B k = b k + 2)
    (hAB : ∑ i, A i = ∑ k, B k) {x : ℂ} {y R : ℝ} (hy : 0 < y) (hyx : y ≤ x.im)
    (hx : ‖x‖ ≤ R) (hxA : ∀ i, ‖x - A i‖ ≤ R) (hxB : ∀ k, ‖x - B k‖ ≤ R) (hN1 : 1 ≤ N)
    (hN : 2 * (R + 1) ≤ N * y ^ 2) (hNE : 12 * ((R + 1) / y) ^ 2 + 4 ≤ N * y) :
    ‖(2 * π) ^ 2 * N ^ 2 * racahKernel a b (N * x - 3 / 2) -
        cexp (N * phaseC A B x) * leadP A x‖ ≤
      kernelLeadC y R / N * ‖cexp (N * phaseC A B x) * leadP A x‖ := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x.im := hy.trans_le hyx
  have hZ : 0 < ((N : ℂ) * x).im := by simp; positivity
  have hAB' : ∑ i, (N • A) i = ∑ k, (N • B) k := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hAB]
  have hk := racahKernel_eq_lead a b (A := N • A) (B := N • B)
    (fun i => by rw [Pi.smul_apply, smul_eq_mul, hA i]) (fun k => by
      rw [Pi.smul_apply, smul_eq_mul, hB k]) hAB' hZ
  rw [phaseC_smul hAB hN0 x, leadP_smul A hN0 hx0] at hk
  set q := cexp (2 * π * I * ((N : ℂ) * x)) with hq
  set E := kernelErr (N • A) (N • B) ((N : ℂ) * x) with hE
  have hNy : 0 < N * y := by positivity
  have hqn : ‖q‖ ≤ 1 / (N * y) := by
    rw [hq, Complex.norm_exp]
    have : (2 * π * I * ((N : ℂ) * x)).re = -(2 * π * (N * x.im)) := by simp
    rw [this, Real.exp_neg, one_div]
    refine inv_anti₀ hNy ?_
    have h1 := Real.add_one_le_exp (2 * π * (N * x.im))
    have h2 : N * y ≤ 2 * π * (N * x.im) := by
      have : N * y ≤ N * x.im := mul_le_mul_of_nonneg_left hyx hN0.le
      nlinarith [Real.pi_gt_three]
    linarith
  have hNy2 : 2 ≤ N * y := by
    have hyR : y ≤ R := hyx.trans ((le_abs_self _).trans ((Complex.abs_im_le_norm x).trans hx))
    have : 2 * (R + 1) ≤ N * y * R := by nlinarith
    nlinarith
  have hq2 : ‖q‖ ≤ 1 / 2 := hqn.trans (by rw [div_le_div_iff₀ hNy (by norm_num)]; linarith)
  have hEn : ‖E‖ ≤ (12 * ((R + 1) / y) ^ 2 + 4) / (N * y) :=
    norm_kernelErr_smul_le hy hyx hx hxA hxB hN1 hN
  have hE1 : ‖E‖ ≤ 1 := hEn.trans (by rw [div_le_one hNy]; exact hNE)
  have h1q : (1 : ℂ) + q ≠ 0 := by
    intro h
    have : ‖q‖ = 1 := by rw [show q = -1 by linear_combination h, norm_neg, norm_one]
    linarith
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hNc : (N : ℂ) ≠ 0 := ofReal_ne_zero.2 hN0.ne'
  have key : (2 * π) ^ 2 * (N : ℂ) ^ 2 * racahKernel a b ((N : ℂ) * x - 3 / 2) -
      cexp (N * phaseC A B x) * leadP A x =
      cexp (N * phaseC A B x) * leadP A x * (cexp E / (1 + q) - 1) := by
    rw [hk]
    field_simp
  rw [key, norm_mul, mul_comm (kernelLeadC y R / N)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_exp_div_one_add_sub_one_le hE1 hq2).trans ?_
  calc 2 * (2 * ‖E‖ + ‖q‖) ≤ 2 * (2 * ((12 * ((R + 1) / y) ^ 2 + 4) / (N * y)) + 1 / (N * y)) := by
        gcongr
    _ = kernelLeadC y R / N := by rw [kernelLeadC]; field_simp

end Lightlike.Asymptotics

import Lightlike.GR.KruskalRegions
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The Schwarzschild exterior in Kruskal coordinates

Gap row G1-020. Source read: S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7,
eqs. (7.78), (7.79), (7.85) (printed pages 187-188); Carroll's `(v, u)` are our `(T, X)`, `G = 1`:

* (7.78) `u = (r/2GM - 1)^{1/2} e^{r/4GM} cosh (t/4GM)`, (7.79) `v = (r/2GM - 1)^{1/2} e^{r/4GM} sinh (t/4GM)`:
  `kruskalChange_exterior`. The Schwarzschild coordinates `(t, r)` enter through the ingoing Eddington–Finkelstein
  time `v_EF = t + r*`, `r* = r + 2M log (r/2M - 1)`, and the chart change `kruskalChange`, whose pull-back of the
  Kruskal metric is the Eddington–Finkelstein metric (`pullback_kruskal_ef`).
* (7.85) the surfaces of constant `t` are `v/u = tanh (t/4GM)`: `kruskalChange_exterior_div`.
* "Our original coordinates `(t, r)` were only good for `r > 2GM`, which is only a part of the manifold": the image
  of the exterior `r > 2M` is exactly region I (`kruskalChange_exterior_mem`, `exists_exterior_of_mem_kruskalI`).
-/

open Matrix Real Set

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- The radial factor `ρ(r) = (r/2M - 1)^{1/2} e^{r/4M}` of the Kruskal coordinates of the exterior. -/
def kruskalRho (r : ℝ) : ℝ := sqrt (r / (2 * M) - 1) * exp (r / (4 * M))

lemma kruskalRho_pos (hM : 0 < M) {r : ℝ} (hr : 2 * M < r) : 0 < kruskalRho M r := by
  have ha : 0 < r / (2 * M) - 1 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
  unfold kruskalRho
  have := sqrt_pos.2 ha
  positivity

/-- `ρ(r)² = F(r)`. -/
lemma kruskalRho_sq (hM : 0 < M) {r : ℝ} (hr : 2 * M < r) : kruskalRho M r ^ 2 = kF M r := by
  have ha : 0 < r / (2 * M) - 1 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have he : exp (r / (2 * M)) = exp (r / (4 * M)) ^ 2 := by
    rw [sq, ← exp_add]; congr 1; field_simp; ring
  unfold kruskalRho kF
  rw [mul_pow, sq_sqrt ha.le, he]

/-- **The Kruskal coordinates of the Schwarzschild exterior** (Carroll (7.78), (7.79)):
`T = ρ(r) sinh (t/4M)`, `X = ρ(r) cosh (t/4M)`, `ρ(r) = (r/2M - 1)^{1/2} e^{r/4M}`. -/
theorem kruskalChange_exterior (hM : 0 < M) {r : ℝ} (hr : 2 * M < r) (t θ φ : ℝ) :
    kruskalChange M ![t + tortoiseExt M r, r, θ, φ] =
      ![kruskalRho M r * sinh (t / (4 * M)), kruskalRho M r * cosh (t / (4 * M)), θ, φ] := by
  have ha : 0 < r / (2 * M) - 1 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have hM0 : M ≠ 0 := hM.ne'
  -- `s = (r/2M - 1)^{1/2} = exp (log (r/2M - 1) / 2)`
  have hs2 : exp (log (r / (2 * M) - 1) / 2) * exp (log (r / (2 * M) - 1) / 2) = r / (2 * M) - 1 := by
    rw [← exp_add, show log (r / (2 * M) - 1) / 2 + log (r / (2 * M) - 1) / 2 = log (r / (2 * M) - 1) by ring,
      exp_log ha]
  have hsq : sqrt (r / (2 * M) - 1) = exp (log (r / (2 * M) - 1) / 2) := by
    conv_lhs => rw [← hs2]
    exact sqrt_mul_self (exp_pos _).le
  have hE : exp ((t + tortoiseExt M r) / (4 * M)) =
      exp (t / (4 * M)) * (sqrt (r / (2 * M) - 1) * exp (r / (4 * M))) := by
    rw [hsq, ← exp_add, ← exp_add]
    congr 1
    unfold tortoiseExt
    field_simp
    ring
  have hE' : kF M r * exp (-((t + tortoiseExt M r) / (4 * M))) =
      exp (-(t / (4 * M))) * (sqrt (r / (2 * M) - 1) * exp (r / (4 * M))) := by
    have h1 : exp (-((t + tortoiseExt M r) / (4 * M))) * exp ((t + tortoiseExt M r) / (4 * M)) = 1 := by
      rw [← exp_add]; simp
    have h2 : exp (-(t / (4 * M))) * exp (t / (4 * M)) = 1 := by
      rw [← exp_add]; simp
    have h3 := kruskalRho_sq M hM hr
    unfold kruskalRho at h3
    have hpos : 0 < exp ((t + tortoiseExt M r) / (4 * M)) := exp_pos _
    apply mul_right_cancel₀ hpos.ne'
    rw [mul_assoc, h1, mul_one, hE, ← h3]
    linear_combination (-(sqrt (r / (2 * M) - 1) * exp (r / (4 * M))) ^ 2) * h2
  ext i
  fin_cases i
  · show (exp ((t + tortoiseExt M r) / (4 * M)) -
        kF M r * exp (-((t + tortoiseExt M r) / (4 * M)))) / 2 = kruskalRho M r * sinh (t / (4 * M))
    rw [hE, hE', sinh_eq]
    unfold kruskalRho
    ring
  · show (exp ((t + tortoiseExt M r) / (4 * M)) +
        kF M r * exp (-((t + tortoiseExt M r) / (4 * M)))) / 2 = kruskalRho M r * cosh (t / (4 * M))
    rw [hE, hE', cosh_eq]
    unfold kruskalRho
    ring
  · rfl
  · rfl

/-- **The surfaces of constant Schwarzschild time are the lines `T/X = tanh (t/4M)`** (Carroll (7.85)). -/
theorem kruskalChange_exterior_div (hM : 0 < M) {r : ℝ} (hr : 2 * M < r) (t θ φ : ℝ) :
    kruskalChange M ![t + tortoiseExt M r, r, θ, φ] 0 / kruskalChange M ![t + tortoiseExt M r, r, θ, φ] 1 =
      tanh (t / (4 * M)) := by
  rw [kruskalChange_exterior M hM hr]
  have hρ := (kruskalRho_pos M hM hr).ne'
  have hc := (cosh_pos (t / (4 * M))).ne'
  show kruskalRho M r * sinh (t / (4 * M)) / (kruskalRho M r * cosh (t / (4 * M))) = tanh (t / (4 * M))
  rw [tanh_eq_sinh_div_cosh]
  field_simp

/-- The Schwarzschild exterior is mapped into region I. -/
theorem kruskalChange_exterior_mem (hM : 0 < M) {r : ℝ} (hr : 2 * M < r) (t : ℝ) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < π) (φ : ℝ) : kruskalChange M ![t + tortoiseExt M r, r, θ, φ] ∈ kruskalI := by
  have hmem : (![t + tortoiseExt M r, r, θ, φ] : Fin 4 → ℝ) ∈ efU :=
    ⟨by show 0 < r; linarith, hθ, hθ'⟩
  refine ⟨kruskalChange_mem M hM hmem, ?_⟩
  rw [kruskalChange_exterior M hM hr]
  show |kruskalRho M r * sinh (t / (4 * M))| < kruskalRho M r * cosh (t / (4 * M))
  have hρ := kruskalRho_pos M hM hr
  rw [abs_mul, abs_of_pos hρ]
  refine mul_lt_mul_of_pos_left ?_ hρ
  rw [abs_lt]
  constructor
  · have := sinh_lt_cosh (-(t / (4 * M)))
    rw [sinh_neg, cosh_neg] at this
    linarith
  · exact sinh_lt_cosh _

/-- **Region I is the Schwarzschild exterior**: every point of region I has Schwarzschild coordinates `(t, r)`
with `r > 2M`. -/
theorem exists_exterior_of_mem_kruskalI (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalI) :
    ∃ t r : ℝ, 2 * M < r ∧ kruskalChange M ![t + tortoiseExt M r, r, y 2, y 3] = y := by
  have hr : 2 * M < kr M y := (two_mul_lt_kr_iff_mem M hM hy.1).2 (Or.inl hy)
  have hρ := kruskalRho_pos M hM hr
  have hX : 0 < y 1 := lt_of_le_of_lt (abs_nonneg _) hy.2
  -- `ρ² = X² - T²`
  have hρ2 : kruskalRho M (kr M y) ^ 2 = y 1 ^ 2 - y 0 ^ 2 := by
    rw [kruskalRho_sq M hM hr]
    unfold kr
    rw [kF_kG M hM hy.1.1]
  refine ⟨4 * M * arsinh (y 0 / kruskalRho M (kr M y)), kr M y, hr, ?_⟩
  rw [kruskalChange_exterior M hM hr]
  have h4 : 4 * M * arsinh (y 0 / kruskalRho M (kr M y)) / (4 * M) =
      arsinh (y 0 / kruskalRho M (kr M y)) := by
    field_simp
  rw [h4, sinh_arsinh, cosh_arsinh]
  have hc : sqrt (1 + (y 0 / kruskalRho M (kr M y)) ^ 2) = y 1 / kruskalRho M (kr M y) := by
    have h5 : 1 + (y 0 / kruskalRho M (kr M y)) ^ 2 = (y 1 / kruskalRho M (kr M y)) ^ 2 := by
      rw [div_pow, div_pow, hρ2]
      have hne : y 1 ^ 2 - y 0 ^ 2 ≠ 0 := by rw [← hρ2]; positivity
      field_simp
      ring
    rw [h5, sqrt_sq (div_pos hX hρ).le]
  rw [hc]
  ext i
  fin_cases i
  · show kruskalRho M (kr M y) * (y 0 / kruskalRho M (kr M y)) = y 0
    field_simp
  · show kruskalRho M (kr M y) * (y 1 / kruskalRho M (kr M y)) = y 1
    field_simp
  · rfl
  · rfl

end Lightlike

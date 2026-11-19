import Lightlike.GR.AdSPoincare
import Lightlike.Spacetime.ChartChange

/-!
# The conformal boundary of anti-de Sitter space

*Global coordinates* (`rads = 1`, `d = 3`): `ds² = -(1 + r²) dt² + dr²/(1 + r²) + r² dΩ²` (`adsGlobal`). With `r = tan ρ`
(`tanChart`) it is `(1/cos²ρ)(-dt² + dρ² + sin²ρ dΩ²)` (`pullback_adsGlobal`): the conformal factor diverges as
`ρ → π/2`, and discarding it gives the metric `-dt² + dρ² + sin²ρ dΩ²` (`adsCompact`), which extends to the
boundary `ρ = π/2` (`adsFactor_tendsto`).

*Poincaré patch*: the dilation `(t, x, y, z) ↦ λ (t, x, y, z)`, `λ > 0`, is an isometry of `adsMetric`
(`adsDilation_isometry`); on the boundary `z = 0` it acts on the Minkowski metric `diag(-1, 1, 1)` by the factor
`λ²` (`dilation_conformal_boundary`): a conformal transformation of the boundary. The rest of the conformal group (special
conformal transformations) is not formalized.

Gap row GE7. Source read (pdftotext): Aharony-Gubser-Maldacena-Ooguri-Oz, arXiv:hep-th/9905111, section 2: global AdS (2.23)
`ds² = R²(-cosh²ρ dτ² + dρ² + sinh²ρ dΩ²)`, its conformal map into one half of the Einstein static universe (2.24), the Poincaré metric (2.27) and
the dilatation `(t, x, u) ↦ (ct, cx, u/c)` (2.28) "identified with the dilatation D in the conformal symmetry group", the conformal group (2.1)-(2.2)
(scale and special conformal transformations); and D. Harlow, *Jerusalem Lectures on Black Holes and Quantum Information*,
arXiv:1409.1231, section 6.1, eqs. (6.4)-(6.6) (global AdS, `r = tan ρ`, "conformally compactify by discarding the diverging
prefactor and including the boundary at ρ = π/2") and section 6.2.2, eq. (6.7) with the text before it (dilatations
`x'^μ = λ x^μ` and special conformal transformations). Hawking–Ellis, ch. 5: not read.
-/

open Matrix Real

noncomputable section

namespace Lightlike

/-- Global anti-de Sitter space (`d = 3`, radius `1`) in coordinates `(t, r, θ, φ)`. -/
def adsGlobal (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal ![-(1 + y 1 ^ 2), 1 / (1 + y 1 ^ 2), y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The compactified metric `-dt² + dρ² + sin²ρ dΩ²` in coordinates `(t, ρ, θ, φ)`. -/
def adsCompact (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal ![-1, 1, sin (y 1) ^ 2, sin (y 1) ^ 2 * sin (y 2) ^ 2]

/-- `r = tan ρ`. -/
def tanChart (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![y 0, tan (y 1), y 2, y 3]

/-- The conformal factor `1/cos² ρ`. -/
def adsFactor (y : Fin 4 → ℝ) : ℝ := 1 / cos (y 1) ^ 2

lemma jac_tanChart {y : Fin 4 → ℝ} (hc : cos (y 1) ≠ 0) :
    jac tanChart y = diagonal ![1, 1 / cos (y 1) ^ 2, 1, 1] := by
  have T0 : ∀ k : Fin 4, pd k (fun z => z 0) y = if k = 0 then 1 else 0 := fun k =>
    pd_coord (n := 4) 0 k (hasDerivAt_id' (y 0))
  have T1 : ∀ k : Fin 4, pd k (fun z => tan (z 1)) y = if k = 1 then 1 / cos (y 1) ^ 2 else 0 := fun k =>
    pd_coord (n := 4) 1 k (Real.hasDerivAt_tan hc)
  have P2 : ∀ k : Fin 4, pd k (fun z => z 2) y = if k = 2 then 1 else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_id' (y 2))
  have P3 : ∀ k : Fin 4, pd k (fun z => z 3) y = if k = 3 then 1 else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_id' (y 3))
  ext μ a
  fin_cases μ <;> fin_cases a <;> simp [jac, tanChart, T0, T1, P2, P3, Matrix.diagonal_apply]

/-- **Global AdS is conformal to the compact metric.** -/
theorem pullback_adsGlobal {y : Fin 4 → ℝ} (hc : cos (y 1) ≠ 0) :
    pullback adsGlobal tanChart y = adsFactor y • adsCompact y := by
  rw [pullback_eq_mul, jac_tanChart hc]
  have hs : sin (y 1) ^ 2 = tan (y 1) ^ 2 * cos (y 1) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  have h1 : 1 + tan (y 1) ^ 2 = 1 / cos (y 1) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]; field_simp; nlinarith [Real.sin_sq_add_cos_sq (y 1)]
  have hg : adsGlobal (tanChart y) = diagonal ![-(1 / cos (y 1) ^ 2), cos (y 1) ^ 2,
      tan (y 1) ^ 2, tan (y 1) ^ 2 * sin (y 2) ^ 2] := by
    simp only [adsGlobal, tanChart, Matrix.cons_val_one, Matrix.cons_val_zero]
    simp [h1]
  rw [hg]
  unfold adsFactor adsCompact
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;> field_simp <;> (try rw [hs]) <;> ring

/-- **The conformal factor diverges at the boundary**: `1/cos² ρ → ∞` as `ρ → π/2` from below. -/
theorem adsFactor_tendsto :
    Filter.Tendsto (fun ρ : ℝ => 1 / cos ρ ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) Filter.atTop := by
  have hc : Filter.Tendsto (fun ρ : ℝ => cos ρ ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Filter.Tendsto (fun ρ : ℝ => cos ρ ^ 2) (nhds (π / 2)) (nhds (cos (π / 2) ^ 2)) :=
        (Real.continuous_cos.pow 2).tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show -(π / 2) < π / 2 by linarith [Real.pi_pos])] with ρ hρ
      exact pow_pos (Real.cos_pos_of_mem_Ioo ⟨hρ.1, hρ.2⟩) 2
  have := hc.inv_tendsto_nhdsGT_zero
  exact this.congr (fun ρ => by simp)

/-- The dilation `x ↦ λ x` (`λ > 0`). -/
def dilation {n : ℕ} (l : ℝ) (y : Fin n → ℝ) : Fin n → ℝ := l • y

lemma jac_dilation {n : ℕ} (l : ℝ) (y : Fin n → ℝ) : jac (dilation l) y = l • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext μ a
  have := pd_coord (n := n) μ a (f := fun t => l * t) (f' := l) (by simpa using (hasDerivAt_id' (y μ)).const_mul l)
  simp only [jac, dilation, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply]
  rw [this]
  by_cases h : a = μ
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **Dilations are isometries of the Poincaré patch of AdS** (`λ ≠ 0`). -/
theorem adsDilation_isometry (L l : ℝ) (hl : l ≠ 0) (y : Fin 4 → ℝ) :
    pullback (adsMetric L) (dilation l) y = adsMetric L y := by
  rw [pullback_eq_mul, jac_dilation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, adsMetric, adsD, dilation, Matrix.diagonal_apply] <;>
    field_simp

/-- The Minkowski metric `diag(-1, 1, 1)` of the boundary of the Poincaré patch. -/
def boundaryMetric (_ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![-1, 1, 1]

/-- **The dilation acts on the boundary conformally**: it multiplies the boundary Minkowski metric by `λ²`. -/
theorem dilation_conformal_boundary (l : ℝ) (y : Fin 3 → ℝ) :
    pullback boundaryMetric (dilation l) y = l ^ 2 • boundaryMetric y := by
  rw [pullback_eq_mul, jac_dilation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, boundaryMetric, Matrix.diagonal_apply] <;> ring

end Lightlike

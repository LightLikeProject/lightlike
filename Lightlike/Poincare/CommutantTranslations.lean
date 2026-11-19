import Lightlike.Poincare.Imprimitivity
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Operators commuting with the translations commute with the functions of the momentum

On the one-particle space `L²(μ; ℂ^{n+1})` over the mass shell the translations act by `e^{i p·a}`. If a bounded
operator `B` commutes with every translation, then it commutes with the multiplication by `φ(p)` for every Schwartz
function `φ` on momentum space (`commute_bcfMul_schwartz`): by Fourier inversion
`φ(p) = ∫ 𝓕φ(ξ) e^{2πi⟨ξ, p⟩} dξ`, so `⟨u, φ(p) v⟩ = ∫ 𝓕φ(ξ) ⟨u, T(a(ξ)) v⟩ dξ` (`inner_bcfMul_schwartz`, Fubini),
with the translation `a(ξ)` of frequency `ξ` (`freqTransl`).

Supporting results for the irreducibility of the one-particle representations; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology BoundedContinuousFunction SchwartzMap Real
open scoped InnerProductSpace FourierTransform

namespace Lightlike.Poincare

noncomputable section

/-- Momentum space with its Euclidean structure (for the Fourier transform). -/
abbrev MomSpace := EuclideanSpace ℝ (Fin 4)

/-- The momentum of a point of the shell, in `MomSpace`. -/
def momE {m : ℝ} (Q : MassShell m) : MomSpace := WithLp.toLp 2 (mom Q)

lemma continuous_momE {m : ℝ} : Continuous (momE (m := m)) := (PiLp.continuous_toLp 2 _).comp continuous_mom

lemma momH_mem_selfAdjoint (p0 : ℝ) (p : Fin 3 → ℝ) : momH p0 p ∈ selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [momH]

/-- The translation of Euclidean frequency `ξ`: `p·a(ξ) = 2π ⟨ξ, p⟩`. -/
def freqTransl (ξ : MomSpace) : Transl :=
  ⟨momH (2 * π * ξ 0) ![-(2 * π * ξ 1), -(2 * π * ξ 2), -(2 * π * ξ 3)], momH_mem_selfAdjoint _ _⟩

lemma coord0_momH (p0 : ℝ) (p : Fin 3 → ℝ) : coord0 (momH p0 p) = p0 := by
  simp [coord0, momH]

lemma pairing_freqTransl {m : ℝ} (Q : MassShell m) (ξ : MomSpace) :
    pairing Q.1 (freqTransl ξ).1 = 2 * π * ⟪ξ, momE Q⟫_ℝ := by
  rw [pairing_eq_minkowski]
  simp only [minkowski, tcoords, freqTransl, coord0_momH, coordV_momH, mom, momE, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, star_trivial]
  ring

variable {m : ℝ} {μ : Measure (MassShell m)} {n : ℕ}

/-- The Schwartz function `φ` of the momentum, as a bounded continuous function on the shell. -/
def schwartzMom (φ : 𝓢(MomSpace, ℂ)) : MassShell m →ᵇ ℂ :=
  φ.toBoundedContinuousFunction.compContinuous ⟨momE, continuous_momE⟩

lemma schwartzMom_apply (φ : 𝓢(MomSpace, ℂ)) (Q : MassShell m) : schwartzMom φ Q = φ (momE Q) := rfl

/-- **Fourier inversion against the translations**: `⟨u, φ(p) v⟩ = ∫ 𝓕φ(ξ) ⟨u, T(a(ξ)) v⟩ dξ`. -/
theorem inner_bcfMul_schwartz [SFinite μ] (φ : 𝓢(MomSpace, ℂ)) (u v : Lp (Spinor n) 2 μ) :
    ⟪u, bcfMul (schwartzMom φ) v⟫_ℂ = ∫ ξ, (𝓕 φ) ξ * ⟪u, translL2 n (freqTransl ξ) v⟫_ℂ := by
  have hinv : ∀ p : MomSpace, φ p = ∫ ξ, Complex.exp (↑(2 * π * ⟪ξ, p⟫_ℝ) * Complex.I) • (𝓕 φ) ξ := by
    intro p
    have h := congrFun (φ.continuous.fourierInv_fourier_eq (φ.integrable (μ := volume)) ((𝓕 φ).integrable (μ := volume))) p
    rw [← h, fourierInv_eq', fourier_coe]
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u v
  -- the integrand on the product
  set F : MassShell m × MomSpace → ℂ := fun z =>
    Complex.exp (↑(2 * π * ⟪z.2, momE z.1⟫_ℝ) * Complex.I) * (𝓕 φ) z.2 * ⟪u z.1, v z.1⟫_ℂ
  have hF : Integrable F (μ.prod volume) := by
    have hprod := hint.mul_prod ((𝓕 φ).integrable (μ := volume))
    refine hprod.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have hc : Continuous fun z : MassShell m × MomSpace =>
          Complex.exp (↑(2 * π * ⟪z.2, momE z.1⟫_ℝ) * Complex.I) * (𝓕 φ) z.2 := by
        have : Continuous fun z : MassShell m × MomSpace => ⟪z.2, momE z.1⟫_ℝ :=
          continuous_snd.inner (continuous_momE.comp continuous_fst)
        exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul this)).mul
          continuous_const)).mul ((𝓕 φ).continuous.comp continuous_snd)
      exact hc.aestronglyMeasurable.mul (hint.1.comp_fst)
    · simp only [F, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [mul_comm]
  -- the left side
  have hL : ⟪u, bcfMul (schwartzMom φ) v⟫_ℂ = ∫ Q, ∫ ξ, F (Q, ξ) ∂volume ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_bcfMul (μ := μ) (schwartzMom φ) v] with Q hQ
    rw [hQ, inner_smul_right, schwartzMom_apply, hinv, ← integral_mul_const]
    rfl
  -- the right side
  have hR : ∫ ξ, (𝓕 φ) ξ * ⟪u, translL2 n (freqTransl ξ) v⟫_ℂ = ∫ ξ, ∫ Q, F (Q, ξ) ∂μ ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [MeasureTheory.L2.inner_def]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_translL2 (μ := μ) n (freqTransl ξ) v] with Q hQ
    rw [hQ, inner_smul_right, pairing_freqTransl]
    simp only [F]
    rw [show Complex.I * (↑(2 * π * ⟪ξ, momE Q⟫_ℝ) : ℂ) = ↑(2 * π * ⟪ξ, momE Q⟫_ℝ) * Complex.I by ring]
    ring
  rw [hL, hR, integral_integral_swap hF]

/-- **An operator commuting with the translations commutes with every Schwartz function of the momentum.** -/
theorem commute_bcfMul_schwartz [SFinite μ] (B : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ)
    (hB : ∀ a f, B (translL2 n a f) = translL2 n a (B f)) (φ : 𝓢(MomSpace, ℂ)) (f : Lp (Spinor n) 2 μ) :
    B (bcfMul (schwartzMom φ) f) = bcfMul (schwartzMom φ) (B f) := by
  refine ext_inner_left ℂ fun u => ?_
  rw [← ContinuousLinearMap.adjoint_inner_left, inner_bcfMul_schwartz, inner_bcfMul_schwartz]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [ContinuousLinearMap.adjoint_inner_left, hB]

end

end Lightlike.Poincare

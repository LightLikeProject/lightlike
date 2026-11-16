import Lightlike.Asymptotics.Lorentzian.Bridge

/-!
# One link of the principal-series vertex as an integral over the chart

Step 1 of the assembly of `eprlVertex = lorVertex`: the combination of EPRL matrix coefficients
along one link is an integral over `ℂ` of `e^S` times the density of `Ω`.
-/

open Matrix Complex
open scoped ComplexConjugate InnerProductSpace
open Lightlike Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz Lightlike.SpinFoam

namespace Lightlike.Asymptotics.Lorentzian

/-- **Unitarity**: `⟪x, π(a⁻¹ b) y⟫ = ⟪π(a) x, π(b) y⟫`. -/
theorem inner_pi_inv_mul (n : ℤ) (ρ : ℝ) (a b : SL2C) (x y : L2C) :
    inner ℂ x (principalSeries n ρ (a⁻¹ * b) y) =
      inner ℂ (principalSeries n ρ a x) (principalSeries n ρ b y) := by
  have h : principalSeries n ρ b y = principalSeries n ρ a (principalSeries n ρ (a⁻¹ * b) y) := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
  rw [h, principalSeries_inner]

/-- **`suV` on a combination of basis vectors**: the combination `Σ c_m Y e_m` of EPRL vectors is the
image under `suV` of the coefficient vector `Σ c_m e_m`. -/
theorem eprlVec_sum (γ : ℝ) (J : ℕ) (c : Fin (dsp (J : ℤ) 0 + 1) → ℂ) :
    ∑ m : Fin (dsp (J : ℤ) 0 + 1), c m • eprlVec γ J m =
      suV (J : ℤ) (eprlRho γ J) 0 (∑ m : Fin (dsp (J : ℤ) 0 + 1),
        c m • EuclideanSpace.single m (1 : ℂ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, eprlVec, dite_eq_left m.2]

/-- **The contracted matrix coefficients are one inner product**: since `eprlCoeff` is conjugate
linear in the bra slot, `Σ u_m v_{m'} D_{m m'}(g) = ⟪Σ conj(u_m) Y e_m, π(g) Σ v_{m'} Y e_{m'}⟫`. -/
theorem eprlCoeff_pair (γ : ℝ) (J : ℕ) (u v : Fin (dsp (J : ℤ) 0 + 1) → ℂ) (g : SL2C) :
    ∑ m : Fin (dsp (J : ℤ) 0 + 1), ∑ m' : Fin (dsp (J : ℤ) 0 + 1),
        u m * v m' * eprlCoeff γ J m m' g =
      inner ℂ (∑ m : Fin (dsp (J : ℤ) 0 + 1), conj (u m) • eprlVec γ J m)
        (principalSeries (J : ℤ) (eprlRho γ J) g
          (∑ m' : Fin (dsp (J : ℤ) 0 + 1), v m' • eprlVec γ J m')) := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right, eprlCoeff, Complex.conj_conj]
  ring

/-- `Λ` of a coherent state of spin `n/2` on the level `(p, q)` with `p = n`, `q = 0`, with the
index cast of `Fin (n+1)` to `Fin (p+q+1)`. -/
theorem lam_emb_cohState_cast (n p q : ℕ) (hp : p = n) (hq : q = 0)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (ζ : Fin 2 → ℂ) :
    lam p q (emb (p + q) *ᵥ fun k : Fin (p + q + 1) => cohState n g (Fin.cast (by omega) k)) ζ =
      (g 0 0 * ζ 0 + g 1 0 * ζ 1) ^ n := by
  subst hp hq
  simpa using lam_emb_cohState p g ζ

/-- `dsp n 0 = n` for the lowest level of `(n/2, ρ)`, `n : ℕ`. -/
theorem dsp_natCast_zero' (n : ℕ) : dsp (n : ℤ) 0 = n := by
  rw [dsp_eq]; simp

/-- The coherent state `|n/2, g⟩`, as a vector of the lowest SU(2) level `ℂ^{dsp + 1}`. -/
noncomputable def cohVec (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : Espace (dsp (n : ℤ) 0) :=
  WithLp.toLp 2 fun k => cohState n g (Fin.cast (by rw [dsp_natCast_zero']) k)

/-- **The coherent state of the lowest level on the chart**: `suV |n/2, g⟩` is, almost everywhere,
`(‖A e₀‖)⁻¹ · wgt(z) · (g₀₀ z + g₁₀)^n`. -/
theorem suV_cohVec_ae (n : ℕ) (ρ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (suV (n : ℤ) ρ 0 (cohVec n g) : ℂ → ℂ) =ᵐ[MeasureTheory.volume] fun z =>
      ((nrmA (tlin (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ))⁻¹ : ℂ) *
        (wgt (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ z * (g 0 0 * z + g 1 0) ^ n) := by
  filter_upwards [suV_ae (n : ℤ) ρ 0 (cohVec n g)] with z hz
  rw [hz]
  have hp : 0 + p0 (n : ℤ) = n := by simp [p0]
  have hq : 0 + q0 (n : ℤ) = 0 := by simp [q0]
  have h := lam_emb_cohState_cast n (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) hp hq g ![z, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h
  exact congrArg _ (congrArg _ h)

/-- An invertible matrix acts injectively on spinors. -/
theorem spinAct_ne_zero_of_det (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) {v : Spinor}
    (hv : v ≠ 0) : spinAct M v ≠ 0 := by
  intro h
  apply hv
  have h1 : M.adjugate * M = M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := Matrix.adjugate_mul M
  have h2 := congrArg (spinAct M.adjugate) h
  rw [← spinAct_mul, h1] at h2
  have h3 : spinAct (M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ)) v = M.det • v := by
    ext i; fin_cases i <;> simp [spinAct]
  rw [h3] at h2
  have h4 : spinAct M.adjugate 0 = 0 := by ext i; fin_cases i <;> simp [spinAct]
  rw [h4] at h2
  exact (smul_eq_zero.mp h2).resolve_left hM

/-- **An affine function of `w` vanishes on a null set** unless it is identically zero. -/
theorem ae_affine_ne_zero (α β : ℂ) (h : α ≠ 0 ∨ β ≠ 0) :
    ∀ᵐ w : ℂ ∂MeasureTheory.volume, α * w + β ≠ 0 := by
  by_cases hα : α = 0
  · have hβ : β ≠ 0 := by simpa [hα] using h
    exact Filter.Eventually.of_forall fun w => by simpa [hα] using hβ
  · have : {w : ℂ | α * w + β = 0} ⊆ {-β / α} := by
      intro w hw
      have hw' : α * w + β = 0 := hw
      simp only [Set.mem_singleton_iff]
      field_simp
      linear_combination hw'
    rw [MeasureTheory.ae_iff]
    exact MeasureTheory.measure_mono_null (by simpa using this) (MeasureTheory.measure_singleton _)

/-- The weight `wgt p q ρ` depends on `p + q` only. -/
theorem wgt_congr {p q p' q' : ℕ} (h : p + q = p' + q') (ρ : ℝ) (z : ℂ) :
    wgt p q ρ z = wgt p' q' ρ z := by
  unfold wgt; rw [h]

/-- **`suV` of a coherent state is a multiple of the explicit homogeneous function**:
`suV |n/2, g⟩ = (‖A e₀‖)⁻¹ · [hvec n 0 ρ |n/2, g⟩]`, as elements of `L²(ℂ)`. -/
theorem suV_cohVec_eq (n : ℕ) (ρ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hm : MeasureTheory.MemLp (chart (hvec n 0 ρ (cohState n g))) 2 MeasureTheory.volume) :
    suV (n : ℤ) ρ 0 (cohVec n g) =
      ((nrmA (tlin (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ))⁻¹ : ℂ) •
        hm.toLp (chart (hvec n 0 ρ (cohState n g))) := by
  refine MeasureTheory.Lp.ext ?_
  have h1 := suV_cohVec_ae n ρ g
  have h2 := MeasureTheory.MemLp.coeFn_toLp hm
  filter_upwards [h1, h2, MeasureTheory.Lp.coeFn_smul (((nrmA (tlin (0 + p0 (n : ℤ))
    (0 + q0 (n : ℤ)) ρ))⁻¹ : ℂ)) (hm.toLp (chart (hvec n 0 ρ (cohState n g))))] with z z1 z2 z3
  rw [z1, z3, Pi.smul_apply, z2, smul_eq_mul, chart_hvec, lam_emb_cohState]
  have hw : wgt (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ z = wgt n 0 ρ z :=
    wgt_congr (by simp [p0, q0]) ρ z
  rw [hw]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]

end Lightlike.Asymptotics.Lorentzian

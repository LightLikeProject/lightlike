import Mathlib
import Lightlike.Lorentz.SL2RIrreducible.PrincipalLadder
import Lightlike.Lorentz.SL2RPlancherel.PrincipalSpherical

/-!
# The odd base coefficient of the principal series of `SL(2,ℝ)`

For the odd principal series `P^{1,iν}` (`ε = 1`), put `ρ = ν/2`. The weight vector `e_0` of weight `1`
(`weightVec 1 ν 0`) has the matrix coefficient `Φ^{odd}_ν(ξ) = ⟪e_0, π(a(ξ)) e_0⟫` (`oddCoeff`), the
analogue of the spherical coefficient of the even series: it belongs to the `K`-type `(1/2, 1/2)`, whose
radial Plancherel density is `ρ coth(πρ)` (Kitaev, arXiv:1711.08169, Eq. (79) at `μ = 1/2`).

With `u = u_ξ(x) = (e^{-ξ} + e^ξ x²)/(1 + x²)` (`sphU`) the integrand of the coefficient is, off the odd part,
a function of `u` alone:

  `conj(e_0(x)) · (π(a(ξ)) e_0)(x) = (1 + u) u^{iρ-1} / (2 cosh(ξ/2) (1 + x²)` + an odd function of `x`,

(`oddIntegrand_eq`), because `(1 + e^ξ x²) e^{-ξ/2}/(1 + x²)² = (1 + u)/(2 cosh(ξ/2)(1 + x²))`
(`even_part_eq`). So `Φ^{odd}_ν(ξ) = (2 cosh(ξ/2))⁻¹ ∫ (u^{iρ-1} + u^{iρ}) dx/(1 + x²)`, a combination of two
spherical averages of the even series at complex-shifted parameter (`oddCoeff_eq_integral`).
-/

open MeasureTheory Set Complex Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2R Lightlike.Lorentz.SL2RPlancherel

/-- **The odd base coefficient** `Φ^{odd}_ν(ξ) = ⟪e_0, π(a(ξ)) e_0⟫` of the odd principal series: the
matrix coefficient between the weight vector of weight `1` and itself, along `a(ξ) = exp((ξ/2) H)`. -/
def oddCoeff (ν ξ : ℝ) : ℂ := diagPairing 1 ν 0 0 (ξ / 2)

lemma weightVec_one_zero (ν y : ℝ) :
    weightVec 1 ν 0 y = Complex.exp (weightExp 1 ν * (Real.log (1 + y ^ 2) : ℝ)) * ((y : ℂ) - I) := by
  simp [weightVec]

lemma conj_weightVec_one_zero (ν x : ℝ) :
    conj (weightVec 1 ν 0 x) =
      Complex.exp (conj (weightExp 1 ν) * (Real.log (1 + x ^ 2) : ℝ)) * ((x : ℂ) + I) := by
  rw [weightVec_one_zero, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_sub,
    Complex.conj_ofReal, Complex.conj_I, sub_neg_eq_add]

/-- `1 + (e^ξ x)² = e^ξ (1 + x²) u_ξ(x)`, in logarithms. -/
lemma log_one_add_scaled (ξ x : ℝ) :
    Real.log (1 + (Real.exp ξ * x) ^ 2) =
      ξ + Real.log (1 + x ^ 2) + Real.log (sphU ξ x) := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hu := sphU_pos ξ x
  have : 1 + (Real.exp ξ * x) ^ 2 = Real.exp ξ * ((1 + x ^ 2) * sphU ξ x) := by
    unfold sphU
    field_simp
    rw [mul_add, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    ring
  rw [this, Real.log_mul (Real.exp_pos ξ).ne' (mul_pos h1 hu).ne', Real.log_exp,
    Real.log_mul h1.ne' hu.ne']
  ring

/-- **The even part**: `e^{-ξ/2} (1 + e^ξ x²)/(1 + x²)² = (1 + u)/(2 cosh(ξ/2) (1 + x²))`. -/
lemma even_part_eq (ξ x : ℝ) :
    Real.exp (-ξ / 2) * (1 + Real.exp ξ * x ^ 2) / (1 + x ^ 2) ^ 2 =
      (1 + sphU ξ x) / (2 * Real.cosh (ξ / 2) * (1 + x ^ 2)) := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have ha : Real.exp ξ = Real.exp (ξ / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hb : Real.exp (-ξ) = (Real.exp (ξ / 2) ^ 2)⁻¹ := by rw [Real.exp_neg, ha]
  have hc : Real.exp (-ξ / 2) = (Real.exp (ξ / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hcosh : 2 * Real.cosh (ξ / 2) = Real.exp (ξ / 2) + (Real.exp (ξ / 2))⁻¹ := by
    rw [Real.cosh_eq, Real.exp_neg]; ring
  have hpos : 0 < Real.exp (ξ / 2) := Real.exp_pos _
  unfold sphU
  rw [hcosh, hc, ha, hb]
  field_simp
  ring

lemma conj_weightExp_one (ν : ℝ) : conj (weightExp 1 ν) = (-(I * ν) - 2) / 2 := by
  simp [weightExp, map_div₀, map_ofNat]
  ring

lemma weightExp_one (ν : ℝ) : weightExp 1 ν = (I * ν - 2) / 2 := by
  simp [weightExp]; ring

/-- `((1 + x²)²)⁻¹ = exp(-2 log(1 + x²))`. -/
lemma inv_sq_one_add_eq (x : ℝ) :
    (((1 + x ^ 2) ^ 2)⁻¹ : ℝ) = Real.exp (-(2 * Real.log (1 + x ^ 2))) := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, show (2 : ℝ) * Real.log (1 + x ^ 2) = ((2 : ℕ) : ℝ) * Real.log (1 + x ^ 2) by norm_num,
    Real.exp_nat_mul, Real.exp_log h1]

/-- **The even part** `(1 + u) u^{iρ-1}/(2 cosh(ξ/2)(1 + x²))` of the integrand of the odd base
coefficient (`u = u_ξ(x)`, `ρ = ν/2`, so `iρ - 1 = weightExp 1 ν`). -/
def oddEven (ν ξ x : ℝ) : ℂ :=
  (((1 + sphU ξ x) / (2 * Real.cosh (ξ / 2) * (1 + x ^ 2)) : ℝ) : ℂ) *
    Complex.exp (weightExp 1 ν * (Real.log (sphU ξ x) : ℝ))

/-- **The odd part** `i x e^{-ξ/2}(e^ξ - 1)/(1 + x²)² · u^{iρ-1}` of the integrand. -/
def oddOdd (ν ξ x : ℝ) : ℂ :=
  I * (x : ℂ) * ((Real.exp (-ξ / 2) * (Real.exp ξ - 1) / (1 + x ^ 2) ^ 2 : ℝ) : ℂ) *
    Complex.exp (weightExp 1 ν * (Real.log (sphU ξ x) : ℝ))

lemma oddEven_neg (ν ξ x : ℝ) : oddEven ν ξ (-x) = oddEven ν ξ x := by
  simp [oddEven, sphU_neg]

lemma oddOdd_neg (ν ξ x : ℝ) : oddOdd ν ξ (-x) = -oddOdd ν ξ x := by
  simp [oddOdd, sphU_neg]

/-- **The integrand of the odd base coefficient**, split into its even and odd parts in `x`:
`conj(e_0(x)) (π(a(ξ)) e_0)(x) = (1 + u) u^{iρ-1}/(2 cosh(ξ/2)(1 + x²))
  + i x e^{-ξ/2}(e^ξ - 1)/(1 + x²)² · u^{iρ-1}`, with `u = u_ξ(x)` and `ρ = ν/2`. -/
lemma oddIntegrand_eq (ν ξ x : ℝ) :
    conj (weightVec 1 ν 0 x) * diagPhase 1 ν 0 (ξ / 2) x = oddEven ν ξ x + oddOdd ν ξ x := by
  unfold oddEven oddOdd
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hexp : Complex.exp (conj (weightExp 1 ν) * (Real.log (1 + x ^ 2) : ℝ)) *
      (Complex.exp (-((ξ / 2 : ℝ) : ℂ) * (I * ν - 1)) *
        Complex.exp (weightExp 1 ν * ((ξ + Real.log (1 + x ^ 2) + Real.log (sphU ξ x) : ℝ) : ℂ))) =
      ((Real.exp (-ξ / 2) * ((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) *
        Complex.exp (weightExp 1 ν * (Real.log (sphU ξ x) : ℝ)) := by
    rw [inv_sq_one_add_eq, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp]
    simp only [← Complex.exp_add]
    congr 1
    rw [conj_weightExp_one, weightExp_one]
    push_cast
    ring
  unfold diagPhase
  rw [conj_weightVec_one_zero, weightVec_one_zero, show 2 * (ξ / 2) = ξ by ring,
    log_one_add_scaled ξ x]
  have hev := even_part_eq ξ x
  calc _ = (Complex.exp (conj (weightExp 1 ν) * (Real.log (1 + x ^ 2) : ℝ)) *
        (Complex.exp (-((ξ / 2 : ℝ) : ℂ) * (I * ν - 1)) *
          Complex.exp (weightExp 1 ν * ((ξ + Real.log (1 + x ^ 2) + Real.log (sphU ξ x) : ℝ) : ℂ)))) *
        (((x : ℂ) + I) * (((Real.exp ξ * x : ℝ) : ℂ) - I)) := by ring
    _ = _ := by
      rw [hexp]
      set c : ℂ := ((Real.exp (-ξ / 2) * ((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) with hc
      set E := Complex.exp (weightExp 1 ν * (Real.log (sphU ξ x) : ℝ)) with hE
      have hA : (((1 + sphU ξ x) / (2 * Real.cosh (ξ / 2) * (1 + x ^ 2)) : ℝ) : ℂ) =
          c * (1 + ((Real.exp ξ : ℝ) : ℂ) * (x : ℂ) ^ 2) := by
        rw [← hev, hc]; push_cast; ring
      have hB : ((Real.exp (-ξ / 2) * (Real.exp ξ - 1) / (1 + x ^ 2) ^ 2 : ℝ) : ℂ) =
          c * (((Real.exp ξ : ℝ) : ℂ) - 1) := by
        rw [hc]; push_cast; ring
      rw [hA, hB, Complex.ofReal_mul]
      linear_combination (-(c * E)) * Complex.I_mul_I

/-- The integrand of a matrix coefficient between weight vectors is integrable (a product of two
`L²` functions). -/
lemma integrable_diag_integrand (ε : ℤ) (ν : ℝ) (j k : ℤ) (t : ℝ) :
    Integrable (fun x => conj (weightVec ε ν j x) * diagPhase ε ν k t x) := by
  have h := L2.integrable_inner (𝕜 := ℂ) (weightL2 ε ν j)
    (principalSeries ε ν (expH t) (weightL2 ε ν k))
  refine h.congr ?_
  filter_upwards [weightL2_ae ε ν j, principalSeries_expH_weightL2_ae ε ν k t] with x e1 e2
  rw [e1, e2, RCLike.inner_apply']

lemma integrable_oddEven (ν ξ : ℝ) : Integrable (oddEven ν ξ) := by
  have hf := integrable_diag_integrand 1 ν 0 0 (ξ / 2)
  have e : oddEven ν ξ = fun x => (1 / 2 : ℂ) *
      ((conj (weightVec 1 ν 0 x) * diagPhase 1 ν 0 (ξ / 2) x) +
        (conj (weightVec 1 ν 0 (-x)) * diagPhase 1 ν 0 (ξ / 2) (-x))) := by
    funext x
    rw [oddIntegrand_eq, oddIntegrand_eq, oddEven_neg, oddOdd_neg]
    ring
  rw [e]
  exact (hf.add hf.comp_neg).const_mul _

lemma integral_oddOdd (ν ξ : ℝ) : ∫ x, oddOdd ν ξ x = 0 := by
  have h := integral_neg_eq_self (oddOdd ν ξ) (volume : Measure ℝ)
  simp only [oddOdd_neg, integral_neg] at h
  have : (2 : ℂ) * ∫ x, oddOdd ν ξ x = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- **The odd base coefficient as an integral of its even part**:
`Φ^{odd}_ν(ξ) = ∫ (1 + u) u^{iρ-1}/(2 cosh(ξ/2)(1 + x²)) dx`, `u = u_ξ(x)`, `ρ = ν/2`. -/
theorem oddCoeff_eq_integral (ν ξ : ℝ) : oddCoeff ν ξ = ∫ x, oddEven ν ξ x := by
  have hf := integrable_diag_integrand 1 ν 0 0 (ξ / 2)
  have hO : Integrable (oddOdd ν ξ) := by
    have e : oddOdd ν ξ = fun x => (conj (weightVec 1 ν 0 x) * diagPhase 1 ν 0 (ξ / 2) x) - oddEven ν ξ x := by
      funext x; rw [oddIntegrand_eq]; ring
    rw [e]; exact hf.sub (integrable_oddEven ν ξ)
  unfold oddCoeff
  rw [diagPairing_eq_integral 1 ν 0 0 (ξ / 2)]
  have e : ∀ x, conj (weightVec 1 ν 0 x) * diagPhase 1 ν 0 (ξ / 2) x = oddEven ν ξ x + oddOdd ν ξ x :=
    oddIntegrand_eq ν ξ
  simp_rw [e]
  rw [integral_add (integrable_oddEven ν ξ) hO, integral_oddOdd, add_zero]

end Lightlike.Lorentz.SL2ROddPlancherel

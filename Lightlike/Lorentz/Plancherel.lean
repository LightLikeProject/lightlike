module

public import Lightlike.Lorentz.PlancherelFourier

/-!
# The Plancherel formula of `SL(2, ℂ)`

For `f ∈ C_c^∞(SL(2, ℂ))` the principal series `π_{n,ρ}` (`n ∈ ℤ`, `ρ ∈ ℝ`, acting on
`L²(ℂ)`) satisfy

`Σ_{n ∈ ℤ} ∫_ℝ (n² + 4ρ²) ‖π_{n,ρ}(f)‖²_HS dρ = 16 π⁴ ∫ |f|² dg`

with the Haar measure `haarC` of `HaarChart.lean`. The Hilbert–Schmidt norm is computed from the
integral kernel `K_f(z', z)` of `π_{n,ρ}(f)` (`psKernel`, `PlancherelKernel.lean`):
`‖π_{n,ρ}(f)‖²_HS = ∫∫ |K_f(z', z)|² d²z' d²z`. Equivalently (trace form), for `F ∈ C_c^∞`,
`Σ_n ∫ (n² + 4ρ²) tr π_{n,ρ}(F) dρ = 16 π⁴ F(1)` with `tr π_{n,ρ}(F) = ∫ K_F(z, z) d²z`.

A smooth function on `SL(2, ℂ)` is here the restriction of a smooth function on the space of
`2 × 2` complex arrays: every `f ∈ C_c^∞(SL(2, ℂ))` is of this form, since `SL(2, ℂ)` is a closed
submanifold of `M₂(ℂ)` (a standard extension fact, not formalised here; Mathlib has no manifold
structure on `SL(2, ℂ)` to state it with).

## Conventions

The constant `16π⁴` depends on five choices, all fixed here.

- **Representation and labels.** For `g = [[α, β], [γ, δ]]`,
  `π_{n,ρ}(g) φ(z) = m_{n,ρ}(βz + δ) φ((αz + γ)/(βz + δ))` with
  `m_{n,ρ}(λ) = |λ|^{2iρ - 2} (λ / |λ|)^n` (`PrincipalSeries.lean`), unitary on `L²(ℂ, d²z)`.
- **Haar measure.** `dg = haarC = d²β d²γ d²δ / |δ|²` in the chart
  `g = [[(1 + βγ)/δ, β], [γ, δ]]`, with `d²z = d Re z d Im z` (`integral_haarC_eq_bruhat`). In
  polar form `∫ f dg = 4π³ ∫_0^∞ F(cosh r) sinh² r dr` for `f(g) = F(‖g‖²_HS / 2)`
  (`Radial.lean`).
- **Range of the labels.** `n` runs over `ℤ` and `ρ` over `ℝ`. Since `π_{n,ρ} ≅ π_{-n,-ρ}`, every
  class is counted twice; the density is `n² + 4ρ²`.
- **Operator, trace and Hilbert–Schmidt norm.** `π_{n,ρ}(f) = ∫ f(g) π_{n,ρ}(g) dg` has the
  kernel `K_f(z, w)` (`psKernel`); `tr π_{n,ρ}(F) = ∫ K_F(z, z) d²z` and
  `‖π_{n,ρ}(f)‖²_HS = ∫∫ |K_f(z', z)|² d²z' d²z`.
- **Sign of `n`.** The phase `(λ / |λ|)^n` with `λ = βz + δ`. The density and the sum over `ℤ`
  are even in `n`, so the opposite sign gives the same formula.

**Perez–Rovelli** (gr-qc/0011037, App. A) use the same objects with the label `σ = 2ρ`: their
(A6) with `μ = iσ` is `π_{n,σ/2}` with the same `n` (`coeFn_principalSeries_perezRovelli`, with
`prMult_eq_cpow` for the powers), their (A8) is `haarC` (`integral_haarC_eq_bruhat`; the
`(i/2)³` turns `dβ ∧ dβ̄` into `d Re β d Im β`), and their density `n² + σ²` is `n² + 4ρ²`. Since
`dσ = 2 dρ`, the formula reads `F(1) = (1/(32π⁴)) Σ_n ∫_ℝ (n² + σ²) tr T_{n,σ}(F) dσ` in their
variables (`plancherel_trace_perezRovelli`). Their (A11) at `g = 1` and (A16) have `1/(8π⁴)`,
four times too large (`testLF_perezRovelli_constant`); restricting to `σ ≥ 0`, which counts each
class once, would need `1/(16π⁴)`, so the factor is not a matter of the range.

**Rühl**, as quoted by Simão (arXiv:2405.01360, App. B.1 and B.3), uses
`dg_R = (2π)⁻⁴ |a₂₂|⁻² d²a₁₂ d²a₂₁ d²a₂₂ = (2π)⁻⁴ haarC` and labels `χ = (ν, ρ_R)` with
homogeneity `λ^{(-ν+iρ_R)/2 - 1} λ̄^{(ν+iρ_R)/2 - 1}` and the action `F ↦ F(g⁻¹ ·)`. This is
`π_{-ν, ρ_R/2}` composed with the inner automorphism `g ↦ (gᵀ)⁻¹` (conjugation by
`[[0, 1], [-1, 0]]`), which does not change traces; this equivalence is argued here, not
formalised. With `ρ_R = σ = 2ρ`, `ν = -n` and the trace of `∫ F(g) D^χ(g) dg_R` equal to
`(2π)⁻⁴ tr π_{-ν, ρ_R/2}(F)`, the formula is Rühl's
`F(1) = ½ Σ_ν ∫_ℝ (ν² + ρ_R²) tr D^χ(F) dρ_R` (`plancherel_trace_ruhl`).

`scripts/lorentz/plancherel_check.py` (Part 3) checks the constant numerically, including the
sectors `n ≠ 0`, from the definition of the kernel alone.

## Main results

- `plancherel_trace`: the trace form, `Σ_n ∫ (n² + 4ρ²) ∫ K_F(z, z) d²z dρ = 16 π⁴ F(1)`, with
  integrability of every `ρ`-integrand.
- `plancherel`: the Hilbert–Schmidt form, with integrability of every integrand (no junk values).
- `plancherel_trace_perezRovelli`, `plancherel_trace_ruhl`: the trace form in the variables of
  Perez–Rovelli and of Rühl, with the constants `1/(32π⁴)` and `1/2`.
- `selfConvExt`, `contDiff_selfConvExt`, `hasCompactSupport_selfConvExt`: `f* ∗ f` extends to a
  smooth compactly supported function on arrays.

## Implementation notes

`integral_psKernel_diag` (`PlancherelTrace.lean`) turns the trace into `π ∫ m_{n,ρ}(λ) Φ(λ⁻¹)`
with `Φ` the orbital integral of the `SU(2)`-average `F♮`; `hasSum_density_orbInt`
(`PlancherelFourier.lean`) sums this against the density by Fourier inversion and the limit
formula. The Hilbert–Schmidt form applies the trace form to `F = f* ∗ f`, whose kernel diagonal is
`∫ |K_f(z', z)|² d²z'` (`psKernel_selfConv_diag`).

## References

- I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR Ser. Mat. 11 (1947) 411–504 (the form of the density).
- M. A. Naimark, *Linear Representations of the Lorentz Group*, Pergamon (1964), Ch. III §11.
- A. Perez, C. Rovelli, *3+1 spinfoam model of quantum gravity with spacelike and timelike
  components*, arXiv:gr-qc/0011037, App. A, eqs. (A6), (A8), (A11), (A16).
- W. Rühl, *The Lorentz Group and Harmonic Analysis*, Benjamin (1970), as quoted in
  J. D. Simão, *Investigations on Lorentzian Spin-foams and Semiclassical Space-times*, PhD
  thesis, Jena (2024), arXiv:2405.01360, App. B.1, B.3 and eq. (B.3.1); Rühl's text itself was
  not consulted.
-/

@[expose] public section

open MeasureTheory Complex Metric Set Filter Topology
open scoped Matrix ComplexConjugate ContDiff

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-! ## Group elements as arrays -/

/-- The inclusion `SL(2, ℂ) → M₂(ℂ)` with values in the arrays `Fin 2 → Fin 2 → ℂ`, which carry
the sup norm used for supports throughout (the coercion `(g : M2)` has type `Matrix`, which carries
no norm instance). -/
abbrev toArr (g : SL2C) : P2 := (g : M2)

/-- `A X 1 = A X` for arrays. -/
lemma mm3_one (A X : P2) : mm3 A X (mat2 1 0 0 1) = Matrix.of A * Matrix.of X := by
  have h : Matrix.of (mat2 (1 : ℂ) 0 0 1) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [Matrix.of_apply]
    fin_cases i <;> fin_cases j <;> simp [mat2]
  rw [mm3, h, Matrix.mul_one]

/-- The product in `SL(2, ℂ)` as a product of arrays. -/
lemma mm3_toArr_mul (h x : SL2C) :
    mm3 (toArr h) (toArr x) (mat2 1 0 0 1) = toArr (h * x) := by
  rw [mm3_one]
  exact (Matrix.SpecialLinearGroup.coe_mul h x).symm

/-- `h⁻¹ (h Y) = Y` for `h ∈ SL(2, ℂ)` and an array `Y`. -/
lemma mm3_inv_mm3 (h : SL2C) (Y : P2) :
    mm3 (toArr h⁻¹) (mm3 (toArr h) Y (mat2 1 0 0 1)) (mat2 1 0 0 1) = Y := by
  rw [mm3_one, mm3_one]
  change ((h⁻¹ : SL2C) : M2) * ((h : M2) * Matrix.of Y) = Matrix.of Y
  rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

/-- The identity of `SL(2, ℂ)` as an array. -/
lemma toArr_one : toArr 1 = mat2 1 0 0 1 := by
  show ((1 : SL2C) : M2) = mat2 1 0 0 1
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  rfl

/-- The inclusion `SL(2, ℂ) → M₂(ℂ)` is a closed embedding. -/
lemma isClosedEmbedding_toArr : Topology.IsClosedEmbedding toArr :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val

/-- The restriction of a compactly supported function on arrays to `SL(2, ℂ)` has compact
support. -/
lemma hasCompactSupport_restrict {F : P2 → ℂ} (hs : HasCompactSupport F) :
    HasCompactSupport fun g => F (toArr g) :=
  hs.comp_isClosedEmbedding isClosedEmbedding_toArr

/-- Group elements of norm at most `C` form a compact set. -/
lemma isCompact_normLe (C : ℝ) : IsCompact (toArr ⁻¹' closedBall 0 C) :=
  isClosedEmbedding_toArr.isCompact_preimage (isCompact_closedBall 0 C)

/-! ## `f* ∗ f` on arrays -/

/-- **`f* ∗ f` on arrays**: `X ↦ ∫ conj F(h) F(h X) dh`. On `SL(2, ℂ)` it is `selfConv` of the
restriction `f = F|_{SL(2,ℂ)}` (`selfConvExt_toArr`). -/
noncomputable def selfConvExt (F : P2 → ℂ) (X : P2) : ℂ :=
  ∫ h, conj (F (toArr h)) * F (mm3 (toArr h) X (mat2 1 0 0 1)) ∂haarC

/-- `selfConvExt F` extends `f* ∗ f`. -/
theorem selfConvExt_toArr (F : P2 → ℂ) (x : SL2C) :
    selfConvExt F (toArr x) = selfConv (fun g => F (toArr g)) x := by
  simp only [selfConvExt, selfConv, mm3_toArr_mul]

/-- `(f* ∗ f)(1) = ‖f‖²_{L²(G)}`. -/
theorem selfConvExt_one (F : P2 → ℂ) :
    selfConvExt F (mat2 1 0 0 1) = ((∫ g, ‖F (toArr g)‖ ^ 2 ∂haarC : ℝ) : ℂ) := by
  rw [← toArr_one, selfConvExt_toArr, selfConv]
  simp_rw [mul_one, Complex.conj_mul', ← Complex.ofReal_pow]
  exact integral_ofReal

/-- `f* ∗ f` is smooth on arrays. -/
theorem contDiff_selfConvExt {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ContDiff ℝ ∞ (selfConvExt F) := by
  obtain ⟨C, -, hCF⟩ := exists_bound_support hs
  have hΦ : ContDiff ℝ ∞ (Function.uncurry fun (A X : P2) =>
      conj (F A) * F (mm3 A X (mat2 1 0 0 1))) :=
    (conjCLE.contDiff.comp (hF.comp contDiff_fst)).mul
      (hF.comp (contDiff_fst.mm3 contDiff_snd contDiff_const))
  have hc := isClosedEmbedding_toArr.continuous
  exact contDiff_parametric_integral_infty hΦ hc.aestronglyMeasurable
    (measurableSet_closedBall.preimage hc.measurable) (isCompact_normLe C).measure_lt_top.ne
    (R := C) (Eventually.of_forall fun h hh => mem_closedBall_zero_iff.1 hh)
    (Eventually.of_forall fun h hh X => by
      rw [mem_preimage, mem_closedBall_zero_iff, not_le] at hh
      simp only [hCF _ hh.le, map_zero, zero_mul])

/-- `f* ∗ f` has compact support on arrays. -/
theorem hasCompactSupport_selfConvExt {F : P2 → ℂ} (hs : HasCompactSupport F) :
    HasCompactSupport (selfConvExt F) := by
  obtain ⟨C, hC, hCF⟩ := exists_bound_support hs
  obtain ⟨D, hD⟩ := (isCompact_normLe C).exists_bound_of_continuousOn
    (f := fun h : SL2C => toArr h⁻¹)
    (isClosedEmbedding_toArr.continuous.comp continuous_inv).continuousOn
  have hI : ‖mat2 (1 : ℂ) 0 0 1‖ ≤ 1 := norm_mat2_le zero_le_one (by simp) (by simp) (by simp)
    (by simp)
  refine HasCompactSupport.intro (isCompact_closedBall (0 : P2) (4 * D * C)) fun X hX => ?_
  rw [mem_closedBall_zero_iff, not_le] at hX
  refine integral_eq_zero_of_ae (Eventually.of_forall fun h => ?_)
  show conj (F (toArr h)) * F (mm3 (toArr h) X (mat2 1 0 0 1)) = 0
  by_cases hh : ‖toArr h‖ ≤ C
  · have hD' : ‖toArr h⁻¹‖ ≤ D := hD h (mem_closedBall_zero_iff.2 hh)
    have hY : C ≤ ‖mm3 (toArr h) X (mat2 1 0 0 1)‖ := by
      by_contra hlt
      have hb := norm_mm3_le (toArr h⁻¹) (mm3 (toArr h) X (mat2 1 0 0 1)) (mat2 1 0 0 1)
      rw [mm3_inv_mm3] at hb
      have hD0 : 0 ≤ D := (norm_nonneg _).trans hD'
      have : ‖X‖ ≤ 4 * D * C := by
        calc ‖X‖ ≤ 4 * ‖toArr h⁻¹‖ * ‖mm3 (toArr h) X (mat2 1 0 0 1)‖ *
              ‖mat2 (1 : ℂ) 0 0 1‖ := hb
          _ ≤ 4 * D * C * 1 := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hD' (by norm_num))
              (not_le.1 hlt).le (norm_nonneg _) (by positivity)) hI (norm_nonneg _)
              (by positivity)
          _ = 4 * D * C := mul_one _
      exact absurd hX (not_lt.2 this)
    rw [hCF _ hY, mul_zero]
  · rw [hCF _ (not_le.1 hh).le, map_zero, zero_mul]

/-! ## The Plancherel formula -/

/-- **The Plancherel formula of `SL(2, ℂ)`, trace form.** For `F` smooth with compact support on
arrays (restricted to `SL(2, ℂ)` in `π_{n,ρ}(F)`), each `ρ ↦ (n² + 4ρ²) tr π_{n,ρ}(F)` is
integrable, with `tr π_{n,ρ}(F) = ∫ K_F(z, z) d²z`, and
`Σ_{n ∈ ℤ} ∫ (n² + 4ρ²) tr π_{n,ρ}(F) dρ = 16 π⁴ F(1)`. -/
theorem plancherel_trace {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    (∀ n : ℤ, Integrable fun ρ : ℝ =>
      ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ z, psKernel n ρ (fun g => F (toArr g)) z z) ∧
    HasSum (fun n : ℤ => ∫ ρ : ℝ,
      ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ z, psKernel n ρ (fun g => F (toArr g)) z z)
      (16 * Real.pi ^ 4 * F (mat2 1 0 0 1)) := by
  have hA := hasSum_density_orbInt (contDiff_su2Avg hF) (hasCompactSupport_su2Avg hs)
    (isSU2ConjInvariant_su2Avg hF.continuous)
  have hT : ∀ n : ℤ, (fun ρ : ℝ => ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) *
      ∫ z, psKernel n ρ (fun g => F (toArr g)) z z) = fun ρ : ℝ => (Real.pi : ℂ) *
      (((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ l, mult n ρ l * orbInt (su2Avg F) l⁻¹) :=
    fun n => by
      funext ρ
      rw [integral_psKernel_diag hF.continuous hs n ρ]
      ring
  refine ⟨fun n => by rw [hT n]; exact (hA.1 n).const_mul _, ?_⟩
  simp_rw [hT, integral_const_mul]
  convert hA.2.mul_left (Real.pi : ℂ) using 1
  rw [su2Avg_one]
  ring

/-- **The Plancherel formula of `SL(2, ℂ)`.** For `f = F|_{SL(2,ℂ)}` with `F` smooth and
compactly supported on arrays, with `K_f(z', z)` the integral kernel of `π_{n,ρ}(f)` on `L²(ℂ)`:
every integrand is integrable (so no value is a junk value), and
`Σ_{n ∈ ℤ} ∫ (n² + 4ρ²) ∫∫ |K_f(z', z)|² d²z' d²z dρ = 16 π⁴ ∫ |f|² dg`, i.e.
`Σ_n ∫ (n² + 4ρ²) ‖π_{n,ρ}(f)‖²_HS dρ = 16 π⁴ ‖f‖²_{L²(G)}`. -/
theorem plancherel {f : SL2C → ℂ} {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F)
    (hfF : ∀ g : SL2C, f g = F (toArr g)) :
    (∀ (n : ℤ) (ρ : ℝ) (z : ℂ), Integrable fun z' => ‖psKernel n ρ f z' z‖ ^ 2) ∧
    (∀ (n : ℤ) (ρ : ℝ), Integrable fun z => ∫ z', ‖psKernel n ρ f z' z‖ ^ 2) ∧
    (∀ n : ℤ, Integrable fun ρ : ℝ =>
      ((n : ℝ) ^ 2 + 4 * ρ ^ 2) * ∫ z, ∫ z', ‖psKernel n ρ f z' z‖ ^ 2) ∧
    HasSum (fun n : ℤ => ∫ ρ : ℝ,
      ((n : ℝ) ^ 2 + 4 * ρ ^ 2) * ∫ z, ∫ z', ‖psKernel n ρ f z' z‖ ^ 2)
      (16 * Real.pi ^ 4 * ∫ g, ‖f g‖ ^ 2 ∂haarC) := by
  obtain rfl : f = fun g => F (toArr g) := funext hfF
  have hf : Continuous fun g => F (toArr g) := hF.continuous.comp isClosedEmbedding_toArr.continuous
  have hfc := hasCompactSupport_restrict hs
  have hE := contDiff_selfConvExt hF hs
  have hEs := hasCompactSupport_selfConvExt hs
  have hK : ∀ (n : ℤ) (ρ : ℝ) (z : ℂ),
      psKernel n ρ (fun g => selfConvExt F (toArr g)) z z =
        ((∫ z', ‖psKernel n ρ (fun g => F (toArr g)) z' z‖ ^ 2 : ℝ) : ℂ) := fun n ρ z => by
    simp_rw [selfConvExt_toArr]
    exact psKernel_selfConv_diag n ρ hf hfc z
  have hz : ∀ (n : ℤ) (ρ : ℝ), Integrable fun z =>
      ∫ z', ‖psKernel n ρ (fun g => F (toArr g)) z' z‖ ^ 2 := fun n ρ => by
    refine (integrable_psKernel_diag hE.continuous hEs n ρ).re.congr
      (Eventually.of_forall fun z => ?_)
    show (psKernel n ρ (fun g => selfConvExt F (toArr g)) z z).re = _
    rw [hK]
    rfl
  have hI : ∀ (n : ℤ) (ρ : ℝ), ∫ z, psKernel n ρ (fun g => selfConvExt F (toArr g)) z z =
      ((∫ z, ∫ z', ‖psKernel n ρ (fun g => F (toArr g)) z' z‖ ^ 2 : ℝ) : ℂ) := fun n ρ => by
    simp_rw [hK]
    exact integral_ofReal
  have hP := plancherel_trace hE hEs
  have hfun : ∀ n : ℤ, (fun ρ : ℝ => ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) *
      ∫ z, psKernel n ρ (fun g => selfConvExt F (toArr g)) z z) = fun ρ : ℝ =>
      ((((n : ℝ) ^ 2 + 4 * ρ ^ 2) *
        ∫ z, ∫ z', ‖psKernel n ρ (fun g => F (toArr g)) z' z‖ ^ 2 : ℝ) : ℂ) := fun n => by
    funext ρ
    rw [hI]
    push_cast
    ring
  have hρ : ∀ n : ℤ, Integrable fun ρ : ℝ => ((n : ℝ) ^ 2 + 4 * ρ ^ 2) *
      ∫ z, ∫ z', ‖psKernel n ρ (fun g => F (toArr g)) z' z‖ ^ 2 := fun n => by
    have h := hP.1 n
    rw [hfun n] at h
    exact h.re.congr (Eventually.of_forall fun ρ => Complex.ofReal_re _)
  refine ⟨fun n ρ z => integrable_psKernel_sq n ρ hf hfc z, hz, hρ, ?_⟩
  have h := hP.2
  simp_rw [hfun, integral_complex_ofReal] at h
  rw [selfConvExt_one, show (16 : ℂ) * (Real.pi : ℂ) ^ 4 *
    ((∫ g, ‖F (toArr g)‖ ^ 2 ∂haarC : ℝ) : ℂ) =
      ((16 * Real.pi ^ 4 * ∫ g, ‖F (toArr g)‖ ^ 2 ∂haarC : ℝ) : ℂ) by push_cast; ring] at h
  exact Complex.hasSum_ofReal.1 h

/-! ## The conventions of Perez–Rovelli and of Rühl

Both sources use the representations `π_{n,ρ}` of this library under the label `σ = 2ρ`; Rühl's
labels also have `ν = -n`, and his Haar measure is `(2π)⁻⁴ dg`. In their variables the formula
above has the constants `1/(32π⁴)` (`plancherel_trace_perezRovelli`) and `1/2`
(`plancherel_trace_ruhl`). -/

/-- **The multiplier of Perez–Rovelli**, `|λ|^{iσ - 2} (λ / |λ|)^n`: the single-valued form of
the factor `λ^{(iσ+n)/2 - 1} λ̄^{(iσ-n)/2 - 1}` of their eq. (A6) with `μ = iσ`
(`prMult_eq_cpow`). -/
noncomputable def prMult (n : ℤ) (σ : ℝ) (w : ℂ) : ℂ :=
  ((‖w‖ : ℝ) : ℂ) ^ (I * σ - 2) * (w / ((‖w‖ : ℝ) : ℂ)) ^ n

/-- `prMult` is the factor `λ^{(iσ+n)/2 - 1} λ̄^{(iσ-n)/2 - 1}` of Perez–Rovelli (A6), with
principal branches, off the negative real axis (where those branches jump). -/
theorem prMult_eq_cpow (n : ℤ) (σ : ℝ) {w : ℂ} (hw : w ≠ 0) (harg : w.arg ≠ Real.pi) :
    prMult n σ w = w ^ ((I * σ + n) / 2 - 1) * conj w ^ ((I * σ - n) / 2 - 1) := by
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw)
  have hph : w / ((‖w‖ : ℝ) : ℂ) = exp (w.arg * I) := by
    rw [div_eq_iff hn, mul_comm]
    exact (norm_mul_exp_arg_mul_I w).symm
  rw [prMult, hph, ← exp_int_mul, cpow_def_of_ne_zero hn, cpow_def_of_ne_zero hw,
    cpow_def_of_ne_zero ((map_ne_zero _).2 hw), ← exp_add, ← exp_add, log_conj w harg,
    ← ofReal_log (norm_nonneg w)]
  congr 1
  simp only [Complex.log, map_add, map_mul, conj_ofReal, conj_I]
  ring

/-- **The label conversion `σ = 2ρ`**: the multiplier `m_{n,ρ}` of `π_{n,ρ}` is the multiplier
of Perez–Rovelli at `σ = 2ρ`, with the same `n`. -/
theorem mult_eq_prMult (n : ℤ) (σ : ℝ) : mult n ((σ / 2 : ℝ) : ℂ) = prMult n σ := by
  funext w
  simp only [mult, prMult]
  congr 2
  push_cast
  ring

/-- **Perez–Rovelli (A6)**: for `g = [[α, β], [γ, δ]]`, almost everywhere,
`π_{n,σ/2}(g) φ(z) = (βz + δ)^{(iσ+n)/2 - 1} (β̄z̄ + δ̄)^{(iσ-n)/2 - 1} φ((αz + γ)/(βz + δ))`,
with the powers in the single-valued form `prMult`: their `T_{n,σ}` is `π_{n,σ/2}`. -/
theorem coeFn_principalSeries_perezRovelli (n : ℤ) (σ : ℝ) (g : SL2C) (φ : L2C) :
    principalSeries n (σ / 2) g φ =ᵐ[volume] fun z =>
      prMult n σ (g 0 1 * z + g 1 1) * φ ((g 0 0 * z + g 1 0) / (g 0 1 * z + g 1 1)) := by
  filter_upwards [coeFn_principalSeries n (σ / 2) g φ] with z hz
  rw [hz, mult_eq_prMult]
  rfl

/-- **Perez–Rovelli (A8)**: `haarC` is their Haar measure `dβ dγ dδ / |δ|²` on
`g = [[(1 + βγ)/δ, β], [γ, δ]]`, with `dβ = d Re β d Im β`. -/
theorem integral_haarC_eq_bruhat {f : SL2C → ℂ} (hf : AEStronglyMeasurable f haarC) :
    ∫ g, f g ∂haarC = ∫ x : Fin 3 → ℂ, ((‖x 2‖ ^ 2)⁻¹ : ℝ) • f (bruhat x) := by
  rw [haarC] at hf ⊢
  rw [integral_map measurable_bruhat.aemeasurable hf,
    integral_withDensity_eq_integral_toReal_smul₀ measurable_bruhatDensity.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [bruhatDensity, ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg _))]

/-- **The kernel of `T_{n,σ}(f)` in the labels of Perez–Rovelli**, their `F_{nσ}(z, z̃)` of
(A13) for `dg = haarC`: `psKernel` with the multiplier `prMult`. -/
noncomputable def prKernel (n : ℤ) (σ : ℝ) (f : SL2C → ℂ) (z w : ℂ) : ℂ :=
  ∫ q : ℂ × ℂ, f (chartPt z w q) * prMult n σ q.2

/-- The kernel `F_{nσ}` of Perez–Rovelli is the kernel `K_f` of `π_{n,σ/2}(f)`. -/
theorem prKernel_eq_psKernel (n : ℤ) (σ : ℝ) (f : SL2C → ℂ) :
    prKernel n σ f = psKernel n (σ / 2) f := by
  funext z w
  simp only [prKernel, psKernel, mult_eq_prMult]

/-- **The Plancherel formula in the conventions of Perez–Rovelli** (gr-qc/0011037, App. A:
`T_{n,σ}` of (A6), `dg` of (A8), `n ∈ ℤ`, `σ ∈ ℝ`), trace form at the identity:
`Σ_n ∫_ℝ (n² + σ²) tr T_{n,σ}(F) dσ = 32 π⁴ F(1)`, i.e.
`F(1) = (1/(32π⁴)) Σ_n ∫_ℝ (n² + σ²) tr T_{n,σ}(F) dσ`. Their (A11) and (A16) have `1/(8π⁴)`
(`testLF_perezRovelli_constant`). -/
theorem plancherel_trace_perezRovelli {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F)
    (hs : HasCompactSupport F) :
    (∀ n : ℤ, Integrable fun σ : ℝ =>
      ((n : ℂ) ^ 2 + (σ : ℂ) ^ 2) * ∫ z, prKernel n σ (fun g => F (toArr g)) z z) ∧
    HasSum (fun n : ℤ => ∫ σ : ℝ,
      ((n : ℂ) ^ 2 + (σ : ℂ) ^ 2) * ∫ z, prKernel n σ (fun g => F (toArr g)) z z)
      (32 * Real.pi ^ 4 * F (mat2 1 0 0 1)) ∧
    F (mat2 1 0 0 1) = (32 * (Real.pi : ℂ) ^ 4)⁻¹ * ∑' n : ℤ, ∫ σ : ℝ,
      ((n : ℂ) ^ 2 + (σ : ℂ) ^ 2) * ∫ z, prKernel n σ (fun g => F (toArr g)) z z := by
  obtain ⟨hi, hP⟩ := plancherel_trace hF hs
  have hfun : ∀ n : ℤ, (fun σ : ℝ => ((n : ℂ) ^ 2 + (σ : ℂ) ^ 2) *
      ∫ z, prKernel n σ (fun g => F (toArr g)) z z) = fun σ : ℝ =>
      (fun ρ : ℝ => ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) *
        ∫ z, psKernel n ρ (fun g => F (toArr g)) z z) (σ / 2) := fun n => by
    funext σ
    simp only [prKernel_eq_psKernel]
    push_cast
    ring
  have hint : ∀ n : ℤ, ∫ σ : ℝ, ((n : ℂ) ^ 2 + (σ : ℂ) ^ 2) *
      ∫ z, prKernel n σ (fun g => F (toArr g)) z z = 2 * ∫ ρ : ℝ,
        ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ z, psKernel n ρ (fun g => F (toArr g)) z z :=
    fun n => by
      rw [hfun n]
      refine (Measure.integral_comp_div (fun ρ : ℝ => ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) *
        ∫ z, psKernel n ρ (fun g => F (toArr g)) z z) 2).trans ?_
      rw [abs_two, Complex.real_smul, ofReal_ofNat]
  have hS : HasSum (fun n : ℤ => ∫ σ : ℝ,
      ((n : ℂ) ^ 2 + (σ : ℂ) ^ 2) * ∫ z, prKernel n σ (fun g => F (toArr g)) z z)
      (32 * Real.pi ^ 4 * F (mat2 1 0 0 1)) := by
    simp_rw [hint]
    convert hP.mul_left 2 using 1
    ring
  refine ⟨fun n => by rw [hfun n]; exact (hi n).comp_div two_ne_zero, hS, ?_⟩
  rw [hS.tsum_eq, ← mul_assoc, inv_mul_cancel₀ (by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (ofReal_ne_zero.2 Real.pi_ne_zero))),
    one_mul]

/-- **The Plancherel formula in the conventions of Rühl**, as quoted by Simão (arXiv:2405.01360,
App. B.3): Haar measure `dg_R = (2π)⁻⁴ dg` (eq. (B.3.1), the measure `haarC` of (A8) scaled),
labels `χ = (ν, ρ_R)` with `ρ_R = σ = 2ρ` and `ν = -n` (App. B.1), so that the trace of
`D^χ(F) = ∫ F(g) D^χ(g) dg_R` is `(2π)⁻⁴ tr T_{-ν,ρ_R}(F)`:
`F(1) = ½ Σ_ν ∫_ℝ (ν² + ρ_R²) tr D^χ(F) dρ_R`. -/
theorem plancherel_trace_ruhl {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    HasSum (fun ν : ℤ => ∫ σ : ℝ, ((ν : ℂ) ^ 2 + (σ : ℂ) ^ 2) *
      (((2 * Real.pi : ℂ) ^ 4)⁻¹ * ∫ z, prKernel (-ν) σ (fun g => F (toArr g)) z z))
      (2 * F (mat2 1 0 0 1)) ∧
    F (mat2 1 0 0 1) = 1 / 2 * ∑' ν : ℤ, ∫ σ : ℝ, ((ν : ℂ) ^ 2 + (σ : ℂ) ^ 2) *
      (((2 * Real.pi : ℂ) ^ 4)⁻¹ * ∫ z, prKernel (-ν) σ (fun g => F (toArr g)) z z) := by
  have hP := ((Equiv.neg ℤ).hasSum_iff.2 (plancherel_trace_perezRovelli hF hs).2.1).mul_left
    ((2 * Real.pi : ℂ) ^ 4)⁻¹
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hS : HasSum (fun ν : ℤ => ∫ σ : ℝ, ((ν : ℂ) ^ 2 + (σ : ℂ) ^ 2) *
      (((2 * Real.pi : ℂ) ^ 4)⁻¹ * ∫ z, prKernel (-ν) σ (fun g => F (toArr g)) z z))
      (2 * F (mat2 1 0 0 1)) := by
    convert hP using 1
    · funext ν
      simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg, neg_sq]
      rw [← integral_const_mul]
      congr 1
      funext σ
      ring
    · field_simp
      ring
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq]
  ring

end Lightlike.Lorentz

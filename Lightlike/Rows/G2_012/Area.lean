import Lightlike.Rows.G2_012.Multiplier

/-!
# The area operator on spin networks with transversal punctures (row G2-012)

A surface `S` crossed transversally, once each, by `k` edges of a graph, with no vertex on `S`:
cylindrical functions of the `k` holonomies `g : Fin k → SU2`.  The area operator is
`A(S) = 8π γ ℓ_P² Σ_i √(C_i)`, with `C_i` the Casimir of `SU(2)` acting on the `i`-th edge, whose value
on spin `j = m / 2` is `j (j + 1)`.  We realise `√C_i` by the Peter–Weyl multiplier `casSqrt`
(`Multiplier.lean`) acting on the `i`-th variable.  The theorem `areaOperator_spinNetwork` is that a
spin-network function is an eigenfunction with eigenvalue `8π γ ℓ_P² Σ_i √(j_i (j_i + 1))`.
-/

open MeasureTheory Lightlike.HarmonicAnalysis UnitaryMatrixRep

namespace Lightlike.Rows.G2_012

noncomputable section

variable (μ : Measure SU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- The square root of the Casimir on the spin-`m/2` representation, `√(m (m + 2)) / 2`. -/
def casSqrt (m : ℕ) : ℝ := Real.sqrt ((m : ℝ) * ((m : ℝ) + 2)) / 2

/-- `casSqrt m = √(j (j + 1))` with `j = m / 2`. -/
theorem casSqrt_eq_sqrt_j (m : ℕ) :
    casSqrt m = Real.sqrt (((m : ℝ) / 2) * ((m : ℝ) / 2 + 1)) := by
  have h : ((m : ℝ) / 2) * ((m : ℝ) / 2 + 1) = ((m : ℝ) * ((m : ℝ) + 2)) / 4 := by ring
  rw [h, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]
  rfl

/-- The multiplier `φ` applied to the `i`-th variable of a function of `k` group elements, the others
being held fixed. -/
def edgeMult {k : ℕ} (i : Fin k) (φ : ℕ → ℝ) (F : (Fin k → SU2) → ℂ) : (Fin k → SU2) → ℂ :=
  fun g => pwMultiplier μ φ (fun h => F (Function.update g i h)) (g i)

/-- **The area operator** of a surface with `k` transversal punctures:
`8π γ ℓ² Σ_i √(C_i)`, where `√(C_i)` is `casSqrt` acting on the `i`-th edge. -/
def areaOperator {k : ℕ} (γ ℓ : ℝ) (F : (Fin k → SU2) → ℂ) : (Fin k → SU2) → ℂ :=
  fun g => ((8 * Real.pi * γ * ℓ ^ 2 : ℝ) : ℂ) * ∑ i : Fin k, edgeMult μ i (casSqrt) F g

/-- The spin-network function with spins `m i / 2` and magnetic indices `a i, b i` on the `k` edges. -/
def spinNetwork {k : ℕ} (m : Fin k → ℕ) (a b : ∀ i, Fin (m i + 1)) : (Fin k → SU2) → ℂ :=
  fun g => ∏ i, su2Coeff (m i) (a i) (b i) (g i)

/-- A multiplier acts on a spin network by the product of its value on the `i`-th edge. -/
theorem edgeMult_spinNetwork {k : ℕ} (φ : ℕ → ℝ) (m : Fin k → ℕ) (a b : ∀ i, Fin (m i + 1))
    (i : Fin k) :
    edgeMult μ i φ (spinNetwork m a b) = fun g => (φ (m i) : ℂ) * spinNetwork m a b g := by
  funext g
  set c : ℂ := ∏ l ∈ Finset.univ.erase i, su2Coeff (m l) (a l) (b l) (g l) with hc
  have hslice : (fun h => spinNetwork m a b (Function.update g i h)) =
      fun h => c * su2Coeff (m i) (a i) (b i) h := by
    funext h
    simp only [spinNetwork]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have h1 : ∏ l ∈ Finset.univ.erase i, su2Coeff (m l) (a l) (b l) (Function.update g i h l) =
        c := by
      apply Finset.prod_congr rfl
      intro l hl
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [h1, Function.update_self]
    ring
  have hg : spinNetwork m a b g = c * su2Coeff (m i) (a i) (b i) (g i) := by
    have := congrFun hslice (g i)
    simpa [Function.update_eq_self] using this
  simp only [edgeMult]
  rw [hslice, pwMultiplier_const_mul_su2Coeff, hg]
  ring

/-- **The area spectrum for transversal punctures**: a spin-network function with spins
`j_i = m i / 2` on the `k` punctured edges is an eigenfunction of the area operator with eigenvalue
`8π γ ℓ² Σ_i √(j_i (j_i + 1))`. -/
theorem areaOperator_spinNetwork {k : ℕ} (γ ℓ : ℝ) (m : Fin k → ℕ) (a b : ∀ i, Fin (m i + 1)) :
    areaOperator μ γ ℓ (spinNetwork m a b) =
      fun g => ((8 * Real.pi * γ * ℓ ^ 2 *
          ∑ i : Fin k, Real.sqrt (((m i : ℝ) / 2) * ((m i : ℝ) / 2 + 1)) : ℝ) : ℂ) *
        spinNetwork m a b g := by
  funext g
  simp only [areaOperator, edgeMult_spinNetwork, casSqrt_eq_sqrt_j]
  push_cast
  rw [← Finset.sum_mul]
  ring

end

end Lightlike.Rows.G2_012

import Lightlike.Gauge.Connection.Transport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Abelian connections: the transport is `exp(-∫ A)`

For `𝔄 = ℂ` (the gauge group `U(1)` for `A = i a`), the transport along the segment `t ↦ x + t ξ` is
`U(t) = exp(-∫₀ᵗ A(x + s ξ)(ξ) ds)` (`isSegmentTransport_abelian`), Svetlichny's `P exp(-∫ A)` (arXiv:math-ph/9902027v1,
p. 41) without path ordering. Around the parallelogram the holonomy is the exponential of minus the sum of the four
line integrals (`squareHolonomy_abelian`), the circulation; for `A = i a` this is `exp(-i ∮ a)`, by Stokes
`exp(i · flux)` (GC1 trust check).
-/

open Set MeasureTheory intervalIntegral

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The line integral `∫₀ᵗ A(x + s ξ)(ξ) ds`. -/
def lineIntegral (A : E → E →L[ℝ] ℂ) (x ξ : E) (t : ℝ) : ℂ := ∫ s in (0 : ℝ)..t, A (x + s • ξ) ξ

/-- **The abelian transport** `U(t) = exp(-∫₀ᵗ A)`. -/
theorem isSegmentTransport_abelian {A : E → E →L[ℝ] ℂ} (hA : Continuous A) (x ξ : E) :
    IsSegmentTransport A x ξ (fun t => Complex.exp (-lineIntegral A x ξ t)) := by
  have hcM : Continuous fun s : ℝ => A (x + s • ξ) ξ :=
    (hA.comp (by fun_prop : Continuous fun s : ℝ => x + s • ξ)).clm_apply continuous_const
  refine ⟨by simp [lineIntegral], fun t _ => ?_⟩
  have hI : HasDerivAt (lineIntegral A x ξ) (A (x + t • ξ) ξ) t :=
    integral_hasDerivAt_right (hcM.intervalIntegrable _ _) (hcM.stronglyMeasurableAtFilter _ _) hcM.continuousAt
  have := (hI.neg.cexp).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  simp only [Pi.neg_apply] at this
  convert this using 1
  ring

/-- **Abelian holonomy around the parallelogram**: with the four leg transports `exp(-∫ A)`, the holonomy is
`exp(-(∫₁ + ∫₂ + ∫₃ + ∫₄))`. -/
theorem squareHolonomy_abelian {A : E → E →L[ℝ] ℂ} (x a b : E) :
    Complex.exp (-lineIntegral A (x + b) (-b) 1) * Complex.exp (-lineIntegral A (x + a + b) (-a) 1) *
        Complex.exp (-lineIntegral A (x + a) b 1) * Complex.exp (-lineIntegral A x a 1) =
      Complex.exp (-(lineIntegral A x a 1 + lineIntegral A (x + a) b 1 + lineIntegral A (x + a + b) (-a) 1 +
        lineIntegral A (x + b) (-b) 1)) := by
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; ring

end Lightlike.Gauge

namespace Lightlike.Gauge

/-- The determinant `det(y, ζ) = y₁ ζ₂ - y₂ ζ₁` on `ℝ × ℝ`. -/
def det2 (y ζ : ℝ × ℝ) : ℝ := y.1 * ζ.2 - y.2 * ζ.1

/-- **The uniform field** `A(y)(ζ) = (i b / 2) det(y, ζ)` on `ℝ²` (a `U(1)` connection with curvature `i b dx₁ ∧ dx₂`). -/
def uniformField (b : ℝ) (y : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  ((b / 2 : ℝ) • Complex.I) • (Complex.ofRealCLM.comp
    (y.1 • ContinuousLinearMap.snd ℝ ℝ ℝ - y.2 • ContinuousLinearMap.fst ℝ ℝ ℝ))

lemma uniformField_apply (b : ℝ) (y ζ : ℝ × ℝ) :
    uniformField b y ζ = ((b / 2 : ℝ) • Complex.I) * (det2 y ζ : ℂ) := by
  simp [uniformField, det2, smul_eq_mul]

/-- The line integral of the uniform field along a leg is `(i b / 2) det(y, ζ)`. -/
lemma lineIntegral_uniformField (b : ℝ) (y ζ : ℝ × ℝ) :
    lineIntegral (uniformField b) y ζ 1 = ((b / 2 : ℝ) • Complex.I) * (det2 y ζ : ℂ) := by
  unfold lineIntegral
  have : ∀ s : ℝ, uniformField b (y + s • ζ) ζ = ((b / 2 : ℝ) • Complex.I) * (det2 y ζ : ℂ) := by
    intro s
    rw [uniformField_apply]
    congr 2
    simp only [det2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  simp_rw [this]
  simp

/-- **Trust check: the `U(1)` holonomy of the uniform field is `exp(-i Φ)`**, with the flux `Φ = b det(a, b')`
through the parallelogram spanned by `a, b'`; equivalently `exp(F(b', a))` with `F = dA = i b dx₁ ∧ dx₂`. -/
theorem squareHolonomy_uniformField (b : ℝ) (x a b' : ℝ × ℝ) :
    lineIntegral (uniformField b) x a 1 + lineIntegral (uniformField b) (x + a) b' 1 +
        lineIntegral (uniformField b) (x + a + b') (-a) 1 + lineIntegral (uniformField b) (x + b') (-b') 1 =
      Complex.I * (b * det2 a b' : ℝ) := by
  simp only [lineIntegral_uniformField]
  simp only [det2, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Complex.real_smul]
  push_cast
  ring

end Lightlike.Gauge

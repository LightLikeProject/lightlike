import Lightlike.Gauge.Connection.Transport

/-!
# Pure gauge connections: exact transport and trivial holonomy

For `g, h : E → 𝔄` with `h g = g h = 1` pointwise, the pure gauge `A = h dg` (`A = g⁻¹ dg`) has the explicit
transport `U(t) = h(x + t ξ) g(x)` along every segment (`isSegmentTransport_pureGauge`), so the transport around
the parallelogram telescopes to `h(x) g(x) = 1` (`squareHolonomy_pureGauge`): a flat connection has trivial holonomy
on this contractible loop (trust check of GC1; Svetlichny, arXiv:math-ph/9902027v1, p. 40, for the transport
equation).
-/

open Set

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- The pure gauge `A = g⁻¹ dg`, with `h = g⁻¹` pointwise: `A(x)(ξ) = h(x) · dg(x)(ξ)`. -/
def pureGauge (g h : E → 𝔄) (x : E) : E →L[ℝ] 𝔄 := (ContinuousLinearMap.mul ℝ 𝔄 (h x)).comp (fderiv ℝ g x)

lemma pureGauge_apply (g h : E → 𝔄) (x ξ : E) : pureGauge g h x ξ = h x * fderiv ℝ g x ξ := rfl

/-- The derivative of the inverse: `dh(ζ) = -h · dg(ζ) · h`. -/
lemma fderiv_inv_apply {g h : E → 𝔄} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (hhg : ∀ y, h y * g y = 1) (hgh : ∀ y, g y * h y = 1) (y ζ : E) :
    fderiv ℝ h y ζ = -(h y * fderiv ℝ g y ζ * h y) := by
  have h1 : fderiv ℝ (fun z => h z * g z) y ζ = 0 := by
    rw [show (fun z => h z * g z) = fun _ => (1 : 𝔄) from funext hhg]; simp
  rw [fderiv_fun_mul' (hh y) (hg y)] at h1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    op_smul_eq_mul] at h1
  calc fderiv ℝ h y ζ = fderiv ℝ h y ζ * (g y * h y) := by rw [hgh, mul_one]
    _ = (fderiv ℝ h y ζ * g y) * h y := by rw [mul_assoc]
    _ = -(h y * fderiv ℝ g y ζ) * h y := by rw [eq_neg_of_add_eq_zero_right h1]
    _ = _ := by rw [neg_mul]

/-- **The transport of a pure gauge**: `U(t) = h(x + t ξ) g(x)`. -/
theorem isSegmentTransport_pureGauge {g h : E → 𝔄} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (hhg : ∀ y, h y * g y = 1) (hgh : ∀ y, g y * h y = 1) (x ξ : E) :
    IsSegmentTransport (pureGauge g h) x ξ (fun t => h (x + t • ξ) * g x) := by
  refine ⟨by simp [hhg], fun t _ => ?_⟩
  have hγ : HasDerivAt (fun s : ℝ => x + s • ξ) ξ t := by
    simpa using ((hasDerivAt_id t).smul_const ξ).const_add x
  have hd : HasDerivAt (fun s : ℝ => h (x + s • ξ)) (fderiv ℝ h (x + t • ξ) ξ) t :=
    (hh _).hasFDerivAt.comp_hasDerivAt t hγ
  have := (hd.mul_const (g x)).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  convert this using 1
  rw [fderiv_inv_apply hg hh hhg hgh, pureGauge_apply]
  noncomm_ring

/-- **A pure gauge has trivial holonomy around the parallelogram** (trust check: a flat connection):
any transports along the four legs `x → x + a → x + a + b → x + b → x` multiply to `1`. -/
theorem squareHolonomy_pureGauge {g h : E → 𝔄} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (hhg : ∀ y, h y * g y = 1) (hgh : ∀ y, g y * h y = 1) {x a b : E} {B : NNReal}
    (hB : ∀ (y ζ : E) (t : ℝ), ‖pureGauge g h (y + t • ζ) ζ‖ ≤ B) {U₁ U₂ U₃ U₄ : ℝ → 𝔄}
    (h₁ : IsSegmentTransport (pureGauge g h) x a U₁)
    (h₂ : IsSegmentTransport (pureGauge g h) (x + a) b U₂)
    (h₃ : IsSegmentTransport (pureGauge g h) (x + a + b) (-a) U₃)
    (h₄ : IsSegmentTransport (pureGauge g h) (x + b) (-b) U₄) :
    U₄ 1 * U₃ 1 * U₂ 1 * U₁ 1 = 1 := by
  have one_mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e : ∀ (y ζ : E) (U : ℝ → 𝔄), IsSegmentTransport (pureGauge g h) y ζ U → U 1 = h (y + ζ) * g y := by
    intro y ζ U hU
    have := segmentTransport_unique (fun t _ => hB y ζ t) hU (isSegmentTransport_pureGauge hg hh hhg hgh y ζ)
      one_mem
    rw [this, one_smul]
  rw [e _ _ _ h₁, e _ _ _ h₂, e _ _ _ h₃, e _ _ _ h₄]
  have e1 : x + a + b + -a = x + b := by abel
  have e2 : x + b + -b = x := by abel
  rw [e1, e2]
  calc h x * g (x + b) * (h (x + b) * g (x + a + b)) * (h (x + a + b) * g (x + a)) * (h (x + a) * g x)
      = h x * (g (x + b) * h (x + b)) * (g (x + a + b) * h (x + a + b)) * (g (x + a) * h (x + a)) * g x := by
        noncomm_ring
    _ = 1 := by rw [hgh, hgh, hgh, mul_one, mul_one, mul_one, hhg]

end Lightlike.Gauge

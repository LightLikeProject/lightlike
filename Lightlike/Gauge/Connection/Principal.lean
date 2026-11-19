import Lightlike.Gauge.Connection.GaugeCovariance

/-!
# The connection 1-form on the trivial principal bundle

Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1, §4.6, pp. 29-31: a connection on a principal
`G`-bundle is a `g`-valued 1-form `ω` on the total space with `ω_p(L_p) = L` on the fundamental vector fields
(eq. (34)) and `ω_{p·g}(v · g) = Ad_{g⁻¹} ω_p(v)` (invariance, eq. (35)); on a trivialisation `U × G`, with
`T_{(x,h)}(U × G) ≃ T_x U × g` by right translation, it is `ω_{(x,h)}(ξ, L) = h⁻¹ (A_U(ξ) + L) h` (eq. (36)), where
`A_U` is the local principal gauge potential.

Here the trivial bundle `U × G` over an open `U ⊆ E` (the source's trivialisation; the form itself is pointwise) with `G` the invertible elements of a normed algebra `𝔄` (tangent vectors at
`(x, h)` written `(ξ, L) ∈ E × 𝔄`, the vertical part `L` by right translation, i.e. the tangent vector `L h`):
* `connectionForm A (x, h) (ξ, L) = h⁻¹ (A(x)(ξ) + L) h` (eq. (36));
* `connectionForm_vertical`: `ω` returns `L` on the fundamental vector `(0, h L h⁻¹)` of `L` (eq. (34));
* `connectionForm_mul_right`: `ω_{(x, h g)}(ξ, L) = g⁻¹ ω_{(x, h)}(ξ, L) g` (eq. (35)); right translation by `g` does
  not change the coordinates `(ξ, L)`;
* `connectionForm_unitSection`: the pullback by the unit section `x ↦ (x, 1)` is `A`;
* `connectionForm_section`: the pullback by the section `x ↦ (x, k(x))` (tangent `(ξ, dk(ξ) k⁻¹)`) is
  `k⁻¹ A k + k⁻¹ dk`, the gauge transform of eq. (38) by `g = k⁻¹`.
-/

open scoped Topology

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- **The connection 1-form** (Svetlichny eq. (36)) at `(x, h)` (with `hi = h⁻¹`), on the tangent vector `(ξ, L)`
(vertical part by right translation): `hi (A(x)(ξ) + L) h`. -/
def connectionForm (A : E → E →L[ℝ] 𝔄) (x : E) (h hi : 𝔄) (ξ : E) (L : 𝔄) : 𝔄 := hi * (A x ξ + L) * h

/-- **(34)**: on the fundamental vector field of `L` at `(x, h)`, i.e. `(0, h L h⁻¹)`, the form returns `L`. -/
theorem connectionForm_vertical (A : E → E →L[ℝ] 𝔄) (x : E) {h hi : 𝔄} (h1 : hi * h = 1) (h2 : h * hi = 1)
    (L : 𝔄) : connectionForm A x h hi 0 (h * L * hi) = L := by
  unfold connectionForm
  rw [map_zero, zero_add]
  calc hi * (h * L * hi) * h = (hi * h) * L * (hi * h) := by noncomm_ring
    _ = L := by rw [h1, one_mul, mul_one]

/-- **(35), invariance**: `ω_{(x, h g)}(ξ, L) = g⁻¹ ω_{(x, h)}(ξ, L) g`. -/
theorem connectionForm_mul_right (A : E → E →L[ℝ] 𝔄) (x : E) (h hi g gi : 𝔄) (ξ : E) (L : 𝔄) :
    connectionForm A x (h * g) (gi * hi) ξ L = gi * connectionForm A x h hi ξ L * g := by
  unfold connectionForm; noncomm_ring

/-- **The local gauge potential is the pullback by the unit section**: `ω_{(x, 1)}(ξ, 0) = A(x)(ξ)`. -/
theorem connectionForm_unitSection (A : E → E →L[ℝ] 𝔄) (x ξ : E) : connectionForm A x 1 1 ξ 0 = A x ξ := by
  unfold connectionForm; simp

/-- **The pullback by a section `x ↦ (x, k(x))`**: its tangent vector is `(ξ, dk(ξ) k⁻¹)` in right-translation
coordinates, and the pullback is `k⁻¹ A(ξ) k + k⁻¹ dk(ξ)`, the gauge transform of eq. (38) by `g = k⁻¹`. -/
theorem connectionForm_section (A : E → E →L[ℝ] 𝔄) {k ki : E → 𝔄} {x : E} (hk : ki x * k x = 1) (ξ : E) :
    connectionForm A x (k x) (ki x) ξ (fderiv ℝ k x ξ * ki x) = ki x * A x ξ * k x + ki x * fderiv ℝ k x ξ := by
  unfold connectionForm
  calc ki x * (A x ξ + fderiv ℝ k x ξ * ki x) * k x
      = ki x * A x ξ * k x + ki x * fderiv ℝ k x ξ * (ki x * k x) := by noncomm_ring
    _ = _ := by rw [hk, mul_one]

/-- The pullback by a section `x ↦ (x, k(x))` over an open `U` is the gauge transform of `A` by `g = k⁻¹`
(eq. (38)), at every `x ∈ U`. -/
theorem connectionForm_section_eq_gaugeTransform (A : E → E →L[ℝ] 𝔄) {k ki : E → 𝔄} {U : Set E} (hU : IsOpen U)
    (hk1 : DifferentiableOn ℝ k U) (hki : DifferentiableOn ℝ ki U) (hk : ∀ y ∈ U, ki y * k y = 1)
    (hk' : ∀ y ∈ U, k y * ki y = 1) {x : E} (hx : x ∈ U) (ξ : E) :
    connectionForm A x (k x) (ki x) ξ (fderiv ℝ k x ξ * ki x) = gaugeTransform ki k A x ξ := by
  have hUx : U ∈ 𝓝 x := hU.mem_nhds hx
  rw [connectionForm_section A (hk x hx), gaugeTransform_apply,
    fderiv_inv_apply_of_mem hUx (hk1.differentiableAt hUx) (hki.differentiableAt hUx) hk (hk' x hx) ξ]
  calc ki x * A x ξ * k x + ki x * fderiv ℝ k x ξ
      = ki x * A x ξ * k x + ki x * fderiv ℝ k x ξ * (ki x * k x) := by rw [hk x hx, mul_one]
    _ = _ := by noncomm_ring

end Lightlike.Gauge

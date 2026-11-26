import Mathlib
import Lightlike.Geometry.HeatKernel.WorldFunctionDiag
import Lightlike.Asymptotics.EulerPrimitive
import Lightlike.Geodesic.Gauss

/-!
# The transport operator in normal coordinates

Let `g` be a coordinate metric on an open `U ⊆ ℝⁿ`, `σ` a function on `U` and `V : ℝⁿ → ℝⁿ` (normal coordinates
centred at a point `p`). Suppose that at `y ∈ U` the gradient of `σ` is `2 g_y(T, ·)` for a vector `T` with
`DV(y) T = V(y)` (for the world function `σ(p, ·)` and `V = V(p, ·)` this is what
`Lightlike.Geodesic.exists_sqDist_eikonal` provides: `T` is the velocity at `y` of the geodesic from `p`). Then for every
differentiable `U`,

`g⁻¹(dσ, d(U ∘ V))(y) / 2 = DU(V(y)) V(y)`   (`IsCoordMetric.coordGradPair_comp_eq_euler`):

the first-order part `g⁻¹(dσ, du)/2` of the transport equations is the **Euler operator** `v ↦ DU(v) v` in normal
coordinates. With `Lightlike.fderiv_exp_eulerPrimitive_apply_self` this solves the transport equation of order `0`:
`u₀ = e^K ∘ V` satisfies `g⁻¹(dσ, du₀)/2 = h u₀` when `h = H ∘ V` with `H(0) = 0`
(`IsCoordMetric.transport_zero_of_euler`).
-/

open Set Filter Matrix
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The pairing with the gradient of `σ` is the derivative along `T`**: if `∂ᵢσ(y) = 2 g_y(T, eᵢ)`, then
`g⁻¹(dσ, du)(y)/2 = du(y) T`. -/
theorem IsCoordMetric.coordGradPair_eq_fderiv (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    {σ u : (Fin n → ℝ) → ℝ} {T : Fin n → ℝ} (hσ : ∀ i, pd i σ y = 2 * Geodesic.pairing g y T (Pi.single i 1))
    (hu : DifferentiableAt ℝ u y) :
    coordGradPair g σ u y / 2 = fderiv ℝ u y T := by
  have hT : T = ∑ j, T j • (Pi.single j 1 : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  have hσ' : ∀ i, pd i σ y = 2 * (g y *ᵥ T) i := fun i => by
    rw [hσ i, Geodesic.pairing]
    congr 1
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h := congrFun (congrFun (hg.symm y hy) i) a
    simp only [Matrix.transpose_apply] at h
    rw [← h]; ring
  -- `g⁻¹ (g T) = T`
  have hinv : (g y)⁻¹ *ᵥ (g y *ᵥ T) = T := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hg.isUnit_det y hy), Matrix.one_mulVec]
  have hsym : ∀ i j, (g y)⁻¹ i j = (g y)⁻¹ j i := hg.inv_symm hy
  unfold coordGradPair
  simp only [hσ']
  conv_rhs => rw [hT, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hTj : ∀ j, T j = ∑ i, (g y)⁻¹ j i * (g y *ᵥ T) i := fun j => by
    have := congrFun hinv j
    simpa [Matrix.mulVec, dotProduct] using this.symm
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hTj j, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsym i j]
  unfold pd
  ring

/-- **The transport operator in normal coordinates is the Euler operator**: if `∂ᵢσ(y) = 2 g_y(T, eᵢ)` and
`DV(y) T = V(y)`, then `g⁻¹(dσ, d(U ∘ V))(y)/2 = DU(V(y)) V(y)`. -/
theorem IsCoordMetric.coordGradPair_comp_eq_euler (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    {σ : (Fin n → ℝ) → ℝ} {V : (Fin n → ℝ) → (Fin n → ℝ)} {T : Fin n → ℝ}
    (hσ : ∀ i, pd i σ y = 2 * Geodesic.pairing g y T (Pi.single i 1))
    (hVd : DifferentiableAt ℝ V y) (hVT : fderiv ℝ V y T = V y) {Φ : (Fin n → ℝ) → ℝ}
    (hΦ : DifferentiableAt ℝ Φ (V y)) :
    coordGradPair g σ (fun z => Φ (V z)) y / 2 = fderiv ℝ Φ (V y) (V y) := by
  rw [hg.coordGradPair_eq_fderiv (u := fun z => Φ (V z)) hy hσ (hΦ.comp y hVd)]
  rw [show (fun z => Φ (V z)) = Φ ∘ V from rfl, fderiv_comp y hΦ hVd, ContinuousLinearMap.comp_apply, hVT]

/-- **The transport equation of order `0` in normal coordinates**: with `h = H ∘ V` near `y`, `H(0) = 0`, and
`u₀ = e^K ∘ V` (`K` the Euler primitive of `H`), `g⁻¹(dσ, du₀)(y)/2 = h(y) u₀(y)`. -/
theorem IsCoordMetric.transport_zero_of_euler (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    {σ : (Fin n → ℝ) → ℝ} {V : (Fin n → ℝ) → (Fin n → ℝ)} {T : Fin n → ℝ}
    (hσ : ∀ i, pd i σ y = 2 * Geodesic.pairing g y T (Pi.single i 1))
    (hVd : DifferentiableAt ℝ V y) (hVT : fderiv ℝ V y T = V y) {H : (Fin n → ℝ) → ℝ}
    (hH : ContDiff ℝ ∞ H) (h0 : H 0 = 0) :
    coordGradPair g σ (fun z => Real.exp (eulerPrimitive H (V z))) y / 2 =
      H (V y) * Real.exp (eulerPrimitive H (V y)) := by
  have hΦ : DifferentiableAt ℝ (fun w => Real.exp (eulerPrimitive H w)) (V y) :=
    ((Real.contDiff_exp.comp (contDiff_eulerPrimitive hH)).differentiable (by simp)) (V y)
  rw [hg.coordGradPair_comp_eq_euler hy hσ hVd hVT hΦ, fderiv_exp_eulerPrimitive_apply_self hH h0]

end Lightlike

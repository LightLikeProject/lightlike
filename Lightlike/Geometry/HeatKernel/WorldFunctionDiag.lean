import Mathlib
import Lightlike.Geometry.HeatKernel.TransportEquations

/-!
# The Laplacian of the world function on the diagonal

For a coordinate metric `g` on an open `U ⊆ ℝⁿ` (any signature), a point `p ∈ U` and a smooth `V : U → ℝⁿ` with
`V(p) = 0` and derivative the identity at `p` (the initial velocity `V(p, ·)` of the short geodesic from `p`, see
`Lightlike.Geodesic.exists_sqDist_eikonal`), the function `σ_p(y) = g_p(V(y), V(y))` has

`Δσ_p(p) = −2n`   (`IsCoordMetric.coordLaplacian_pairing_diag`)

for the nonnegative Laplacian `Δ = −ρ⁻¹ ∂ᵢ(ρ g^{ij} ∂ⱼ)`. Hence the coefficient `Δσ/4 + n/2` of the transport equations
(`Lightlike.IsTransport`) vanishes on the diagonal (`IsCoordMetric.transportCoeff_diag`), which is what makes the
transport equation of order `0` solvable with `u₀(p) = 1`.

The proof: `σ_p = Σ_{ab} g_p(a, b) V_a V_b`, the product rule `Δ(V_a V_b) = V_a ΔV_b + V_b ΔV_a − 2 g⁻¹(dV_a, dV_b)`
(`IsCoordMetric.coordLaplacian_mul`) at `p`, where `V = 0` and `∂ᵢV_a = δᵢₐ`, gives `−2 g^{ab}(p)`, and
`Σ_{ab} g_{ab} g^{ab} = n`.
-/

open Set Filter Matrix
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The partial derivatives of a map with derivative the identity at `p`. -/
theorem pd_of_hasFDerivAt_id {V : (Fin n → ℝ) → (Fin n → ℝ)} {p : Fin n → ℝ}
    (hV : HasFDerivAt V (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) (i a : Fin n) :
    pd i (fun y => V y a) p = if i = a then 1 else 0 := by
  have h : HasFDerivAt (fun y => V y a)
      ((ContinuousLinearMap.proj a : (Fin n → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.id ℝ (Fin n → ℝ))) p :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) a (V p)).comp p hV
  unfold pd
  rw [h.fderiv]
  simp [Pi.single_apply, eq_comm]

/-- `Σ_{ab} g_{ab} g^{ab} = n` for an invertible symmetric matrix. -/
theorem sum_mul_inv_symm {G : Matrix (Fin n) (Fin n) ℝ} (hG : IsUnit G.det) (hs : Gᵀ = G) :
    ∑ a, ∑ b, G a b * G⁻¹ a b = n := by
  have h1 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have htr := congrArg Matrix.trace h1
  rw [Matrix.trace_one, Fintype.card_fin] at htr
  rw [← htr]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hinv : (G⁻¹)ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hs]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have := congrFun (congrFun hinv a) b
  simpa [Matrix.transpose_apply] using this.symm

/-- **The Laplacian of `g_p(V, V)` at `p`** is `−2n` when `V(p) = 0` and `DV(p) = id`. -/
theorem IsCoordMetric.coordLaplacian_pairing_diag (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U)
    {V : (Fin n → ℝ) → (Fin n → ℝ)} (hVs : ∀ a, ContDiffOn ℝ ∞ (fun y => V y a) U) (hV0 : V p = 0)
    (hVd : HasFDerivAt V (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) :
    coordLaplacian g (fun y => ∑ a, ∑ b, V y a * (g p a b * V y b)) p = -2 * n := by
  -- write the function as a sum with constant coefficients `g_p(a, b)` of the products `V_a V_b`
  have hfun : (fun y => ∑ a, ∑ b, V y a * (g p a b * V y b)) =
      fun y => ∑ ab ∈ (Finset.univ : Finset (Fin n × Fin n)), g p ab.1 ab.2 * (V y ab.1 * V y ab.2) := by
    funext y
    rw [← Finset.univ_product_univ, Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hprod : ∀ ab : Fin n × Fin n, ContDiffOn ℝ ∞ (fun y => V y ab.1 * V y ab.2) U := fun ab =>
    (hVs ab.1).mul (hVs ab.2)
  rw [hfun, hg.coordLaplacian_sum_smul _ (fun ab => g p ab.1 ab.2) hprod hp]
  -- each product: `Δ(V_a V_b)(p) = −2 g^{ab}(p)`
  have hab : ∀ ab : Fin n × Fin n, coordLaplacian g (fun y => V y ab.1 * V y ab.2) p = -2 * (g p)⁻¹ ab.1 ab.2 := by
    intro ab
    rw [hg.coordLaplacian_mul (hVs ab.1) (hVs ab.2) hp]
    have h0 : ∀ a, V p a = 0 := fun a => by rw [hV0]; rfl
    rw [h0, h0, zero_mul, zero_mul, zero_add, zero_sub]
    unfold coordGradPair
    simp only [pd_of_hasFDerivAt_id hVd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    ring
  simp only [hab]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have hsum := sum_mul_inv_symm (hg.isUnit_det p hp) (hg.symm p hp)
  calc ∑ a, ∑ b, g p (a, b).1 (a, b).2 * (-2 * (g p)⁻¹ (a, b).1 (a, b).2)
      = -2 * ∑ a, ∑ b, g p a b * (g p)⁻¹ a b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    _ = -2 * n := by rw [hsum]

/-- **The transport coefficient vanishes on the diagonal**: `Δσ_p(p)/4 + n/2 = 0`. -/
theorem IsCoordMetric.transportCoeff_diag (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U)
    {V : (Fin n → ℝ) → (Fin n → ℝ)} (hVs : ∀ a, ContDiffOn ℝ ∞ (fun y => V y a) U) (hV0 : V p = 0)
    (hVd : HasFDerivAt V (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) :
    coordLaplacian g (fun y => ∑ a, ∑ b, V y a * (g p a b * V y b)) p / 4 + n / 2 = 0 := by
  rw [hg.coordLaplacian_pairing_diag hp hVs hV0 hVd]
  ring

end Lightlike

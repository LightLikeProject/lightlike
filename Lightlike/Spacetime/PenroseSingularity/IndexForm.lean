import Lightlike.Spacetime.PenroseSingularity.SecondVariation
import Lightlike.Spacetime.PenroseSingularity.JacobiGeom

/-!
# The index form in a chart (G1-012, step D4)

Along a curve with velocity `w`, the second-order coefficient of a variation by the field `W` with covariant derivative
`P` is `bQ g x w W P = g(P, P) - g(R(w, W) W, w)`-type quadratic form, `tide g x w W W' = g(R(w, W) W', ...)` being the
symmetric tidal bilinear form. This file proves the polarisation identity of `bQ`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The tidal bilinear form `g(R(w, W) W', ·)`: `(W, W') ↦ g (R(w, W), W')`. -/
def tide (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w W W' : Fin n → ℝ) : ℝ :=
  gpairAt g x (Lightlike.Geodesic.riemannApply g x w W) W'

/-- The quadratic form `g(P, P) - g(R(w, W) W, w)` for a field `W` with covariant derivative `P`. -/
def bQ (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w W P : Fin n → ℝ) : ℝ :=
  gpairAt g x P P - tide g x w W W

theorem tide_eq (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W W' : Fin n → ℝ) :
    tide g x w W W' =
      ∑ b, ∑ σ, ∑ μ, ∑ ν, Lightlike.riemannLower g b σ μ ν x * W' b * w σ * W μ * w ν :=
  gpair_riemannApply hg hx w W W'

/-- The tidal form is symmetric. -/
theorem tide_symm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W W' : Fin n → ℝ) :
    tide g x w W W' = tide g x w W' W :=
  gpair_riemannApply_symm hg hx w W W'

/-- The tidal form is additive and homogeneous in the first slot. -/
theorem tide_add_smul (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W η W' : Fin n → ℝ)
    (ε : ℝ) : tide g x w (W + ε • η) W' = tide g x w W W' + ε * tide g x w η W' := by
  rw [tide_eq hg hx, tide_eq hg hx, tide_eq hg hx]
  have h : ∀ b σ μ ν, Lightlike.riemannLower g b σ μ ν x * W' b * w σ * (W + ε • η) μ * w ν =
      Lightlike.riemannLower g b σ μ ν x * W' b * w σ * W μ * w ν +
        ε * (Lightlike.riemannLower g b σ μ ν x * W' b * w σ * η μ * w ν) := fun b σ μ ν => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The pairing is additive and homogeneous in each slot. -/
theorem gpairAt_add_smul_left (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u v w : Fin n → ℝ) (ε : ℝ) :
    gpairAt g x (u + ε • v) w = gpairAt g x u w + ε * gpairAt g x v w := by
  simp only [gpairAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **Polarisation of the quadratic form.** -/
theorem bQ_add_smul (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W η P Q : Fin n → ℝ)
    (ε : ℝ) :
    bQ g x w (W + ε • η) (P + ε • Q) = bQ g x w W P + 2 * ε * (gpairAt g x P Q - tide g x w W η) +
      ε ^ 2 * bQ g x w η Q := by
  unfold bQ
  have hs := gpairAt_symm hg hx
  have e1 : gpairAt g x (P + ε • Q) (P + ε • Q) = gpairAt g x P P + 2 * ε * gpairAt g x P Q +
      ε ^ 2 * gpairAt g x Q Q := by
    rw [gpairAt_add_smul_left, hs P (P + ε • Q), hs Q (P + ε • Q), gpairAt_add_smul_left,
      gpairAt_add_smul_left, hs Q P]
    ring
  have e2 : tide g x w (W + ε • η) (W + ε • η) = tide g x w W W + 2 * ε * tide g x w W η +
      ε ^ 2 * tide g x w η η := by
    rw [tide_add_smul hg hx, tide_symm hg hx w W (W + ε • η), tide_symm hg hx w η (W + ε • η),
      tide_add_smul hg hx, tide_add_smul hg hx, tide_symm hg hx w η W]
    ring
  rw [e1, e2]
  ring

/-- `covDAlong` is the derivative plus the Christoffel contraction. -/
theorem covDAlong_eq_add (x v W W' : Fin n → ℝ) :
    (fun a => covDAlong g x v W W' a) = W' + Lightlike.Geodesic.gammaApply g x v W := by
  ext a
  simp [covDAlong, Lightlike.Geodesic.gammaApply, mul_assoc]

/-- **Derivative of the pairing of a Jacobi covariant derivative with a field.** For a Jacobi field `J` with
covariant derivative `P` along a geodesic `γ` with velocity `w`, and any field `η` with derivative `η'`,
`d/dt g(P, η) = g(P, η' + Γ(w, η)) - g(R(w, J) η, ...)`. -/
theorem hasDerivAt_pair_jacobi (hg : Lightlike.IsCoordMetric g U) {γ w J P : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : Lightlike.Geodesic.IsJacobiOn g γ w J P I) (hγU : ∀ t ∈ I, γ t ∈ U) {t : ℝ} (ht : t ∈ I)
    {η : ℝ → Fin n → ℝ} {η' : Fin n → ℝ} (hη : HasDerivAt η η' t) :
    HasDerivAt (fun r => gpairAt g (γ r) (P r) (η r))
      (gpairAt g (γ t) (P t) (η' + Lightlike.Geodesic.gammaApply g (γ t) (w t) (η t)) -
        tide g (γ t) (w t) (J t) (η t)) t := by
  have hγ : HasDerivAt γ (w t) t := hJ.geodesic.1 t ht
  have h := hasDerivAt_gpair hg hγ (hγU t ht) (hJ.deriv_cov t ht) hη
  refine h.congr_deriv ?_
  rw [covDAlong_eq_add, covDAlong_eq_add]
  have e : -Lightlike.Geodesic.gammaApply g (γ t) (w t) (P t) - Lightlike.Geodesic.riemannApply g (γ t) (w t) (J t) +
      Lightlike.Geodesic.gammaApply g (γ t) (w t) (P t) = -Lightlike.Geodesic.riemannApply g (γ t) (w t) (J t) := by
    abel
  rw [e]
  have : gpairAt g (γ t) (-Lightlike.Geodesic.riemannApply g (γ t) (w t) (J t)) (η t) = - tide g (γ t) (w t) (J t) (η t) :=
    gpairAt_neg_left _ _ _ _
  rw [this]
  ring

/-- **For a Jacobi field the quadratic form is the derivative of `g(P, J)`.** -/
theorem hasDerivAt_pair_self_jacobi (hg : Lightlike.IsCoordMetric g U) {γ w J P : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : Lightlike.Geodesic.IsJacobiOn g γ w J P I) (hγU : ∀ t ∈ I, γ t ∈ U) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun r => gpairAt g (γ r) (P r) (J r)) (bQ g (γ t) (w t) (J t) (P t)) t := by
  have h := hasDerivAt_pair_jacobi hg hJ hγU ht (hJ.deriv_field t ht)
  refine h.congr_deriv ?_
  unfold bQ
  congr 2
  abel

/-- An antisymmetric array contracted with a symmetric one vanishes. -/
theorem sum_antisymm_symm {f c : Fin n → Fin n → ℝ} (hf : ∀ μ ν, f μ ν = -f ν μ) (hc : ∀ μ ν, c μ ν = c ν μ) :
    ∑ μ, ∑ ν, f μ ν * c μ ν = 0 := by
  have h : ∑ μ, ∑ ν, f μ ν * c μ ν = -∑ μ, ∑ ν, f μ ν * c μ ν := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hf ν μ, hc ν μ]; ring
  linarith

/-- The tidal form vanishes when the first slot is the velocity. -/
theorem tide_w_left (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W' : Fin n → ℝ) :
    tide g x w w W' = 0 := by
  rw [tide_eq hg hx]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun σ _ => ?_
  have h := sum_antisymm_symm (f := fun μ ν => Lightlike.riemannLower g b σ μ ν x)
    (c := fun μ ν => w μ * w ν)
    (fun μ ν => Lightlike.riemannLower_antisymm_last g b σ μ ν x) (fun μ ν => mul_comm _ _)
  calc ∑ μ, ∑ ν, Lightlike.riemannLower g b σ μ ν x * W' b * w σ * w μ * w ν
      = (W' b * w σ) * ∑ μ, ∑ ν, Lightlike.riemannLower g b σ μ ν x * (w μ * w ν) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        ring
    _ = 0 := by rw [h]; ring

/-- The tidal form vanishes when the second slot is the velocity. -/
theorem tide_w_right (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W : Fin n → ℝ) :
    tide g x w W w = 0 := by
  rw [tide_symm hg hx]; exact tide_w_left hg hx w W

/-- **`bQ` is invariant under adding a multiple of the velocity**, for a null velocity orthogonal to `P`. -/
theorem bQ_add_w (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W P : Fin n → ℝ)
    (a b : ℝ) (hww : gpairAt g x w w = 0) (hPw : gpairAt g x P w = 0) :
    bQ g x w (W + a • w) (P + b • w) = bQ g x w W P := by
  unfold bQ
  have hs := gpairAt_symm hg hx
  have e1 : gpairAt g x (P + b • w) (P + b • w) = gpairAt g x P P := by
    have hwP : gpairAt g x w P = 0 := by rw [hs]; exact hPw
    have hP1 : gpairAt g x P (P + b • w) = gpairAt g x P P := by
      rw [hs P (P + b • w), gpairAt_add_smul_left, hwP]; ring
    have hP2 : gpairAt g x w (P + b • w) = 0 := by
      rw [hs w (P + b • w), gpairAt_add_smul_left, hPw, hww]; ring
    rw [gpairAt_add_smul_left, hP1, hP2]
    ring
  have e2 : tide g x w (W + a • w) (W + a • w) = tide g x w W W := by
    rw [tide_add_smul hg hx, tide_w_left hg hx, tide_symm hg hx w W (W + a • w), tide_add_smul hg hx,
      tide_w_left hg hx]
    ring
  rw [e1, e2]

end Lightlike.Penrose

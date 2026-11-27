import Mathlib
import Lightlike.Spacetime.LaplaceBeltrami.CoordCalculus

/-!
# The coordinate Laplacian of a function with a parameter is jointly smooth

For a coordinate metric `g` on an open `U ⊆ ℝⁿ`, a finite-dimensional parameter space `P`, an open `Ω ⊆ P × ℝⁿ` whose
points have their second component in `U`, and `F : P × ℝⁿ → ℝ` smooth on `Ω`, the partial derivatives in the second
variable (`pdY`) and the coordinate Laplacian in the second variable,
`(p, y) ↦ Δ_g (F(p, ·))(y)` (`IsCoordMetric.contDiffOn_coordLaplacian_param`), are smooth on `Ω`. This is the joint
regularity of the transport coefficient `Δ_y σ(p, y)/4 + n/2` of the world function, needed for the smoothness of the
heat-kernel coefficients `u_k(p, y)`.
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The partial derivative in the second variable, `∂_{y_j} F(p, y)`, as the derivative of `F` along `(0, e_j)`. -/
def pdY (j : Fin n) (F : P × (Fin n → ℝ) → ℝ) (q : P × (Fin n → ℝ)) : ℝ :=
  fderiv ℝ F q ((0 : P), (Pi.single j 1 : Fin n → ℝ))

theorem contDiffOn_pdY {Ω : Set (P × (Fin n → ℝ))} (hΩ : IsOpen Ω) {F : P × (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F Ω) (j : Fin n) : ContDiffOn ℝ ∞ (pdY j F) Ω :=
  (hF.fderiv_of_isOpen hΩ (by exact_mod_cast le_top)).clm_apply contDiffOn_const

/-- **The partial derivative in `y` at fixed `p` is `pdY`.** -/
theorem pd_eq_pdY {Ω : Set (P × (Fin n → ℝ))} (hΩ : IsOpen Ω) {F : P × (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F Ω) {q : P × (Fin n → ℝ)} (hq : q ∈ Ω) (j : Fin n) :
    pd j (fun y => F (q.1, y)) q.2 = pdY j F q := by
  have hd : HasFDerivAt F (fderiv ℝ F q) (q.1, q.2) :=
    ((hF.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have h : HasFDerivAt (fun y => F (q.1, y))
      ((fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ P (Fin n → ℝ))) q.2 :=
    hd.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
  unfold pd pdY
  rw [h.fderiv]
  rfl

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The slice `{y | (p, y) ∈ Ω}` is open. -/
theorem isOpen_slice {Ω : Set (P × (Fin n → ℝ))} (hΩ : IsOpen Ω) (p : P) : IsOpen {y | (p, y) ∈ Ω} :=
  hΩ.preimage (continuous_const.prodMk continuous_id)

/-- **The coordinate Laplacian in the second variable is jointly smooth.** -/
theorem IsCoordMetric.contDiffOn_coordLaplacian_param (hg : IsCoordMetric g U) {Ω : Set (P × (Fin n → ℝ))}
    (hΩ : IsOpen Ω) (hΩU : ∀ q ∈ Ω, q.2 ∈ U) {F : P × (Fin n → ℝ) → ℝ} (hF : ContDiffOn ℝ ∞ F Ω) :
    ContDiffOn ℝ ∞ (fun q : P × (Fin n → ℝ) => coordLaplacian g (fun y => F (q.1, y)) q.2) Ω := by
  have hg2 : ∀ i j, ContDiffOn ℝ ∞ (fun q : P × (Fin n → ℝ) => (g q.2)⁻¹ i j) Ω := fun i j =>
    (hg.contDiffOn_inv i j).comp contDiffOn_snd fun q hq => hΩU q hq
  have hρ : ContDiffOn ℝ ∞ (fun q : P × (Fin n → ℝ) => coordDensity g q.2) Ω :=
    hg.contDiffOn_coordDensity.comp contDiffOn_snd fun q hq => hΩU q hq
  -- the flux as a jointly smooth function
  set Φ : Fin n → P × (Fin n → ℝ) → ℝ := fun i q => coordDensity g q.2 * ∑ j, (g q.2)⁻¹ i j * pdY j F q with hΦ
  have hΦs : ∀ i, ContDiffOn ℝ ∞ (Φ i) Ω := fun i =>
    hρ.mul (ContDiffOn.sum fun j _ => (hg2 i j).mul (contDiffOn_pdY hΩ hF j))
  have hflux : ∀ q ∈ Ω, ∀ i, coordFlux g (fun y => F (q.1, y)) i =ᶠ[𝓝 q.2] fun y => Φ i (q.1, y) := by
    intro q hq i
    filter_upwards [(isOpen_slice hΩ q.1).mem_nhds (show (q.1, q.2) ∈ Ω from hq)] with y hy
    simp only [coordFlux, hΦ]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [pd_eq_pdY hΩ hF (q := (q.1, y)) hy j]
  have heq : ∀ q ∈ Ω, coordLaplacian g (fun y => F (q.1, y)) q.2 =
      -(coordDensity g q.2)⁻¹ * ∑ i, pdY i (Φ i) q := by
    intro q hq
    unfold coordLaplacian
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_congr (hflux q hq i) i]
    exact pd_eq_pdY hΩ (hΦs i) hq i
  refine ContDiffOn.congr ?_ heq
  refine (hρ.inv fun q hq => (hg.coordDensity_pos (hΩU q hq)).ne').neg.mul ?_
  exact ContDiffOn.sum fun i _ => contDiffOn_pdY hΩ (hΦs i) i

end Lightlike

import Lightlike.Spacetime.ChartTensor
import Lightlike.Spacetime.RaychaudhuriManifold
import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.RicciContinuous
import Lightlike.Spacetime.EHManifold.Perturbation
import Lightlike.Spacetime.EHManifold.DeltaChristoffel

/-!
# The covariant derivative of a metric perturbation in a chart (M16, step 2)

For a symmetric bilinear field `h` on a manifold and the Levi-Civita connection of a metric `g`, the intrinsic covariant
derivative `(∇_X h)(v, w)` (main's `covDerivBilinAt`) has, in the chart at `x₀`, the components
`∇ₐ h_{bc} = ∂ₐ h_{bc} - Γᵐ_{ab} h_{mc} - Γᵐ_{ac} h_{bm}` of the coordinate metric and the coordinate components of `h`
(`covH`): `covDerivBilinAt_coordField`, and for any vectors `covDerivBilinAt_eq_sum`.

So the boundary vector of the variation `W^ρ = g^{ρl} g^{σν} (∇_σ h_{lν} - ∇_l h_{σν})` (`Wvec_eq_cov`) is a vector field:
`palatiniField`, defined at each point by its components `W` in the chart at that point, has components `W` in the chart
at any `x₀` (`hv_palatiniField`). The proof: the coordinate metric and `∇h` transform with the Jacobian of the change of
chart (`coordMetric_chJac`, `covArr_chJac`), and then `G⁻¹ψ` with `ψ_l = Σ G⁻¹_{σν} (∇_σ h_{lν} - ∇_l h_{σν})` transforms
as a vector (`psiC_conj`, `inv_psiC_conj`, from the basis independence of a metric trace, `sum_inv_mul_conj`).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology Matrix

noncomputable section

namespace Lightlike

section Algebra

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ}

/-- A vector in the standard basis. -/
theorem vec_expand (p : Fin n → ℝ) : p = ∑ a, p a • (Pi.single a 1 : Fin n → ℝ) := by
  ext i; simp [Pi.single_apply]

/-- The components formula of a covariant derivative of a bilinear form is trilinear:
`D p q r - B(Γ(q, p), r) - B(q, Γ(r, p)) = Σ pᵃ qᵇ rᶜ (D(eₐ, e_b, e_c) - B(Γ(e_b, eₐ), e_c) - B(e_b, Γ(e_c, eₐ)))`. -/
theorem covComp_expand (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (Γ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (p q r : Fin n → ℝ) :
    D p q r - B (Γ q p) r - B q (Γ r p) =
      ∑ a, ∑ b, ∑ c, p a * q b * r c * (D (Pi.single a 1) (Pi.single b 1) (Pi.single c 1)
        - B (Γ (Pi.single b 1) (Pi.single a 1)) (Pi.single c 1)
        - B (Pi.single b 1) (Γ (Pi.single c 1) (Pi.single a 1))) := by
  have hp : D p q r - B (Γ q p) r - B q (Γ r p) =
      ∑ a, p a * (D (Pi.single a 1) q r - B (Γ q (Pi.single a 1)) r - B q (Γ r (Pi.single a 1))) := by
    conv_lhs => rw [vec_expand p]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib]
  have hq : ∀ a, D (Pi.single a 1) q r - B (Γ q (Pi.single a 1)) r - B q (Γ r (Pi.single a 1)) =
      ∑ b, q b * (D (Pi.single a 1) (Pi.single b 1) r - B (Γ (Pi.single b 1) (Pi.single a 1)) r
        - B (Pi.single b 1) (Γ r (Pi.single a 1))) := fun a => by
    conv_lhs => rw [vec_expand q]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib]
  have hr : ∀ a b, D (Pi.single a 1) (Pi.single b 1) r - B (Γ (Pi.single b 1) (Pi.single a 1)) r
      - B (Pi.single b 1) (Γ r (Pi.single a 1)) =
      ∑ c, r c * (D (Pi.single a 1) (Pi.single b 1) (Pi.single c 1)
        - B (Γ (Pi.single b 1) (Pi.single a 1)) (Pi.single c 1)
        - B (Pi.single b 1) (Γ (Pi.single c 1) (Pi.single a 1))) := fun a b => by
    conv_lhs => rw [vec_expand r]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib]
  rw [hp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hq a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hr a b, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring
end Algebra

section MatrixAlg

open Matrix

variable {n : ℕ}

theorem sum_mul_eq_trace (A C : Matrix (Fin n) (Fin n) ℝ) :
    ∑ a, ∑ b, A a b * C a b = trace (A * Cᵀ) := by
  simp [trace, Matrix.mul_apply]

/-- **A metric trace does not depend on the basis**: `Σ (JᵀGJ)⁻¹ₐ_b (JᵀTJ)ₐ_b = Σ G⁻¹ₐ_b Tₐ_b` when `JᵀGJ` is
invertible. -/
theorem sum_inv_mul_conj (G T J : Matrix (Fin n) (Fin n) ℝ) (hJG : IsUnit (Jᵀ * G * J).det) :
    ∑ a, ∑ b, (Jᵀ * G * J)⁻¹ a b * (Jᵀ * T * J) a b = ∑ a, ∑ b, G⁻¹ a b * T a b := by
  have hdet : (Jᵀ * G * J).det = J.det * G.det * J.det := by
    rw [det_mul, det_mul, det_transpose]
  have hJ : IsUnit J.det := by
    rw [hdet] at hJG
    exact isUnit_of_mul_isUnit_right hJG
  have hJt : IsUnit Jᵀ.det := by rwa [det_transpose]
  rw [sum_mul_eq_trace, sum_mul_eq_trace, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e : (Jᵀ * T * J)ᵀ = Jᵀ * Tᵀ * J := by
    rw [transpose_mul, transpose_mul, transpose_transpose]; simp only [Matrix.mul_assoc]
  rw [e]
  have h1 : J⁻¹ * (G⁻¹ * Jᵀ⁻¹) * (Jᵀ * Tᵀ * J) = J⁻¹ * (G⁻¹ * Tᵀ) * J := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᵀ⁻¹ Jᵀ, nonsing_inv_mul _ hJt, Matrix.one_mul]
  rw [h1, trace_mul_comm, ← Matrix.mul_assoc, mul_nonsing_inv _ hJ, Matrix.one_mul]
theorem conj_apply (J A : Matrix (Fin n) (Fin n) ℝ) (σ ν : Fin n) :
    (Jᵀ * A * J) σ ν = ∑ a, ∑ c, J a σ * A a c * J c ν := by
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The covector `ψ_l = Σ G⁻¹_{σν} (C_{σlν} - C_{lσν})` of a metric `G` and a three-index array `C`. -/
def psiC (G : Matrix (Fin n) (Fin n) ℝ) (C : Fin n → Fin n → Fin n → ℝ) (l : Fin n) : ℝ :=
  ∑ σ, ∑ ν, G⁻¹ σ ν * (C σ l ν - C l σ ν)

/-- A three-index array in the basis `e'_σ = Σ_a J_{aσ} e_a`. -/
def conjC (J : Matrix (Fin n) (Fin n) ℝ) (C : Fin n → Fin n → Fin n → ℝ) : Fin n → Fin n → Fin n → ℝ :=
  fun σ b ν => ∑ a, ∑ b', ∑ c, J a σ * J b' b * J c ν * C a b' c

/-- **`ψ` is a covector**: `ψ'_l = Σ_b J_{bl} ψ_b` under the change of basis `J`. -/
theorem psiC_conj (G J : Matrix (Fin n) (Fin n) ℝ) (C : Fin n → Fin n → Fin n → ℝ)
    (hJG : IsUnit (Jᵀ * G * J).det) (l : Fin n) :
    psiC (Jᵀ * G * J) (conjC J C) l = ∑ b, J b l * psiC G C b := by
  set S : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a c => ∑ b, J b l * (C a b c - C b a c) with hS
  have hT : ∀ σ ν, conjC J C σ l ν - conjC J C l σ ν = (Jᵀ * S * J) σ ν := fun σ ν => by
    rw [conj_apply]
    simp only [conjC, hS, Matrix.of_apply, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
    · conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring
  unfold psiC
  simp only [hT]
  rw [sum_inv_mul_conj G S J hJG]
  simp only [hS, Matrix.of_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => by ring

/-- **`G⁻¹ψ` is a vector**: `J (G'⁻¹ ψ') = G⁻¹ ψ` for `G' = JᵀGJ` and `C' = J·J·J·C`. -/
theorem inv_psiC_conj (G J : Matrix (Fin n) (Fin n) ℝ) (C : Fin n → Fin n → Fin n → ℝ)
    (hJG : IsUnit (Jᵀ * G * J).det) :
    J *ᵥ ((Jᵀ * G * J)⁻¹ *ᵥ psiC (Jᵀ * G * J) (conjC J C)) = G⁻¹ *ᵥ psiC G C := by
  have hdet : (Jᵀ * G * J).det = J.det * G.det * J.det := by
    rw [det_mul, det_mul, det_transpose]
  have hJ : IsUnit J.det := by
    rw [hdet] at hJG
    exact isUnit_of_mul_isUnit_right hJG
  have hJt : IsUnit Jᵀ.det := by rwa [det_transpose]
  have hψ : psiC (Jᵀ * G * J) (conjC J C) = Jᵀ *ᵥ psiC G C := by
    funext l
    rw [psiC_conj G J C hJG l, Matrix.mulVec, dotProduct]
    simp only [transpose_apply]
  rw [hψ, mulVec_mulVec, mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  congr 1
  rw [show J * (J⁻¹ * (G⁻¹ * Jᵀ⁻¹)) * Jᵀ = (J * J⁻¹) * G⁻¹ * (Jᵀ⁻¹ * Jᵀ) by simp only [Matrix.mul_assoc],
    mul_nonsing_inv _ hJ, nonsing_inv_mul _ hJt, Matrix.one_mul, Matrix.mul_one]

end MatrixAlg

section Components

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)

/-- The components of `h` in the chart at `x₀`, as a bilinear form on `ℝⁿ`. -/
def symComp (y' : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ σ, ∑ ν, h.coordComp x₀ y' σ ν •
    (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)

/-- The component field of `h` in the chart at `x₀`. -/
def BH (y : M) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  symComp h x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y)

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
theorem symComp_apply (y' : Fin n → ℝ) (a b : Fin n → ℝ) :
    symComp h x₀ y' a b = ∑ σ, ∑ ν, a σ * b ν * h.coordComp x₀ y' σ ν := by
  unfold symComp
  simp only [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
theorem symComp_single (y' : Fin n → ℝ) (b c : Fin n) :
    symComp h x₀ y' (Pi.single b 1) (Pi.single c 1) = h.coordComp x₀ y' b c := by
  rw [symComp_apply]
  simp [Pi.single_apply]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- `h` in the components of the chart: `h(u, w) = û ⬝ (h_{ij} ŵ)`. -/
theorem symBil_hv {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) :
    h.h _ u w = hv x₀ _ u ⬝ᵥ (h.coordComp x₀ y *ᵥ hv x₀ _ w) := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hdec : ∀ z : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y),
      z = ∑ i, hv x₀ _ z i • coordBasis x₀ hp i := fun z => by
    conv_lhs => rw [← symmL_hv x₀ hp z,
      show hv x₀ _ z = ∑ i, hv x₀ _ z i • Pi.single i (1 : ℝ) by ext i; simp [Pi.single_apply]]
    simp only [map_sum, map_smul, coordBasis_apply]
  conv_lhs => rw [hdec u, hdec w]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    ← h.coordComp_eq x₀ hy, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- `h` is the bilinear form with components `BH` on the chart domain. -/
theorem symBil_eq_bilOf {y : M} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
    h.h y u v = bilOf x₀ (BH h x₀) y u v := by
  have key := symBil_hv h x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hy)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hy] at key
  rw [key u v, bilOf, BH, symComp_apply]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
theorem differentiableAt_symComp {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    DifferentiableAt ℝ (symComp h x₀) y := by
  unfold symComp
  have hc : ∀ σ ν : Fin n, DifferentiableAt ℝ (fun y' => h.coordComp x₀ y' σ ν) y := fun σ ν =>
    ((h.coordComp_smooth x₀ σ ν).contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hy)).differentiableAt
      (by simp)
  exact differentiableAt_sum_smul (fun σ ν y' => h.coordComp x₀ y' σ ν)
    (fun σ ν => (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)) hc

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The component field `BH` is differentiable on the chart domain. -/
theorem mdiffAt_BH {x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (BH h x₀) x := by
  have hd := differentiableAt_symComp h x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hx)
  have hφ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) x :=
    mdifferentiableAt_extChartAt (by simpa using hx)
  exact (hd.mdifferentiableAt).comp x hφ

variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [LocallySmoothConnection cov]

/-- **The covariant derivative of `h` in the components of the chart at `x₀`.** -/
theorem covDerivBilinAt_symBil {x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (X₀ v₀ w₀ : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (fun y u v => h.h y u v) x X₀ v₀ w₀ =
      (mvfderiv 𝓘(ℝ, Fin n → ℝ) (BH h x₀) x X₀) (hv x₀ x v₀) (hv x₀ x w₀)
        - BH h x₀ x (gamHat cov x₀ x (hv x₀ x v₀) (hv x₀ x X₀)) (hv x₀ x w₀)
        - BH h x₀ x (hv x₀ x v₀) (gamHat cov x₀ x (hv x₀ x w₀) (hv x₀ x X₀)) := by
  have hxb := mem_baseSet_of_mem_source x₀ hx
  rw [← covDerivBilinAt_bilOf cov x₀ hxb (mdiffAt_BH h x₀ hx)]
  unfold Connection.covDerivBilinAt
  have heq : (fun y => h.h y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y))
      =ᶠ[nhds x] fun y => bilOf x₀ (BH h x₀) y (FiberBundle.extend (Fin n → ℝ) v₀ y)
        (FiberBundle.extend (Fin n → ℝ) w₀ y) := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds hx] with y hy
    exact symBil_eq_bilOf h x₀ hy _ _
  have hm : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ)
      (fun y => h.h y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) x X₀ =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (fun y => bilOf x₀ (BH h x₀) y (FiberBundle.extend (Fin n → ℝ) v₀ y)
        (FiberBundle.extend (Fin n → ℝ) w₀ y)) x X₀ := by
    rw [heq.mfderiv_eq]
    simp [tangentSpaceCast]
    rfl
  simp only [symBil_eq_bilOf h x₀ hx]
  rw [hm]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The derivative of the component field `BH` along `X` is the derivative of the components in the chart. -/
theorem mvfderiv_BH {x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (X₀ : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) (BH h x₀) x X₀ =
      fderiv ℝ (symComp h x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) (hv x₀ x X₀) := by
  rw [mvfderiv_eq_chart₀ x₀ (BH h x₀) hx (mdiffAt_BH h x₀ hx) X₀, mfderiv_extChartAt_apply' x₀ hx X₀]
  have hy := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hx
  have heq : BH h x₀ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm =ᶠ[nhds (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x)]
      symComp h x₀ := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hy] with y' hy'
    simp only [Function.comp_apply, BH, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy']
  rw [heq.fderiv_eq]

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The derivative of the components `h_{bc}` is the derivative of `symComp` on the basis vectors. -/
theorem pd_coordComp {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (a b c : Fin n) :
    pd a (fun z => h.coordComp x₀ z b c) y =
      fderiv ℝ (symComp h x₀) y (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) := by
  have hd := differentiableAt_symComp h x₀ hy
  obtain ⟨L, hL⟩ : ∃ L : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ,
      L = (ContinuousLinearMap.apply ℝ ℝ (Pi.single c (1 : ℝ) : Fin n → ℝ)).comp
        (ContinuousLinearMap.apply ℝ ((Fin n → ℝ) →L[ℝ] ℝ) (Pi.single b (1 : ℝ) : Fin n → ℝ)) := ⟨_, rfl⟩
  have hfun : (fun z => h.coordComp x₀ z b c) = (⇑L) ∘ symComp h x₀ := by
    funext z; rw [hL]; simp [symComp_single]
  have hc : fderiv ℝ ((⇑L) ∘ symComp h x₀) y = L.comp (fderiv ℝ (symComp h x₀) y) := by
    have hLd : DifferentiableAt ℝ (⇑L) (symComp h x₀ y) := by fun_prop
    rw [fderiv_comp (𝕜 := ℝ) (g := ⇑L) (f := symComp h x₀) y hLd hd, (L.hasFDerivAt (x := symComp h x₀ y)).fderiv]
  unfold pd
  rw [hfun, hc, hL]
  rfl

omit [LocallySmoothConnection cov] in
/-- The components formula on the standard basis is `covH`. -/
theorem covComp_basis (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (hLC : cov.IsLeviCivita g) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (a b c : Fin n) :
    fderiv ℝ (symComp h x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) (Pi.single a 1) (Pi.single b 1) (Pi.single c 1)
      - BH h x₀ x (gamHat cov x₀ x (Pi.single b 1) (Pi.single a 1)) (Pi.single c 1)
      - BH h x₀ x (Pi.single b 1) (gamHat cov x₀ x (Pi.single c 1) (Pi.single a 1)) =
      covH (g.coordMetric x₀) (h.coordComp x₀) a b c (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) := by
  have hxb := mem_baseSet_of_mem_source x₀ hx
  have hy := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hx
  simp only [gamHat_coord cov x₀ g hLC hxb, map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, BH, symComp_single, ← pd_coordComp h x₀ hy]
  unfold covH
  ring

/-- **The covariant derivative of `h` on coordinate vectors is `covH`**: `(∇_{∂ₐ} h)(∂_b, ∂_c) = ∇ₐ h_{bc}` for the
coordinate metric and the components of `h` in the chart at `x₀`, for the Levi-Civita connection. -/
theorem covDerivBilinAt_coordField (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (hLC : cov.IsLeviCivita g) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (a b c : Fin n) :
    cov.covDerivBilinAt (fun y u v => h.h y u v) x (coordField x₀ a x) (coordField x₀ b x) (coordField x₀ c x) =
      covH (g.coordMetric x₀) (h.coordComp x₀) a b c (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) := by
  have hxb := mem_baseSet_of_mem_source x₀ hx
  rw [covDerivBilinAt_symBil h x₀ cov hx, mvfderiv_BH h x₀ hx]
  simp only [hv_coordField x₀ hxb]
  exact covComp_basis h x₀ cov g hLC hx a b c

/-- **The covariant derivative of `h` in a chart, for any vectors**:
`(∇_X h)(v, w) = Σ Xᵃ vᵇ wᶜ ∇ₐ h_{bc}` with the components `X̂, v̂, ŵ` in the chart at `x₀`. -/
theorem covDerivBilinAt_eq_sum (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (hLC : cov.IsLeviCivita g) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (X₀ v₀ w₀ : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (fun y u v => h.h y u v) x X₀ v₀ w₀ =
      ∑ a, ∑ b, ∑ c, hv x₀ x X₀ a * hv x₀ x v₀ b * hv x₀ x w₀ c *
        covH (g.coordMetric x₀) (h.coordComp x₀) a b c (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) := by
  rw [covDerivBilinAt_symBil h x₀ cov hx, mvfderiv_BH h x₀ hx, covComp_expand]
  simp only [covComp_basis h x₀ cov g hLC hx]

end Components

section Field

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)

/-- The boundary vector `W` of the variation in the chart at `x₀` (`Wvec` of the coordinate metric and the components of
`h`). -/
def pvec (x₀ : M) (y : Fin n → ℝ) : Fin n → ℝ := fun ρ => Wvec (g.coordMetric x₀) (h.coordComp x₀) ρ y

/-- The covariant derivative `∇ₐ h_{bc}` in the chart at `x₀`, as an array. -/
def covArr (x₀ : M) (y : Fin n → ℝ) : Fin n → Fin n → Fin n → ℝ :=
  fun a b c => covH (g.coordMetric x₀) (h.coordComp x₀) a b c y

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
theorem pvec_eq (x₀ : M) (y : Fin n → ℝ) :
    pvec g h x₀ y = (g.coordMetric x₀ y)⁻¹ *ᵥ psiC (g.coordMetric x₀ y) (covArr g h x₀ y) := by
  have hgs : ∀ z a b, g.coordMetric x₀ z a b = g.coordMetric x₀ z b a := fun z a b => by
    have := congrFun (congrFun (g.coordMetric_transpose x₀ z) b) a
    simpa [Matrix.transpose_apply] using this
  funext ρ
  rw [pvec, Wvec_eq_cov _ _ y hgs (fun z a b => h.coordComp_symm x₀ z a b) ρ]
  simp only [Matrix.mulVec, dotProduct, psiC, covArr]

/-- **The boundary vector field of the variation**: at `p`, the tangent vector with components `W` in the chart at `p`. -/
def palatiniField (p : M) : TangentSpace 𝓘(ℝ, Fin n → ℝ) p :=
  (tTriv (E := Fin n → ℝ) p).symmL ℝ p (pvec g h p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p))

/-- The Jacobian at `p` of the change from the chart at `p` to the chart at `x₀`: the components of `∂^p_σ` in the
chart at `x₀`. -/
def chJac (x₀ p : M) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun m σ => hv x₀ p (coordField p σ p) m

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
theorem hv_symmL_chJac {x₀ p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (w : Fin n → ℝ) :
    hv x₀ p ((tTriv (E := Fin n → ℝ) p).symmL ℝ p w) = chJac x₀ p *ᵥ w := by
  have hpp := mem_baseSet_of_mem_source p (mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p)
  have hpx := mem_baseSet_of_mem_source x₀ hp
  have hL : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p,
      hv x₀ p v = (tTriv (E := Fin n → ℝ) x₀).continuousLinearMapAt ℝ p v :=
    fun v => ((tTriv (E := Fin n → ℝ) x₀).continuousLinearMapAt_apply_of_mem ℝ hpx v).symm
  conv_lhs => rw [vec_expand w]
  simp only [map_sum, map_smul, symmL_eq_coordField p hpp]
  rw [hL, map_sum]
  funext m
  simp only [← hL, Finset.sum_apply, Matrix.mulVec, dotProduct, chJac, Matrix.of_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hL, map_smul, ← hL, Pi.smul_apply, smul_eq_mul, mul_comm]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The coordinate metric transforms with the Jacobian: `G^p = Jᵀ G^{x₀} J` at `p`. -/
theorem coordMetric_chJac {x₀ p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    g.coordMetric p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) =
      (chJac x₀ p)ᵀ * g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) * chJac x₀ p := by
  ext σ ν
  have hc := g_coordField g p σ ν (mem_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv (mem_extChartAt_source p)] at hc
  rw [← hc, g_hv' x₀ g hp, conj_apply]
  simp only [Matrix.mulVec, dotProduct, chJac, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

/-- `∇h` transforms with the Jacobian: `∇^p_{abc} = Σ J J J ∇^{x₀}` at `p`. -/
theorem covArr_chJac {x₀ p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    covArr g h p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) =
      conjC (chJac x₀ p) (covArr g h x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p)) := by
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  funext a b c
  rw [covArr, ← covDerivBilinAt_coordField h p (leviCivita g) g hLC (mem_extChartAt_source p) a b c,
    covDerivBilinAt_eq_sum h x₀ (leviCivita g) g hLC hp]
  simp only [conjC, chJac, Matrix.of_apply, covArr]

/-- **The boundary vector field is a vector field**: its components in the chart at any `x₀` are `W` of that chart. -/
theorem hv_palatiniField {x₀ p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    hv x₀ p (palatiniField g h p) = pvec g h x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  have hdet : IsUnit ((chJac x₀ p)ᵀ * g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) * chJac x₀ p).det := by
    rw [← coordMetric_chJac g hp]
    exact g.coordMetric_isUnit_det p (mem_extChartAt_target p)
  rw [palatiniField, hv_symmL_chJac hp, pvec_eq, pvec_eq, coordMetric_chJac g hp, covArr_chJac g h hp]
  exact inv_psiC_conj _ _ _ hdet

end Field

section Smooth

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- `∇ₐ h_{bc}` in a chart is smooth on the chart target. -/
theorem contDiffOn_covArr (x₀ : M) (a b c : Fin n) :
    ContDiffOn ℝ ∞ (fun y => covArr g h x₀ y a b c) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have hgc := g.isCoordMetric_coordMetric x₀
  have hU := isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀
  have hH := h.coordComp_smooth x₀
  simp only [covArr, covH]
  exact ((contDiffOn_pd (hH b c) hU a).sub (ContDiffOn.sum fun m _ =>
    (contDiffOn_christoffel hgc m a b).mul (hH m c))).sub (ContDiffOn.sum fun m _ =>
    (contDiffOn_christoffel hgc m a c).mul (hH b m))

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The components `W` of the boundary vector in a chart are smooth on the chart target. -/
theorem contDiffOn_pvec (x₀ : M) :
    ContDiffOn ℝ ∞ (pvec g h x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have hgc := g.isCoordMetric_coordMetric x₀
  have hGi : ∀ i j, ContDiffOn ℝ ∞ (fun y => (g.coordMetric x₀ y)⁻¹ i j) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    contDiffOn_inv_entry hgc.smooth fun y hy => (hgc.isUnit_det y hy).ne_zero
  have hC := contDiffOn_covArr g h x₀
  have e : pvec g h x₀ = fun y ρ => ∑ l, (g.coordMetric x₀ y)⁻¹ ρ l *
      ∑ σ, ∑ ν, (g.coordMetric x₀ y)⁻¹ σ ν * (covArr g h x₀ y σ l ν - covArr g h x₀ y l σ ν) := by
    funext y ρ
    rw [pvec_eq]
    simp only [Matrix.mulVec, dotProduct, psiC]
  rw [e]
  refine contDiffOn_pi.2 fun ρ => ContDiffOn.sum fun l _ => (hGi ρ l).mul (ContDiffOn.sum fun σ _ =>
    ContDiffOn.sum fun ν _ => (hGi σ ν).mul ((hC σ l ν).sub (hC l σ ν)))

/-- **The boundary vector field of the variation is smooth.** -/
theorem contMDiff_palatiniField :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, palatiniField g h q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) := by
  intro p
  have hpp := mem_baseSet_of_mem_source p (mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p)
  rw [(tTriv (E := Fin n → ℝ) p).contMDiffAt_section_iff hpp]
  have hy := mem_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p
  have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (pvec g h p ∘ extChartAt 𝓘(ℝ, Fin n → ℝ) p) p :=
    ((contDiffOn_pvec g h p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hy)).contMDiffAt.comp p
      (contMDiffAt_extChartAt (n := ∞))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p)] with q hq
  exact hv_palatiniField g h hq

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- **The boundary vector vanishes where `h` vanishes near the point.** -/
theorem palatiniField_eq_zero {p : M} (hp : ∀ᶠ q in 𝓝 p, h.h q = 0) : palatiniField g h p = 0 := by
  set y₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) p p
  have hz : ∀ᶠ z in 𝓝 y₀, ∀ i j, h.coordComp p z i j = 0 := by
    filter_upwards [(continuousAt_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) p).preimage_mem_nhds
      (by rwa [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv (mem_extChartAt_source p)])] with z hz i j
    have hz' : h.h ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm z) = 0 := hz
    unfold SymBilinField.coordComp
    rw [hz']
    rfl
  have hC : covArr g h p y₀ = 0 := by
    funext a b c
    have hpd : pd a (fun z => h.coordComp p z b c) y₀ = 0 := by
      unfold pd
      rw [Filter.EventuallyEq.fderiv_eq (f := fun _ => (0 : ℝ)) (hz.mono fun z hz => hz b c)]
      simp
    simp only [covArr, covH, hpd, hz.self_of_nhds, mul_zero, Finset.sum_const_zero, sub_zero]
    rfl
  have hW : pvec g h p y₀ = 0 := by
    rw [pvec_eq, hC]
    have : psiC (g.coordMetric p y₀) (0 : Fin n → Fin n → Fin n → ℝ) = 0 := by
      funext l; simp [psiC]
    rw [this, Matrix.mulVec_zero]
  rw [palatiniField, hW, map_zero]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The boundary vector vanishes outside a compact set outside which `h` vanishes. -/
theorem palatiniField_eq_zero_of_notMem [T2Space M] {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ q, q ∉ K → h.h q = 0) {p : M} (hp : p ∉ K) : palatiniField g h p = 0 :=
  palatiniField_eq_zero g h (Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hp) hsupp)

end Smooth

end Lightlike

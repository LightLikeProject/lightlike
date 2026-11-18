import Mathlib
import Lightlike.Canonical.HamiltonianBracket
import Lightlike.Canonical.PairingCovariance
import Lightlike.Canonical.HamiltonianFirstOrder
import Lightlike.Canonical.IntegrationByParts

/-!
# The Lie-derivative form of the momentum constraint is the ADM form

`∫ π^{ij} (ℒ_ξ h)_ij = ∫ −2 (h ξ)_i ∇_k π^{ik}` for a compactly supported `ξ` (ADM 1962, eq. (3.14b)), by the pointwise
identity `π^{ij} (ℒ_ξ h)_ij + 2 (h ξ)_i ∇_k π^{ik} = 2 ∂_j (π^{ij} h_{ik} ξ^k)` and `∫ ∂_j F = 0`.
-/

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- `h_{ki} Γ^i_{jl} = ½ (∂_j h_{kl} + ∂_l h_{kj} − ∂_k h_{jl})`, at a point where the metric is invertible. -/
lemma lower_christoffel (g : TensorField d) {x : Fin d → ℝ} (hdet : IsUnit (g x).det) (k j l : Fin d) :
    ∑ i, g x k i * Lightlike.christoffel g i j l x =
      1 / 2 * (Lightlike.pd j (fun y => g y k l) x + Lightlike.pd l (fun y => g y k j) x -
        Lightlike.pd k (fun y => g y j l) x) := by
  unfold Lightlike.christoffel
  have hmul : ∀ m, ∑ i, g x k i * (g x)⁻¹ i m = if k = m then 1 else 0 := by
    intro m
    have := congrFun (congrFun (Matrix.mul_nonsing_inv (g x) hdet) k) m
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have : ∀ i, g x k i * (1 / 2 * ∑ m, (g x)⁻¹ i m * (Lightlike.pd j (fun y => g y m l) x +
      Lightlike.pd l (fun y => g y m j) x - Lightlike.pd m (fun y => g y j l) x)) =
      ∑ m, 1 / 2 * (g x k i * (g x)⁻¹ i m) * (Lightlike.pd j (fun y => g y m l) x +
        Lightlike.pd l (fun y => g y m j) x - Lightlike.pd m (fun y => g y j l) x) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by ring
  simp only [this]
  rw [Finset.sum_comm]
  have e : ∀ m, ∑ i, 1 / 2 * (g x k i * (g x)⁻¹ i m) * (Lightlike.pd j (fun y => g y m l) x +
      Lightlike.pd l (fun y => g y m j) x - Lightlike.pd m (fun y => g y j l) x) =
      (if k = m then 1 / 2 else 0) * (Lightlike.pd j (fun y => g y m l) x +
        Lightlike.pd l (fun y => g y m j) x - Lightlike.pd m (fun y => g y j l) x) := by
    intro m
    rw [← Finset.sum_mul, ← Finset.mul_sum, hmul m]
    split_ifs <;> simp
  simp only [e]
  simp [Finset.sum_ite_eq]

/-- The pure index algebra behind the integration by parts: with `ξ_i = Σ_k g_ik ξ^k`,
`π^{ij} (ℒ_ξ g)_ij + 2 ξ_i ∇_k π^{ik} = 2 ∂_j (π^{ij} ξ_i)`. -/
lemma adm_algebra (π g : Fin d → Fin d → ℝ) (dh : Fin d → Fin d → Fin d → ℝ) (dξ : Fin d → Fin d → ℝ)
    (dπ : Fin d → Fin d → Fin d → ℝ) (ξ : Fin d → ℝ) (Γ : Fin d → Fin d → Fin d → ℝ)
    (hπ : ∀ i j, π i j = π j i) (hg : ∀ i j, g i j = g j i) (hdh : ∀ k i j, dh k i j = dh k j i)
    (hΓ : ∀ m k l, ∑ i, g m i * Γ i k l = 1 / 2 * (dh k m l + dh l m k - dh m k l)) :
    ∑ i, ∑ j, π i j * (∑ k, ξ k * dh k i j + ∑ k, g k j * dξ i k + ∑ k, g i k * dξ j k) +
      2 * ∑ i, (∑ k, g i k * ξ k) * (∑ k, dπ k i k + ∑ k, ∑ l, Γ i k l * π k l) =
    2 * ∑ j, ∑ i, (dπ j i j * (∑ k, g i k * ξ k) + π i j * (∑ k, dh j i k * ξ k + ∑ k, g i k * dξ j k)) := by
  -- the three pieces
  have hA : ∑ i, ∑ j, π i j * ∑ k, g k j * dξ i k = ∑ i, ∑ j, π i j * ∑ k, g i k * dξ j k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hπ i j]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hg k i]
  -- the Christoffel piece
  have hC : ∑ i, (∑ k, g i k * ξ k) * (∑ k, ∑ l, Γ i k l * π k l) =
      ∑ m, ξ m * ∑ k, ∑ l, π k l * (1 / 2 * (dh k m l + dh l m k - dh m k l)) := by
    have e1 : ∀ i, (∑ k, g i k * ξ k) * (∑ k, ∑ l, Γ i k l * π k l) =
        ∑ m, ∑ k, ∑ l, ξ m * π k l * (g m i * Γ i k l) := by
      intro i
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hg i m]; ring
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hΓ m k l, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hT1 : ∑ i, ∑ j, π i j * ∑ k, ξ k * dh k i j = ∑ m, ξ m * ∑ k, ∑ l, π k l * dh m k l := by
    have : ∀ i j, π i j * ∑ k, ξ k * dh k i j = ∑ k, ξ k * (π i j * dh k i j) := fun i j => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    have : ∀ i : Fin d, ∑ j, ∑ k, ξ k * (π i j * dh k i j) = ∑ k, ξ k * ∑ j, π i j * dh k i j := fun i => by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    simp only [this]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [← Finset.mul_sum]
  have hP : ∀ m, ∑ k, ∑ l, π k l * (1 / 2 * (dh k m l + dh l m k - dh m k l)) =
      ∑ k, ∑ l, π k l * dh k m l - 1 / 2 * ∑ k, ∑ l, π k l * dh m k l := by
    intro m
    have h1 : ∑ k, ∑ l, π k l * dh l m k = ∑ k, ∑ l, π k l * dh k m l := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [hπ l k]
    have : ∀ k l, π k l * (1 / 2 * (dh k m l + dh l m k - dh m k l)) =
        1 / 2 * (π k l * dh k m l) + 1 / 2 * (π k l * dh l m k) - 1 / 2 * (π k l * dh m k l) := fun k l => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h1]; ring
  have hR : ∑ j, ∑ i, π i j * ∑ k, dh j i k * ξ k = ∑ m, ξ m * ∑ k, ∑ l, π k l * dh k m l := by
    have : ∀ j i, π i j * ∑ k, dh j i k * ξ k = ∑ k, ξ k * (π i j * dh j k i) := fun j i => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [hdh j i k]; ring
    simp only [this]
    have e2 : ∀ j, ∑ i, ∑ k, ξ k * (π i j * dh j k i) = ∑ k, ξ k * ∑ i, π i j * dh j k i := fun j => by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hπ i j]
  have hD : ∑ i, (∑ k, g i k * ξ k) * ∑ k, dπ k i k = ∑ j, ∑ i, dπ j i j * (∑ k, g i k * ξ k) := by
    have : ∀ i, (∑ k, g i k * ξ k) * ∑ k, dπ k i k = ∑ j, dπ j i j * (∑ k, g i k * ξ k) := fun i => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    exact Finset.sum_comm
  have hE : ∑ j, ∑ i, π i j * ∑ k, g i k * dξ j k = ∑ i, ∑ j, π i j * ∑ k, g i k * dξ j k :=
    Finset.sum_comm
  have hLHS : ∑ i, ∑ j, π i j * (∑ k, ξ k * dh k i j + ∑ k, g k j * dξ i k + ∑ k, g i k * dξ j k) =
      ∑ i, ∑ j, π i j * ∑ k, ξ k * dh k i j + ∑ i, ∑ j, π i j * ∑ k, g k j * dξ i k +
        ∑ i, ∑ j, π i j * ∑ k, g i k * dξ j k := by
    simp only [mul_add, Finset.sum_add_distrib]
  have hRHS : ∑ j, ∑ i, (dπ j i j * (∑ k, g i k * ξ k) + π i j * (∑ k, dh j i k * ξ k + ∑ k, g i k * dξ j k)) =
      ∑ j, ∑ i, dπ j i j * (∑ k, g i k * ξ k) + ∑ j, ∑ i, π i j * ∑ k, dh j i k * ξ k +
        ∑ j, ∑ i, π i j * ∑ k, g i k * dξ j k := by
    simp only [mul_add, Finset.sum_add_distrib]; ring
  have hsplit : ∑ i, (∑ k, g i k * ξ k) * (∑ k, dπ k i k + ∑ k, ∑ l, Γ i k l * π k l) =
      ∑ i, (∑ k, g i k * ξ k) * ∑ k, dπ k i k + ∑ i, (∑ k, g i k * ξ k) * (∑ k, ∑ l, Γ i k l * π k l) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have hCm : ∑ m, ξ m * ∑ k, ∑ l, π k l * (1 / 2 * (dh k m l + dh l m k - dh m k l)) =
      ∑ m, ξ m * ∑ k, ∑ l, π k l * dh k m l - 1 / 2 * ∑ m, ξ m * ∑ k, ∑ l, π k l * dh m k l := by
    rw [Finset.sum_congr rfl fun m _ => by rw [hP m], Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hLHS, hRHS, hsplit, hA, hC, hCm, hT1, hR, hD, hE]
  ring


/-- The partial derivative of `y ↦ Σ_k g_ik ξ^k`, by the Leibniz rule. -/
lemma pd_lower {g : TensorField d} {ξ : VectorField d} (hg : SmoothTensor g) (hξ : SmoothVec ξ) (j i : Fin d)
    (x : Fin d → ℝ) :
    Lightlike.pd j (fun y => ∑ k, g y i k * ξ y k) x =
      ∑ k, (Lightlike.pd j (fun y => g y i k) x * ξ x k + g x i k * Lightlike.pd j (fun y => ξ y k) x) := by
  rw [Lightlike.pd_sum Finset.univ (f := fun k y => g y i k * ξ y k)
    (fun k _ => ((hg i k).differentiable (by simp) x).mul ((hξ k).differentiable (by simp) x))]
  exact Finset.sum_congr rfl fun k _ =>
    Lightlike.pd_mul ((hg i k).differentiable (by simp) x) ((hξ k).differentiable (by simp) x) j

/-- The flux `F_j = Σ_i π^{ij} ξ_i` with `ξ_i = Σ_k h_ik ξ^k`. -/
def momentumFlux (ξ : VectorField d) (h π : TensorField d) (j : Fin d) (y : Fin d → ℝ) : ℝ :=
  ∑ i, π y i j * ∑ k, h y i k * ξ y k

/-- The flux `F_j` is smooth. -/
lemma smooth_momentumFlux {ξ : VectorField d} {h π : TensorField d} (hξ : SmoothVec ξ) (hh : SmoothTensor h)
    (hπ : SmoothTensor π) (j : Fin d) : ContDiff ℝ ∞ (momentumFlux ξ h π j) := by
  unfold momentumFlux
  exact ContDiff.sum fun i _ => (hπ i j).mul (ContDiff.sum fun k _ => (hh i k).mul (hξ k))

/-- The flux `F_j` has compact support when the shift has. -/
lemma compact_momentumFlux {ξ : VectorField d} (h π : TensorField d)
    (hξc : ∀ k, HasCompactSupport (fun y => ξ y k)) (j : Fin d) : HasCompactSupport (momentumFlux ξ h π j) := by
  unfold momentumFlux
  refine hcs_sum _ _ fun i _ => ?_
  refine HasCompactSupport.mul_left ?_
  exact hcs_sum _ _ fun k _ => (hξc k).mul_left

/-- **The pointwise identity.** -/
theorem momentum_pointwise {ξ : VectorField d} {h π : TensorField d} (hξ : SmoothVec ξ) (hh : SmoothTensor h)
    (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π) (hπs : ∀ x, (π x)ᵀ = π x) (x : Fin d → ℝ) :
    momentumDensity ξ h π x + 2 * ∑ i, (∑ k, h x i k * ξ x k) * momentumDivergence h π i x =
      2 * ∑ j, Lightlike.pd j (momentumFlux ξ h π j) x := by
  have hsymh : ∀ y i j, h y i j = h y j i := fun y i j => by
    have := (hpos y).1.apply i j
    simpa using this.symm
  have hdet : IsUnit (h x).det := (hpos x).det_pos.ne'.isUnit
  have hflux : ∀ j, Lightlike.pd j (momentumFlux ξ h π j) x = ∑ i,
      (Lightlike.pd j (fun y => π y i j) x * ∑ k, h x i k * ξ x k + π x i j *
        (∑ k, Lightlike.pd j (fun y => h y i k) x * ξ x k + ∑ k, h x i k * Lightlike.pd j (fun y => ξ y k) x)) := by
    intro j
    unfold momentumFlux
    rw [Lightlike.pd_sum Finset.univ (f := fun i y => π y i j * ∑ k, h y i k * ξ y k)
      (fun i _ => ((hπ i j).differentiable (by simp) x).mul
        ((ContDiff.sum fun k _ => (hh i k).mul (hξ k)).differentiable (by simp) x))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Lightlike.pd_mul ((hπ i j).differentiable (by simp) x)
      ((ContDiff.sum fun k _ => (hh i k).mul (hξ k)).differentiable (by simp) x) j, pd_lower hh hξ j i x,
      Finset.sum_add_distrib]
  have := adm_algebra (π x) (h x) (fun k i j => Lightlike.pd k (fun y => h y i j) x)
    (fun j k => Lightlike.pd j (fun y => ξ y k) x) (fun k i j => Lightlike.pd k (fun y => π y i j) x) (ξ x)
    (fun i k l => Lightlike.christoffel h i k l x)
    (fun i j => by have := congrFun (congrFun (hπs x) i) j; simpa using this.symm)
    (fun i j => hsymh x i j)
    (fun k i j => by rw [show (fun y => h y i j) = fun y => h y j i from funext fun y => hsymh y i j])
    (fun m k l => lower_christoffel h hdet m k l)
  simp only [hflux]
  unfold momentumDensity momentumDivergence lieDeriv
  exact this

/-- **The Lie-derivative form of the momentum constraint is the ADM form.** -/
theorem momentumConstraint_eq_adm_of_smooth {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hξc : ∀ k, HasCompactSupport (fun y => ξ y k)) {h π : TensorField d} (hh : SmoothTensor h)
    (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π) (hπs : ∀ x, (π x)ᵀ = π x) :
    momentumConstraint ξ h π =
      ∫ x, -2 * ∑ i, (∑ k, h x i k * ξ x k) * momentumDivergence h π i x := by
  have hdet : ∀ y, (h y).det ≠ 0 := fun y => (hpos y).det_pos.ne'
  set A : (Fin d → ℝ) → ℝ := fun x => -2 * ∑ i, (∑ k, h x i k * ξ x k) * momentumDivergence h π i x with hA
  have hAc : Continuous A := by
    refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
    refine (continuous_finset_sum _ fun k _ => (hh i k).continuous.mul (hξ k).continuous).mul ?_
    unfold momentumDivergence
    refine (continuous_finset_sum _ fun k _ => (smooth_pd (hπ i k) k).continuous).add ?_
    exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ =>
      (contDiff_christoffel hh hdet i k l).continuous.mul (hπ k l).continuous
  have hAs : HasCompactSupport A := by
    refine HasCompactSupport.mul_left ?_
    refine hcs_sum _ _ fun i _ => ?_
    refine HasCompactSupport.mul_right ?_
    exact hcs_sum _ _ fun k _ => (hξc k).mul_left
  have hAi : Integrable A := hAc.integrable_of_hasCompactSupport hAs
  have hpt : ∀ x, momentumDensity ξ h π x = A x + 2 * ∑ j, Lightlike.pd j (momentumFlux ξ h π j) x := by
    intro x
    have := momentum_pointwise hξ hh hpos hπ hπs x
    simp only [hA]
    linarith
  unfold momentumConstraint
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hFi : ∀ j, Integrable (fun x => Lightlike.pd j (momentumFlux ξ h π j) x) := fun j =>
    integrable_pd (smooth_momentumFlux hξ hh hπ j) (compact_momentumFlux h π hξc j) j
  have hz : ∀ j ∈ Finset.univ, ∫ x, Lightlike.pd j (momentumFlux ξ h π j) x = 0 := fun j _ =>
    integral_pd_eq_zero ((smooth_momentumFlux hξ hh hπ j).of_le (by simp)) (compact_momentumFlux h π hξc j) j
  have e2 : ∫ x, 2 * ∑ j, Lightlike.pd j (momentumFlux ξ h π j) x = 0 := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ fun j _ => hFi j, Finset.sum_eq_zero hz, mul_zero]
  rw [MeasureTheory.integral_add hAi ((integrable_finsetSum _ fun j _ => hFi j).const_mul 2), e2, add_zero]

end Lightlike.Canonical

end

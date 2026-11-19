import Lightlike.Spacetime.DivergenceFree
import Lightlike.Spacetime.EinsteinEquations
import Lightlike.Spacetime.ChartTensor

/-!
# Conservation of the source of the Einstein equations (G1-010)

`divBilinAt_eq_zero_of_einsteinEq`: if `G + Λ g = κ T` with `κ ≠ 0` for the Levi-Civita connection of `g`, the source is
conserved, `∇^μ T_{μν} = 0` (`divBilinAt`). The Einstein tensor is divergence free (`einstein_divergence_free_proved`),
the metric is parallel (`covDerivBilinAt_metric`, metric compatibility), and the covariant derivative of a field of
bilinear forms is linear in the field for differentiable pairings (`covDerivBilinAt_linear`).

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.38), (4.42), (4.43),
  pp. 110–111: energy-momentum conservation `∇^μ T_{μν} = 0`, the Einstein tensor "always obeys `∇^μ G_{μν} = 0`", and
  `G_{μν} = κ T_{μν}` with a conserved right-hand side.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

section Conservation

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [LocallySmoothConnection cov]

omit [LocallySmoothConnection cov] in
/-- **The metric is parallel** for a compatible connection: `∇g = 0`. -/
theorem covDerivBilinAt_metric (h : cov.IsMetricCompatible g) (x : M)
    (X₀ v₀ w₀ : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (fun y a b => g.g y a b) x X₀ v₀ w₀ = 0 := by
  have hX := mdiffAt_of_smoothNear (eventually_extend (E := Fin n → ℝ) x X₀)
  have hv := mdiffAt_of_smoothNear (eventually_extend (E := Fin n → ℝ) x v₀)
  have hw := mdiffAt_of_smoothNear (eventually_extend (E := Fin n → ℝ) x w₀)
  have hc := h (FiberBundle.extend (Fin n → ℝ) X₀) (FiberBundle.extend (Fin n → ℝ) v₀)
    (FiberBundle.extend (Fin n → ℝ) w₀) x hX hv hw
  simp only [FiberBundle.extend_apply_self] at hc
  unfold Connection.covDerivBilinAt
  have key : ∀ a b c : ℝ, a = b + c → a - b - c = 0 := fun a b c h => by rw [h]; ring
  exact key _ _ _ hc

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [LocallySmoothConnection cov] in
/-- **The covariant derivative of a field of bilinear forms is linear in the field**, for pairings differentiable
along the extensions. -/
theorem covDerivBilinAt_linear {T₁ T₂ : Π x : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) x → TangentSpace 𝓘(ℝ, Fin n → ℝ) x → ℝ}
    (c₁ c₂ : ℝ) (x : M) (X₀ v₀ w₀ : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
    (h₁ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) (fun y => T₁ y (FiberBundle.extend (Fin n → ℝ) v₀ y)
      (FiberBundle.extend (Fin n → ℝ) w₀ y)) x)
    (h₂ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) (fun y => T₂ y (FiberBundle.extend (Fin n → ℝ) v₀ y)
      (FiberBundle.extend (Fin n → ℝ) w₀ y)) x) :
    cov.covDerivBilinAt (fun y a b => c₁ * T₁ y a b + c₂ * T₂ y a b) x X₀ v₀ w₀ =
      c₁ * cov.covDerivBilinAt T₁ x X₀ v₀ w₀ + c₂ * cov.covDerivBilinAt T₂ x X₀ v₀ w₀ := by
  unfold Connection.covDerivBilinAt
  beta_reduce
  have e : (fun y => c₁ * T₁ y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y) +
      c₂ * T₂ y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) =
      (c₁ • fun y => T₁ y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) +
        (c₂ • fun y => T₂ y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) := by
    funext y; simp [smul_eq_mul]
  rw [e, mfderiv_add (h₁.const_smul c₁) (h₂.const_smul c₂), const_smul_mfderiv h₁, const_smul_mfderiv h₂]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  generalize ((mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) fun y => T₁ y (FiberBundle.extend (Fin n → ℝ) v₀ y)
    (FiberBundle.extend (Fin n → ℝ) w₀ y)) x) X₀ = A₁
  generalize ((mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) fun y => T₂ y (FiberBundle.extend (Fin n → ℝ) v₀ y)
    (FiberBundle.extend (Fin n → ℝ) w₀ y)) x) X₀ = A₂
  ring

/-- The pairing `y ↦ G(V y, W y)` of the Einstein tensor with two fields smooth near `x` is differentiable at `x`. -/
theorem mdiffAt_einstein_pair (hLC : cov.IsLeviCivita g) (x : M) {V W : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hV : SmoothNear V x) (hW : SmoothNear W x) :
    MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) (fun y => cov.einsteinField g y (V y) (W y)) x := by
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hxb : x ∈ (tTriv (E := Fin n → ℝ) x).baseSet := by
    rw [extChartAt_source] at hxs; simp [tTriv, TangentBundle.trivializationAt_baseSet]
  have hV' := (mdiffAt_hat_iff x V hxb).1 (mdiffAt_of_smoothNear hV)
  have hW' := (mdiffAt_hat_iff x W hxb).1 (mdiffAt_of_smoothNear hW)
  have hB : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) (fun y => BE g x y (hat x V y) (hat x W y)) x :=
    ((mdiffAt_BE g hxs).clm_apply hV').clm_apply hW'
  refine hB.congr_of_eventuallyEq ?_
  filter_upwards [(tTriv (E := Fin n → ℝ) x).open_baseSet.mem_nhds hxb] with y hy
  exact einsteinField_eq_bilOf g cov x hLC hy (V y) (W y)

set_option backward.isDefEq.respectTransparency false in
/-- **The source of the Einstein equations is conserved**: if `G + Λ g = κ T` with `κ ≠ 0` (for the Levi-Civita
connection), then `∇^μ T_{μν} = 0`. -/
theorem divBilinAt_eq_zero_of_einsteinEq {Λ κ : ℝ}
    {T : Π x : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) x → TangentSpace 𝓘(ℝ, Fin n → ℝ) x → ℝ}
    (hE : g.EinsteinEq cov Λ κ T) (hκ : κ ≠ 0) (x : M) (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.divBilinAt g T x w = 0 := by
  have hLC := hE.1
  have hT : T = fun y a b => (1 / κ) * cov.einsteinField g y a b + (Λ / κ) * g.g y a b := by
    funext y a b
    have := hE.2 y a b
    field_simp
    linarith
  have hdiv := einstein_divergence_free_proved g cov x hLC w
  rw [hT]
  unfold Connection.divBilinAt at hdiv ⊢
  have hlin : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, ∀ v' : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      cov.covDerivBilinAt (fun y a b => (1 / κ) * cov.einsteinField g y a b + (Λ / κ) * g.g y a b) x v v' w =
        (1 / κ) * cov.covDerivBilinAt (cov.einsteinField g) x v v' w := fun v v' => by
    rw [covDerivBilinAt_linear cov _ _ x v v' w
      (mdiffAt_einstein_pair g cov hLC x (eventually_extend x v') (eventually_extend x w))
      (mdiffAt_gpair g (mdiffAt_of_smoothNear (eventually_extend x v')) (mdiffAt_of_smoothNear (eventually_extend x w))),
      covDerivBilinAt_metric g cov hLC.2 x v v' w, mul_zero, add_zero]
  simp only at hdiv ⊢
  calc _ = ∑ i, ∑ j, (Matrix.of fun i j => g.g x (Module.finBasis ℝ (Fin n → ℝ) i : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
          (Module.finBasis ℝ (Fin n → ℝ) j : TangentSpace 𝓘(ℝ, Fin n → ℝ) x))⁻¹ i j *
        ((1 / κ) * cov.covDerivBilinAt (cov.einsteinField g) x
          (Module.finBasis ℝ (Fin n → ℝ) i : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
          (Module.finBasis ℝ (Fin n → ℝ) j : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) w) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ (hlin _ _)
    _ = (1 / κ) * ∑ i, ∑ j, (Matrix.of fun i j => g.g x (Module.finBasis ℝ (Fin n → ℝ) i : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
          (Module.finBasis ℝ (Fin n → ℝ) j : TangentSpace 𝓘(ℝ, Fin n → ℝ) x))⁻¹ i j *
        cov.covDerivBilinAt (cov.einsteinField g) x
          (Module.finBasis ℝ (Fin n → ℝ) i : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
          (Module.finBasis ℝ (Fin n → ℝ) j : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) w := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by rw [hdiv, mul_zero]

end Conservation

end Lightlike

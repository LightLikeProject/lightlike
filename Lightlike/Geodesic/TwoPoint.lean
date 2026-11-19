import Lightlike.Geodesic.ExpJoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The map `(p, v) ↦ (p, exp_p v)` is a diffeomorphism near a zero vector

For a coordinate metric `g` on `U` and `x ∈ U`, the map `(p, v) ↦ (p, exp_p v)` restricts to a
diffeomorphism from a neighbourhood of `(x, 0)` onto a neighbourhood of `(x, x)`
(`Lightlike.Geodesic.exists_twoPoint_diffeo`): near `x`, two points are joined by a geodesic
whose initial velocity depends smoothly on them.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Theorem 2.2.6, pages 47–49, first
  step of the proof (every point of the zero section has a neighbourhood on which `E` is a
  diffeomorphism). The second step, a diffeomorphism from a neighbourhood of the whole zero
  section onto a neighbourhood of the diagonal, is not stated here.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The linear equivalence `(ξ, η) ↦ (ξ, ξ + η)` of `ℝⁿ × ℝⁿ`, the derivative of
`(p, v) ↦ (p, exp_p v)` at a zero vector. -/
def shearEquiv (n : ℕ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) +
        ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)))
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ) -
        ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)))
    (fun q => by ext <;> simp)
    (fun q => by ext <;> simp)

/-- **The map `(p, v) ↦ (p, exp_p v)` is a diffeomorphism near `(x, 0)`** (Kunzinger–Steinbauer,
Theorem 2.2.6, first step of the proof).

For `x ∈ U` there are `ρ > 0`, a map `E` of `(p, v)` (the exponential map, as in
`exists_expMap_joint`) and an open partial homeomorphism `Θ` of `ℝⁿ × ℝⁿ`, smooth with smooth
inverse, with `(x, 0)` in its source, source contained in `B(x, ρ) × B(0, ρ)`, and
`Θ (p, v) = (p, E (p, v))` on the source. -/
theorem exists_twoPoint_diffeo (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (ρ : ℝ) (E : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
      (Θ : OpenPartialHomeomorph ((Fin n → ℝ) × (Fin n → ℝ)) ((Fin n → ℝ) × (Fin n → ℝ))),
      0 < ρ ∧ (∀ p ∈ ball x ρ, E (p, 0) = p) ∧
      ContDiffOn ℝ ∞ E (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) ∧
      (∀ p ∈ ball x ρ, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, E (p, v) ∈ U) ∧
      (∀ p ∈ ball x ρ, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ,
        γ 0 = p ∧ w 0 = v ∧ IsGeodesicOn g γ w (Ioo (-1) 2) ∧
        ∀ t ∈ Icc (-1 : ℝ) 1, γ t = E (p, t • v)) ∧
      ((x, (0 : Fin n → ℝ)) ∈ Θ.source) ∧
      Θ.source ⊆ ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ ∧
      (∀ q ∈ Θ.source, Θ q = (q.1, E q)) ∧
      ContDiffOn ℝ ∞ Θ Θ.source ∧ ContDiffOn ℝ ∞ Θ.symm Θ.target := by
  obtain ⟨ρ, E, hρ, hE0, hEs, hEd, hEU, hEg⟩ := exists_expMap_joint hg hx
  set f : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) := fun q => (q.1, E q) with hf
  have hopen : IsOpen (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) := isOpen_ball.prod isOpen_ball
  have hx0 : (x, (0 : Fin n → ℝ)) ∈ ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ :=
    ⟨mem_ball_self hρ, mem_ball_self hρ⟩
  have hfs : ContDiffOn ℝ ∞ f (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) :=
    contDiff_fst.contDiffOn.prodMk hEs
  have hfat : ContDiffAt ℝ ∞ f (x, 0) := hfs.contDiffAt (hopen.mem_nhds hx0)
  have hfd : HasFDerivAt f ((shearEquiv n : _ ≃L[ℝ] _) :
      (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ)) (x, 0) :=
    hasFDerivAt_fst.prodMk hEd
  have hstrict := hfat.hasStrictFDerivAt' hfd (by simp)
  set Θ₀ := hstrict.toOpenPartialHomeomorph f with hΘ₀
  have h0src : (x, (0 : Fin n → ℝ)) ∈ Θ₀.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hfc : ContinuousAt (fderiv ℝ f) (x, 0) :=
    (hfat.fderiv_right (m := 0) (by simp)).continuousAt
  have hunit : ∀ᶠ q in 𝓝 (x, (0 : Fin n → ℝ)), IsUnit (fderiv ℝ f q) := by
    have hmem : {L : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ) | IsUnit L} ∈
        𝓝 (fderiv ℝ f (x, 0)) := by
      refine Units.isOpen.mem_nhds ?_
      rw [hfd.fderiv]
      exact ⟨ContinuousLinearEquiv.toUnit (shearEquiv n), rfl⟩
    exact hfc.preimage_mem_nhds hmem
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    interior (Θ₀.source ∩ (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) ∩ {q | IsUnit (fderiv ℝ f q)})
    with hS
  have hSopen : IsOpen S := isOpen_interior
  have hx0S : (x, (0 : Fin n → ℝ)) ∈ S :=
    mem_interior_iff_mem_nhds.2
      (inter_mem (inter_mem (Θ₀.open_source.mem_nhds h0src) (hopen.mem_nhds hx0)) hunit)
  have hSsub : S ⊆ Θ₀.source ∩ (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) ∩
      {q | IsUnit (fderiv ℝ f q)} := interior_subset
  have hsrc : (Θ₀.restrOpen S hSopen).source = S := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact inter_eq_right.2 fun q hq => (hSsub hq).1.1
  refine ⟨ρ, E, Θ₀.restrOpen S hSopen, hρ, hE0, hEs, hEU, hEg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]; exact hx0S
  · rw [hsrc]; exact fun q hq => (hSsub hq).1.2
  · intro q _; rfl
  · rw [hsrc]
    exact hfs.mono fun q hq => (hSsub hq).1.2
  · intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    set q := (Θ₀.restrOpen S hSopen).symm y with hq
    have hqS : q ∈ S := by
      have h1 := (Θ₀.restrOpen S hSopen).map_target hy
      rwa [hsrc] at h1
    obtain ⟨u, hu⟩ := (hSsub hqS).2
    have hfq : ContDiffAt ℝ ∞ f q := hfs.contDiffAt (hopen.mem_nhds (hSsub hqS).1.2)
    have he : ((ContinuousLinearEquiv.ofUnit u :
        ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) :
        (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ)) = fderiv ℝ f q := by
      rw [← hu]; rfl
    have hfd' : HasFDerivAt f
        ((ContinuousLinearEquiv.ofUnit u :
          ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) :
          (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × (Fin n → ℝ)) q := by
      rw [he]; exact (hfq.differentiableAt (by simp)).hasFDerivAt
    exact (Θ₀.restrOpen S hSopen).contDiffAt_symm hy hfd' hfq

end Lightlike.Geodesic

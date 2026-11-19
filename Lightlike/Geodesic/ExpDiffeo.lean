import Lightlike.Geodesic.ExpSmooth
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The exponential map is a diffeomorphism near the origin: normal neighbourhoods

For a coordinate metric `g` on an open set `U ⊆ ℝⁿ` of any signature and `x ∈ U`, the
exponential map at `x` restricts to a diffeomorphism from a ball about `0` onto an open
neighbourhood of `x` (`Lightlike.Geodesic.exists_expMap_diffeo`). The ball is star shaped, so its
image is a normal neighbourhood of `x` in the sense of the source.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Theorem 2.1.14 (pages 38–39) and the
  definition of a normal neighbourhood after it (page 39). Differences: a coordinate metric on an
  open subset of `ℝⁿ` instead of a semi-Riemannian manifold; the exponential map is given by its
  defining property (`E v` is the endpoint at time `1` of a geodesic from `x` with initial
  velocity `v`) on a ball, not as a map on the maximal domain `D_p`.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The exponential map is a diffeomorphism near the origin** (Kunzinger–Steinbauer,
Theorem 2.1.14, for a coordinate metric of any signature).

For `x ∈ U` there are `ρ > 0` and an open partial homeomorphism `φ` of `ℝⁿ` with source the ball
of radius `ρ` about `0`, smooth with smooth inverse, with `φ 0 = x` and derivative the identity at
`0`, such that every `v` in the ball is the initial velocity of a geodesic from `x`, defined on
`(-1, 2)`, which reaches `φ v` at time `1` and is `t ↦ φ (t • v)` on `[0, 1]` (the radial
geodesic to `φ v`). So `φ` is `exp_x` on the ball, and its target is a normal neighbourhood of
`x`.

The theorem is local: in a chart the geodesics of the manifold are the coordinate geodesics, and
the statement only concerns a neighbourhood of `0` in the tangent space, so the maximal domain
`D_p` of the exponential map plays no part. -/
theorem exists_expMap_diffeo (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)), 0 < ρ ∧
      φ.source = ball 0 ρ ∧ φ 0 = x ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 ∧ φ.target ⊆ U ∧
      ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ, γ 0 = x ∧ w 0 = v ∧ γ 1 = φ v ∧
        IsGeodesicOn g γ w (Ioo (-1) 2) ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t = φ (t • v) := by
  obtain ⟨ρ₀, E, hρ₀, hE0, hEs, hEd, hEU, hEg⟩ := exists_expMap_smooth hg hx
  have hEat : ContDiffAt ℝ ∞ E 0 := hEs.contDiffAt (ball_mem_nhds 0 hρ₀)
  have hEd' : HasFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) 0 := hEd
  have hstrict : HasStrictFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) 0 :=
    hEat.hasStrictFDerivAt' hEd' (by simp)
  set φ₀ := hstrict.toOpenPartialHomeomorph E with hφ₀
  have h0src : (0 : Fin n → ℝ) ∈ φ₀.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- the derivative of `E` is invertible near `0`
  have hfc : ContinuousAt (fderiv ℝ E) 0 :=
    (hEat.fderiv_right (m := 0) (by simp)).continuousAt
  have hunit : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), IsUnit (fderiv ℝ E v) := by
    have hmem : {L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) | IsUnit L} ∈ 𝓝 (fderiv ℝ E 0) :=
      Units.isOpen.mem_nhds (by rw [hEd.fderiv]; exact isUnit_one)
    exact hfc.preimage_mem_nhds hmem
  have hnhds : φ₀.source ∩ ball 0 ρ₀ ∩ {v | IsUnit (fderiv ℝ E v)} ∈ 𝓝 (0 : Fin n → ℝ) :=
    inter_mem (inter_mem (φ₀.open_source.mem_nhds h0src) (ball_mem_nhds 0 hρ₀)) hunit
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 hnhds
  have hsub1 : ball (0 : Fin n → ℝ) ρ ⊆ φ₀.source := fun v hv => (hsub hv).1.1
  have hsub2 : ball (0 : Fin n → ℝ) ρ ⊆ ball 0 ρ₀ := fun v hv => (hsub hv).1.2
  have hsrc : (φ₀.restrOpen (ball 0 ρ) isOpen_ball).source = ball 0 ρ := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact inter_eq_right.2 hsub1
  refine ⟨ρ, φ₀.restrOpen (ball 0 ρ) isOpen_ball, hρ, hsrc, hE0, ?_, ?_, hEd, ?_,
    fun v hv => hEg v (hsub2 hv)⟩
  · rw [hsrc]
    exact hEs.mono hsub2
  · intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    set v := (φ₀.restrOpen (ball 0 ρ) isOpen_ball).symm y with hv
    have hvs : v ∈ ball (0 : Fin n → ℝ) ρ := by
      rw [← hsrc]; exact (φ₀.restrOpen (ball 0 ρ) isOpen_ball).map_target hy
    obtain ⟨u, hu⟩ := (hsub hvs).2
    have hEv : ContDiffAt ℝ ∞ E v := hEs.contDiffAt (isOpen_ball.mem_nhds (hsub2 hvs))
    have he : ((ContinuousLinearEquiv.ofUnit u : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ E v := by
      rw [← hu]; rfl
    have hfd : HasFDerivAt E
        ((ContinuousLinearEquiv.ofUnit u : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
          (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) v := by
      rw [he]; exact (hEv.differentiableAt (by simp)).hasFDerivAt
    exact (φ₀.restrOpen (ball 0 ρ) isOpen_ball).contDiffAt_symm hy hfd hEv
  · intro y hy
    have hv : (φ₀.restrOpen (ball 0 ρ) isOpen_ball).symm y ∈ ball (0 : Fin n → ℝ) ρ := by
      have h1 := (φ₀.restrOpen (ball 0 ρ) isOpen_ball).map_target hy
      rwa [hsrc] at h1
    have := hEU _ (hsub2 hv)
    rwa [show E ((φ₀.restrOpen (ball 0 ρ) isOpen_ball).symm y) = y from
      (φ₀.restrOpen (ball 0 ρ) isOpen_ball).right_inv hy] at this

end Lightlike.Geodesic

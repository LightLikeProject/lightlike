import Lightlike.Spacetime.GERow10.NullCovector

/-!
# The weak energy condition for the Klein–Gordon field at a point (G1-010)

For a timelike `u` the Klein–Gordon tensor `T = dφ ⊗ dφ − (½ |dφ|² + V) g` gives
`T(u, u) = (dφ u)² + (½ |dφ|² + V) · (−g(u, u))`, with `|dφ|² = tr_g (dφ ⊗ dφ)`.

* `scalarT_timelike`: this formula.
* `exists_dual_vector`: the metric dual `p` of `dφ` (`dφ v = g(p, v)`) and `tr_g (dφ ⊗ dφ) = g(p, p)`.
* `scalar_weakEC_of_nonneg_potential`: for a non-negative potential value the weak energy condition holds, whatever `dφ` is
  (when `dφ` is timelike the reverse Cauchy–Schwarz inequality controls the negative gradient term).

**Limits.** Pointwise; the form of `T` is Carroll's (1.112) as in `KleinGordonNEC.lean`; no source for the statement itself.
-/

noncomputable section
namespace Lightlike

section Pointwise
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- The value of the Klein–Gordon tensor on a vector with itself, with the squared norm of the gradient made explicit. -/
theorem scalarT_self_apply (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ) (u : V) :
    scalarT g hg dφ Vp u u =
      (dφ u) ^ 2 + ((1 / 2) * traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate + Vp) * (-g u u) := by
  rw [scalarT_apply]; ring

/-- **The metric dual of a covector**: there is `p` with `dφ v = g(p, v)` for all `v`, and `tr_g (dφ ⊗ dφ) = g(p, p)`. -/
theorem exists_dual_vector (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) :
    ∃ p : V, (∀ v, dφ v = g p v) ∧ traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate = g p p := by
  have hnd := hg.bilinForm_nondegenerate
  set D := g.toBilinForm.toDual hnd with hD
  set p : V := D.symm (dφ : V →ₗ[ℝ] ℝ) with hp
  have hpv : ∀ v, dφ v = g p v := fun v => by
    have h : D p = (dφ : V →ₗ[ℝ] ℝ) := D.apply_symm_apply _
    have := congrArg (fun f => f v) h
    simpa [hD, LinearMap.BilinForm.toDual_def, ContinuousLinearMap.toBilinForm] using this.symm
  refine ⟨p, hpv, ?_⟩
  have hcomp : (D.symm.toLinearMap ∘ₗ (dφ.smulRight dφ).toBilinForm) =
      (dφ : V →ₗ[ℝ] ℝ).smulRight p := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smulRight_apply]
    have : (dφ.smulRight dφ).toBilinForm v = dφ v • (dφ : V →ₗ[ℝ] ℝ) := by
      ext w; simp [ContinuousLinearMap.toBilinForm]
    rw [this, map_smul]
    rfl
  unfold traceG
  rw [← hD, hcomp, LinearMap.trace_smulRight]
  simpa using hpv p

/-- **The weak energy condition for a Klein–Gordon field with non-negative potential value**, for any gradient. -/
theorem scalar_weakEC_of_nonneg_potential (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ)
    {Vp : ℝ} (hV : 0 ≤ Vp) : WeakEC g (scalarT g hg dφ Vp) := fun u hu => by
  obtain ⟨p, hpv, hs⟩ := exists_dual_vector g hg dφ
  rw [scalarT_self_apply, hs, hpv u]
  have hN : 0 < -g u u := by linarith
  have hcs := lorentz_reverse_cs (m := 3) hg hu p
  have hsym : g u p = g p u := hg.symm u p
  rw [hsym] at hcs
  by_cases hpp : 0 ≤ g p p
  · have : 0 ≤ ((1 / 2) * g p p + Vp) * (-g u u) := mul_nonneg (by positivity) hN.le
    nlinarith [sq_nonneg (g p u)]
  · have hpp := not_le.mp hpp
    nlinarith [mul_pos hN (neg_pos.mpr hpp), mul_nonneg hV hN.le]

end Pointwise

end Lightlike

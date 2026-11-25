import Lightlike.Spacetime.ScalarEnergyConditions.ScalarWeakECSharp

/-!
# The sharp weak energy condition for a timelike Klein–Gordon gradient (G1-010)

For `T = dφ ⊗ dφ − (½ |dφ|² + V) g` with `|dφ|² = tr_g (dφ ⊗ dφ) < 0` (timelike gradient):

* `scalarT_dual_self`: with `p` the metric dual of `dφ`, `T(p, p) = (−g(p,p)) (V − ½ |dφ|²)`.
* `scalar_weakEC_iff_of_timelike`: `WeakEC ↔ 0 ≤ V − ½ |dφ|²`, i.e. `V ≥ −½ (−|dφ|²)`. The extremal observer is
  the one at rest with respect to `dφ` (the reverse Cauchy–Schwarz inequality is an equality at `u = p`).

Together with `scalar_weakEC_iff` this settles the sharp criterion except for a null non-zero gradient.

**Limits.** Pointwise; no source for the statement itself.
-/

noncomputable section
namespace Lightlike

section Pointwise
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- Value of the Klein–Gordon tensor on the metric dual `p` of a timelike gradient. -/
theorem scalarT_dual_self (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ)
    (p : V) (hpv : ∀ v, dφ v = g p v)
    (hs : traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate = g p p) :
    scalarT g hg dφ Vp p p =
      (-g p p) * (Vp - (1 / 2) * traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate) := by
  rw [scalarT_self_apply, hpv p, hs]
  ring

/-- **Sharp weak energy condition for a timelike gradient**: `WeakEC ↔ 0 ≤ V − ½ |dφ|²`. -/
theorem scalar_weakEC_iff_of_timelike (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g)
    (dφ : V →L[ℝ] ℝ) (Vp : ℝ)
    (h : traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate < 0) :
    WeakEC g (scalarT g hg dφ Vp) ↔
      0 ≤ Vp - (1 / 2) * traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate := by
  obtain ⟨p, hpv, hs⟩ := exists_dual_vector g hg dφ
  have hp : g p p < 0 := hs ▸ h
  constructor
  · intro hW
    have h1 := hW p hp
    rw [scalarT_dual_self g hg dφ Vp p hpv hs] at h1
    have hN : 0 < -g p p := by linarith
    exact nonneg_of_mul_nonneg_right h1 hN
  · intro hpos u hu
    rw [scalarT_self_apply, hs, hpv u]
    rw [hs] at hpos
    have hN : 0 < -g u u := by linarith
    have hcs := lorentz_reverse_cs (m := 3) hg hu p
    have hsym : g u p = g p u := hg.symm u p
    rw [hsym] at hcs
    nlinarith [mul_nonneg hpos hN.le]

end Pointwise

end Lightlike

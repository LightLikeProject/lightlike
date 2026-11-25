import Lightlike.Spacetime.ScalarEnergyConditions.ScalarWeakECTimelike

/-!
# The sharp weak energy condition for a null Klein–Gordon gradient (G1-010)

For `T = dφ ⊗ dφ − (½ |dφ|² + V) g` with `|dφ|² = tr_g (dφ ⊗ dφ) = 0` (null or zero gradient):

* `scalar_weakEC_iff_of_null`: `WeakEC ↔ 0 ≤ V`. Necessity: with `p` the metric dual of `dφ` and `u₀` timelike,
  either `g(p, u₀) = 0` and `u₀` itself violates the condition, or `u = u₀ + t p` has `dφ u = g(p, u₀)`
  constant while `g(u, u) → −∞`.

**Limits.** Pointwise; no source for the statement itself.
-/

noncomputable section
namespace Lightlike

section Pointwise
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- **Sharp weak energy condition for a null (or zero) gradient**: `WeakEC ↔ 0 ≤ V`. -/
theorem scalar_weakEC_iff_of_null (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g)
    (dφ : V →L[ℝ] ℝ) (Vp : ℝ)
    (h : traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate = 0) :
    WeakEC g (scalarT g hg dφ Vp) ↔ 0 ≤ Vp := by
  constructor
  · intro hW
    by_contra hneg
    have hW' : 0 < -Vp := by linarith [not_le.mp hneg]
    obtain ⟨p, hpv, hs⟩ := exists_dual_vector g hg dφ
    have hpp : g p p = 0 := hs ▸ h
    obtain ⟨u0, hu0⟩ := hg.exists_timelike (by norm_num)
    have hN0 : 0 < -g u0 u0 := by linarith
    set c : ℝ := g p u0 with hc
    by_cases hc0 : c = 0
    · have h1 := hW u0 hu0
      rw [scalarT_self_apply, h, hpv u0, ← hc, hc0] at h1
      nlinarith [mul_pos hW' hN0]
    · set t : ℝ := -(c ^ 2 + 1) / (2 * (-Vp) * c) with ht
      have htc : t * c = -(c ^ 2 + 1) / (2 * (-Vp)) := by
        rw [ht]; field_simp
      have hsym : g u0 p = g p u0 := hg.symm _ _
      have hguu : g (u0 + t • p) (u0 + t • p) = g u0 u0 + 2 * (t * c) := by
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hsym, hpp, ← hc]
        ring
      have hdu : dφ (u0 + t • p) = c := by
        rw [hpv, map_add, map_smul, smul_eq_mul, hpp, ← hc]; ring
      have hneg' : g (u0 + t • p) (u0 + t • p) < 0 := by
        rw [hguu, htc]
        have : 0 < (c ^ 2 + 1) / (2 * (-Vp)) := by positivity
        have e : -(c ^ 2 + 1) / (2 * (-Vp)) = -((c ^ 2 + 1) / (2 * (-Vp))) := by ring
        rw [e]; linarith
      have h1 := hW _ hneg'
      rw [scalarT_self_apply, h, hdu, hguu, htc] at h1
      have e2 : (1 / 2 * 0 + Vp) * -(g u0 u0 + 2 * (-(c ^ 2 + 1) / (2 * -Vp))) =
          Vp * (-g u0 u0) - (c ^ 2 + 1) := by
        have hVne : Vp ≠ 0 := by intro h0; rw [h0] at hW'; simp at hW'
        field_simp
        ring
      rw [e2] at h1
      nlinarith [mul_pos hW' hN0]
  · exact scalar_weakEC_of_nonneg_potential g hg dφ

end Pointwise

end Lightlike

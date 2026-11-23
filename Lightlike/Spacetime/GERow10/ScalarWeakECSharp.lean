import Lightlike.Spacetime.GERow10.ScalarWeakEC

/-!
# The sharp weak energy condition for the Klein–Gordon field (G1-010)

For a Klein–Gordon tensor `T = dφ ⊗ dφ − (½ |dφ|² + V) g` at a point:

* `exists_timelike_ker`: if `dφ = 0` or `dφ` is spacelike (`|dφ|² = tr_g (dφ ⊗ dφ) > 0`) there is a timelike `u` with `dφ u = 0`.
* `scalar_weakEC_iff`: for such a gradient, `WeakEC ↔ 0 ≤ ½ |dφ|² + V`.
* `scalar_weakEC_iff_of_zero`: for `dφ = 0`, `WeakEC ↔ 0 ≤ V` (converse of the trust check of GE14).

**Limits.** Pointwise; for timelike or null `dφ` only the sufficient direction `scalar_weakEC_of_nonneg_potential` is proved.
-/

noncomputable section
namespace Lightlike

section Pointwise
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- If `dφ = 0` or `dφ` has positive squared norm, some timelike vector lies in the kernel of `dφ`. -/
theorem exists_timelike_ker (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ)
    (h : dφ = 0 ∨ 0 < traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate) :
    ∃ u : V, g u u < 0 ∧ dφ u = 0 := by
  obtain ⟨u0, hu0⟩ := hg.exists_timelike (by norm_num)
  obtain ⟨p, hpv, hs⟩ := exists_dual_vector g hg dφ
  rcases h with h | h
  · exact ⟨u0, hu0, by simp [h]⟩
  · rw [hs] at h
    set c : ℝ := g p u0 / g p p with hc
    have hcp : c * g p p = g p u0 := by rw [hc]; field_simp
    refine ⟨u0 - c • p, ?_, ?_⟩
    · have hsym : g u0 p = g p u0 := hg.symm _ _
      have : g (u0 - c • p) (u0 - c • p) = g u0 u0 - (g p u0) ^ 2 / g p p := by
        simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hsym]
        rw [hc]; field_simp; ring
      rw [this]
      have : 0 ≤ (g p u0) ^ 2 / g p p := by positivity
      linarith
    · rw [hpv, map_sub, map_smul, smul_eq_mul, hcp]; ring

/-- **Sharp weak energy condition** for a Klein–Gordon field whose gradient vanishes or is spacelike:
`WeakEC ↔ 0 ≤ ½ |dφ|² + V`. -/
theorem scalar_weakEC_iff (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ)
    (h : dφ = 0 ∨ 0 < traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate) :
    WeakEC g (scalarT g hg dφ Vp) ↔
      0 ≤ (1 / 2) * traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate + Vp := by
  constructor
  · intro hW
    obtain ⟨u, hu, hk⟩ := exists_timelike_ker g hg dφ h
    have h1 := hW u hu
    rw [scalarT_self_apply, hk] at h1
    have hN : 0 < -g u u := by linarith
    have : 0 ≤ ((1 / 2) * traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate + Vp) * (-g u u) := by
      simpa using h1
    exact nonneg_of_mul_nonneg_left this hN
  · intro hpos u hu
    rw [scalarT_self_apply]
    have hN : 0 < -g u u := by linarith
    have := mul_nonneg hpos hN.le
    nlinarith [sq_nonneg (dφ u)]

/-- **Converse of the trust check of GE14**: for `dφ = 0` the weak energy condition holds exactly when `V ≥ 0`. -/
theorem scalar_weakEC_iff_of_zero (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (Vp : ℝ) :
    WeakEC g (scalarT g hg 0 Vp) ↔ 0 ≤ Vp := by
  have h0 : traceG g ((0 : V →L[ℝ] ℝ).smulRight (0 : V →L[ℝ] ℝ)) hg.bilinForm_nondegenerate = 0 := by
    have h00 : ContinuousLinearMap.toBilinForm (0 : V →L[ℝ] V →L[ℝ] ℝ) = 0 := by
      ext x y; simp [ContinuousLinearMap.toBilinForm]
    simp [traceG, h00]
  rw [scalar_weakEC_iff g hg 0 Vp (Or.inl rfl), h0]
  constructor <;> intro h <;> linarith

end Pointwise

end Lightlike

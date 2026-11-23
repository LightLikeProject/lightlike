import Lightlike.Oscillatory.PhaseReduction

/-!
# A function whose gradient vanishes on a hypersurface has a degenerate Hessian (SF10, P2 defect)

`hessMat φ a` is the matrix of second partial derivatives of `φ` built from `fderiv`, which takes
the junk value `0` at points where a function is not differentiable.  If the partial derivatives
`∂ᵢ φ` all vanish on a set `Z` through `a` whose tangent cone at `a` contains a hyperplane
`ker ℓ`, then every row of `hessMat φ a` is a multiple of the functional `ℓ`: the Hessian has
rank at most one and its determinant is `0` for `n ≥ 2`.

This is the abstract core of the statement defect of `lorHessian_invertible_at_critical` (the
vertex action jumps across the branch cut of `Complex.log`, where `fderiv` is the junk `0`).
Supporting lemmas only.
-/

open Filter Topology Lightlike.Oscillatory

namespace Lightlike.SpinFoam.CutRank

variable {n : ℕ}

/-- A function that vanishes on `Z`, differentiable or not at `a ∈ Z`, has derivative zero along
every tangent direction of `Z` at `a`. -/
theorem fderiv_apply_eq_zero_of_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} {Z : Set E} {a : E} (haZ : a ∈ Z) (hg : ∀ y ∈ Z, g y = 0) {u : E}
    (hu : u ∈ tangentConeAt ℝ Z a) : fderiv ℝ g a u = 0 := by
  by_cases hdiff : DifferentiableAt ℝ g a
  · obtain ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hu
    have h := (hdiff.hasFDerivAt.hasFDerivWithinAt (s := Z)).lim hd₀ hds hcd
    have h0 : Tendsto (fun m => c m • (g (a + d m) - g a)) l (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hds] with m hm
      simp [hg _ hm, hg _ haZ]
    exact tendsto_nhds_unique h h0
  · rw [fderiv_zero_of_not_differentiableAt hdiff]
    rfl

/-- A real-linear functional `D : E →L[ℝ] ℂ` that vanishes on `ker ℓ` is a complex multiple of `ℓ`:
`D x = ℓ x · D w` for `ℓ w = 1`. -/
theorem apply_eq_of_ker {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] ℂ) (ℓ : E →L[ℝ] ℝ) {w : E} (hw : ℓ w = 1)
    (hD : ∀ u, ℓ u = 0 → D u = 0) (x : E) : D x = ((ℓ x : ℝ) : ℂ) * D w := by
  have h0 : ℓ (x - ℓ x • w) = 0 := by simp [hw]
  have h1 := hD _ h0
  rw [map_sub, map_smul, sub_eq_zero] at h1
  rw [h1, Complex.real_smul]

/-- **Rank-one Hessian**: if all partial derivatives of `φ` vanish on a set `Z ∋ a` whose tangent
cone at `a` contains `ker ℓ` for a nonzero functional `ℓ`, then `det (hessMat φ a) = 0`
(for `n ≥ 2`). -/
theorem det_hessMat_eq_zero_of_cut (hn : 2 ≤ n) {φ : (Fin n → ℝ) → ℂ} {a : Fin n → ℝ}
    {Z : Set (Fin n → ℝ)} (haZ : a ∈ Z) (hZ : ∀ y ∈ Z, ∀ i, coordDeriv φ i y = 0)
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (htan : ∀ u, ℓ u = 0 → u ∈ tangentConeAt ℝ Z a) :
    (hessMat φ a).det = 0 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨w0, hw0⟩ : ∃ w, ℓ w ≠ 0 := by
    by_contra h
    exact hℓ (ContinuousLinearMap.ext fun x => not_not.1 (not_exists.1 h x))
  set w : Fin n → ℝ := (ℓ w0)⁻¹ • w0 with hwdef
  have hw : ℓ w = 1 := by simp [hwdef, hw0]
  have hrow : ∀ i x, fderiv ℝ (fun y => coordDeriv φ i y) a x =
      ((ℓ x : ℝ) : ℂ) * fderiv ℝ (fun y => coordDeriv φ i y) a w := fun i x =>
    apply_eq_of_ker _ ℓ hw (fun u hu =>
      fderiv_apply_eq_zero_of_tangent haZ (fun y hy => hZ y hy i) (htan u hu)) x
  have hM : hessMat φ a = Matrix.vecMulVec
      (fun i => fderiv ℝ (fun y => coordDeriv φ i y) a w)
      (fun j => ((ℓ (Pi.single j 1) : ℝ) : ℂ)) := by
    ext i j
    rw [Matrix.vecMulVec_apply]
    exact (hrow i (Pi.single j 1)).trans (mul_comm _ _)
  rw [hM]
  exact Matrix.det_vecMulVec _ _

end Lightlike.SpinFoam.CutRank

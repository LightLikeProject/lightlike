import Lightlike.Asymptotics.Lorentzian.Stationary

/-!
# Critical points of the Lorentzian action with `SU(2)` group elements

Elimination of the spinor `z` is an equivalence (`exists_max_iff_relation`): the weight of a
triangle can be made maximal by a choice of `z` exactly when `A⁻¹ ξ` is a nonzero multiple of
`B⁻¹ J ξ'`, with `A = X_a†`, `B = X_b†` (BDFHP eq. (20)). When `A` and `B` are unitary, that
multiple is a phase, and the relation says the two coherent states `A⁻¹ ξ` and `B⁻¹ J ξ'` have
the same spin vector (`su2_relation_iff_spinVec`): this is the gluing condition of the
Euclidean theory.

The ingredients are the identity `2 |⟨x,y⟩|² = ‖x‖²‖y‖² + n̂(x)·n̂(y)` (`two_norm_inner_sq`), and
the fact that a unit spinor is determined up to a phase by its spin vector
(`exists_phase_of_spinVec_eq`).
-/

open Complex
open scoped ComplexConjugate

namespace Lightlike.Asymptotics.Lorentzian

/-- `2 |⟨x, y⟩|² = ‖x‖² ‖y‖² + n̂(x) · n̂(y)`: the overlap of two coherent states in terms of the
angle between their spin vectors. -/
lemma two_norm_inner_sq (x y : Spinor) :
    2 * ‖inner ℂ x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 + ∑ i, spinVec x i * spinVec y i := by
  simp only [Fin.sum_univ_three, spinVec, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    PiLp.inner_apply, RCLike.inner_apply]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A unit phase does not change the normal of a spinor. -/
lemma spinVec_smul_unit {u : ℂ} (hu : ‖u‖ = 1) (x : Spinor) (i : Fin 3) :
    spinVec (u • x) i = spinVec x i := by
  have h1 : conj u * u = 1 := by
    rw [Complex.conj_mul', hu]; simp
  fin_cases i
  · simp only [spinVec, PiLp.smul_apply, smul_eq_mul]
    have : conj (u * x 0) * (u * x 1) = conj (x 0) * x 1 := by
      calc _ = (conj u * u) * (conj (x 0) * x 1) := by rw [map_mul]; ring
        _ = _ := by rw [h1, one_mul]
    rw [this]
  · simp only [spinVec, PiLp.smul_apply, smul_eq_mul]
    have : conj (u * x 0) * (u * x 1) = conj (x 0) * x 1 := by
      calc _ = (conj u * u) * (conj (x 0) * x 1) := by rw [map_mul]; ring
        _ = _ := by rw [h1, one_mul]
    rw [this]
  · simp only [spinVec, PiLp.smul_apply, smul_eq_mul, norm_mul, hu, one_mul]

/-- Two unit spinors have the same normal exactly when they differ by a phase: the normal
`spinVec` is the Bloch vector, and it determines a unit spinor up to `U(1)`. -/
theorem exists_phase_of_spinVec_eq {x y : Spinor} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : ∀ i, spinVec x i = spinVec y i) : ∃ u : ℂ, ‖u‖ = 1 ∧ y = u • x := by
  have hxx := two_norm_inner_sq x x
  have hxy := two_norm_inner_sq x y
  have hn : ∑ i, spinVec x i * spinVec y i = ∑ i, spinVec x i * spinVec x i :=
    Finset.sum_congr rfl fun i _ => by rw [h i]
  have hxx' : ‖inner ℂ x x‖ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [hx]
  have hxx2 : ∑ i, spinVec x i * spinVec x i = 1 := by
    rw [hxx', hx] at hxx; linarith
  have hip : ‖inner ℂ x y‖ = ‖x‖ * ‖y‖ := by
    have h2 : ‖inner ℂ x y‖ ^ 2 = 1 := by
      rw [hx, hy, hn, hxx2] at hxy; linarith
    rw [hx, hy, mul_one]
    have := norm_nonneg (inner ℂ x y)
    nlinarith
  have hx0 : x ≠ 0 := by intro h0; rw [h0] at hx; simp at hx
  have hy0 : y ≠ 0 := by intro h0; rw [h0] at hy; simp at hy
  obtain ⟨r, _, hr⟩ := (norm_inner_eq_norm_iff hx0 hy0).1 hip
  refine ⟨r, ?_, hr⟩
  have := congrArg norm hr
  rw [norm_smul, hx, hy] at this
  linarith

/-- For unit spinors, equal normals is the same as being related by a unit phase. -/
theorem phase_iff_spinVec_eq {x y : Spinor} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (∃ u : ℂ, ‖u‖ = 1 ∧ y = u • x) ↔ ∀ i, spinVec x i = spinVec y i := by
  refine ⟨fun ⟨u, hu, hyx⟩ i => ?_, exists_phase_of_spinVec_eq hx hy⟩
  rw [hyx, spinVec_smul_unit hu]

/-- BDFHP eq. (20) for unitary group elements: for isometries `A`, `B` of the spinor space
(`SU(2)` elements) and unit spinors `ξ`, `ξ'`, the relation `A⁻¹ξ = c B⁻¹Jξ'` with a unit `c`
holds exactly when the normal of `A⁻¹ξ` equals the normal of `B⁻¹Jξ'`, that is when the rotated
normals `n(A⁻¹ξ)` and `-n(B⁻¹ξ')` agree. -/
theorem su2_relation_iff {A B : Spinor ≃ₗᵢ[ℂ] Spinor} {ξ ξ' : Spinor}
    (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1) :
    (∃ c : ℂ, ‖c‖ = 1 ∧ A.symm ξ = c • B.symm (jMap ξ')) ↔
      ∀ i, spinVec (B.symm (jMap ξ')) i = spinVec (A.symm ξ) i := by
  have h1 : ‖A.symm ξ‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hξ]
  have h2 : ‖B.symm (jMap ξ')‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, norm_jMap, hξ']
  exact phase_iff_spinVec_eq h2 h1

/-- Non-vacuity: the spinor `e0` is related to itself by the phase `1`. -/
example : ∃ u : ℂ, ‖u‖ = 1 ∧ e0 = u • e0 := ⟨1, by simp, by simp⟩

/-- Wrong-model control: `e0` and `e1` have opposite normals (`spinVec_e0`, `spinVec_e1`), so no
phase relates them. -/
example : ¬ ∃ u : ℂ, ‖u‖ = 1 ∧ e1 = u • e0 := by
  rintro h
  have := (phase_iff_spinVec_eq norm_e0 norm_e1).1 h 2
  rw [spinVec_e0, spinVec_e1] at this
  norm_num at this

end Lightlike.Asymptotics.Lorentzian

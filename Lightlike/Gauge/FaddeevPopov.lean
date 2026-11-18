import Lightlike.Gauge.GaugeFlow

/-!
# The Faddeev-Popov matrix, finite-dimensional core

For constraints `φ_b` (first class) and gauge conditions `G_a` on Physlib's flat phase space, the Faddeev-Popov matrix
at a point is `M_{ab} = {G_a, φ_b}`. `dG_a (X_{φ_b}) = M_{ab}` (`pairing_fpMatrix`): the matrix is the derivative of the
gauge condition along the gauge directions. If its determinant (the Faddeev-Popov determinant) does not vanish, the
gauge directions `X_{φ_b}(x)` are linearly independent and meet the tangent space `{v | dG_a (v) = 0}` of the gauge
slice only in zero: the orbit is transversal to the slice at `x` (`linearIndependent_hamField_of_det_ne_zero`,
`eq_zero_of_mem_ker_of_det_ne_zero`). Infinitesimal statement; the global statements (every orbit meets the slice, the
Gribov copies) are not covered here.
-/

open InnerProductSpace
open ClassicalMechanics

namespace Lightlike.Gauge

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {m : ℕ}

/-- The Faddeev-Popov matrix `M_{ab} = {G_a, φ_b}` of gauge conditions `G` and constraints `φ`. -/
noncomputable def fpMatrix (G φ : Fin m → X → X → ℝ) (p q : X) : Matrix (Fin m) (Fin m) ℝ :=
  fun a b => poissonBracket (G a) (φ b) p q

/-- **`dG_a (X_{φ_b}) = M_{ab}`**. -/
theorem pairing_fpMatrix (G φ : Fin m → X → X → ℝ) (p q : X) (a b : Fin m) :
    pairing (phaseGrad (G a) p q) (hamField (φ b) p q) = fpMatrix G φ p q a b :=
  pairing_hamField _ _ p q

/-- The pairing is linear in its second argument. -/
theorem pairing_sum {ι : Type*} (s : Finset ι) (u : X × X) (g : ι → ℝ) (w : ι → X × X) :
    pairing u (∑ i ∈ s, g i • w i) = ∑ i ∈ s, g i * pairing u (w i) := by
  induction s using Finset.cons_induction with
  | empty => simp [pairing]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    simp only [pairing, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, inner_add_right,
      inner_smul_right]
    ring

/-- `dG_a` of a combination of gauge directions is the matrix times the coefficients. -/
theorem pairing_sum_hamField (G φ : Fin m → X → X → ℝ) (p q : X) (g : Fin m → ℝ) (a : Fin m) :
    pairing (phaseGrad (G a) p q) (∑ b, g b • hamField (φ b) p q) = (fpMatrix G φ p q).mulVec g a := by
  rw [pairing_sum]
  simp only [Matrix.mulVec, dotProduct, pairing_fpMatrix]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Transversality**: a nonzero Faddeev-Popov determinant makes the gauge directions linearly independent. -/
theorem linearIndependent_hamField_of_det_ne_zero (G φ : Fin m → X → X → ℝ) (p q : X)
    (hdet : (fpMatrix G φ p q).det ≠ 0) : LinearIndependent ℝ fun b => hamField (φ b) p q := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h0 : (fpMatrix G φ p q).mulVec g = 0 := by
    funext a
    rw [← pairing_sum_hamField, hg]
    simp [pairing]
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h0) a

/-- **The orbit meets the gauge slice's tangent space only in zero**: a combination of gauge directions annihilated
by every `dG_a` is zero when the Faddeev-Popov determinant is nonzero. -/
theorem eq_zero_of_mem_ker_of_det_ne_zero (G φ : Fin m → X → X → ℝ) (p q : X)
    (hdet : (fpMatrix G φ p q).det ≠ 0) (g : Fin m → ℝ)
    (hker : ∀ a, pairing (phaseGrad (G a) p q) (∑ b, g b • hamField (φ b) p q) = 0) : g = 0 := by
  have h0 : (fpMatrix G φ p q).mulVec g = 0 := funext fun a => by rw [← pairing_sum_hamField]; exact hker a
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h0

/-- **Negative control, the horizon**: where the Faddeev-Popov determinant vanishes, some nonzero combination of the gauge
directions is tangent to the gauge slice (killed by every `dG_a`), so transversality fails; the hypothesis of
`eq_zero_of_mem_ker_of_det_ne_zero` cannot be dropped. -/
theorem exists_ker_of_det_eq_zero (G φ : Fin m → X → X → ℝ) (p q : X)
    (hdet : (fpMatrix G φ p q).det = 0) :
    ∃ g : Fin m → ℝ, g ≠ 0 ∧ ∀ a, pairing (phaseGrad (G a) p q) (∑ b, g b • hamField (φ b) p q) = 0 := by
  obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact ⟨g, hg0, fun a => by rw [pairing_sum_hamField, hg]; rfl⟩

/-- The bracket matrix `({ψ_i, ψ_j})` of the combined family `ψ = (φ, G)` of constraints and gauge conditions, at a point. -/
noncomputable def combinedBracket (φ G : Fin m → X → X → ℝ) (p q : X) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.of fun i j => poissonBracket (Sum.elim φ G i) (Sum.elim φ G j) p q

open Matrix in
/-- **The constraints with the gauge conditions form a second-class system** (Wipf's lectures, arXiv:hep-th/9312078, Section 5.2,
after eq. (5.30)): at a point where the constraints are first class (`{φ_a, φ_b} = 0`), the bracket matrix of `(φ, G)` is nonsingular iff the
Faddeev-Popov determinant `det {G_a, φ_b}` is nonzero. -/
theorem combinedBracket_det_ne_zero_iff (φ G : Fin m → X → X → ℝ) (p q : X)
    (hfirst : ∀ a b, poissonBracket (φ a) (φ b) p q = 0) :
    (combinedBracket φ G p q).det ≠ 0 ↔ (fpMatrix G φ p q).det ≠ 0 := by
  have hrow : ∀ (w : Fin m ⊕ Fin m → ℝ) (a : Fin m),
      (combinedBracket φ G p q *ᵥ w) (Sum.inl a) = -((fpMatrix G φ p q)ᵀ *ᵥ (w ∘ Sum.inr)) a := by
    intro w a
    simp only [Matrix.mulVec, dotProduct, combinedBracket, Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, hfirst, zero_mul, Finset.sum_const_zero, zero_add, Matrix.transpose_apply, fpMatrix,
      Function.comp_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [poissonBracket_antisymm]; ring
  have hrow' : ∀ (w : Fin m ⊕ Fin m → ℝ) (a : Fin m),
      (combinedBracket φ G p q *ᵥ w) (Sum.inr a) =
        (fpMatrix G φ p q *ᵥ (w ∘ Sum.inl)) a + ∑ b, poissonBracket (G a) (G b) p q * w (Sum.inr b) := by
    intro w a
    simp only [Matrix.mulVec, dotProduct, combinedBracket, Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, fpMatrix, Function.comp_apply]
  constructor
  · intro hC hM
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hM
    apply hC
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim u 0, fun h => hu0 (by
      funext b; simpa using congrFun h (Sum.inl b)), ?_⟩
    funext i
    rcases i with a | a
    · rw [hrow]; simp
    · rw [hrow']; simp [Function.comp_def, hu]
  · intro hM hC
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hC
    have hMt : (fpMatrix G φ p q)ᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
    have hv : w ∘ Sum.inr = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hMt (funext fun a => ?_)
      have := congrFun hw (Sum.inl a)
      rw [hrow] at this
      simpa using this
    have hu : w ∘ Sum.inl = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hM (funext fun a => ?_)
      have := congrFun hw (Sum.inr a)
      rw [hrow'] at this
      have hv' : ∀ b, w (Sum.inr b) = 0 := fun b => congrFun hv b
      simpa [hv'] using this
    apply hw0
    funext i
    rcases i with a | a
    · exact congrFun hu a
    · exact congrFun hv a

end Lightlike.Gauge

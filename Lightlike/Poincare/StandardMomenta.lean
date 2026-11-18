module

public import Lightlike.Poincare.LittleGroups
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Standard momenta and the massive little group

Signature `(+,−,−,−)`. The standard momenta of the Wigner classification: the rest momentum `(m, 0, 0, 0)`
(`massiveStd`), the light-like momentum `(1, 0, 0, 1)` (`masslessStd`); with `tachyonStd` of `LittleGroups` they
represent the orbits `p² = m² > 0`, `p² = 0`, `p² < 0`. The little group of the rest momentum, for `m ≠ 0`, is
compact (`isCompact_littleGroup_massive`; it is the rotation group `SO(3)`).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2 (orbits and stabilisers).
-/

@[expose] public section

open Lorentz LorentzGroup Matrix
open scoped Lorentz.Vector

noncomputable section

namespace Lightlike.Poincare

/-- The standard momentum of a massive particle: `(m, 0, 0, 0)`. -/
def massiveStd (m : ℝ) : Lorentz.Vector 3 := m • Lorentz.Vector.basis (Sum.inl 0)

/-- The standard momentum of a massless particle: `(1, 0, 0, 1)`. -/
def masslessStd : Lorentz.Vector 3 := Lorentz.Vector.basis (Sum.inl 0) + Lorentz.Vector.basis (Sum.inr 2)

lemma massiveStd_apply (m : ℝ) (μ : Fin 1 ⊕ Fin 3) :
    massiveStd m μ = if μ = Sum.inl 0 then m else 0 := by
  simp [massiveStd, Lorentz.Vector.basis_apply, eq_comm]

/-- `p² = m²` for the rest momentum. -/
theorem minkowskiProduct_massiveStd (m : ℝ) :
    ⟪massiveStd m, massiveStd m⟫ₘ = m ^ 2 := by
  rw [massiveStd, Lorentz.Vector.minkowskiProduct_smul_self]
  simp [minkowskiMatrix.inl_0_inl_0, Lorentz.Vector.basis_apply]

/-- `p² = 0` for the light-like standard momentum. -/
theorem minkowskiProduct_masslessStd : ⟪masslessStd, masslessStd⟫ₘ = 0 := by
  simp [masslessStd, Lorentz.Vector.basis_apply, minkowskiMatrix.inl_0_inl_0,
    minkowskiMatrix.inr_i_inr_i]

/-- `p² = −κ²` for the tachyonic standard momentum. -/
theorem minkowskiProduct_tachyonStd (κ : ℝ) : ⟪tachyonStd κ, tachyonStd κ⟫ₘ = -κ ^ 2 := by
  have : tachyonStd κ = κ • Lorentz.Vector.basis (Sum.inr 2) := by
    funext μ
    simp [tachyonStd, Lorentz.Vector.basis_apply, eq_comm]
  rw [this, Lorentz.Vector.minkowskiProduct_smul_self]
  simp [minkowskiMatrix.inr_i_inr_i, Lorentz.Vector.basis_apply]


/-- The first column of an element of the little group of the rest momentum is `e₀`. -/
lemma littleGroup_massive_col {m : ℝ} (hm : m ≠ 0) {Λ : LorentzGroup 3}
    (hΛ : Λ ∈ littleGroup (massiveStd m)) (μ : Fin 1 ⊕ Fin 3) :
    Λ.1 μ (Sum.inl 0) = if μ = Sum.inl 0 then 1 else 0 := by
  have h : Λ.1 *ᵥ massiveStd m = massiveStd m := by
    rw [← Lorentz.Vector.smul_eq_mulVec]; exact hΛ
  have h2 := congrFun h μ
  simp only [Matrix.mulVec, dotProduct, massiveStd_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h2
  by_cases hμ : μ = Sum.inl 0
  · simp only [hμ, if_true] at h2 ⊢
    exact (mul_left_inj' hm).1 (by simpa using h2)
  · simp only [hμ, if_false] at h2 ⊢
    exact h2.resolve_right hm

/-- The defining relation `Λᵀ η Λ = η` on the entry `(a, b)`. -/
lemma lorentz_entry_rel (Λ : LorentzGroup 3) (a b : Fin 1 ⊕ Fin 3) :
    ∑ μ, Λ.1 μ a * (Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) μ) * Λ.1 μ b = minkowskiMatrix a b := by
  have h := (mem_iff_transpose_mul_minkowskiMatrix_mul_self Λ.1).1 Λ.2
  have h2 := congrFun (congrFun h a) b
  rw [minkowskiMatrix.as_diagonal] at h2 ⊢
  simpa [Matrix.mul_apply, Matrix.mul_diagonal] using h2

/-- All entries of an element of the little group of the rest momentum have modulus at most one. -/
lemma littleGroup_massive_entry_bound {m : ℝ} (hm : m ≠ 0) {Λ : LorentzGroup 3}
    (hΛ : Λ ∈ littleGroup (massiveStd m)) (a b : Fin 1 ⊕ Fin 3) : |Λ.1 a b| ≤ 1 := by
  have hc := littleGroup_massive_col hm hΛ
  rcases b with ⟨b0⟩ | j
  · fin_cases b0
    rcases a with ⟨a0⟩ | i
    · fin_cases a0; simp [hc]
    · simp [hc]
  · have hrow : Λ.1 (Sum.inl 0) (Sum.inr j) = 0 := by
      have := lorentz_entry_rel Λ (Sum.inl 0) (Sum.inr j)
      simp [Fintype.sum_sum_type, hc, Fin.sum_univ_three, minkowskiMatrix.as_diagonal] at this
      simpa using this
    have hsq : ∑ i : Fin 3, Λ.1 (Sum.inr i) (Sum.inr j) ^ 2 = 1 := by
      have := lorentz_entry_rel Λ (Sum.inr j) (Sum.inr j)
      simp [Fintype.sum_sum_type, hrow, minkowskiMatrix.as_diagonal] at this
      nlinarith [this]
    rcases a with ⟨a0⟩ | i
    · fin_cases a0; simp [hrow]
    · have hle : Λ.1 (Sum.inr i) (Sum.inr j) ^ 2 ≤ 1 := by
        rw [← hsq]
        exact Finset.single_le_sum (f := fun i : Fin 3 => Λ.1 (Sum.inr i) (Sum.inr j) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)

/-- **The little group of the rest momentum is compact** (it is `SO(3)`). -/
theorem isCompact_littleGroup_massive {m : ℝ} (hm : m ≠ 0) :
    IsCompact (littleGroup (massiveStd m)) := by
  have hclosed : IsClosed (littleGroup (massiveStd m)) := by
    have hcont : Continuous fun Λ : LorentzGroup 3 => Λ.1 *ᵥ massiveStd m :=
      (continuous_subtype_val.matrix_mulVec continuous_const)
    have : littleGroup (massiveStd m) = (fun Λ : LorentzGroup 3 => Λ.1 *ᵥ massiveStd m) ⁻¹' {massiveStd m} := by
      ext Λ
      simp [littleGroup, Lorentz.Vector.smul_eq_mulVec]
    rw [this]
    exact isClosed_singleton.preimage hcont
  have hK : IsCompact {M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ | ∀ a b, M a b ∈ Set.Icc (-1 : ℝ) 1} := by
    have : IsCompact (Set.univ.pi fun a : Fin 1 ⊕ Fin 3 => Set.univ.pi fun b : Fin 1 ⊕ Fin 3 => Set.Icc (-1 : ℝ) 1) :=
      isCompact_univ_pi fun a => isCompact_univ_pi fun b => isCompact_Icc
    convert this using 1
    ext M
    simp [Set.mem_pi]
  rw [LorentzGroup.isClosedEmbedding_val.isInducing.isCompact_iff]
  refine hK.of_isClosed_subset (LorentzGroup.isClosedEmbedding_val.isClosedMap _ hclosed) ?_
  rintro _ ⟨Λ, hΛ, rfl⟩ a b
  exact abs_le.1 (littleGroup_massive_entry_bound hm hΛ a b)

end Lightlike.Poincare

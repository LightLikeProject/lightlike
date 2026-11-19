import Lightlike.Gauge.DiracAlgo
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The secondary constraints do not depend on the selected block

A. Wipf, *Hamilton's Formalism for Systems with Constraints*, arXiv:hep-th/9312078, Section 3.3 (read), p. 16: "In this case
`u` is not fixed and 3.24 is only solvable if `h_m w^m_a ≈ 0` for all left null-eigenvectors `w_a` of `C`", and p. 17: "For
every left null-eigenvector `w^j_a` of the rectangular matrix `C_jm = {φ_j, φ_m}` the conditions `w^j_a {φ_j, H} ≈ 0` are
fulfilled ... we assume that the rank of `C` is constant on `Γ_c`."

`DiracAlgo.stages` computes the secondary constraints `χ = h₂ - D B⁻¹ h₁` from a selected invertible block `B` of the
consistency matrix (a chart). At a point where a selection is admissible (its block invertible, its Schur complement zero,
which constant rank gives), `χ = 0` is equivalent to the solvability of the full consistency system
`{S_i, H} + ∑_a {S_i, φ_a} u_a = 0`, which does not mention the selection, and that is equivalent to Wipf's condition
`w · h = 0` for every left null vector `w` of `C`. So two admissible selections give the same next constraint set near a point
of the surface: the pointwise `hcover` statement does not depend on the chart.

* `Sel.Admissible`, `Stage.Consistent`, `Stage.consistency_translate_symm`;
* `Stage.chiFun_zero_iff`, `Stage.chiFun_zero_iff_of_admissible`, `Stage.zeroSet_next_inter`: chart independence;
* `exists_mulVec_add_eq_zero_iff`, `Stage.consistent_iff_leftNull`, `Stage.chiFun_zero_iff_leftNull`: Wipf's left
  null-eigenvector form.
-/

namespace Lightlike.Gauge

open Matrix

variable {E : Type*} {M : ℕ}

/-- **An admissible selection at `x`**: its block is invertible and its Schur complement vanishes (the local form of
constant rank, `DiracSchur.schur_eq_zero_of_rank_le_block`). -/
def Sel.Admissible (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) {S : Stage E} (σ : Sel S M) (x : E) : Prop :=
  IsUnit (S.consCm br φ σ x).toBlocks₁₁.det ∧
    (S.consCm br φ σ x).toBlocks₂₂ =
      (S.consCm br φ σ x).toBlocks₂₁ * (S.consCm br φ σ x).toBlocks₁₁⁻¹ * (S.consCm br φ σ x).toBlocks₁₂

/-- **The consistency condition at `x`**, without a selection: `{S_i, H} + ∑_a {S_i, φ_a} u_a = 0` is solvable. -/
def Stage.Consistent (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S : Stage E) (x : E) : Prop :=
  ∃ u : Fin M → ℝ, ∀ i : Fin S.n, br (S.Φ i) H x + ∑ a, br (S.Φ i) (φ a) x * u a = 0

/-- The consistency system in any selected splitting follows from the selection-free one. -/
theorem Stage.consistency_translate_symm (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (S : Stage E) (σ : Sel S M) (x : E) (h : S.Consistent br φ H x) :
    ∃ u' : Fin σ.r ⊕ Fin σ.l → ℝ, S.consCm br φ σ x *ᵥ u' + S.consH br H σ x = 0 := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u ∘ σ.eC.symm, ?_⟩
  funext i
  have h1 := hu (σ.eR.symm i)
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Stage.consCm, Stage.consH, Matrix.of_apply, Pi.zero_apply,
    Function.comp_apply]
  rw [Equiv.sum_comp σ.eC.symm (fun a => br (S.Φ (σ.eR.symm i)) (φ a) x * u a)]
  linarith

/-- **The secondary constraints vanish exactly where the consistency system is solvable**, for an admissible selection. -/
theorem Stage.chiFun_zero_iff (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S : Stage E)
    {σ : Sel S M} {x : E} (hσ : σ.Admissible br φ x) :
    (∀ j, S.chiFun br φ H σ j x = 0) ↔ S.Consistent br φ H x := by
  have key := exists_multiplier_iff_chi (S.consCm br φ σ) (S.consH br H σ) hσ.1 hσ.2
  constructor
  · intro h
    obtain ⟨u', hu'⟩ := key.mpr (funext h)
    exact S.consistency_translate br φ H σ x u' hu'
  · intro h j
    exact congrFun (key.mp (S.consistency_translate_symm br φ H σ x h)) j

/-- **Chart independence**: two selections admissible at `x` give the same condition `χ(x) = 0`. -/
theorem Stage.chiFun_zero_iff_of_admissible (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (S : Stage E) {σ σ' : Sel S M} {x : E} (hσ : σ.Admissible br φ x) (hσ' : σ'.Admissible br φ x) :
    (∀ j, S.chiFun br φ H σ j x = 0) ↔ ∀ j, S.chiFun br φ H σ' j x = 0 :=
  (S.chiFun_zero_iff br φ H hσ).trans (S.chiFun_zero_iff br φ H hσ').symm

/-- **The next constraint set does not depend on the chart**: on a set where two selections are admissible, the next stages
built from them have the same zero set. -/
theorem Stage.zeroSet_next_inter [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S : Stage E)
    {σ σ' : Sel S M} {U : Set E} (hσ : ∀ x ∈ U, σ.Admissible br φ x) (hσ' : ∀ x ∈ U, σ'.Admissible br φ x) :
    zeroSet (S.next br φ H σ).Φ ∩ U = zeroSet (S.next br φ H σ').Φ ∩ U := by
  ext x
  show x ∈ zeroSet (appendStage S.Φ (S.chiFun br φ H σ)) ∩ U ↔ x ∈ zeroSet (appendStage S.Φ (S.chiFun br φ H σ')) ∩ U
  rw [zeroSet_appendStage, zeroSet_appendStage]
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hS, hχ⟩, hU⟩
    exact ⟨⟨hS, (S.chiFun_zero_iff_of_admissible br φ H (hσ x hU) (hσ' x hU)).mp hχ⟩, hU⟩
  · rintro ⟨⟨hS, hχ⟩, hU⟩
    exact ⟨⟨hS, (S.chiFun_zero_iff_of_admissible br φ H (hσ x hU) (hσ' x hU)).mpr hχ⟩, hU⟩

/-- **The Fredholm alternative**: `C u + h = 0` is solvable iff `w · h = 0` for every left null vector `w` of `C`. -/
theorem exists_mulVec_add_eq_zero_iff {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (h : Fin n → ℝ) :
    (∃ u, C *ᵥ u + h = 0) ↔ ∀ w : Fin n → ℝ, w ᵥ* C = 0 → w ⬝ᵥ h = 0 := by
  constructor
  · rintro ⟨u, hu⟩ w hw
    rw [eq_neg_of_add_eq_zero_right hu, dotProduct_neg, Matrix.dotProduct_mulVec, hw, zero_dotProduct, neg_zero]
  · intro hw
    have hmem : -h ∈ LinearMap.range (Matrix.mulVecLin C) := by
      refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ (-h)).mp fun f hf => ?_
      set w : Fin n → ℝ := fun i => f (Pi.single i 1) with hw'
      have hfw : ∀ v, f v = w ⬝ᵥ v := fun v => by
        conv_lhs => rw [← Finset.univ_sum_single v]
        rw [map_sum]
        simp only [dotProduct, hw']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show Pi.single i (v i) = v i • Pi.single i (1 : ℝ) by
          ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, smul_eq_mul, mul_comm]
      have hwC : w ᵥ* C = 0 := by
        funext a
        have h0 := (Submodule.mem_dualAnnihilator f).mp hf (C *ᵥ Pi.single a 1) ⟨Pi.single a 1, rfl⟩
        rw [hfw, Matrix.dotProduct_mulVec] at h0
        simpa [dotProduct_single] using h0
      rw [hfw, dotProduct_neg, hw w hwC, neg_zero]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_⟩
    rw [Matrix.mulVecLin_apply] at hu
    rw [hu, neg_add_cancel]

/-- **Wipf's form of the consistency condition**: the system is solvable iff `∑_i w_i {S_i, H} = 0` for every left null vector
`w` of `C_ia = {S_i, φ_a}`. -/
theorem Stage.consistent_iff_leftNull (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S : Stage E)
    (x : E) : S.Consistent br φ H x ↔
      ∀ w : Fin S.n → ℝ, (∀ a, ∑ i, w i * br (S.Φ i) (φ a) x = 0) → ∑ i, w i * br (S.Φ i) H x = 0 := by
  have h := exists_mulVec_add_eq_zero_iff (Matrix.of fun i a => br (S.Φ i) (φ a) x) (fun i => br (S.Φ i) H x)
  constructor
  · rintro ⟨u, hu⟩ w hw
    refine (h.mp ⟨u, funext fun i => ?_⟩) w (funext fun a => ?_)
    · simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      linarith [hu i]
    · simpa [Matrix.vecMul, dotProduct] using hw a
  · intro hw
    obtain ⟨u, hu⟩ := h.mpr fun w hwC => by
      simpa [dotProduct] using hw w fun a => by simpa [Matrix.vecMul, dotProduct] using congrFun hwC a
    refine ⟨u, fun i => ?_⟩
    have := congrFun hu i
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    linarith

/-- **The secondary constraints are Wipf's** (Section 3.3, p. 16): for an admissible selection, `χ(x) = 0` iff
`w · h(x) = 0` for every left null vector `w` of `C(x)`. -/
theorem Stage.chiFun_zero_iff_leftNull (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (S : Stage E) {σ : Sel S M} {x : E} (hσ : σ.Admissible br φ x) :
    (∀ j, S.chiFun br φ H σ j x = 0) ↔
      ∀ w : Fin S.n → ℝ, (∀ a, ∑ i, w i * br (S.Φ i) (φ a) x = 0) → ∑ i, w i * br (S.Φ i) H x = 0 :=
  (S.chiFun_zero_iff br φ H hσ).trans (S.consistent_iff_leftNull br φ H x)

end Lightlike.Gauge

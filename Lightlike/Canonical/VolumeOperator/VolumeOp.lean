import Lightlike.Canonical.VolumeOperator.Volume
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# The volume operator at a node

Fourth piece of row G2-014 (milestone CA4). At a node with `K` edges the volume operator is
`V = κ · √|Q|`, where `Q = ∑_{I<J<K} s_{IJK} q_{IJK}` (`Qnode`, signs `s_{IJK}` real) is Hermitian
and `√|·|` is the continuous functional calculus of the Hermitian matrix `Q` (`volumeOp`).
The constant `κ` is the regularization constant.

We prove that `Q` is Hermitian, that `volumeOp` acts on an eigenvector of `Q` with eigenvalue `μ`
as multiplication by `κ √|μ|` (`volumeOp_mulVec_of_eigenvector`), that it is zero on gauge-invariant
trivalent nodes (`volumeOp_three_mulVec_eq_zero`), and that two regularization constants give
different results on any eigenvector with nonzero eigenvalue (`volumeOp_ne_of_ne`).
-/

open Matrix

namespace Lightlike.Rows.G2_014

variable {K : ℕ} {n : Fin K → ℕ}

/-- The node operator `Q = ∑_{I<J<K} s_{IJK} q_{IJK}`, with real signs `s`. -/
noncomputable def Qnode (n : Fin K → ℕ) (s : Fin K → Fin K → Fin K → ℝ) :
    Matrix (Idx n) (Idx n) ℂ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin K × Fin K × Fin K => t.1 < t.2.1 ∧ t.2.1 < t.2.2),
    (s t.1 t.2.1 t.2.2 : ℂ) • qOp n t.1 t.2.1 t.2.2

/-- `Q` is Hermitian. -/
theorem Qnode_isHermitian (s : Fin K → Fin K → Fin K → ℝ) : (Qnode n s).IsHermitian := by
  unfold Matrix.IsHermitian Qnode
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
  rw [conjTranspose_smul, qOp_conjTranspose ht.1.ne ((ht.1.trans ht.2).ne) ht.2.ne]
  simp

/-- The volume operator `V = κ √|Q|` at a node (continuous functional calculus of the
Hermitian matrix `Q`; `κ` is the regularization constant). -/
noncomputable def volumeOp (κ : ℝ) (n : Fin K → ℕ) (s : Fin K → Fin K → Fin K → ℝ) :
    Matrix (Idx n) (Idx n) ℂ :=
  κ • cfc (fun x : ℝ => Real.sqrt |x|) (Qnode n s)

/-- The functional calculus of a Hermitian matrix acts on an eigenvector with eigenvalue `μ`
as multiplication by `f μ`. -/
lemma cfc_mulVec_of_eigenvector {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (v : m → ℂ) (μ : ℝ)
    (h : A *ᵥ v = (μ : ℂ) • v) :
    cfc f A *ᵥ v = (f μ : ℂ) • v := by
  rw [Matrix.IsHermitian.cfc_eq hA f]
  set U : Matrix m m ℂ := (hA.eigenvectorUnitary : Matrix m m ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set D : Matrix m m ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  set w : m → ℂ := star U *ᵥ v with hw
  have hv : U *ᵥ w = v := by rw [hw, mulVec_mulVec, hUU', one_mulVec]
  have hDw : D *ᵥ w = (μ : ℂ) • w := by
    have h1 : (U * D * star U) *ᵥ v = (μ : ℂ) • v := by
      rw [← hspec]; exact h
    have h2 := congrArg (fun x => star U *ᵥ x) h1
    have h3 : star U * (U * D * star U) = D * star U := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [mulVec_mulVec, mulVec_smul, h3] at h2
    rw [hw, mulVec_mulVec]
    exact h2
  have hD' : diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *ᵥ w = (f μ : ℂ) • w := by
    ext i
    have hi := congrFun hDw i
    simp only [hD, mulVec_diagonal, Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    by_cases hwi : w i = 0
    · simp [hwi]
    · have : hA.eigenvalues i = μ := by
        have := mul_right_cancel₀ hwi hi
        exact Complex.ofReal_injective this
      rw [this]
      rfl
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  change (U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * star U) *ᵥ v = _
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change U *ᵥ (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *ᵥ w) = _
  rw [hD', mulVec_smul, hv]

/-- On an eigenvector of `Q` with eigenvalue `μ`, the volume operator is multiplication by
`κ √|μ|`. -/
theorem volumeOp_mulVec_of_eigenvector (κ : ℝ) (s : Fin K → Fin K → Fin K → ℝ)
    (v : Idx n → ℂ) (μ : ℝ) (h : Qnode n s *ᵥ v = (μ : ℂ) • v) :
    volumeOp κ n s *ᵥ v = ((κ * Real.sqrt |μ| : ℝ) : ℂ) • v := by
  have h1 := cfc_mulVec_of_eigenvector (Qnode_isHermitian s) (fun x : ℝ => Real.sqrt |x|) v μ h
  unfold volumeOp
  rw [Matrix.smul_mulVec, h1]
  ext i
  simp [Complex.real_smul, mul_assoc]

/-- For three edges, `Q` is a real multiple of `q_{012}`. -/
lemma Qnode_three (n : Fin 3 → ℕ) (s : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Qnode n s = (s 0 1 2 : ℂ) • qOp n 0 1 2 := by
  have hS : Finset.univ.filter
      (fun t : Fin 3 × Fin 3 × Fin 3 => t.1 < t.2.1 ∧ t.2.1 < t.2.2) = {((0 : Fin 3), 1, 2)} := by
    decide
  unfold Qnode
  rw [hS, Finset.sum_singleton]

/-- **The volume operator vanishes on gauge-invariant trivalent nodes**, for every
regularization constant `κ` and every choice of signs. -/
theorem volumeOp_three_mulVec_eq_zero {n : Fin 3 → ℕ} (κ : ℝ) (s : Fin 3 → Fin 3 → Fin 3 → ℝ)
    {ψ : Idx n → ℂ} (hψ : IsInvariant n ψ) : volumeOp κ n s *ᵥ ψ = 0 := by
  have hQ : Qnode n s *ᵥ ψ = ((0 : ℝ) : ℂ) • ψ := by
    rw [Qnode_three, Matrix.smul_mulVec, qOp_three_mulVec_eq_zero hψ]
    simp
  rw [volumeOp_mulVec_of_eigenvector κ s ψ 0 hQ]
  simp

/-- A wrong regularization constant is detected: on an eigenvector `ψ ≠ 0` of `Q` with
nonzero eigenvalue, two different constants `κ ≠ κ'` give different volumes. -/
theorem volumeOp_ne_of_ne {κ κ' : ℝ} (hκ : κ ≠ κ') (s : Fin K → Fin K → Fin K → ℝ)
    {ψ : Idx n → ℂ} (hψ : ψ ≠ 0) {μ : ℝ} (hμ : μ ≠ 0)
    (h : Qnode n s *ᵥ ψ = (μ : ℂ) • ψ) :
    volumeOp κ n s *ᵥ ψ ≠ volumeOp κ' n s *ᵥ ψ := by
  intro heq
  rw [volumeOp_mulVec_of_eigenvector κ s ψ μ h, volumeOp_mulVec_of_eigenvector κ' s ψ μ h] at heq
  obtain ⟨i, hi⟩ : ∃ i, ψ i ≠ 0 := Function.ne_iff.mp hψ
  have := congrFun heq i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ hi this
  have h3 : κ * Real.sqrt |μ| = κ' * Real.sqrt |μ| := by exact_mod_cast h2
  have hs : Real.sqrt |μ| ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact abs_pos.mpr hμ
  exact hκ (mul_right_cancel₀ hs h3)

end Lightlike.Rows.G2_014

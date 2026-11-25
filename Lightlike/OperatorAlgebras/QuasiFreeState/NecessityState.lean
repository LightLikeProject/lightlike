import Lightlike.OperatorAlgebras.QuasiFreeState.ComplexStructure
import Lightlike.OperatorAlgebras.QuasiFreeState.BoundedForm

/-!
# States dominated by a quasi-free state, from their kernels

Let `κ : V → ℂ` with `κ(0) = 1` define the kernel `M(φ, ψ) = exp(i ω(φ, ψ)/2) κ(ψ - φ)`. If `M` is positive
semidefinite and `2 qfKer - M` is too (`M ≤ 2 qfKer`), then there is a state `ψ` of the C*-algebra `qfAlgebra ω η` with
`ψ(W(x)) = κ(x)` (`exists_state_of_kernel`): the form `(x, y) ↦ Σ conj(y_b) M(b, a) x_a` is bounded by the Gram form of the
GNS space, hence given by a bounded operator `T` (`exists_op_of_bdd_form`), and `ψ(a) = ⟨Ω, T a Ω⟩`.
This is the construction of the states `ψ_±` of which the quasi-free state is the mean in the necessity proof.
-/

open scoped InnerProductSpace ComplexConjugate ComplexOrder

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (ω η : LinearMap.BilinForm ℝ V)

/-- The kernel `exp(i ω(φ, ψ)/2) κ(ψ - φ)` of a function `κ`. -/
noncomputable def kernelOf (κ : V → ℂ) : Matrix V V ℂ :=
  Matrix.of fun φ ψ => Complex.exp (Complex.I * ((ω φ ψ / 2 : ℝ) : ℂ)) * κ (ψ - φ)

/-- `qfKer` is the kernel of the Gaussian. -/
lemma qfKer_eq_kernelOf : qfKer ω η = kernelOf ω (fun x => ((gaussVal η x : ℝ) : ℂ)) := by
  ext φ ψ
  simp only [qfKer, kernelOf, Matrix.of_apply, gaussVal]

/-- The sesquilinear form of a kernel on finitely supported coefficients. -/
noncomputable def kform (M : Matrix V V ℂ) (x y : V →₀ ℂ) : ℂ :=
  y.sum fun b yb => x.sum fun a xa => star yb * M b a * xa

variable {ω η}

lemma kform_add_left (M : Matrix V V ℂ) (x x' y : V →₀ ℂ) : kform M (x + x') y = kform M x y + kform M x' y := by
  unfold kform
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun b _ => ?_
  rw [Finsupp.sum_add_index' (h := fun a xa => star (y b) * M b a * xa) (fun a => by simp)
    (fun a b₁ b₂ => by ring)]

lemma kform_smul_left (M : Matrix V V ℂ) (c : ℂ) (x y : V →₀ ℂ) : kform M (c • x) y = c * kform M x y := by
  unfold kform
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun b _ => ?_
  rw [Finsupp.mul_sum, Finsupp.sum_smul_index' (by simp)]
  refine Finsupp.sum_congr fun a _ => ?_
  simp only [smul_eq_mul]; ring

lemma kform_add_right (M : Matrix V V ℂ) (x y y' : V →₀ ℂ) : kform M x (y + y') = kform M x y + kform M x y' := by
  unfold kform
  rw [Finsupp.sum_add_index' (fun b => by simp) (fun b b₁ b₂ => by
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib])]

lemma kform_smul_right (M : Matrix V V ℂ) (c : ℂ) (x y : V →₀ ℂ) :
    kform M x (c • y) = conj c * kform M x y := by
  unfold kform
  rw [Finsupp.sum_smul_index' (by simp [Finsupp.sum]), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun b _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  simp only [smul_eq_mul, star_mul', Complex.star_def]; ring


lemma kform_conj {M : Matrix V V ℂ} (hM : M.IsHermitian) (x y : V →₀ ℂ) :
    conj (kform M x y) = kform M y x := by
  unfold kform
  rw [Finsupp.sum, map_sum]
  simp only [Finsupp.sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : star (M b a) = M a b := by
    have := congrFun (congrFun hM a) b
    simpa using this
  simp only [map_mul, Complex.conj_conj, Complex.star_def] at h ⊢
  rw [h]
  ring

/-- The Gram form of the GNS vectors is the form of `qfKer`. -/
lemma inner_qfPhi [Fact (qfKerM ω η).PosSemidef] (hω : ∀ a b, ω a b = -ω b a) (x y : V →₀ ℂ) :
    ⟪qfPhi ω η y, qfPhi ω η x⟫_ℂ = kform (qfKer ω η) x y := by
  unfold qfPhi kform
  simp only [Finsupp.linearCombination_apply]
  rw [Finsupp.sum, Finsupp.sum, sum_inner]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_sum]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_kq ω η hω]
  simp only [Complex.star_def]
  ring


lemma kform_sub_matrix (A B : Matrix V V ℂ) (x y : V →₀ ℂ) : kform (A - B) x y = kform A x y - kform B x y := by
  unfold kform
  rw [← Finsupp.sum_sub]
  refine Finsupp.sum_congr fun b _ => ?_
  rw [← Finsupp.sum_sub]
  refine Finsupp.sum_congr fun a _ => ?_
  simp [Matrix.sub_apply]; ring

lemma kform_smul_matrix (c : ℂ) (A : Matrix V V ℂ) (x y : V →₀ ℂ) : kform (c • A) x y = c * kform A x y := by
  unfold kform
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun b _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  simp [Matrix.smul_apply]; ring

/-- **The bound of a dominated form**: `|β(x, y)| ≤ 2 ‖ι x‖ ‖ι y‖` when `0 ≤ M ≤ 2 qfKer`. -/
lemma kform_bound [Fact (qfKerM ω η).PosSemidef] (hω : ∀ a b, ω a b = -ω b a) (κ : V → ℂ)
    (hpos : (kernelOf ω κ).PosSemidef) (hdom : ((2 : ℂ) • qfKer ω η - kernelOf ω κ).PosSemidef)
    (x y : V →₀ ℂ) :
    ‖kform (kernelOf ω κ) x y‖ ≤ 2 * ‖qfPhi ω η x‖ * ‖qfPhi ω η y‖ := by
  set M := kernelOf ω κ with hM
  have hre : ∀ z : V →₀ ℂ, 0 ≤ (kform M z z).re ∧ (kform M z z).re ≤ 2 * ‖qfPhi ω η z‖ ^ 2 := fun z => by
    have h1 : 0 ≤ kform M z z := hpos.2 z
    have h2 : 0 ≤ kform ((2 : ℂ) • qfKer ω η - M) z z := hdom.2 z
    rw [kform_sub_matrix, kform_smul_matrix, ← inner_qfPhi hω z z] at h2
    rw [inner_self_eq_norm_sq_to_K] at h2
    refine ⟨(Complex.nonneg_iff.1 h1).1, ?_⟩
    have := (Complex.nonneg_iff.1 h2).1
    simp at this
    have e : (((‖qfPhi ω η z‖ : ℝ) : ℂ) ^ 2).re = ‖qfPhi ω η z‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [e] at this
    linarith
  letI c : PreInnerProductSpace.Core ℂ (V →₀ ℂ) :=
    { inner := fun x y => kform M y x
      conj_inner_symm := fun x y => by
        show conj (kform M x y) = kform M y x
        exact kform_conj hpos.1 x y
      re_inner_nonneg := fun x => (hre x).1
      add_left := fun x x' y => kform_add_right M y x x'
      smul_left := fun x y r => kform_smul_right M r y x }
  have hcs := InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  change ‖kform M y x‖ * ‖kform M x y‖ ≤ (kform M x x).re * (kform M y y).re at hcs
  have hsym : ‖kform M y x‖ = ‖kform M x y‖ := by
    rw [← kform_conj hpos.1 x y, Complex.norm_conj]
  rw [hsym] at hcs
  have h2 : ‖kform M x y‖ ^ 2 ≤ (2 * ‖qfPhi ω η x‖) ^ 2 * 0 + (2 * ‖qfPhi ω η x‖ * ‖qfPhi ω η y‖) ^ 2 := by
    have hx := hre x
    have hy := hre y
    nlinarith [mul_le_mul hx.2 hy.2 hy.1 (by positivity)]
  have h3 : ‖kform M x y‖ ^ 2 ≤ (2 * ‖qfPhi ω η x‖ * ‖qfPhi ω η y‖) ^ 2 := by
    simpa using h2
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h3


lemma kform_twNormSq (κ : V → ℂ) (hω : ∀ a b, ω a b = -ω b a) (x : V →₀ ℂ) :
    Finsupp.linearCombination ℂ κ (twNormSq ω x) = kform (kernelOf ω κ) x x := by
  unfold twNormSq kform
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun φ _ => ?_
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun ψ _ => ?_
  rw [Finsupp.linearCombination_single]
  have h1 : ω (-φ) ψ = -ω φ ψ := by simp
  have h2 : -φ + ψ = ψ - φ := by abel
  simp only [kernelOf, Matrix.of_apply, h1, h2, smul_eq_mul, Complex.star_def]
  push_cast
  ring_nf

/-- **A state from a dominated kernel**: if `κ(0) = 1`, the kernel `kernelOf ω κ` is positive semidefinite and bounded by
`2 qfKer`, then `ψ(a) = ⟨Ω, T a Ω⟩` is a state of `qfAlgebra` with `ψ(W(x)) = κ(x)`. -/
theorem exists_state_of_kernel [Fact (qfKerM ω η).PosSemidef] (hω : ∀ a b, ω a b = -ω b a) (κ : V → ℂ)
    (hκ0 : κ 0 = 1) (hpos : (kernelOf ω κ).PosSemidef)
    (hdom : ((2 : ℂ) • qfKer ω η - kernelOf ω κ).PosSemidef) :
    ∃ ψ : qfAlgebra ω η hω →ₗ[ℂ] ℂ, IsState ψ ∧ ∀ x, ψ (qfWA ω η hω x) = κ x := by
  have hd : DenseRange (qfPhi ω η) := by
    have h := dense_range_qfPhi ω η
    rwa [LinearMap.coe_range] at h
  obtain ⟨T, hT⟩ := exists_op_of_bdd_form (qfPhi ω η) hd (kform (kernelOf ω κ)) 2 (by norm_num)
    (kform_bound hω κ hpos hdom) (kform_add_left _) (kform_smul_left _) (kform_add_right _)
    (kform_smul_right _)
  let ψ : qfAlgebra ω η hω →ₗ[ℂ] ℂ :=
    { toFun := fun a => ⟪qfVac ω η, T ((a : QFSpace ω η →L[ℂ] QFSpace ω η) (qfVac ω η))⟫_ℂ
      map_add' := fun a b => by simp [inner_add_right]
      map_smul' := fun c a => by simp [inner_smul_right] }
  have hΩ : qfVac ω η = qfPhi ω η (Finsupp.single 0 1) := by
    rw [qfPhi_single]; rfl
  have hψW : ∀ x, ψ (qfWA ω η hω x) = κ x := fun x => by
    show ⟪qfVac ω η, T ((qfOp ω η hω x) (qfVac ω η))⟫_ℂ = κ x
    have h1 : (qfOp ω η hω x) (qfVac ω η) = qfPhi ω η (Finsupp.single x 1) := by
      rw [qfPhi_single]; exact qfW_vac ω η hω x
    rw [h1, hΩ, hT]
    simp [kform, kernelOf, hκ0]
  refine ⟨ψ, ⟨?_, ?_⟩, hψW⟩
  · have : (1 : qfAlgebra ω η hω) = qfWA ω η hω 0 := ((isWeylSystem_qfWA ω η hω).map_zero).symm
    rw [this, hψW, hκ0]
  · intro a
    have hlc : ψ.comp (Finsupp.linearCombination ℂ (qfWA ω η hω)) = Finsupp.linearCombination ℂ κ := by
      apply Finsupp.lhom_ext
      intro z c
      simp [hψW]
    have hspan : ((Submodule.span ℂ (Set.range (qfWA ω η hω)) : Submodule ℂ (qfAlgebra ω η hω)) :
        Set (qfAlgebra ω η hω)) ⊆ {a | 0 ≤ ψ (star a * a)} := by
      intro z hz
      obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hz
      have hz' : z = Finsupp.linearCombination ℂ (qfWA ω η hω) c := by
        rw [Finsupp.linearCombination_apply]; exact hc.symm
      show 0 ≤ ψ (star z * z)
      rw [hz', ← linearCombination_twNormSq' (isWeylSystem_qfWA ω η hω) c]
      have := LinearMap.congr_fun hlc (twNormSq ω c)
      simp only [LinearMap.comp_apply] at this
      rw [this, kform_twNormSq κ hω]
      exact hpos.2 c
    have hcont : Continuous (fun a : qfAlgebra ω η hω => ψ (star a * a)) := by
      show Continuous (fun b : qfAlgebra ω η hω => ⟪qfVac ω η, T ((star (b : QFSpace ω η →L[ℂ] QFSpace ω η) *
        (b : QFSpace ω η →L[ℂ] QFSpace ω η)) (qfVac ω η))⟫_ℂ)
      exact continuous_const.inner (T.continuous.comp
        ((ContinuousLinearMap.apply ℂ (QFSpace ω η) (qfVac ω η)).continuous.comp
          ((continuous_star.comp continuous_subtype_val).mul continuous_subtype_val)))
    have hclosed : IsClosed {a : qfAlgebra ω η hω | 0 ≤ ψ (star a * a)} :=
      isClosed_le continuous_const hcont
    exact (hclosed.closure_subset_iff.2 hspan)
      ((dense_span_qfWA ω η hω).closure_eq ▸ Set.mem_univ a)

end Lightlike.OperatorAlgebras.QuasiFreeState

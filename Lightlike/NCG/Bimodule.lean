import Lightlike.NCG.FiniteSpectralTriple
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Idempotents

/-!
# The bimodule of a real finite spectral triple and the links of its Krajewski diagram

M. Paschke, A. Sitarz, arXiv:q-alg/9612029, Section 2 (read): for central orthogonal projections `Pᵢ` of `A` with
`∑ Pᵢ = 1` (for `A = ⊕ Mₙᵢ(ℂ)` the units of the summands), the subspaces `Hᵢⱼ = Pᵢ H Pⱼ`, where `ξ b = J π(b*) J ξ`,
decompose `H` (Lemma 1, p. 2); `J` maps `Hᵢⱼ` onto `Hⱼᵢ`, so `dim Hᵢⱼ = dim Hⱼᵢ` (Lemma 4, p. 3); a grading preserves
each `Hᵢⱼ` (Lemma 3, p. 3, first half); and the first-order condition forces `Dᵢⱼ,ₖₗ = Pᵢⱼ D Pₖₗ = 0` unless `i = k` or
`j = l` (Lemma 6, p. 5). In Krajewski's language (arXiv:hep-th/9701081, Section 4.1, p. 17) the `Hᵢⱼ` are the vertices
of the diagram and `D` joins only vertices in the same row or column.

* `CentralPartition A ι`;
* `rightOp`, `leftP`, `rightP`, `proj` (`Eᵢⱼ = π(Pᵢ) J π(Pⱼ) J`), `Hsub`;
* `completeOrthogonalIdempotents_proj` (Lemma 1), `J_mem_Hsub`, `finrank_Hsub_symm` (Lemma 4),
  `grading_mem_Hsub` (Lemma 3, first half), `proj_D_proj_eq_zero` (Lemma 6).
-/

open scoped InnerProductSpace

namespace Lightlike.NCG

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A central partition of unity** of `A`: self-adjoint central elements `Pᵢ` with `Pᵢ Pⱼ = δᵢⱼ Pᵢ` and
`∑ Pᵢ = 1`. -/
structure CentralPartition (A ι : Type*) [Ring A] [StarRing A] [Fintype ι] [DecidableEq ι] where
  /-- The projections. -/
  P : ι → A
  /-- `Pᵢ* = Pᵢ`. -/
  star_P : ∀ i, star (P i) = P i
  /-- `Pᵢ Pⱼ = δᵢⱼ Pᵢ`. -/
  mul_P : ∀ i j, P i * P j = if i = j then P i else 0
  /-- `∑ Pᵢ = 1`. -/
  sum_P : ∑ i, P i = 1
  /-- `Pᵢ` is central. -/
  central : ∀ i a, P i * a = a * P i

variable {T : FiniteSpectralTriple A H}

/-- **The right action** `ξ ↦ J π(b) J ξ`, a linear map (`J` is antilinear). -/
def rightOp (R : RealStructure T) (b : A) : H →ₗ[ℂ] H where
  toFun x := R.J (T.π b (R.J x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    simp only [LinearMap.map_smulₛₗ, ContinuousLinearMap.map_smul, RingHom.id_apply, starRingEnd_self_apply]

lemma rightOp_apply (R : RealStructure T) (b : A) (x : H) : rightOp R b x = R.J (T.π b (R.J x)) := rfl

lemma rightOp_mul (R : RealStructure T) (b c : A) : rightOp R (b * c) = rightOp R b * rightOp R c := by
  ext x
  simp only [rightOp_apply, Module.End.mul_apply, map_mul, ContinuousLinearMap.mul_apply, R.J_J]

lemma rightOp_one (R : RealStructure T) : rightOp R 1 = 1 := by
  ext x
  simp only [rightOp_apply, map_one, ContinuousLinearMap.one_apply, R.J_J, Module.End.one_apply]

lemma rightOp_sum (R : RealStructure T) (b : ι → A) : rightOp R (∑ i, b i) = ∑ i, rightOp R (b i) := by
  ext x
  simp only [rightOp_apply, map_sum, ContinuousLinearMap.sum_apply, LinearMap.sum_apply]

variable (T) in
/-- `π(Pᵢ)`, as a linear map. -/
def leftP (C : CentralPartition A ι) (i : ι) : H →ₗ[ℂ] H := (T.π (C.P i) : H →L[ℂ] H)

/-- `J π(Pⱼ) J`. -/
def rightP (R : RealStructure T) (C : CentralPartition A ι) (j : ι) : H →ₗ[ℂ] H := rightOp R (C.P j)

/-- **The projection onto `Hᵢⱼ`**, `Eᵢⱼ = π(Pᵢ) J π(Pⱼ) J`. -/
def proj (R : RealStructure T) (C : CentralPartition A ι) (p : ι × ι) : H →ₗ[ℂ] H :=
  leftP T C p.1 * rightP R C p.2

/-- **The vertex** `Hᵢⱼ = π(Pᵢ) J π(Pⱼ) J H`. -/
def Hsub (R : RealStructure T) (C : CentralPartition A ι) (i j : ι) : Submodule ℂ H :=
  LinearMap.range (proj R C (i, j))

lemma leftP_apply (C : CentralPartition A ι) (i : ι) (x : H) : leftP T C i x = T.π (C.P i) x := rfl

lemma rightP_apply (R : RealStructure T) (C : CentralPartition A ι) (j : ι) (x : H) :
    rightP R C j x = R.J (T.π (C.P j) (R.J x)) := rfl

lemma proj_apply (R : RealStructure T) (C : CentralPartition A ι) (i j : ι) (x : H) :
    proj R C (i, j) x = leftP T C i (rightP R C j x) := rfl

lemma leftP_leftP (C : CentralPartition A ι) (i k : ι) (x : H) :
    leftP T C i (leftP T C k x) = if i = k then leftP T C i x else 0 := by
  simp only [leftP_apply]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, C.mul_P]
  split_ifs <;> simp

lemma rightP_rightP (R : RealStructure T) (C : CentralPartition A ι) (j l : ι) (x : H) :
    rightP R C j (rightP R C l x) = if j = l then rightP R C j x else 0 := by
  have := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_mul R (C.P j) (C.P l))
  simp only [Module.End.mul_apply] at this
  rw [rightP, rightP, ← this, C.mul_P]
  split_ifs
  · rfl
  · simp [rightOp_apply]

/-- The left and the right actions commute (the order-zero condition). -/
lemma rightP_leftP (R : RealStructure T) (C : CentralPartition A ι) (i j : ι) (x : H) :
    rightP R C j (leftP T C i x) = leftP T C i (rightP R C j x) :=
  (R.order_zero (C.P i) (C.P j) x).symm

lemma sum_leftP (C : CentralPartition A ι) (x : H) : ∑ i, leftP T C i x = x := by
  simp only [leftP_apply]
  rw [← ContinuousLinearMap.sum_apply, ← map_sum, C.sum_P, map_one, ContinuousLinearMap.one_apply]

lemma sum_rightP (R : RealStructure T) (C : CentralPartition A ι) (x : H) : ∑ j, rightP R C j x = x := by
  have := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_sum R C.P)
  simp only [LinearMap.sum_apply, C.sum_P, rightOp_one, Module.End.one_apply] at this
  exact this.symm

/-- **Paschke-Sitarz, Lemma 1**: the `Eᵢⱼ` are complete orthogonal idempotents, so `H = ⊕ Hᵢⱼ`. -/
theorem completeOrthogonalIdempotents_proj (R : RealStructure T) (C : CentralPartition A ι) :
    CompleteOrthogonalIdempotents (proj R C) := by
  have hmul : ∀ p q : ι × ι, proj R C p * proj R C q = if p = q then proj R C p else 0 := by
    rintro ⟨i, j⟩ ⟨k, l⟩
    ext x
    simp only [Module.End.mul_apply, proj_apply]
    rw [rightP_leftP, leftP_leftP, rightP_rightP]
    by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl, proj_apply]
  refine ⟨⟨fun p => ?_, fun p q hpq => ?_⟩, ?_⟩
  · show proj R C p * proj R C p = proj R C p
    rw [hmul, if_pos rfl]
  · show proj R C p * proj R C q = 0
    rw [hmul, if_neg hpq]
  · ext x
    simp only [LinearMap.sum_apply, Fintype.sum_prod_type, proj_apply, Module.End.one_apply]
    simp only [← map_sum, sum_rightP, sum_leftP]

/-- `J Eᵢⱼ J = Eⱼᵢ`. -/
lemma J_proj_J (R : RealStructure T) (C : CentralPartition A ι) (i j : ι) (x : H) :
    R.J (proj R C (i, j) (R.J x)) = proj R C (j, i) x := by
  have h := R.order_zero (C.P j) (C.P i) x
  simp only [proj_apply, leftP_apply, rightP_apply, R.J_J] at h ⊢
  exact h.symm

/-- **Paschke-Sitarz, Lemma 4**: `J` maps `Hᵢⱼ` into `Hⱼᵢ`. -/
theorem J_mem_Hsub (R : RealStructure T) (C : CentralPartition A ι) {i j : ι} {x : H} (hx : x ∈ Hsub R C i j) :
    R.J x ∈ Hsub R C j i := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨R.J y, by rw [← J_proj_J R C i j (R.J y), R.J_J]⟩

/-- `J` as a real-linear equivalence `Hᵢⱼ ≃ Hⱼᵢ`. -/
def JEquiv (R : RealStructure T) (C : CentralPartition A ι) (i j : ι) : Hsub R C i j ≃ₗ[ℝ] Hsub R C j i where
  toFun x := ⟨R.J (x : H), J_mem_Hsub R C x.2⟩
  invFun x := ⟨R.J (x : H), J_mem_Hsub R C x.2⟩
  map_add' x y := Subtype.ext (map_add R.J (x : H) y)
  map_smul' r x := Subtype.ext <| by
    show R.J ((r : ℂ) • (x : H)) = (r : ℂ) • R.J x
    rw [LinearMap.map_smulₛₗ, Complex.conj_ofReal]
  left_inv x := Subtype.ext (R.J_J (x : H))
  right_inv x := Subtype.ext (R.J_J (x : H))

/-- **Paschke-Sitarz, Lemma 4**: `dim Hᵢⱼ = dim Hⱼᵢ`, the multiplicity matrix is symmetric. -/
theorem finrank_Hsub_symm (R : RealStructure T) (C : CentralPartition A ι) (i j : ι) :
    Module.finrank ℂ (Hsub R C i j) = Module.finrank ℂ (Hsub R C j i) := by
  have h := (JEquiv R C i j).finrank_eq
  rw [finrank_real_of_complex, finrank_real_of_complex] at h
  omega

/-- **Paschke-Sitarz, Lemma 3** (first half): a grading maps `Hᵢⱼ` into itself. -/
theorem grading_mem_Hsub (R : RealStructure T) (G : Grading T R) (C : CentralPartition A ι) {i j : ι} {x : H}
    (hx : x ∈ Hsub R C i j) : G.γ x ∈ Hsub R C i j := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨G.γ y, ?_⟩
  have hπ : ∀ a z, G.γ (T.π a z) = T.π a (G.γ z) := fun a z => by
    have := congrArg (fun f : H →L[ℂ] H => f z) (G.γ_π a)
    simpa only [ContinuousLinearMap.mul_apply] using this
  simp only [proj_apply, leftP_apply, rightP_apply, hπ, G.γ_J]

/-- **Paschke-Sitarz, Lemma 6**: the first-order condition forces `Eᵢⱼ D Eₖₗ = 0` unless `i = k` or `j = l`: `D` joins
only vertices of the Krajewski diagram in the same row or column. -/
theorem proj_D_proj_eq_zero (R : RealStructure T) (C : CentralPartition A ι) {i j k l : ι} (hik : i ≠ k)
    (hjl : j ≠ l) (x : H) : proj R C (i, j) (T.D (proj R C (k, l) x)) = 0 := by
  set y := proj R C (k, l) x with hy
  have hLy : leftP T C k y = y := by
    rw [hy, proj_apply, leftP_leftP, if_pos rfl]
  have hRy : rightP R C l y = y := by
    rw [hy, proj_apply, rightP_leftP, rightP_rightP, if_pos rfl]
  have hRy' : R.J (T.π (C.P l) (R.J y)) = y := hRy
  have hLy' : T.π (C.P k) y = y := hLy
  have hfo := R.first_order (C.P k) (C.P l) y
  simp only [FiniteSpectralTriple.comm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, hRy',
    hLy'] at hfo
  have key : T.D y - leftP T C k (T.D y) = rightP R C l (T.D y) - rightP R C l (leftP T C k (T.D y)) := by
    rw [← map_sub]; exact hfo
  have := congrArg (fun z => proj R C (i, j) z) key
  simp only [map_sub, proj_apply] at this
  rw [rightP_leftP R C k j, leftP_leftP, if_neg hik, rightP_rightP, if_neg hjl, rightP_rightP, if_neg hjl] at this
  simp only [map_zero, sub_zero, sub_self] at this
  rw [proj_apply]
  exact this

end Lightlike.NCG

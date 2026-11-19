import Lightlike.NCG.Chirality
import Lightlike.NCG.MixedSummands

/-!
# The signs of the chirality for real summands (Krajewski's Table 1)

T. Krajewski, arXiv:hep-th/9701081, Section 3.3, p. 14 (read): "In the real case, it is still given by a symmetric matrix
with entries in `ℤ` whose indices label irreducibles representations of `A`. However, it is no longer the intersection
form and the signs of its entries satisfy additional requirements that are summarized ... in table 1", with
`μ_{iαj} μ_{iᾱj} ≥ 0` (`i` complex, `j` real or quaternionic) and `μ_{iαjβ} μ_{iᾱjβ̄} ≥ 0` (`i`, `j` complex), where
"the indices `α` and `β` distinguish a representation from its complex conjugate".

A grading of a real triple is a grading of its complexification (`Complexification.grading`), and an orientable one
stays orientable with `X_p = φ(x_p)`, `Y_p = φ(y_p)` (`Complexification.isOrientable`). On the complexified model `γ`
is the sign `c_kl` on each vertex (`Chirality.lean`), and `φ(x)` on the conjugate block is the complex conjugate of `φ(x)`
on the fundamental one; on a quaternionic block `ι(q)₁₁ = conj ι(q)₀₀`. So `c` agrees on a vertex and its conjugate
vertex, and the signed multiplicities `μ_kl = c_kl r_kl` satisfy Table 1's sign conditions.

* `IsOrientableA`, `Complexification.grading`, `Complexification.isOrientable`;
* `chiScalarAt_conj`: the scalar on a conjugate corner is the conjugate scalar;
* `Xm`, `Rm`, `muSigned`, `exists_ne_zero_of_multiplicity`, `muSigned_mul_nonneg_of`, `idxH_zero`: the signed
  multiplicities of a mixed algebra;
* `table1_complex_complex`, `table1_complex_real`, `table1_complex_quat`, `muSigned_symm`, `table1_real_complex`,
  `table1_quat_complex`: Table 1's sign conditions.
-/

namespace Lightlike.NCG

noncomputable section

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple A H} (R : RealStructure T)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

/-- **An orientable grading of a real triple**: `γ = ∑_p π(x_p) J π(y_p) J` with `x_p, y_p ∈ A`. -/
def IsOrientableA (G : Grading T R) {m : ℕ} (x y : Fin m → A) : Prop :=
  ∀ v, G.γ v = ∑ p, T.π (x p) (rightOp R (y p) v)

/-- `γ` commutes with the complex span of `π(A)`. -/
lemma grading_comm_of_mem_span (G : Grading T R) {X : H →L[ℂ] H} (hX : X ∈ Submodule.span ℂ (Set.range T.π)) :
    G.γ * X = X * G.γ := by
  induction hX using Submodule.span_induction with
  | mem s hs => obtain ⟨a, rfl⟩ := hs; exact G.γ_π a
  | zero => rw [mul_zero, zero_mul]
  | add X₁ X₂ _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
  | smul c X _ h => rw [mul_smul_comm, smul_mul_assoc, h]

/-- **A grading of the complexification.** -/
def Complexification.grading (C : Complexification T d) (G : Grading T R) : Grading C.triple (C.realStructure R) where
  γ := G.γ
  isSelfAdjoint_γ := G.isSelfAdjoint_γ
  γ_γ := G.γ_γ
  γ_J := G.γ_J
  γ_π a := grading_comm_of_mem_span R G (C.mem_span a)
  D_γ := G.D_γ

/-- **Orientability passes to the complexification**, with `X_p = φ(x_p)`, `Y_p = φ(y_p)`. -/
theorem Complexification.isOrientable (C : Complexification T d) (G : Grading T R) {m : ℕ} {x y : Fin m → A}
    (hG : IsOrientableA R G x y) :
    IsOrientable (C.realStructure R) (C.grading R G) (fun p => C.φ (x p)) (fun p => C.φ (y p)) := by
  intro v
  show G.γ v = ∑ p, C.σ (C.φ (x p)) (R.J (C.σ (C.φ (y p)) (R.J v)))
  simp only [← C.pi_eq]
  exact hG v

/-- **The scalar on a conjugate corner is the conjugate scalar.** -/
lemma chiScalarAt_conj {n : ι → ℕ} {m : ℕ} (X Y : Fin m → MatSum n) {k k' l l' : ι} {α : Fin (n k)}
    {α' : Fin (n k')} {β : Fin (n l)} {β' : Fin (n l')}
    (hX : ∀ p, X p k' α' α' = starRingEnd ℂ (X p k α α)) (hY : ∀ p, Y p l' β' β' = starRingEnd ℂ (Y p l β β)) :
    chiScalarAt X Y k' l' α' β' = starRingEnd ℂ (chiScalarAt X Y k l α β) := by
  simp only [chiScalarAt, hX, hY, map_sum, map_mul]

section Mixed

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι₃]
  [DecidableEq ι₃] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ} {n₃ : ι₃ → ℕ} [∀ i, NeZero (n₁ i)] [∀ i, NeZero (n₂ i)]
  [∀ i, NeZero (n₃ i)]
variable {T' : FiniteSpectralTriple (MatSumMixed n₁ n₂ n₃) H} (R' : RealStructure T') (G : Grading T' R')
variable {m : ℕ} (x y : Fin m → MatSumMixed n₁ n₂ n₃)

/-- The coefficients `X_p = φ(x_p)` of the complexified chirality. -/
abbrev Xm : Fin m → MatSum (Sum.elim n₁ (dMixed T')) := fun p => phiMixed T' (x p)

/-- The real structure of the complexified mixed triple. -/
abbrev Rm : RealStructure (mixedComplexification T').triple := (mixedComplexification T').realStructure R'

/-- The signed multiplicity `μ_kl = Re(c_kl) r_kl` of the complexified mixed triple. -/
def muSigned (k l : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) : ℝ :=
  (chiScalar (Xm x) (Xm y) k l).re * multiplicity (Rm R') k l

variable {x y}

/-- A nonzero multiplicity space has a nonzero vector. -/
lemma exists_ne_zero_of_multiplicity {k l : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)} (h : multiplicity (Rm R') k l ≠ 0) :
    ∃ v ∈ Vsub (Rm R') k l, v ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun hb => h ?_
  rw [multiplicity, hb, finrank_bot]

/-- **The chirality agrees on conjugate vertices** whenever the scalars are conjugate: the product of the signed
multiplicities is `≥ 0`. -/
lemma muSigned_mul_nonneg_of (hG : IsOrientableA R' G x y) {k k' l l' : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)}
    (hc : ∀ v ∈ Vsub (Rm R') k l, v ≠ 0 →
      chiScalar (Xm x) (Xm y) k' l' = starRingEnd ℂ (chiScalar (Xm x) (Xm y) k l)) :
    0 ≤ muSigned R' x y k l * muSigned R' x y k' l' := by
  by_cases h0 : multiplicity (Rm R') k l = 0
  · simp [muSigned, h0]
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_multiplicity R' h0
  have hG' := (mixedComplexification T').isOrientable R' G hG
  have hℂ := (mixedComplexification T').isComplexLinear
  have hreal : starRingEnd ℂ (chiScalar (Xm x) (Xm y) k l) = chiScalar (Xm x) (Xm y) k l :=
    conj_chiScalar (Rm R') hℂ ((mixedComplexification T').grading R' G) hG' hv hv0
  rw [muSigned, muSigned, hc v hv hv0, hreal]
  have : 0 ≤ (chiScalar (Xm x) (Xm y) k l).re * (chiScalar (Xm x) (Xm y) k l).re := mul_self_nonneg _
  have hm : (0 : ℝ) ≤ multiplicity (Rm R') k l * multiplicity (Rm R') k' l' := by positivity
  nlinarith

variable (x y)

/-- `idxH j 0 = (0, 0)`. -/
lemma idxH_zero {ι : Type*} {n : ι → ℕ} [∀ i, NeZero (n i)] (j : ι) :
    idxH (n := n) j (0 : Fin (n j * 2)) = (0, 0) := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [idxH, finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- **Table 1, complex against complex** (Krajewski, Section 3.3, p. 14: `μ_{iαjβ} μ_{iᾱjβ̄} ≥ 0`). -/
theorem table1_complex_complex (hG : IsOrientableA R' G x y) (i j : ι₂) (b : Bool)
    (h₁ : psiPart (psi₂ T') true (Pi.single i 1) ≠ 0) (h₂ : psiPart (psi₂ T') false (Pi.single i 1) ≠ 0)
    (h₃ : psiPart (psi₂ T') b (Pi.single j 1) ≠ 0) (h₄ : psiPart (psi₂ T') (!b) (Pi.single j 1) ≠ 0) :
    0 ≤ muSigned R' x y (.inr (.inl ⟨(i, true), h₁⟩)) (.inr (.inl ⟨(j, b), h₃⟩)) *
      muSigned R' x y (.inr (.inl ⟨(i, false), h₂⟩)) (.inr (.inl ⟨(j, !b), h₄⟩)) := by
  refine muSigned_mul_nonneg_of R' G hG fun v _ _ => ?_
  refine chiScalarAt_conj _ _ (fun p => ?_) (fun p => ?_)
  · show phiPAll (x p).2.1 (i, false) 0 0 = starRingEnd ℂ (phiPAll (x p).2.1 (i, true) 0 0)
    simp [phiPAll]
  · show phiPAll (y p).2.1 (j, !b) 0 0 = starRingEnd ℂ (phiPAll (y p).2.1 (j, b) 0 0)
    cases b <;> simp [phiPAll]

/-- **Table 1, complex against real** (Krajewski, Section 3.3, p. 14: `μ_{iαj} μ_{iᾱj} ≥ 0`). -/
theorem table1_complex_real (hG : IsOrientableA R' G x y) (i : ι₂) (j : ι₁)
    (h₁ : psiPart (psi₂ T') true (Pi.single i 1) ≠ 0) (h₂ : psiPart (psi₂ T') false (Pi.single i 1) ≠ 0) :
    0 ≤ muSigned R' x y (.inr (.inl ⟨(i, true), h₁⟩)) (.inl j) *
      muSigned R' x y (.inr (.inl ⟨(i, false), h₂⟩)) (.inl j) := by
  refine muSigned_mul_nonneg_of R' G hG fun v _ _ => ?_
  refine chiScalarAt_conj _ _ (fun p => ?_) (fun p => ?_)
  · show phiPAll (x p).2.1 (i, false) 0 0 = starRingEnd ℂ (phiPAll (x p).2.1 (i, true) 0 0)
    simp [phiPAll]
  · show phiR (y p).1 j 0 0 = starRingEnd ℂ (phiR (y p).1 j 0 0)
    simp [phiR_apply, ofRealM]

/-- **Table 1, complex against quaternionic** (Krajewski, Section 3.3, p. 14: `μ_{iαj} μ_{iᾱj} ≥ 0`): on `ℂ²ⁿ` the
entries `ι(q)₀₀` and `ι(q)₁₁` are conjugate. -/
theorem table1_complex_quat (hG : IsOrientableA R' G x y) (i : ι₂) (j : ι₃)
    (h₁ : psiPart (psi₂ T') true (Pi.single i 1) ≠ 0) (h₂ : psiPart (psi₂ T') false (Pi.single i 1) ≠ 0) :
    0 ≤ muSigned R' x y (.inr (.inl ⟨(i, true), h₁⟩)) (.inr (.inr j)) *
      muSigned R' x y (.inr (.inl ⟨(i, false), h₂⟩)) (.inr (.inr j)) := by
  refine muSigned_mul_nonneg_of R' G hG fun v hv hv0 => ?_
  have hG' := (mixedComplexification T').isOrientable R' G hG
  have hℂ := (mixedComplexification T').isComplexLinear
  set e₁ : Fin (n₃ j * 2) := finProdFinEquiv (0, 1)
  have hcorner : chiScalarAt (Xm x) (Xm y) (.inr (.inl ⟨(i, true), h₁⟩)) (.inr (.inr j)) 0 e₁ =
      chiScalar (Xm x) (Xm y) (.inr (.inl ⟨(i, true), h₁⟩)) (.inr (.inr j)) :=
    chiScalarAt_eq (Rm R') hℂ ((mixedComplexification T').grading R' G) hG' hv hv0 0 e₁
  rw [← hcorner]
  refine chiScalarAt_conj _ _ (fun p => ?_) (fun p => ?_)
  · show phiPAll (x p).2.1 (i, false) 0 0 = starRingEnd ℂ (phiPAll (x p).2.1 (i, true) 0 0)
    simp [phiPAll]
  · show phiH (y p).2.2 j 0 0 = starRingEnd ℂ (phiH (y p).2.2 j e₁ e₁)
    have he : idxH (n := n₃) j e₁ = (0, 1) := Equiv.symm_apply_apply _ _
    rw [phiH_apply, phiHFun_apply, phiHFun_apply, idxH_zero, he]
    simp only [quatToMat_apply]
    simp [Complex.ext_iff]

/-- **The signed multiplicity matrix is symmetric** (Krajewski, Section 3.3, p. 13: `χᵢⱼ = χⱼᵢ`, and `mᵢⱼ = mⱼᵢ`). -/
theorem muSigned_symm (hG : IsOrientableA R' G x y) (k l : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) :
    muSigned R' x y l k = muSigned R' x y k l := by
  have hm : multiplicity (Rm R') l k = multiplicity (Rm R') k l := multiplicity_symm (Rm R') l k
  by_cases h0 : multiplicity (Rm R') k l = 0
  · simp [muSigned, hm, h0]
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_multiplicity R' h0
  have hG' := (mixedComplexification T').isOrientable R' G hG
  have hc : chiScalar (Xm x) (Xm y) l k = chiScalar (Xm x) (Xm y) k l :=
    chiScalar_symm (Rm R') (mixedComplexification T').isComplexLinear ((mixedComplexification T').grading R' G) hG'
      hv hv0
  rw [muSigned, muSigned, hc, hm]

/-- **Table 1, real against complex** (Krajewski, Section 3.3, p. 14: `μ_{ijα} μ_{ijᾱ} ≥ 0`). -/
theorem table1_real_complex (hG : IsOrientableA R' G x y) (j : ι₁) (i : ι₂)
    (h₁ : psiPart (psi₂ T') true (Pi.single i 1) ≠ 0) (h₂ : psiPart (psi₂ T') false (Pi.single i 1) ≠ 0) :
    0 ≤ muSigned R' x y (.inl j) (.inr (.inl ⟨(i, true), h₁⟩)) *
      muSigned R' x y (.inl j) (.inr (.inl ⟨(i, false), h₂⟩)) := by
  rw [muSigned_symm R' G x y hG (.inr (.inl ⟨(i, true), h₁⟩)) (.inl j),
    muSigned_symm R' G x y hG (.inr (.inl ⟨(i, false), h₂⟩)) (.inl j)]
  exact table1_complex_real R' G x y hG i j h₁ h₂

/-- **Table 1, quaternionic against complex** (Krajewski, Section 3.3, p. 14: `μ_{ijα} μ_{ijᾱ} ≥ 0`). -/
theorem table1_quat_complex (hG : IsOrientableA R' G x y) (j : ι₃) (i : ι₂)
    (h₁ : psiPart (psi₂ T') true (Pi.single i 1) ≠ 0) (h₂ : psiPart (psi₂ T') false (Pi.single i 1) ≠ 0) :
    0 ≤ muSigned R' x y (.inr (.inr j)) (.inr (.inl ⟨(i, true), h₁⟩)) *
      muSigned R' x y (.inr (.inr j)) (.inr (.inl ⟨(i, false), h₂⟩)) := by
  rw [muSigned_symm R' G x y hG (.inr (.inl ⟨(i, true), h₁⟩)) (.inr (.inr j)),
    muSigned_symm R' G x y hG (.inr (.inl ⟨(i, false), h₂⟩)) (.inr (.inr j))]
  exact table1_complex_quat R' G x y hG i j h₁ h₂

end Mixed

end

end Lightlike.NCG

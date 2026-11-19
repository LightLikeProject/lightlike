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
  `table1_quat_complex`: Table 1's sign conditions;
* `trace_grading_of_phi`, `pR`, `phiMixed_pR`, `pH`, `eH`, `phiH_pH`, `phiMixed_pH`, `interForm`,
  `interForm_real_real`, `interForm_quat_quat`, `interForm_real_quat`: the intersection form `Tr(γ π(p) J π(q) J)` of
  minimal projections, `μ`, `4μ` and `2μ` (Table 1).
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

/-- **The intersection form through a complexification**: if `φ(p)` and `φ(q)` are sums of diagonal corners, then
`Tr(γ π(p) J π(q) J) = ∑_t ∑_u c_{k_t l_u} r_{k_t l_u}` on the complexified model. -/
theorem trace_grading_of_phi [∀ i, NeZero (d i)] (C : Complexification T d) (G : Grading T R) {m : ℕ}
    {x y : Fin m → A} (hG : IsOrientableA R G x y) (p q : A) {s s' : Type*} [Fintype s] [Fintype s'] (k : s → ι)
    (α : ∀ t, Fin (d (k t))) (l : s' → ι) (β : ∀ u, Fin (d (l u)))
    (hp : C.φ p = ∑ t, unit d (k t) (α t) (α t)) (hq : C.φ q = ∑ u, unit d (l u) (β u) (β u)) :
    LinearMap.trace ℂ H ((G.γ : H →ₗ[ℂ] H) * (T.π p : H →ₗ[ℂ] H) * rightOp R q) =
      ∑ t, ∑ u, chiScalar (fun r => C.φ (x r)) (fun r => C.φ (y r)) (k t) (l u) *
        multiplicity (C.realStructure R) (k t) (l u) := by
  have h1 : (T.π p : H →ₗ[ℂ] H) = ∑ t, lU C.triple (k t) (α t) (α t) := by
    ext v
    simp only [LinearMap.sum_apply, lU, ContinuousLinearMap.coe_coe]
    rw [C.pi_eq, hp, map_sum, ContinuousLinearMap.sum_apply]
    rfl
  have h2 : rightOp R q = ∑ u, rU (C.realStructure R) (l u) (β u) (β u) := by
    ext v
    simp only [LinearMap.sum_apply, rU, rightOp_apply]
    rw [C.pi_eq, hq, map_sum, ContinuousLinearMap.sum_apply, map_sum]
    rfl
  rw [h1, h2]
  exact trace_grading_sum (C.realStructure R) C.isComplexLinear (C.grading R G) (C.isOrientable R G hG) k α l β

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

/-- The minimal projection `E^i_{00}` of a real summand. -/
def pR (i : ι₁) : MatSumMixed n₁ n₂ n₃ := (Pi.single i (Matrix.single 0 0 1), 0, 0)

/-- **`φ(E^i_{00}) = E^{(i)}_{00}`** for a real summand. -/
lemma phiMixed_pR (i : ι₁) :
    phiMixed T' (pR i) = unit (Sum.elim n₁ (dMixed T')) (Sum.inl i) 0 0 := by
  funext q
  rcases q with k | p | j
  · show phiR (Pi.single i (Matrix.single 0 0 1) : MatSumR n₁) k = _
    simp only [unit]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same]
      show ((Pi.single k (Matrix.single 0 0 1) : MatSumR n₁) k).map (↑) = (Matrix.single (0 : Fin (n₁ k)) 0 (1 : ℂ))
      rw [Pi.single_eq_same]
      ext a b
      by_cases ha : (0 : Fin (n₁ k)) = a <;> by_cases hb : (0 : Fin (n₁ k)) = b <;>
        simp [Matrix.single_apply, ha, hb] <;> split_ifs <;> simp
    · rw [Pi.single_eq_of_ne (show (Sum.inl k : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) ≠ Sum.inl i from
        fun h => hk (Sum.inl_injective h))]
      ext a b
      simp [phiR_apply, ofRealM, Pi.single_eq_of_ne hk]
      rfl
  · show phiPAll (0 : MatSum n₂) p.1 = _
    simp only [unit]
    rw [Pi.single_eq_of_ne (show (Sum.inr (Sum.inl p) : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) ≠ Sum.inl i from
      Sum.inr_ne_inl)]
    ext a b
    simp [phiPAll]
    rfl
  · show phiH (0 : MatSumH n₃) j = _
    simp only [unit]
    rw [Pi.single_eq_of_ne (show (Sum.inr (Sum.inr j) : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) ≠ Sum.inl i from
      Sum.inr_ne_inl)]
    rw [map_zero]
    rfl

/-- The minimal projection `E^i_{00}(1)` of a quaternionic summand. -/
def pH (i : ι₃) : MatSumMixed n₁ n₂ n₃ := (0, 0, Pi.single i (Matrix.single 0 0 1))

/-- The two corners `(0, 0)` and `(0, 1)` of `ℂ²ⁿ`. -/
def eH (i : ι₃) (t : Fin 2) : Fin (n₃ i * 2) := finProdFinEquiv (0, t)

/-- **`φ(E^i_{00}(1)) = E_{(0,0)(0,0)} + E_{(0,1)(0,1)}`** on the quaternionic block: a minimal projection of `Mₙ(ℍ)` has
rank `2` in `ℂ²ⁿ`. -/
lemma phiH_pH (i : ι₃) :
    (phiH (Pi.single i (Matrix.single 0 0 1) : MatSumH n₃)) i = ∑ t, Matrix.single (eH i t) (eH i t) (1 : ℂ) := by
  ext x y
  obtain ⟨⟨a, s⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨b, u⟩, rfl⟩ := finProdFinEquiv.surjective y
  rw [phiH_apply, phiHFun_apply, Pi.single_eq_same, Matrix.sum_apply]
  simp only [idxH, Equiv.symm_apply_apply, eH, Matrix.single_apply, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
  rw [Fin.sum_univ_two]
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 0
    · subst hb
      fin_cases s <;> fin_cases u <;> simp [quatToMat_apply, Complex.ext_iff]
    · have hb' : ¬ (0 : Fin (n₃ i)) = b := fun h => hb h.symm
      simp [hb']
  · have ha' : ¬ (0 : Fin (n₃ i)) = a := fun h => ha h.symm
    simp [ha']

/-- **`φ(pH i)` is the sum of the two corners** of the quaternionic block. -/
lemma phiMixed_pH (i : ι₃) :
    phiMixed T' (pH i) = ∑ t, unit (Sum.elim n₁ (dMixed T')) (Sum.inr (Sum.inr i)) (eH i t) (eH i t) := by
  funext q
  rw [Finset.sum_apply]
  rcases q with k | p | j
  · show phiR (0 : MatSumR n₁) k = _
    simp only [unit]
    refine Eq.trans ?_ (Finset.sum_eq_zero fun t _ => Pi.single_eq_of_ne
      (show (Sum.inl k : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) ≠ Sum.inr (Sum.inr i) from Sum.inl_ne_inr) _).symm
    rw [map_zero]
    rfl
  · show phiPAll (0 : MatSum n₂) p.1 = _
    simp only [unit]
    refine Eq.trans ?_ (Finset.sum_eq_zero fun t _ => Pi.single_eq_of_ne
      (show (Sum.inr (Sum.inl p) : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) ≠ Sum.inr (Sum.inr i) from
        fun h => Sum.inl_ne_inr (Sum.inr_injective h)) _).symm
    exact phiPAll_zero _
  · show phiH (Pi.single i (Matrix.single 0 0 1) : MatSumH n₃) j = _
    simp only [unit]
    by_cases hj : j = i
    · subst hj
      exact (phiH_pH j).trans (Finset.sum_congr rfl fun t _ =>
        (Pi.single_eq_same (M := fun q => Matrix (Fin (Sum.elim n₁ (dMixed T') q)) (Fin (Sum.elim n₁ (dMixed T') q)) ℂ)
          (Sum.inr (Sum.inr j)) (Matrix.single (eH j t) (eH j t) 1)).symm)
    · refine Eq.trans ?_ (Finset.sum_eq_zero fun t _ => Pi.single_eq_of_ne
        (show (Sum.inr (Sum.inr j) : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃)) ≠ Sum.inr (Sum.inr i) from
          fun h => hj (Sum.inr_injective (Sum.inr_injective h))) _).symm
      show phiH (Pi.single i (Matrix.single 0 0 1) : MatSumH n₃) j = (0 : Matrix (Fin (n₃ j * 2)) (Fin (n₃ j * 2)) ℂ)
      ext a b
      rw [phiH_apply, phiHFun_apply, Pi.single_eq_of_ne hj]
      simp

/-- The intersection form `∩(p, q) = Tr(γ π(p) J π(q) J)`. -/
def interForm (p q : MatSumMixed n₁ n₂ n₃) : ℂ :=
  LinearMap.trace ℂ H ((G.γ : H →ₗ[ℂ] H) * (T'.π p : H →ₗ[ℂ] H) * rightOp R' q)

/-- **Table 1, real against real** (Krajewski, Section 3.3, p. 14: `∩ᵢⱼ = μᵢⱼ`). -/
theorem interForm_real_real (hG : IsOrientableA R' G x y) (i j : ι₁) :
    interForm R' G (pR i) (pR j) =
      chiScalar (Xm (T' := T') x) (Xm (T' := T') y) (.inl i) (.inl j) * multiplicity (Rm R') (.inl i) (.inl j) := by
  have h : interForm R' G (pR i) (pR j) = ∑ _t : Unit, ∑ _u : Unit, chiScalar (Xm (T' := T') x) (Xm (T' := T') y)
      (Sum.inl i) (Sum.inl j) * (multiplicity (Rm R') (Sum.inl i) (Sum.inl j) : ℂ) :=
    trace_grading_of_phi R' (mixedComplexification T') G hG (pR i) (pR j)
    (fun _ : Unit => (Sum.inl i : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃))) (fun _ => (0 : Fin (n₁ i)))
    (fun _ : Unit => (Sum.inl j : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃))) (fun _ => (0 : Fin (n₁ j)))
    (by rw [Fintype.sum_unique]; exact phiMixed_pR i) (by rw [Fintype.sum_unique]; exact phiMixed_pR j)
  rw [h, Fintype.sum_unique, Fintype.sum_unique]

/-- **Table 1, quaternionic against quaternionic** (Krajewski, Section 3.3, p. 14: `∩ᵢⱼ = 4 μᵢⱼ`). -/
theorem interForm_quat_quat (hG : IsOrientableA R' G x y) (i j : ι₃) :
    interForm R' G (pH i) (pH j) =
      4 * (chiScalar (Xm (T' := T') x) (Xm (T' := T') y) (.inr (.inr i)) (.inr (.inr j)) *
        multiplicity (Rm R') (.inr (.inr i)) (.inr (.inr j))) := by
  have h : interForm R' G (pH i) (pH j) = ∑ _t : Fin 2, ∑ _u : Fin 2, chiScalar (Xm (T' := T') x) (Xm (T' := T') y)
      (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) *
        (multiplicity (Rm R') (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) : ℂ) :=
    trace_grading_of_phi R' (mixedComplexification T') G hG (pH i) (pH j)
    (fun _ : Fin 2 => (Sum.inr (Sum.inr i) : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃))) (eH i)
    (fun _ : Fin 2 => (Sum.inr (Sum.inr j) : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃))) (eH j)
    (phiMixed_pH i) (phiMixed_pH j)
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Table 1, real against quaternionic** (Krajewski, Section 3.3, p. 14: `∩ᵢⱼ = 2 μᵢⱼ`). -/
theorem interForm_real_quat (hG : IsOrientableA R' G x y) (i : ι₁) (j : ι₃) :
    interForm R' G (pR i) (pH j) =
      2 * (chiScalar (Xm (T' := T') x) (Xm (T' := T') y) (.inl i) (.inr (.inr j)) * multiplicity (Rm R') (.inl i) (.inr (.inr j))) := by
  have h : interForm R' G (pR i) (pH j) = ∑ _t : Unit, ∑ _u : Fin 2, chiScalar (Xm (T' := T') x) (Xm (T' := T') y)
      (Sum.inl i) (Sum.inr (Sum.inr j)) * (multiplicity (Rm R') (Sum.inl i) (Sum.inr (Sum.inr j)) : ℂ) :=
    trace_grading_of_phi R' (mixedComplexification T') G hG (pR i) (pH j)
    (fun _ : Unit => (Sum.inl i : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃))) (fun _ => (0 : Fin (n₁ i)))
    (fun _ : Fin 2 => (Sum.inr (Sum.inr j) : ι₁ ⊕ (BlocksP (psi₂ T') ⊕ ι₃))) (eH j)
    (by rw [Fintype.sum_unique]; exact phiMixed_pR i) (phiMixed_pH j)
  rw [h, Fintype.sum_unique]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

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

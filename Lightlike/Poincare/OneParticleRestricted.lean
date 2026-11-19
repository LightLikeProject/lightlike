import Lightlike.Poincare.OneParticleSpectrum
import Mathlib.Topology.Algebra.Group.OpenMapping

/-!
# The one-particle representation of the restricted Poincaré group

The representation `V(a, A) = T(a) U(A)` of `ℝ⁴ ⋊ SL(2,ℂ)` depends on `A` only through its image
`Λ = toRestrictedLorentzGroup A` in the restricted Lorentz group, up to the sign `(−1)^n` of the centre
(`inducedL2_eq_of_toRestricted_eq`). For integer spin (`n` even) it is therefore a unitary representation of the
restricted Poincaré group `ℝ⁴ ⋊ SO⁺(1,3)` (`poincareR`, `poincareR_mul`), and for spin `0` it is
`(V(a, Λ) ψ)(p) = e^{i p·a} ψ(Λ⁻¹ p)` (`coeFn_poincareL2_scalar`). For half-integer spin it is a representation of
the double cover only, as in the source.

Supporting results for the one-particle space; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2

namespace Lightlike.Poincare

noncomputable section

variable {m : ℝ} {μ : Measure (MassShell m)}

/-- An element of the kernel of the covering map is `±1`. -/
lemma eq_or_eq_neg_of_toRestricted_eq {A B : SL2C}
    (h : _root_.Lorentz.SL2C.toRestrictedLorentzGroup A = _root_.Lorentz.SL2C.toRestrictedLorentzGroup B) :
    ((B⁻¹ * A : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ ((B⁻¹ * A : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  have h1 : _root_.Lorentz.SL2C.toLorentzGroup (B⁻¹ * A) = 1 := by
    have hAB : _root_.Lorentz.SL2C.toLorentzGroup A = _root_.Lorentz.SL2C.toLorentzGroup B :=
      congrArg Subtype.val h
    rw [map_mul, map_inv, hAB, inv_mul_cancel]
  exact (_root_.Lorentz.SL2C.toLorentzGroup_eq_one_iff _).1 h1

lemma actP_of_coe_eq {C : SL2C} (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (C : Matrix (Fin 2) (Fin 2) ℂ) = -1)
    (P : Matrix (Fin 2) (Fin 2) ℂ) : actP C P = P := by
  rcases hC with h | h <;> simp [actP, h]

lemma shellAct_of_coe_eq {C : SL2C} (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (C : Matrix (Fin 2) (Fin 2) ℂ) = -1)
    (P : MassShell m) : shellAct C P = P := Subtype.ext (actP_of_coe_eq hC P.1)

lemma translAct_of_coe_eq {C : SL2C}
    (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (C : Matrix (Fin 2) (Fin 2) ℂ) = -1) (a : Transl) :
    translAct C a = a := Subtype.ext (actP_of_coe_eq hC a.1)

/-- The Wigner rotation of `±1` is `±1`. -/
lemma wigField_of_coe_eq (hm : 0 < m) (n : ℕ) {C : SL2C}
    (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (C : Matrix (Fin 2) (Fin 2) ℂ) = -1) (Q : MassShell m) :
    ((wigField hm n C Q : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (if (C : Matrix (Fin 2) (Fin 2) ℂ) = 1 then 1 else (-1 : ℂ) ^ n) • 1 := by
  have hCi : ((C⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ ((C⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rcases hC with h | h
    · left; rw [Matrix.SpecialLinearGroup.coe_inv, h, Matrix.adjugate_one]
    · right; rw [Matrix.SpecialLinearGroup.coe_inv, h, Matrix.adjugate_fin_two]
      ext i j; fin_cases i <;> fin_cases j <;> simp
  have hw : ((wignerSU2 hm C (shellAct C⁻¹ Q) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (C : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [wignerSU2, wigner, shellAct_of_coe_eq hCi, shellAct_of_coe_eq hC, Matrix.SpecialLinearGroup.coe_mul]
    rcases hC with h | h
    · rw [h, Matrix.mul_one, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    · rw [h, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
  simp only [wigField, spinRep_apply, hw]
  by_cases h1 : (C : Matrix (Fin 2) (Fin 2) ℂ) = 1
  · rw [if_pos h1, h1, spinMat_one, one_smul]
  · rw [if_neg h1]
    have h2 : (C : Matrix (Fin 2) (Fin 2) ℂ) = -1 := hC.resolve_left h1
    rw [h2, ← negOne_coe, spinMat_negOne]

/-- **`U(A)` depends on `A` only through its Lorentz transformation, up to `(−1)^n`.** -/
lemma inducedL2_eq_of_toRestricted_eq (hm : 0 < m) {n : ℕ} (heven : Even n)
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) {A B : SL2C}
    (h : _root_.Lorentz.SL2C.toRestrictedLorentzGroup A = _root_.Lorentz.SL2C.toRestrictedLorentzGroup B)
    (f : Lp (Spinor n) 2 μ) : inducedL2 hm n hμ A f = inducedL2 hm n hμ B f := by
  have hC := eq_or_eq_neg_of_toRestricted_eq h
  have hA : A = B * (B⁻¹ * A) := by group
  have hCf : inducedL2 hm n hμ (B⁻¹ * A) f = f := by
    apply Lp.ext
    have hCi : (((B⁻¹ * A)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
        (((B⁻¹ * A)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
      rcases hC with h' | h'
      · left; rw [Matrix.SpecialLinearGroup.coe_inv, h', Matrix.adjugate_one]
      · right; rw [Matrix.SpecialLinearGroup.coe_inv, h', Matrix.adjugate_fin_two]
        ext i j; fin_cases i <;> fin_cases j <;> simp
    filter_upwards [coeFn_inducedL2 hm n hμ (B⁻¹ * A) f] with Q hQ
    rw [hQ, shellAct_of_coe_eq hCi]
    have hU := wigField_of_coe_eq hm n hC Q
    simp only [uAct, hU, heven.neg_one_pow, ite_self, one_smul, Matrix.one_mulVec, WithLp.toLp_ofLp]
  rw [hA, inducedL2_mul, hCf]

lemma translAct_eq_of_toRestricted_eq {A B : SL2C}
    (h : _root_.Lorentz.SL2C.toRestrictedLorentzGroup A = _root_.Lorentz.SL2C.toRestrictedLorentzGroup B)
    (a : Transl) : translAct A a = translAct B a := by
  have hA : A = B * (B⁻¹ * A) := by group
  rw [hA, translAct_mul, translAct_of_coe_eq (eq_or_eq_neg_of_toRestricted_eq h)]

/-! ## The restricted Poincaré group -/

/-- A lift of a restricted Lorentz transformation to `SL(2,ℂ)`. -/
def liftR (Λ : LorentzGroup.restricted 3) : SL2C := (exists_lift_restricted Λ).choose

lemma toRestricted_liftR (Λ : LorentzGroup.restricted 3) :
    _root_.Lorentz.SL2C.toRestrictedLorentzGroup (liftR Λ) = Λ := (exists_lift_restricted Λ).choose_spec

/-- The restricted Lorentz group acting on translations. -/
def translActR (Λ : LorentzGroup.restricted 3) (a : Transl) : Transl := translAct (liftR Λ) a

/-- **The representation of the restricted Poincaré group** `ℝ⁴ ⋊ SO⁺(1,3)` (integer spin). -/
def poincareR (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (a : Transl)
    (Λ : LorentzGroup.restricted 3) : Lp (Spinor n) 2 μ →ₗᵢ[ℂ] Lp (Spinor n) 2 μ :=
  poincareL2 hm n hμ a (liftR Λ)

/-- For integer spin, `V(a, A)` is `poincareR` at the Lorentz transformation of `A`. -/
lemma poincareL2_eq_poincareR (hm : 0 < m) {n : ℕ} (heven : Even n)
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (a : Transl) (A : SL2C) (f : Lp (Spinor n) 2 μ) :
    poincareL2 hm n hμ a A f = poincareR hm n hμ a (_root_.Lorentz.SL2C.toRestrictedLorentzGroup A) f := by
  simp only [poincareR, poincareL2, LinearIsometry.coe_comp, Function.comp_apply]
  rw [inducedL2_eq_of_toRestricted_eq hm heven hμ (toRestricted_liftR _).symm]

/-- **The group law of the restricted Poincaré group**: `V(a, Λ) V(b, Λ') = V(a + Λ b, Λ Λ')`. -/
theorem poincareR_mul (hm : 0 < m) {n : ℕ} (heven : Even n)
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (a b : Transl) (Λ Λ' : LorentzGroup.restricted 3)
    (f : Lp (Spinor n) 2 μ) :
    poincareR hm n hμ a Λ (poincareR hm n hμ b Λ' f) = poincareR hm n hμ (a + translActR Λ b) (Λ * Λ') f := by
  simp only [poincareR, translActR]
  rw [poincareL2_mul, poincareL2_eq_poincareR hm heven hμ, map_mul, toRestricted_liftR, toRestricted_liftR]
  rfl

theorem poincareR_one (hm : 0 < m) {n : ℕ} (heven : Even n)
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (f : Lp (Spinor n) 2 μ) :
    poincareR hm n hμ 0 1 f = f := by
  rw [← map_one _root_.Lorentz.SL2C.toRestrictedLorentzGroup, ← poincareL2_eq_poincareR hm heven hμ,
    poincareL2_one]

/-! ## Spin `0` -/

lemma spinMat_zero (g : Matrix (Fin 2) (Fin 2) ℂ) : spinMat 0 g = 1 := by
  have h : kron 0 g = kron 0 1 := by
    ext s t
    simp [kron_apply]
  rw [spinMat, h, ← spinMat, spinMat_one]

/-- **The scalar one-particle representation**: `(V(a, A) ψ)(p) = e^{i p·a} ψ(A⁻¹ p)`. -/
theorem coeFn_poincareL2_scalar (hm : 0 < m) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ)
    (a : Transl) (A : SL2C) (f : Lp (Spinor 0) 2 μ) :
    (poincareL2 hm 0 hμ a A f : MassShell m → Spinor 0) =ᵐ[μ]
      fun Q => Complex.exp (Complex.I * pairing Q.1 a.1) • f (shellAct A⁻¹ Q) := by
  have h2 := (hμ A⁻¹).quasiMeasurePreserving.ae_eq_comp (Filter.EventuallyEq.rfl (f := (f : MassShell m → Spinor 0)))
  filter_upwards [coeFn_translL2 0 a (inducedL2 hm 0 hμ A f), coeFn_inducedL2 hm 0 hμ A f] with Q e1 e2
  simp only [poincareL2, LinearIsometry.coe_comp, Function.comp_apply]
  rw [e1, e2]
  congr 1
  simp only [uAct, wigField, spinRep_apply, spinMat_zero, Matrix.one_mulVec, WithLp.toLp_ofLp]

/-! ## Strong continuity on the restricted Poincaré group -/

local instance (k : ℕ) : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin k → Fin k → ℂ))

local instance (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))

local instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))

local instance : LocallyCompactSpace (Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 1 ⊕ Fin 3 → Fin 1 ⊕ Fin 3 → ℝ))

local instance : LocallyCompactSpace SL2C :=
  (Topology.IsClosedEmbedding.subtypeVal (isClosed_eq (continuous_id.matrix_det) continuous_const) :
    Topology.IsClosedEmbedding (Subtype.val : SL2C → Matrix (Fin 2) (Fin 2) ℂ)).locallyCompactSpace

local instance : SecondCountableTopology SL2C :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

lemma isClosed_restricted : IsClosed ((LorentzGroup.restricted 3 : Subgroup (LorentzGroup 3)) : Set (LorentzGroup 3)) := by
  have hv : Continuous fun Λ : LorentzGroup 3 => (Λ.1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :=
    continuous_subtype_val
  have h1 : IsClosed {Λ : LorentzGroup 3 | Λ.1.det = 1} := isClosed_eq hv.matrix_det continuous_const
  have h2 : IsClosed {Λ : LorentzGroup 3 | 0 ≤ Λ.1 (Sum.inl 0) (Sum.inl 0)} :=
    isClosed_le continuous_const (hv.matrix_elem _ _)
  exact h1.inter h2

local instance : LocallyCompactSpace (LorentzGroup.restricted 3) := by
  have h1 : Topology.IsClosedEmbedding (Subtype.val : LorentzGroup.restricted 3 → LorentzGroup 3) :=
    isClosed_restricted.isClosedEmbedding_subtypeVal
  have h2 := (LorentzGroup.isClosedEmbedding_val (d := 3)).comp h1
  exact h2.locallyCompactSpace

/-- The covering map is continuous (its entries are traces `½ tr(σ_i A σ_j Aᴴ)`). -/
lemma continuous_toLorentzGroup : Continuous (_root_.Lorentz.SL2C.toLorentzGroup : SL2C → LorentzGroup 3) := by
  apply continuous_induced_rng.2
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : ∀ M : SL2C, ((_root_.Lorentz.SL2C.toLorentzGroup M).1 i j : ℝ) = (Matrix.trace
      ((PauliMatrix.pauliSelfAdjoint' i).1 * (M.1 * (PauliMatrix.pauliSelfAdjoint' j).1 * M.1ᴴ)) / 2).re := by
    intro M
    rw [← _root_.Lorentz.SL2C.toLorentzGroup_eq_trace, Complex.ofReal_re]
  have hM : Continuous fun M : SL2C => (M.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have h : Continuous fun M : SL2C => (Matrix.trace
      ((PauliMatrix.pauliSelfAdjoint' i).1 * (M.1 * (PauliMatrix.pauliSelfAdjoint' j).1 * M.1ᴴ)) / 2).re :=
    Complex.continuous_re.comp (((continuous_const.matrix_mul ((hM.matrix_mul continuous_const).matrix_mul
      hM.matrix_conjTranspose)).matrix_trace).div_const 2)
  exact h.congr fun M => (e M).symm

lemma continuous_toRestricted :
    Continuous (_root_.Lorentz.SL2C.toRestrictedLorentzGroup : SL2C → LorentzGroup.restricted 3) :=
  continuous_induced_rng.2 continuous_toLorentzGroup

/-- **The covering map is open** (open mapping theorem for `σ`-compact groups). -/
lemma isOpenMap_toRestricted :
    IsOpenMap (_root_.Lorentz.SL2C.toRestrictedLorentzGroup : SL2C → LorentzGroup.restricted 3) :=
  MonoidHom.isOpenMap_of_sigmaCompact _ _root_.Lorentz.SL2C.toRestrictedLorentzGroup_surjective
    continuous_toRestricted

/-- **The representation of the restricted Poincaré group is strongly continuous** (integer spin). -/
theorem continuous_poincareR (hm : 0 < m) {n : ℕ} (heven : Even n) [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (f : Lp (Spinor n) 2 μ) :
    Continuous fun x : Transl × LorentzGroup.restricted 3 => poincareR hm n hμ x.1 x.2 f := by
  have hq : Topology.IsQuotientMap (Prod.map (id : Transl → Transl)
      (_root_.Lorentz.SL2C.toRestrictedLorentzGroup : SL2C → LorentzGroup.restricted 3)) :=
    (IsOpenMap.id.prodMap isOpenMap_toRestricted).isQuotientMap (continuous_id.prodMap continuous_toRestricted)
      (Function.surjective_id.prodMap _root_.Lorentz.SL2C.toRestrictedLorentzGroup_surjective)
  rw [hq.continuous_iff]
  have e : ((fun x : Transl × LorentzGroup.restricted 3 => poincareR hm n hμ x.1 x.2 f) ∘
      Prod.map id _root_.Lorentz.SL2C.toRestrictedLorentzGroup) =
        fun y : Transl × SL2C => poincareL2 hm n hμ y.1 y.2 f := by
    funext y
    exact (poincareL2_eq_poincareR hm heven hμ y.1 y.2 f).symm
  rw [e]
  exact continuous_poincareL2 hm hμ f

end

end Lightlike.Poincare

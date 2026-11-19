import Lightlike.Poincare.SnagCovariance
import Lightlike.Poincare.CommutantTranslations
import Mathlib.Analysis.Matrix.PosDef

/-!
# The momentum measure of an irreducible positive-energy representation sits on one orbit

For a strongly continuous unitary representation `V(a, A)` of `ℝ⁴ ⋊ SL(2,ℂ)` (`IsPoincareRep`), the translations
form a unitary representation of `ℝ⁴` (`translRep`) with a joint spectral measure `P` (SNAG). Writing the momentum
`p` as the Hermitian matrix `hermOf (J p)`, `J = diag(1, −1, −1, −1)`, the Lorentz transformations act on `P` by
`V(0, A) P(S) V(0, A)⁻¹ = P(A · S)` (`covariant_jointSpectralMeasure`). If `V` is irreducible
(`IsIrreducibleRep`), the projection of every invariant Borel set is `0` or `1` (`momPVM_invariant_eq_zero_or_one`;
Freitag, Lemma V.7.1). Under positive energy, the projection of the closed forward cone is `1`, and then `P` is
concentrated on one orbit: a mass shell `p² = m²`, `m > 0`, the light cone, or `{0}` (`exists_orbit`; Freitag,
Proposition V.7.2).

## References

* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §7, Lemma 7.1, page 150, and Proposition 7.2, page 151.
-/

open scoped InnerProductSpace ComplexOrder
open Filter Topology MeasureTheory Matrix Lightlike.Lorentz Lightlike.OperatorAlgebras.Spectral
  Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Poincare

noncomputable section

/-! ## Coordinates of translations and momenta -/

/-- The translation with coordinates `x`: the Hermitian matrix `x⁰ + x·σ`. -/
def hermOf (x : Fin 4 → ℝ) : Transl := ⟨momH (x 0) ![x 1, x 2, x 3], momH_mem_selfAdjoint _ _⟩

lemma tcoords_hermOf (x : Fin 4 → ℝ) : tcoords (hermOf x) = x := by
  funext i
  fin_cases i <;> simp [tcoords, hermOf, coord0_momH, coordV_momH]

lemma hermOf_tcoords (a : Transl) : hermOf (tcoords a) = a := by
  have ha : (a.1 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]; exact a.2
  apply Subtype.ext
  change momH (coord0 a.1) ![coordV a.1 0, coordV a.1 1, coordV a.1 2] = a.1
  have e : (![coordV a.1 0, coordV a.1 1, coordV a.1 2] : Fin 3 → ℝ) = coordV a.1 := by
    funext i; fin_cases i <;> rfl
  rw [e]
  exact momH_coords ha

lemma hermOf_add (x y : Fin 4 → ℝ) : hermOf (x + y) = hermOf x + hermOf y := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOf, momH] <;> ring

lemma hermOf_zero : hermOf 0 = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOf, momH]

lemma continuous_hermOf : Continuous hermOf := by
  refine Continuous.subtype_mk ?_ _
  unfold momH
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- `J = diag(1, −1, −1, −1)`. -/
def flipJ (p : Fin 4 → ℝ) : Fin 4 → ℝ := ![p 0, -p 1, -p 2, -p 3]

lemma flipJ_flipJ (p : Fin 4 → ℝ) : flipJ (flipJ p) = p := by
  funext i; fin_cases i <;> simp [flipJ]

lemma continuous_flipJ : Continuous flipJ := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [flipJ] <;> fun_prop

/-- `∑ x_k p_k` is the Minkowski pairing of the momentum `hermOf (J p)` with the translation `hermOf x`. -/
lemma sum_mul_eq_pairing (x p : Fin 4 → ℝ) : ∑ k, x k * p k = pairing (hermOf (flipJ p)).1 (hermOf x).1 := by
  rw [pairing]
  change _ = (mink (momH _ _) (momH _ _)).re
  rw [mink_momH, Complex.ofReal_re]
  simp [flipJ, Fin.sum_univ_four]
  ring

lemma translAct_zero' (A : SL2C) : translAct A 0 = 0 := Subtype.ext (by simp [translAct, actP])

/-! ## Representations of `ℝ⁴ ⋊ SL(2,ℂ)` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous unitary representation of `ℝ⁴ ⋊ SL(2,ℂ)`: `V(a, A) V(b, B) = V(a + A·b, AB)`. -/
structure IsPoincareRep (V : Transl → SL2C → (H ≃ₗᵢ[ℂ] H)) : Prop where
  map_one : ∀ ψ, V 0 1 ψ = ψ
  map_mul : ∀ a b A B ψ, V a A (V b B ψ) = V (a + translAct A b) (A * B) ψ
  continuous : ∀ ψ, Continuous fun x : Transl × SL2C => V x.1 x.2 ψ

/-- Irreducibility: every closed invariant subspace is `0` or everything. -/
def IsIrreducibleRep (V : Transl → SL2C → (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∀ K : Submodule ℂ H, IsClosed (K : Set H) → (∀ a A, ∀ ψ ∈ K, V a A ψ ∈ K) → K = ⊥ ∨ K = ⊤

variable {V : Transl → SL2C → (H ≃ₗᵢ[ℂ] H)} (hV : IsPoincareRep V)
include hV

/-- The translations, as a unitary representation of `ℝ⁴`. -/
def translRep (x : Fin 4 → ℝ) : H ≃ₗᵢ[ℂ] H := V (hermOf x) 1

lemma isUnitaryRepRn_translRep : IsUnitaryRepRn (translRep (V := V)) where
  map_zero ψ := by simp only [translRep, hermOf_zero, hV.map_one]
  map_add x y ψ := by
    simp only [translRep]
    rw [hV.map_mul, translAct_one, mul_one, hermOf_add]
  continuous ψ := (hV.continuous ψ).comp (continuous_hermOf.prodMk continuous_const)

lemma V_eq_transl_mul (a : Transl) (A : SL2C) (ψ : H) : V a A ψ = translRep (V := V) (tcoords a) (V 0 A ψ) := by
  simp only [translRep, hermOf_tcoords]
  rw [hV.map_mul, translAct_zero', add_zero, one_mul]

lemma covariance_translRep (A : SL2C) (x : Fin 4 → ℝ) (ψ : H) :
    V 0 A (translRep (V := V) x ψ) = translRep (V := V) (tcoords (translAct A (hermOf x))) (V 0 A ψ) := by
  simp only [translRep, hermOf_tcoords]
  rw [hV.map_mul, hV.map_mul, zero_add, mul_one, translAct_zero', add_zero, one_mul]

/-- The Lorentz action on momenta in the coordinates of `P`: `p ↦ J (A⁻¹ · J p)` is the dual of `x ↦ A · x`. -/
def dualAct (A : SL2C) (p : Fin 4 → ℝ) : Fin 4 → ℝ := flipJ (tcoords (translAct A⁻¹ (hermOf (flipJ p))))

omit hV in
lemma sum_mul_dualAct (A : SL2C) (x p : Fin 4 → ℝ) :
    ∑ k, tcoords (translAct A (hermOf x)) k * p k = ∑ k, x k * dualAct A p k := by
  rw [sum_mul_eq_pairing, sum_mul_eq_pairing, dualAct, flipJ_flipJ, hermOf_tcoords, hermOf_tcoords]
  conv_lhs => rw [show hermOf (flipJ p) = translAct A (translAct A⁻¹ (hermOf (flipJ p))) by
    rw [← translAct_mul, mul_inv_cancel, translAct_one]]
  exact pairing_actP A _ _

omit hV in
lemma continuous_dualAct (A : SL2C) : Continuous (dualAct A) := by
  refine continuous_flipJ.comp ?_
  have h : Continuous fun a : Transl => tcoords a := by
    refine continuous_pi fun i => ?_
    have hval : Continuous fun a : Transl => (a.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
    have h0 : Continuous fun a : Transl => coord0 a.1 :=
      Complex.continuous_re.comp (((hval.matrix_elem 0 0).add (hval.matrix_elem 1 1)).div_const 2)
    have hV' : ∀ k, Continuous fun a : Transl => coordV a.1 k := fun k =>
      (continuous_apply k).comp (continuous_coordV.comp hval)
    fin_cases i
    · exact h0
    · exact hV' 0
    · exact hV' 1
    · exact hV' 2
  exact h.comp ((continuous_translAct.comp (continuous_const.prodMk continuous_id)).comp
    (continuous_hermOf.comp continuous_flipJ))

omit hV in
/-- A set of momenta defined by an `SL(2,ℂ)`-invariant property of the momentum matrix is invariant. -/
lemma dualAct_preimage {Φ : Matrix (Fin 2) (Fin 2) ℂ → Prop} (hΦ : ∀ (B : SL2C) M, Φ (actP B M) ↔ Φ M)
    (A : SL2C) : dualAct A ⁻¹' {p | Φ (hermOf (flipJ p)).1} = {p | Φ (hermOf (flipJ p)).1} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, dualAct, flipJ_flipJ, hermOf_tcoords]
  exact hΦ A⁻¹ _

/-! ## Invariant sets have projection `0` or `1` -/

/-- **A projection commuting with an irreducible representation is `0` or `1`.** -/
lemma proj_eq_zero_or_one (hirr : IsIrreducibleRep V) {Q : H →L[ℂ] H} (hQ : IsStarProjection Q)
    (hcomm : ∀ a A ψ, Q (V a A ψ) = V a A (Q ψ)) : Q = 0 ∨ Q = 1 := by
  let K : Submodule ℂ H := LinearMap.ker ((1 - Q : H →L[ℂ] H) : H →ₗ[ℂ] H)
  have hK : IsClosed (K : Set H) := (1 - Q : H →L[ℂ] H).isClosed_ker
  have hmem : ∀ ψ, ψ ∈ K ↔ Q ψ = ψ := fun ψ => by
    change (1 - Q : H →L[ℂ] H) ψ = 0 ↔ _
    rw [_root_.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero, eq_comm]
  have hinv : ∀ a A, ∀ ψ ∈ K, V a A ψ ∈ K := fun a A ψ hψ => by
    rw [hmem] at hψ ⊢
    rw [hcomm, hψ]
  have hQQ : ∀ ψ, Q (Q ψ) = Q ψ := fun ψ => by
    rw [← ContinuousLinearMap.mul_apply, hQ.isIdempotentElem.eq]
  rcases hirr K hK hinv with h | h
  · left
    ext ψ
    have : Q ψ ∈ K := (hmem _).2 (hQQ ψ)
    rw [h, Submodule.mem_bot] at this
    simpa using this
  · right
    ext ψ
    have : ψ ∈ K := h ▸ Submodule.mem_top
    simpa using (hmem ψ).1 this

/-! ## The momentum measure -/

/-- **The joint spectral measure of the translations** of `V`. -/
def momPVMRep : ProjectionValuedMeasure (Fin 4 → ℝ) H :=
  (exists_jointSpectralMeasure (isUnitaryRepRn_translRep hV)).choose

lemma translRep_eq_integral (x : Fin 4 → ℝ) (ψ : H) :
    translRep (V := V) x ψ =
      (momPVMRep hV).integral (fun p => Complex.exp (Complex.I * ((∑ k, x k * p k : ℝ) : ℂ))) ψ :=
  (exists_jointSpectralMeasure (isUnitaryRepRn_translRep hV)).choose_spec x ψ

omit hV in
/-- The momenta whose matrix `hermOf (J p)` has the property `Φ`. -/
def momSet (Φ : Matrix (Fin 2) (Fin 2) ℂ → Prop) : Set (Fin 4 → ℝ) := {p | Φ (hermOf (flipJ p)).1}

omit hV in
lemma continuous_momMat : Continuous fun p : Fin 4 → ℝ => ((hermOf (flipJ p)) : Matrix (Fin 2) (Fin 2) ℂ) :=
  continuous_subtype_val.comp (continuous_hermOf.comp continuous_flipJ)

/-- **Ergodicity** (Freitag, Lemma V.7.1): for an irreducible `V`, the projection of an invariant Borel set of
momenta is `0` or `1`. -/
theorem momPVM_invariant_eq_zero_or_one (hirr : IsIrreducibleRep V) {Φ : Matrix (Fin 2) (Fin 2) ℂ → Prop}
    (hΦ : ∀ (B : SL2C) M, Φ (actP B M) ↔ Φ M) (hS : MeasurableSet (momSet Φ)) :
    momPVMRep hV (momSet Φ) = 0 ∨ momPVMRep hV (momSet Φ) = 1 := by
  have hc := commute_of_invariant (translRep_eq_integral hV) hS
  refine proj_eq_zero_or_one hV hirr ((momPVMRep hV).isStarProjection_apply _) fun a A ψ => ?_
  rw [V_eq_transl_mul hV, V_eq_transl_mul hV a A, hc.1,
    hc.2 (V 0 A) (fun x => tcoords (translAct A (hermOf x))) (dualAct A) (continuous_dualAct A).measurable
      (sum_mul_dualAct A) (covariance_translRep hV A) (dualAct_preimage hΦ A)]

/-- Positive energy: the momentum measure is carried by the closed forward cone. -/
def IsPositiveEnergy : Prop := momPVMRep hV (momSet fun M => M.PosSemidef) = 1

/-! ## Concentration on one orbit -/

omit hV in
/-- A finite measure on `ℝ` taking only the values `0` and its total mass is a point mass. -/
lemma exists_atom_of_zero_or_univ {ν : Measure ℝ} [IsFiniteMeasure ν] (hν0 : ν Set.univ ≠ 0)
    (h01 : ∀ B, MeasurableSet B → ν B = 0 ∨ ν B = ν Set.univ) : ∃ c : ℝ, ν {c} = ν Set.univ := by
  set M := ν Set.univ
  have hM : M ≠ ⊤ := measure_ne_top ν _
  -- `F(x) = ν(-∞, x]` is `0` or `M`, tends to `M` at `+∞` and to `0` at `-∞`
  have htop : ∃ x, ν (Set.Iic x) = M := by
    have h := tendsto_measure_Iic_atTop ν
    by_contra hne
    push_neg at hne
    have hz : ∀ x, ν (Set.Iic x) = 0 := fun x => ((h01 _ measurableSet_Iic).resolve_right (hne x))
    have : M = 0 := tendsto_nhds_unique h (tendsto_const_nhds.congr fun x => (hz x).symm)
    exact hν0 this
  have hbot : ∃ x, ν (Set.Iic x) = 0 := by
    have hanti : Antitone fun k : ℕ => Set.Iic (-(k : ℝ)) := fun i j hij =>
      Set.Iic_subset_Iic.2 (by simp only [neg_le_neg_iff, Nat.cast_le]; exact hij)
    have h := tendsto_measure_iInter_atTop (μ := ν) (fun k => measurableSet_Iic.nullMeasurableSet) hanti
      ⟨0, measure_ne_top ν _⟩
    have hempty : (⋂ k : ℕ, Set.Iic (-(k : ℝ))) = ∅ := by
      ext y
      simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨k, hk⟩ := exists_nat_gt (-y)
      exact ⟨k, by linarith⟩
    rw [hempty, measure_empty] at h
    by_contra hne
    push_neg at hne
    have hz : ∀ k : ℕ, ν (Set.Iic (-(k : ℝ))) = M := fun k => ((h01 _ measurableSet_Iic).resolve_left (hne _))
    have : M = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr fun k => (hz k).symm) h
    exact hν0 this
  obtain ⟨x₁, hx₁⟩ := htop
  obtain ⟨x₀, hx₀⟩ := hbot
  set T := {x : ℝ | ν (Set.Iic x) = M}
  have hTbdd : BddBelow T := ⟨x₀, fun x hx => by
    by_contra hlt
    push_neg at hlt
    have := measure_mono (μ := ν) (Set.Iic_subset_Iic.2 hlt.le)
    rw [hx, hx₀] at this
    exact hν0 (le_antisymm this zero_le)⟩
  set c := sInf T
  have hmono : ∀ x y, x ≤ y → ν (Set.Iic x) = M → ν (Set.Iic y) = M := fun x y hxy hx =>
    le_antisymm (measure_mono (Set.subset_univ _)) (hx ▸ measure_mono (Set.Iic_subset_Iic.2 hxy))
  -- `ν(-∞, c] = M`
  have hc1 : ν (Set.Iic c) = M := by
    have hk : ∀ k : ℕ, ν (Set.Iic (c + 1 / (k + 1))) = M := fun k => by
      obtain ⟨x, hxT, hxlt⟩ := exists_lt_of_csInf_lt ⟨x₁, hx₁⟩ (show c < c + 1 / (k + 1) by
        have : (0 : ℝ) < 1 / (k + 1) := by positivity
        linarith)
      exact hmono x _ hxlt.le hxT
    have hI : Set.Iic c = ⋂ k : ℕ, Set.Iic (c + 1 / (k + 1)) := by
      ext y
      simp only [Set.mem_Iic, Set.mem_iInter]
      constructor
      · intro hy k
        have : (0 : ℝ) < 1 / (k + 1) := by positivity
        linarith
      · intro hy
        by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        have := hy k
        linarith
    have hanti : Antitone fun k : ℕ => Set.Iic (c + 1 / ((k : ℝ) + 1)) := fun i j hij =>
      Set.Iic_subset_Iic.2 (by gcongr)
    have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun k => measurableSet_Iic.nullMeasurableSet)
      hanti ⟨0, measure_ne_top ν _⟩
    rw [← hI] at hlim
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun k => (hk k).symm)
  -- `ν(-∞, c) = 0`
  have hc0 : ν (Set.Iio c) = 0 := by
    have hk : ∀ k : ℕ, ν (Set.Iic (c - 1 / (k + 1))) = 0 := fun k => by
      refine (h01 _ measurableSet_Iic).resolve_right fun hM' => ?_
      have := csInf_le hTbdd (show c - 1 / (k + 1) ∈ T from hM')
      have : (0 : ℝ) < 1 / (k + 1) := by positivity
      linarith
    have hU : Set.Iio c = ⋃ k : ℕ, Set.Iic (c - 1 / (k + 1)) := by
      ext y
      simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have : (0 : ℝ) < 1 / (k + 1) := by positivity
        linarith
    rw [hU]
    exact measure_iUnion_null fun k => hk k
  refine ⟨c, ?_⟩
  have hsplit : Set.Iic c = Set.Iio c ∪ {c} := (Set.Iio_union_right).symm
  have := measure_union (μ := ν) (Set.disjoint_singleton_right.2 (show c ∉ Set.Iio c from lt_irrefl c))
    (measurableSet_singleton c)
  rw [← hsplit, hc1, hc0, zero_add] at this
  exact this.symm

/-- The mass shell `p² = m²`, `p⁰ > 0`, in momentum coordinates. -/
def shellSet (m : ℝ) : Set (Fin 4 → ℝ) := momSet fun M => M ∈ MassShellH m

/-- The forward light cone `p² = 0`, `p⁰ > 0`, in momentum coordinates. -/
def coneSet : Set (Fin 4 → ℝ) := momSet fun M => M ∈ LightConeH

/-- The zero momentum. -/
def zeroSet : Set (Fin 4 → ℝ) := momSet fun M => M = 0

omit hV in
lemma actP_invariant {Φ : Matrix (Fin 2) (Fin 2) ℂ → Prop} (hΦ : ∀ (B : SL2C) {M}, Φ M → Φ (actP B M))
    (B : SL2C) (M : Matrix (Fin 2) (Fin 2) ℂ) : Φ (actP B M) ↔ Φ M :=
  ⟨fun h => by simpa [actP_inv_actP] using hΦ B⁻¹ h, hΦ B⟩

omit hV in
lemma psd_actP (B : SL2C) {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.PosSemidef) : (actP B M).PosSemidef :=
  hM.mul_mul_conjTranspose_same _

omit hV in
lemma isClosed_momSet_psd : IsClosed (momSet fun M => M.PosSemidef) :=
  Matrix.posSemidef_is_closed.preimage continuous_momMat

omit hV in
lemma continuous_detRe : Continuous fun p : Fin 4 → ℝ => ((hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ).det).re :=
  Complex.continuous_re.comp continuous_momMat.matrix_det

omit hV in
lemma det_eq_re_of_psd {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.PosSemidef) : M.det = (M.det.re : ℂ) := by
  have h := hM.det_nonneg
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    exact (Complex.nonneg_iff.1 h).2.symm

/-- **Concentration on one orbit** (Freitag, Proposition V.7.2): the momentum measure of an irreducible
positive-energy representation is carried by one mass shell `p² = m²`, `m > 0`, by the light cone, or by `{0}`. -/
theorem exists_orbit [Nontrivial H] (hirr : IsIrreducibleRep V) (hpos : IsPositiveEnergy hV) :
    (∃ m > 0, momPVMRep hV (shellSet m) = 1) ∨ momPVMRep hV coneSet = 1 ∨ momPVMRep hV zeroSet = 1 := by
  set P := momPVMRep hV
  obtain ⟨ψ₀, hψ₀⟩ := exists_ne (0 : H)
  set ν := P.assoc ψ₀
  have hνuniv : (ν Set.univ).toReal = ‖ψ₀‖ ^ 2 := by
    rw [ProjectionValuedMeasure.assoc_apply _ _ MeasurableSet.univ, P.apply_univ,
      ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hν0 : ν Set.univ ≠ 0 := by
    intro h
    rw [h, ENNReal.toReal_zero] at hνuniv
    exact hψ₀ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hνuniv.symm))
  -- the projection values and the scalar measure
  have hP0 : ∀ {S}, MeasurableSet S → P S = 0 → ν S = 0 := fun {S} hS h => by
    have := ProjectionValuedMeasure.assoc_apply P ψ₀ hS
    rw [h, ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re] at this
    exact (ENNReal.toReal_eq_zero_iff _).1 this |>.resolve_right (measure_ne_top _ _)
  have hP1 : ∀ {S}, MeasurableSet S → P S = 1 → ν S = ν Set.univ := fun {S} hS h => by
    have h1 := ProjectionValuedMeasure.assoc_apply P ψ₀ hS
    have h2 := ProjectionValuedMeasure.assoc_apply P ψ₀ MeasurableSet.univ
    rw [h, P.apply_univ] at *
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (h1.trans h2.symm)
  have hpos' : ∀ {Φ : Matrix (Fin 2) (Fin 2) ℂ → Prop}, (∀ (B : SL2C) M, Φ (actP B M) ↔ Φ M) →
      MeasurableSet (momSet Φ) → ν (momSet Φ) ≠ 0 → P (momSet Φ) = 1 := fun {Φ} hΦ hS hne =>
    (momPVM_invariant_eq_zero_or_one hV hirr hΦ hS).resolve_left fun h => hne (hP0 hS h)
  -- the distribution of `p²` on the forward cone
  have hPSDm : MeasurableSet (momSet fun M => M.PosSemidef) := isClosed_momSet_psd.measurableSet
  set f : (Fin 4 → ℝ) → ℝ := fun p => ((hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ).det).re
  set ν' : Measure ℝ := (ν.restrict (momSet fun M => M.PosSemidef)).map f
  have hlev : ∀ B : Set ℝ, MeasurableSet B → ν' B = ν (momSet fun M => M.PosSemidef ∧ M.det.re ∈ B) := by
    intro B hB
    rw [Measure.map_apply continuous_detRe.measurable hB, Measure.restrict_apply (continuous_detRe.measurable hB)]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, momSet, Set.mem_setOf_eq]
    exact and_comm
  have hlevm : ∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet (momSet fun M => M.PosSemidef ∧ M.det.re ∈ B) := fun B hB =>
    hPSDm.inter (continuous_detRe.measurable hB)
  have hlevinv : ∀ B : Set ℝ, ∀ (A : SL2C) M, (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.PosSemidef ∧ M.det.re ∈ B)
      (actP A M) ↔ (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.PosSemidef ∧ M.det.re ∈ B) M := fun B =>
    actP_invariant (Φ := fun M : Matrix (Fin 2) (Fin 2) ℂ => M.PosSemidef ∧ M.det.re ∈ B)
      fun A {M} hM => ⟨psd_actP A hM.1, by rw [det_actP]; exact hM.2⟩
  have hν'univ : ν' Set.univ = ν Set.univ := by
    rw [hlev _ MeasurableSet.univ]
    have e : (momSet fun M : Matrix (Fin 2) (Fin 2) ℂ => M.PosSemidef ∧ M.det.re ∈ Set.univ) =
        momSet fun M => M.PosSemidef := by ext p; simp [momSet]
    rw [e]
    exact hP1 hPSDm hpos
  haveI : IsFiniteMeasure ν' := by
    refine ⟨?_⟩
    rw [hν'univ]
    exact measure_lt_top _ _
  have h01 : ∀ B, MeasurableSet B → ν' B = 0 ∨ ν' B = ν' Set.univ := fun B hB => by
    rw [hlev B hB, hν'univ]
    rcases momPVM_invariant_eq_zero_or_one hV hirr (hlevinv B) (hlevm B hB) with h | h
    · exact Or.inl (hP0 (hlevm B hB) h)
    · exact Or.inr (hP1 (hlevm B hB) h)
  obtain ⟨c, hc⟩ := exists_atom_of_zero_or_univ (hν'univ ▸ hν0) h01
  have hcne : ν (momSet fun M => M.PosSemidef ∧ M.det.re ∈ ({c} : Set ℝ)) ≠ 0 := by
    rw [← hlev _ (measurableSet_singleton c), hc, hν'univ]
    exact hν0
  -- the three cases
  rcases lt_trichotomy c 0 with hc0 | rfl | hc0
  · exfalso
    apply hcne
    have e : (momSet fun M : Matrix (Fin 2) (Fin 2) ℂ => M.PosSemidef ∧ M.det.re ∈ ({c} : Set ℝ)) = ∅ := by
      ext p
      simp only [momSet, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hM hdet
      have := (Complex.nonneg_iff.1 hM.det_nonneg).1
      linarith
    rw [e, measure_empty]
  · -- `p² = 0`: the cone or `{0}`
    have hsub : (momSet fun M : Matrix (Fin 2) (Fin 2) ℂ => M.PosSemidef ∧ M.det.re ∈ ({0} : Set ℝ)) ⊆
        coneSet ∪ zeroSet := by
      intro p hp
      simp only [momSet, Set.mem_setOf_eq, Set.mem_singleton_iff] at hp
      by_cases h0 : (hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ) = 0
      · exact Or.inr h0
      · refine Or.inl ⟨hp.1, ?_, h0⟩
        rw [det_eq_re_of_psd hp.1, hp.2, Complex.ofReal_zero]
    have hconem : MeasurableSet coneSet := by
      have e : coneSet = (momSet fun M => M.PosSemidef) ∩ {p | ((hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ)).det = 0}
          ∩ {p | (hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0} := by
        ext p; simp [coneSet, momSet, LightConeH, and_assoc]
      rw [e]
      exact (hPSDm.inter (isClosed_eq continuous_momMat.matrix_det continuous_const).measurableSet).inter
        (isOpen_ne_fun continuous_momMat continuous_const).measurableSet
    have hzerom : MeasurableSet zeroSet := (isClosed_eq continuous_momMat continuous_const).measurableSet
    have hle := measure_mono (μ := ν) hsub
    rcases eq_or_ne (ν coneSet) 0 with hcone | hcone
    · right; right
      refine hpos' (Φ := fun M => M = 0)
        (actP_invariant (Φ := fun M : Matrix (Fin 2) (Fin 2) ℂ => M = 0) fun A {M} hM => by
          rw [hM, actP_zero]) hzerom ?_
      intro hz
      apply hcne
      exact le_antisymm (hle.trans ((measure_union_le _ _).trans (by
        rw [hcone, zero_add]; exact hz.le))) zero_le
    · right; left
      exact hpos' (Φ := fun M => M ∈ LightConeH)
        (actP_invariant (Φ := fun M : Matrix (Fin 2) (Fin 2) ℂ => M ∈ LightConeH) fun A {M} hM =>
          actP_mem_lightCone A hM) hconem hcone
  · -- `p² = c > 0`: the mass shell `m = √c`
    left
    refine ⟨Real.sqrt c, Real.sqrt_pos.2 hc0, ?_⟩
    have hsub : (momSet fun M : Matrix (Fin 2) (Fin 2) ℂ => M.PosSemidef ∧ M.det.re ∈ ({c} : Set ℝ)) ⊆
        shellSet (Real.sqrt c) := by
      intro p hp
      simp only [momSet, Set.mem_setOf_eq, Set.mem_singleton_iff] at hp
      have hdet : (hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ).det = (c : ℂ) := by
        rw [det_eq_re_of_psd hp.1, hp.2]
      refine ⟨(hp.1.posDef_iff_det_ne_zero).2 (by rw [hdet]; exact_mod_cast hc0.ne'), ?_⟩
      rw [hdet, Real.sq_sqrt hc0.le]
    have hshellm : MeasurableSet (shellSet (Real.sqrt c)) := by
      have e : shellSet (Real.sqrt c) = (momSet fun M => M.PosSemidef) ∩
          {p | ((hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ)).det = ((Real.sqrt c ^ 2 : ℝ) : ℂ)} := by
        ext p
        simp only [shellSet, momSet, MassShellH, Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨hpd, hd⟩; exact ⟨hpd.posSemidef, hd⟩
        · rintro ⟨hpsd, hd⟩
          refine ⟨hpsd.posDef_iff_det_ne_zero.2 ?_, hd⟩
          rw [hd, Real.sq_sqrt hc0.le]
          exact_mod_cast hc0.ne'
      rw [e]
      exact hPSDm.inter (isClosed_eq continuous_momMat.matrix_det continuous_const).measurableSet
    refine hpos' (Φ := fun M => M ∈ MassShellH (Real.sqrt c))
      (actP_invariant (Φ := fun M : Matrix (Fin 2) (Fin 2) ℂ => M ∈ MassShellH (Real.sqrt c)) fun A {M} hM =>
        act_mem A hM) hshellm ?_
    intro hz
    exact hcne (le_antisymm ((measure_mono hsub).trans hz.le) zero_le)

end

end Lightlike.Poincare

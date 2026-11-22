module

public import Mathlib
public import Lightlike.Lorentz.SL2C

/-!
# Momentum space in spinor form and the little groups of the Poincaré group

HA6 (Wigner's classification), first piece. A four-momentum `p = (p₀, p₁, p₂, p₃)` is written as the
Hermitian matrix `P = [[p₀ + p₃, p₁ - i p₂], [p₁ + i p₂, p₀ - p₃]]`, so that `det P = p₀² - p₁² - p₂² - p₃²`
is the Minkowski square in the signature `(+,−,−,−)`. The group `SL(2,ℂ)`, the double cover of the
restricted Lorentz group, acts by `P ↦ A P A†` and preserves `det`.

* `Herm2`, the instance `MulAction SL2C Herm2`, `det_smul` (the mass square is invariant), `ofVec`,
  `det_ofVec`.
* **Little groups** are the stabilizers `MulAction.stabilizer SL2C P`:
  * massive `P = m·1` (`m ≠ 0`): the stabilizer is the image of `SU(2)` (`stabilizer_restMom`),
    which is compact (`isCompact_stabilizer_restMom`);
  * massless `P = E·diag(1,0)` (`E ≠ 0`): the stabilizer is the group of upper triangular matrices
    `[[a, b], [0, a⁻¹]]` with `|a| = 1` (`mem_stabilizer_lightMom`), a double cover of `ISO(2)`: the
    phase `a` is a homomorphism onto the circle whose kernel is the group of `upper t`, `t ∈ ℂ`
    (`phase`, `ker_phase`), and conjugation by `diag(a, a⁻¹)` multiplies `t` by `a²`;
  * tachyonic `P = m·diag(1,−1)` (`m ≠ 0`): the stabilizer is `SU(1,1)`, which is not compact
    (`not_isCompact_stabilizer_tachMom`).

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5 (the little groups
`SO(3)`, `ISO(2)`, `SO(2,1)`); only the statements proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

/-- Momentum space in spinor form: the Hermitian `2 × 2` complex matrices. -/
abbrev Herm2 : Type := {M : Matrix (Fin 2) (Fin 2) ℂ // M.IsHermitian}

/-- The action `P ↦ A P A†` of `SL(2,ℂ)` on Hermitian matrices. -/
def actMat (A : SL2C) (P : Herm2) : Herm2 :=
  ⟨(A : Matrix (Fin 2) (Fin 2) ℂ) * P.1 * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ, by
    have h := P.2
    unfold Matrix.IsHermitian at h ⊢
    simp [Matrix.conjTranspose_mul, h, Matrix.mul_assoc]⟩

/-- `SL(2,ℂ)` acts on spinor momenta by `P ↦ A P A†`. -/
instance : MulAction SL2C Herm2 where
  smul := actMat
  one_smul P := Subtype.ext (by
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) * P.1 * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = P.1
    simp)
  mul_smul A B P := Subtype.ext (by
    change ((A * B : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * P.1 *
        ((A * B : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      (A : Matrix (Fin 2) (Fin 2) ℂ) * ((B : Matrix (Fin 2) (Fin 2) ℂ) * P.1 *
        (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc])

lemma coe_smul (A : SL2C) (P : Herm2) :
    ((A • P : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (A : Matrix (Fin 2) (Fin 2) ℂ) * P.1 * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl

/-- **The mass square is Lorentz invariant**: `det (A P A†) = det P` for `A ∈ SL(2,ℂ)`. -/
theorem det_smul (A : SL2C) (P : Herm2) : (A • P : Herm2).1.det = P.1.det := by
  rw [coe_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    A.2]
  simp

/-- The Hermitian matrix of the four-momentum `p = (p₀, p₁, p₂, p₃)`. -/
def ofVec (p : Fin 4 → ℝ) : Herm2 :=
  ⟨!![(p 0 + p 3 : ℝ), ((p 1 : ℝ) : ℂ) - Complex.I * (p 2 : ℝ);
      ((p 1 : ℝ) : ℂ) + Complex.I * (p 2 : ℝ), (p 0 - p 3 : ℝ)], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, sub_eq_add_neg]⟩

/-- **The determinant is the Minkowski square in signature `(+,−,−,−)`.** -/
theorem det_ofVec (p : Fin 4 → ℝ) :
    (ofVec p).1.det = ((p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 : ℝ) : ℂ) := by
  simp only [ofVec, Matrix.det_fin_two_of]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-! ## The massive little group: `SU(2)` -/

/-- The rest momentum `(m, 0, 0, 0)`, the matrix `m · 1`. -/
def restMom (m : ℝ) : Herm2 :=
  ⟨(m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ), by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]⟩

lemma restMom_eq_ofVec (m : ℝ) : restMom m = ofVec ![m, 0, 0, 0] := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [restMom, ofVec]

/-- **The little group of a massive momentum is `SU(2)`**: the stabilizer of the rest momentum
`m·1` (`m ≠ 0`) in `SL(2,ℂ)` is the image of `SU(2)`. -/
theorem stabilizer_restMom {m : ℝ} (hm : m ≠ 0) :
    MulAction.stabilizer SL2C (restMom m) = SL2C.ofSU2.range := by
  ext A
  rw [MulAction.mem_stabilizer_iff, MonoidHom.mem_range]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  constructor
  · intro h
    have h1 : (A : Matrix (Fin 2) (Fin 2) ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
      have h2 := congrArg Subtype.val h
      rw [coe_smul] at h2
      simp only [restMom, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at h2
      exact smul_right_injective _ hmC (by simpa using h2)
    have hU : (A : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      rw [Matrix.mem_specialUnitaryGroup_iff]
      exact ⟨Matrix.mem_unitaryGroup_iff.mpr h1, A.2⟩
    exact ⟨⟨_, hU⟩, Subtype.ext rfl⟩
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    rw [coe_smul]
    have hu := Matrix.mem_unitaryGroup_iff.mp u.2.1
    simp only [restMom, SL2C.coe_ofSU2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [show (u.1 : Matrix (Fin 2) (Fin 2) ℂ) * (u.1)ᴴ = 1 from hu]

/-- A matrix of `SL(2,ℂ)` fixes the rest momentum exactly when `A A† = 1`. -/
lemma mem_stabilizer_restMom_iff {m : ℝ} (hm : m ≠ 0) (A : SL2C) :
    A ∈ MulAction.stabilizer SL2C (restMom m) ↔
      (A : Matrix (Fin 2) (Fin 2) ℂ) * star (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [stabilizer_restMom hm, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    exact Matrix.mem_unitaryGroup_iff.mp u.2.1
  · intro h1
    have hU : (A : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      rw [Matrix.mem_specialUnitaryGroup_iff]
      exact ⟨Matrix.mem_unitaryGroup_iff.mpr h1, A.2⟩
    exact ⟨⟨_, hU⟩, Subtype.ext rfl⟩

/-- **The massive little group is compact**: the stabilizer of `m·1` (`m ≠ 0`) is a compact subset
of `SL(2,ℂ)`, a closed set of matrices whose entries have modulus at most `1`. -/
theorem isCompact_stabilizer_restMom {m : ℝ} (hm : m ≠ 0) :
    IsCompact ((MulAction.stabilizer SL2C (restMom m) : Subgroup SL2C) : Set SL2C) := by
  have hind : Topology.IsInducing (fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ)) := ⟨rfl⟩
  refine hind.isCompact_iff.mpr ?_
  have himg : (fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ)) ''
      ((MulAction.stabilizer SL2C (restMom m) : Subgroup SL2C) : Set SL2C) =
      {M : Matrix (Fin 2) (Fin 2) ℂ | M * star M = 1} ∩ {M | M.det = 1} := by
    ext M
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact ⟨(mem_stabilizer_restMom_iff hm A).mp hA, A.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨M, h2⟩, (mem_stabilizer_restMom_iff hm ⟨M, h2⟩).mpr h1, rfl⟩
  rw [himg]
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ?_ ?_
  · exact (isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const).inter
      (isClosed_eq continuous_id.matrix_det continuous_const)
  · rintro M ⟨h1, -⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff.mpr h1) i j

/-! ## The massless little group: a double cover of `ISO(2)` -/

/-- The massless momentum `(E/2, 0, 0, E/2)`, the matrix `E · diag(1, 0)`. -/
def lightMom (E : ℝ) : Herm2 :=
  ⟨(E : ℂ) • !![1, 0; 0, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]⟩

lemma lightMom_eq_ofVec (E : ℝ) : lightMom E = ofVec ![E / 2, 0, 0, E / 2] := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lightMom, ofVec]

/-- The entries of `A (E diag(1,0)) A†`: `E · A_{i0} conj(A_{j0})`. -/
lemma smul_lightMom_apply (A : SL2C) (E : ℝ) (i j : Fin 2) :
    ((A • lightMom E : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      (E : ℂ) * (A i 0 * (starRingEnd ℂ) (A j 0)) := by
  rw [coe_smul]
  simp [lightMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring

/-- **The little group of a massless momentum**: a matrix `A ∈ SL(2,ℂ)` fixes `E·diag(1,0)`
(`E ≠ 0`) exactly when it is upper triangular with `|A₀₀| = 1`, that is
`A = [[e^{iθ}, b], [0, e^{-iθ}]]`. -/
theorem mem_stabilizer_lightMom {E : ℝ} (hE : E ≠ 0) (A : SL2C) :
    A ∈ MulAction.stabilizer SL2C (lightMom E) ↔ A 1 0 = 0 ∧ ‖A 0 0‖ = 1 := by
  have hEC : (E : ℂ) ≠ 0 := by exact_mod_cast hE
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
    have h11 := congrFun (congrFun (congrArg Subtype.val h) 1) 1
    rw [smul_lightMom_apply] at h00 h11
    simp only [lightMom] at h00 h11
    simp at h00 h11
    have hc : A 1 0 = 0 := by
      rcases h11 with h | h
      · exact absurd h hE
      · exact h
    refine ⟨hc, ?_⟩
    have h3 : A 0 0 * (starRingEnd ℂ) (A 0 0) = 1 :=
      mul_left_cancel₀ hEC (by rw [mul_one]; exact h00)
    have h4 : (‖A 0 0‖ : ℂ) ^ 2 = 1 := by
      rw [← Complex.mul_conj']; exact h3
    have h5 : ‖A 0 0‖ ^ 2 = 1 := by exact_mod_cast h4
    nlinarith [norm_nonneg (A 0 0)]
  · rintro ⟨hc, hn⟩
    apply Subtype.ext
    ext i j
    rw [smul_lightMom_apply]
    have h3 : A 0 0 * (starRingEnd ℂ) (A 0 0) = 1 := by
      rw [Complex.mul_conj']
      simp [hn]
    fin_cases i <;> fin_cases j <;> simp [lightMom, hc, h3]

/-- The phase `a` of the upper triangular matrix `[[a, b], [0, a⁻¹]]`, a homomorphism from the
little group of `E = 1` to the circle; it is the rotation of `ISO(2)`, through the angle `2 arg a`. -/
noncomputable def phase : MulAction.stabilizer SL2C (lightMom 1) →* Circle where
  toFun A := ⟨A.1 0 0, mem_sphere_zero_iff_norm.mpr
    (((mem_stabilizer_lightMom one_ne_zero A.1).mp A.2).2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    have hB := ((mem_stabilizer_lightMom one_ne_zero B.1).mp B.2).1
    change ((A.1 * B.1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, hB]
    rfl

lemma coe_phase (A : MulAction.stabilizer SL2C (lightMom 1)) :
    ((phase A : Circle) : ℂ) = A.1 0 0 := rfl

/-- **The kernel of the phase is the group of translations** `upper t`, `t ∈ ℂ ≅ ℝ²`: the massless
little group is an extension of the circle by `ℝ²`. -/
theorem mem_ker_phase (A : MulAction.stabilizer SL2C (lightMom 1)) :
    A ∈ phase.ker ↔ ∃ t : ℂ, A.1 = SL2C.upper t := by
  have hA := (mem_stabilizer_lightMom one_ne_zero A.1).mp A.2
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : A.1 0 0 = 1 := by
      have := congrArg (fun z : Circle => (z : ℂ)) h
      simpa [coe_phase] using this
    refine ⟨A.1 0 1, SL2C.ext' ?_ rfl ?_ ?_⟩
    · simpa [SL2C.upper] using h1
    · simpa [SL2C.upper] using hA.1
    · have := SL2C.det_eq A.1
      rw [h1, hA.1] at this
      simpa [SL2C.upper] using this
  · rintro ⟨t, ht⟩
    apply Subtype.ext
    have := congrArg (fun g : SL2C => g 0 0) ht
    simpa [coe_phase, SL2C.upper] using this

/-- **Conjugation by `diag(a, a⁻¹)` rotates the translations**: `diag(a,a⁻¹) · upper t =
upper (a² t) · diag(a,a⁻¹)`, the action of the rotation `a ↦ a²` of `ISO(2)` on `ℝ² ≅ ℂ`. -/
theorem diagSL_mul_upper (a : ℂ) (ha : a ≠ 0) (t : ℂ) :
    SL2C.diagSL a ha * SL2C.upper t = SL2C.upper (a ^ 2 * t) * SL2C.diagSL a ha := by
  apply SL2C.ext' <;>
    simp [SL2C.diagSL, SL2C.upper, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

/-! ## The tachyonic little group is not compact -/

/-- The tachyonic momentum `(0, 0, 0, m)` with `p² = -m²`, the matrix `m · diag(1, -1)`. -/
def tachMom (m : ℝ) : Herm2 :=
  ⟨(m : ℂ) • !![1, 0; 0, -1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]⟩

lemma tachMom_eq_ofVec (m : ℝ) : tachMom m = ofVec ![0, 0, 0, m] := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tachMom, ofVec]

/-- The real symmetric matrix `[[c, s], [s, c]]` of determinant `c² - s² = 1`, in `SL(2,ℂ)`. -/
noncomputable def realBoost (c s : ℝ) (h : c * c - s * s = 1) : SL2C :=
  SL2C.mk c s s c (by exact_mod_cast h)

/-- A real matrix `[[c, s], [s, c]]` of determinant one fixes the tachyonic momentum. -/
lemma realBoost_mem_stabilizer (m c s : ℝ) (h : c * c - s * s = 1) :
    realBoost c s h ∈ MulAction.stabilizer SL2C (tachMom m) := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  rw [coe_smul]
  have h' : (c : ℂ) * c - s * s = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realBoost, tachMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    first
    | linear_combination (m : ℂ) * h'
    | linear_combination (-(m : ℂ)) * h'
    | ring

/-- The hyperbolic boost `[[cosh t, sinh t], [sinh t, cosh t]]`. -/
noncomputable def boostSL (t : ℝ) : SL2C :=
  realBoost (Real.cosh t) (Real.sinh t) (by nlinarith [Real.cosh_sq_sub_sinh_sq t])

/-- The boosts fix the tachyonic momentum. -/
lemma boostSL_mem_stabilizer (m t : ℝ) : boostSL t ∈ MulAction.stabilizer SL2C (tachMom m) :=
  realBoost_mem_stabilizer m _ _ _

lemma boostSL_apply_zero_zero (t : ℝ) : (boostSL t) 0 0 = ((Real.cosh t : ℝ) : ℂ) := by
  simp [boostSL, realBoost]

/-- **A tachyonic momentum has a non-compact little group**: the stabilizer of `m·diag(1,−1)`
(this is `SU(1,1) ≅ SL(2,ℝ)`) contains the boosts, on which the entry `A₀₀ = cosh t` is unbounded,
so it is not a compact subset of `SL(2,ℂ)`. -/
theorem not_isCompact_stabilizer_tachMom (m : ℝ) :
    ¬ IsCompact ((MulAction.stabilizer SL2C (tachMom m) : Subgroup SL2C) : Set SL2C) := by
  intro hK
  have hc : Continuous fun A : SL2C => (A 0 0).re :=
    Complex.continuous_re.comp
      ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val))
  obtain ⟨C, hC⟩ := (hK.image hc).bddAbove
  have hmem := boostSL_mem_stabilizer m (2 * C)
  have h1 : ((boostSL (2 * C)) 0 0).re ≤ C := hC ⟨boostSL (2 * C), hmem, rfl⟩
  rw [boostSL_apply_zero_zero, Complex.ofReal_re, Real.cosh_eq] at h1
  have h2 := Real.add_one_le_exp (2 * C)
  have h3 := Real.exp_pos (-(2 * C))
  linarith

end Lightlike.Lorentz.Poincare

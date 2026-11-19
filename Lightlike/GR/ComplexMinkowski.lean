import Mathlib

/-!
# Complexified Minkowski space as 2 × 2 matrices, its null cone, and twistor lines

Complexified Minkowski space `M_ℂ = ℂ⁴` is identified with `2 × 2` complex matrices, `ℂ²⊗ℂ²`, by the spinor map
`x ↦ x^{αα̇} = (1/√2) [[x⁰ + x³, x¹ − i x²], [x¹ + i x², x⁰ − x³]]` (`spinorMat`, a linear equivalence `spinorEquiv`;
`spinorTensorEquiv : ℂ² ⊗ ℂ² ≃ M₂(ℂ)` sends `a ⊗ b` to the outer product `a bᵀ`). The Minkowski form is twice the
determinant (`qC_eq_two_det`), so the null cone `qC x = 0` is the set of matrices of rank at most one, the outer
products `a bᵀ` of two spinors (`qC_eq_zero_iff`), i.e. the pure tensors (`qC_eq_zero_iff_tmul`). Real Minkowski space
is the set of Hermitian matrices (`isHermitian_spinorMat_iff`).

The conformal compactification is read through twistor space: a point `x` gives the 2-plane
`L_x = {(μ, λ) : μ^{α̇} = x^{αα̇} λ_α} ⊆ ℂ⁴` (`twistorLine`, the incidence relation), of dimension two
(`finrank_twistorLine`), determined by `x` (`twistorLine_injective`) and complementary to the plane at infinity
`I = {λ = 0}` (`twistorLine_inf_infinity`); conversely every 2-plane complementary to `I` is some `L_x`
(`exists_twistorLine_eq`), so `M_ℂ` is the affine chart of the Grassmannian of 2-planes of `ℂ⁴` (planes meeting `I`
are the points at infinity). Two lines meet iff their points are null separated (`twistorLine_inf_ne_bot_iff`). The
Plücker coordinates `X^{AB} = Z₁^A Z₂^B − Z₂^A Z₁^B` of a 2-plane satisfy the Klein-quadric relation
`X⁰¹X²³ − X⁰²X¹³ + X⁰³X¹² = 0` (`plucker_klein`), and conversely every nonzero skew `X` on the Klein quadric is a
decomposable bivector `Z₁ ∧ Z₂` (`klein_decomposable`).

Gap row G3-061. Source read (pdftotext): T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196: section 1.2
"2-spinors in Minkowski space", eqs. (1.2)–(1.4), p. 5 (the spinor matrix, `η_ab v^a v^b = 2 det(v^{αα̇})`, null iff
`v^{αα̇} = a^α ã^α̇`); section 1.3 "Real slices and spinor conjugations", eqs. (1.12)–(1.13), p. 7 (real Minkowski space as
Hermitian matrices); section 1.4 "Twistor space", eqs. (1.21)–(1.23), p. 9 and (1.24)–(1.28), p. 10 (the incidence relation,
a point as a line `ℂ² ⊂ ℂ⁴`, every linear embedding put in incidence form, lines meet iff null separated); section 2.3
"Conformal structures", eqs. (2.24)–(2.29), pp. 19–21 and footnote 2, p. 20 (bi-twistors, the Klein quadric
`Q = {X ∈ CP⁵ | ε_{ABCD} X^{AB} X^{CD} = 0}`, the infinity twistor and points at infinity).
**Conventions.** The source's metric has signature `(+, −, −, −)`, `qC x = x⁰² − x¹² − x²² − x³²`; the library's `η` has
`(−, +, +, +)`, i.e. `−qC`. Indices: `Z = (μ^{0̇}, μ^{1̇}, λ_0, λ_1)` as in (1.22). Mathlib's `Module.Grassmannian`
parametrises quotients (`G(n − k, V; F)` is the subspace Grassmannian); we use 2-dimensional submodules directly.
-/

open Matrix Complex
open scoped TensorProduct

noncomputable section

namespace Lightlike

/-! ## The spinor matrix -/

/-- The spinor matrix `x^{αα̇} = (1/√2) [[x⁰ + x³, x¹ − i x²], [x¹ + i x², x⁰ − x³]]` (Adamo (1.12)). -/
def spinorMat (x : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![x 0 + x 3, x 1 - I * x 2; x 1 + I * x 2, x 0 - x 3]

/-- The inverse of the spinor map. -/
def spinorInv (m : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • ![m 0 0 + m 1 1, m 0 1 + m 1 0, I * (m 0 1 - m 1 0), m 0 0 - m 1 1]

private lemma sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact_mod_cast this.ne'

private lemma sqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  have : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  exact_mod_cast this

/-- **`M_ℂ ≅ M₂(ℂ)`**: the spinor map is a linear equivalence. -/
def spinorEquiv : (Fin 4 → ℂ) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := spinorMat
  invFun := spinorInv
  map_add' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [spinorMat] <;> ring
  map_smul' c x := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [spinorMat] <;> ring
  left_inv x := by
    have h := sqrt2_ne
    have h2 := sqrt2_sq
    ext i; fin_cases i <;> simp [spinorMat, spinorInv] <;> field_simp <;> ring_nf <;> simp [h2, Complex.I_sq] <;> ring
  right_inv m := by
    have h := sqrt2_ne
    have h2 := sqrt2_sq
    ext i j; fin_cases i <;> fin_cases j <;> simp [spinorMat, spinorInv] <;> field_simp <;> ring_nf <;>
      simp [h2, Complex.I_sq] <;> ring

/-- The complexified Minkowski form in the source's signature `(+, −, −, −)`. -/
def qC (x : Fin 4 → ℂ) : ℂ := x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2

/-- **The Minkowski form is twice the determinant** (Adamo (1.3)). -/
theorem qC_eq_two_det (x : Fin 4 → ℂ) : qC x = 2 * (spinorMat x).det := by
  have h := sqrt2_ne
  have h2 := sqrt2_sq
  rw [Matrix.det_fin_two]
  simp [spinorMat, qC]
  field_simp
  ring_nf
  simp [h2, Complex.I_sq]
  ring

/-! ## The null cone -/

/-- A `2 × 2` matrix has determinant zero iff it is an outer product `a bᵀ`. -/
theorem det_eq_zero_iff_vecMulVec (m : Matrix (Fin 2) (Fin 2) ℂ) :
    m.det = 0 ↔ ∃ a b : Fin 2 → ℂ, m = vecMulVec a b := by
  constructor
  · intro h
    rw [Matrix.det_fin_two] at h
    by_cases h00 : m 0 0 = 0
    · by_cases h01 : m 0 1 = 0
      · refine ⟨![0, 1], ![m 1 0, m 1 1], ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [vecMulVec, h00, h01]
      · have h10 : m 1 0 = 0 := by
          have hp : m 0 1 * m 1 0 = 0 := by rw [h00] at h; linear_combination -h
          exact (mul_eq_zero.1 hp).resolve_left h01
        refine ⟨![m 0 1, m 1 1], ![0, 1], ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [vecMulVec, h00, h10]
    · refine ⟨![m 0 0, m 1 0], ![1, m 0 1 / m 0 0], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec] <;> (try field_simp) <;>
        first | linear_combination h | linear_combination -h | ring
  · rintro ⟨a, b, rfl⟩
    rw [Matrix.det_fin_two]
    simp [vecMulVec]
    ring

/-- **The null cone of `M_ℂ` is the set of rank-one spinor matrices** (Adamo (1.4)): `qC x = 0` iff
`x^{αα̇} = a^α ã^α̇`. -/
theorem qC_eq_zero_iff (x : Fin 4 → ℂ) :
    qC x = 0 ↔ ∃ a b : Fin 2 → ℂ, spinorMat x = vecMulVec a b := by
  rw [qC_eq_two_det, mul_eq_zero, or_iff_right two_ne_zero]
  exact det_eq_zero_iff_vecMulVec _

/-- **`ℂ² ⊗ ℂ² ≅ M₂(ℂ)`**, sending `a ⊗ b` to the outer product `a bᵀ` (`tensorEquiv_tmul`). -/
def spinorTensorEquiv : (Fin 2 → ℂ) ⊗[ℂ] (Fin 2 → ℂ) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).equivFun ≪≫ₗ
    LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

lemma tensorEquiv_tmul (a b : Fin 2 → ℂ) : spinorTensorEquiv (a ⊗ₜ b) = vecMulVec a b := by
  ext i j
  change ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).equivFun (a ⊗ₜ b) (i, j) =
    vecMulVec a b i j
  rw [Module.Basis.equivFun_apply, Module.Basis.tensorProduct_repr_tmul_apply]
  simp [vecMulVec, mul_comm]

/-- **`M_ℂ ≅ ℂ² ⊗ ℂ²`, with the null cone as the pure tensors.** -/
theorem qC_eq_zero_iff_tmul (x : Fin 4 → ℂ) :
    qC x = 0 ↔ ∃ a b : Fin 2 → ℂ, spinorTensorEquiv.symm (spinorEquiv x) = a ⊗ₜ b := by
  rw [qC_eq_zero_iff]
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, ?_⟩
    rw [LinearEquiv.symm_apply_eq, tensorEquiv_tmul]
    exact h
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, ?_⟩
    rw [LinearEquiv.symm_apply_eq, tensorEquiv_tmul] at h
    exact h

/-! ## The real slice -/

lemma star_inv_sqrt2_mul {A B : ℂ}
    (h : star (((Real.sqrt 2 : ℂ)⁻¹) * A) = ((Real.sqrt 2 : ℂ)⁻¹) * B) : star A = B := by
  have hc : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [star_inv₀]
    congr 1
    exact Complex.conj_ofReal _
  rw [star_mul', hc] at h
  exact mul_left_cancel₀ (inv_ne_zero sqrt2_ne) h

/-- **Real Minkowski space is the set of Hermitian spinor matrices** (Adamo (1.13)). -/
theorem isHermitian_spinorMat_iff (x : Fin 4 → ℂ) :
    (spinorMat x).IsHermitian ↔ ∀ i, (x i).im = 0 := by
  constructor
  · intro h
    have e : ∀ i j, star (spinorMat x j i) = spinorMat x i j := fun i j => by
      have := congrFun (congrFun h i) j
      simpa [Matrix.conjTranspose_apply] using this
    have f00 : star (x 0 + x 3) = x 0 + x 3 := star_inv_sqrt2_mul (by simpa [spinorMat] using e 0 0)
    have f11 : star (x 0 - x 3) = x 0 - x 3 := star_inv_sqrt2_mul (by simpa [spinorMat] using e 1 1)
    have f01 : star (x 1 + I * x 2) = x 1 - I * x 2 :=
      star_inv_sqrt2_mul (by simpa [spinorMat] using e 0 1)
    have g00 := congrArg Complex.im f00
    have g11 := congrArg Complex.im f11
    have g01 := congrArg Complex.im f01
    have r01 := congrArg Complex.re f01
    simp at g00 g11 g01 r01
    intro i
    fin_cases i <;> simp <;> linarith
  · intro h
    have hx : ∀ i, star (x i) = x i := fun i => Complex.conj_eq_iff_im.2 (h i)
    have hc : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact Complex.conj_ofReal _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinorMat, Matrix.conjTranspose_apply, star_mul', hc, hx, Complex.conj_I] <;> ring

/-! ## Twistor lines: the compactification as 2-planes in `ℂ⁴` -/

/-- The `4 × 2` matrix of the incidence relation `μ^{α̇} = x^{αα̇} λ_α` (Adamo (1.23)), for twistors
`Z = (μ^{0̇}, μ^{1̇}, λ_0, λ_1)`. -/
def incidenceMat (x : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 2) ℂ :=
  !![spinorMat x 0 0, spinorMat x 1 0; spinorMat x 0 1, spinorMat x 1 1; 1, 0; 0, 1]

/-- The incidence map `λ ↦ (μ, λ)`. -/
def incidence (x : Fin 4 → ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) := Matrix.toLin' (incidenceMat x)

/-- The projection `Z ↦ λ` onto the undotted part. -/
def lambdaPart : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := Matrix.toLin' !![0, 0, 1, 0; 0, 0, 0, 1]

lemma lambdaPart_apply (Z : Fin 4 → ℂ) : lambdaPart Z = ![Z 2, Z 3] := by
  ext i; fin_cases i <;> simp [lambdaPart, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

lemma incidence_apply (x : Fin 4 → ℂ) (l : Fin 2 → ℂ) :
    incidence x l = ![spinorMat x 0 0 * l 0 + spinorMat x 1 0 * l 1,
      spinorMat x 0 1 * l 0 + spinorMat x 1 1 * l 1, l 0, l 1] := by
  ext i; fin_cases i <;> simp [incidence, incidenceMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma lambdaPart_incidence (x : Fin 4 → ℂ) (l : Fin 2 → ℂ) : lambdaPart (incidence x l) = l := by
  rw [lambdaPart_apply, incidence_apply]
  ext i; fin_cases i <;> simp

lemma incidence_injective (x : Fin 4 → ℂ) : Function.Injective (incidence x) := fun l l' h => by
  have := congrArg lambdaPart h
  rwa [lambdaPart_incidence, lambdaPart_incidence] at this

/-- **The twistor line of a point** `x ∈ M_ℂ`: the 2-plane `{(μ, λ) : μ^{α̇} = x^{αα̇} λ_α}` of `ℂ⁴` (a projective line in
`CP³`, Adamo p. 10). -/
def twistorLine (x : Fin 4 → ℂ) : Submodule ℂ (Fin 4 → ℂ) := LinearMap.range (incidence x)

/-- The plane at infinity `I = {λ = 0}` (the infinity twistor of Adamo (2.29)). -/
def infinityPlane : Submodule ℂ (Fin 4 → ℂ) := LinearMap.ker lambdaPart

/-- Twistor lines are 2-planes. -/
theorem finrank_twistorLine (x : Fin 4 → ℂ) : Module.finrank ℂ (twistorLine x) = 2 := by
  unfold twistorLine
  rw [LinearMap.finrank_range_of_inj (incidence_injective x)]
  simp

/-- **Twistor lines are complementary to the plane at infinity.** -/
theorem twistorLine_inf_infinity (x : Fin 4 → ℂ) : twistorLine x ⊓ infinityPlane = ⊥ := by
  rw [eq_bot_iff]
  rintro Z ⟨⟨l, rfl⟩, hZ⟩
  have : l = 0 := by
    have := (LinearMap.mem_ker.1 hZ)
    rwa [lambdaPart_incidence] at this
  simp [this]

/-- **A point is determined by its twistor line.** -/
theorem twistorLine_injective : Function.Injective twistorLine := by
  intro x y h
  have key : ∀ l, incidence x l = incidence y l := by
    intro l
    have hm : incidence x l ∈ twistorLine y := h ▸ LinearMap.mem_range_self _ l
    obtain ⟨l', hl'⟩ := hm
    have hl : l' = l := by
      have := congrArg lambdaPart hl'
      rwa [lambdaPart_incidence, lambdaPart_incidence] at this
    rw [← hl', hl]
  have hm : spinorMat x = spinorMat y := by
    have e0 := key ![1, 0]
    have e1 := key ![0, 1]
    rw [incidence_apply, incidence_apply] at e0 e1
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using congrFun e0 0
    · simpa using congrFun e0 1
    · simpa using congrFun e1 0
    · simpa using congrFun e1 1
  exact spinorEquiv.injective hm

/-- **Every 2-plane complementary to the plane at infinity is a twistor line** (Adamo (1.24)–(1.25), p. 10: every
linear embedding of a projective line, after fixing its parametrization, has the form of the incidence relations):
complexified Minkowski space is the affine chart of the Grassmannian of 2-planes of `ℂ⁴` complementary to `I`. -/
theorem exists_twistorLine_eq (L : Submodule ℂ (Fin 4 → ℂ)) (hL : Module.finrank ℂ L = 2)
    (hI : L ⊓ infinityPlane = ⊥) : ∃ x, twistorLine x = L := by
  set f : L →ₗ[ℂ] (Fin 2 → ℂ) := lambdaPart.domRestrict L with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    have hmem : (z : Fin 4 → ℂ) ∈ L ⊓ infinityPlane := ⟨z.2, LinearMap.mem_ker.2 hz⟩
    rw [hI, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact Subtype.ext hmem
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hL]; simp)).1 hinj
  set e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  set Z : Fin 2 → Fin 4 → ℂ := fun a => (e.symm (Pi.single a 1) : Fin 4 → ℂ) with hZ
  have hZL : ∀ a, Z a ∈ L := fun a => (e.symm (Pi.single a 1)).2
  have hlam : ∀ a, lambdaPart (Z a) = (Pi.single a (1 : ℂ) : Fin 2 → ℂ) := fun a => by
    have h := e.apply_symm_apply (Pi.single a (1 : ℂ))
    exact h
  have h2 : ∀ a, Z a 2 = (Pi.single a (1 : ℂ) : Fin 2 → ℂ) 0 := fun a => by
    have := congrFun (hlam a) 0
    rw [lambdaPart_apply] at this
    simpa using this
  have h3 : ∀ a, Z a 3 = (Pi.single a (1 : ℂ) : Fin 2 → ℂ) 1 := fun a => by
    have := congrFun (hlam a) 1
    rw [lambdaPart_apply] at this
    simpa using this
  set m : Matrix (Fin 2) (Fin 2) ℂ := !![Z 0 0, Z 0 1; Z 1 0, Z 1 1] with hm
  refine ⟨spinorEquiv.symm m, ?_⟩
  have hsm : spinorMat (spinorEquiv.symm m) = m := spinorEquiv.apply_symm_apply m
  have hle : twistorLine (spinorEquiv.symm m) ≤ L := by
    rintro _ ⟨l, rfl⟩
    have : incidence (spinorEquiv.symm m) l = l 0 • Z 0 + l 1 • Z 1 := by
      rw [incidence_apply, hsm]
      ext i
      fin_cases i
      · simp [hm]; ring
      · simp [hm]; ring
      · simp [h2]
      · simp [h3]
    rw [this]
    exact L.add_mem (L.smul_mem _ (hZL 0)) (L.smul_mem _ (hZL 1))
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_twistorLine, hL])

/-- **Two twistor lines meet iff their points are null separated** (Adamo (1.26)–(1.28)). -/
theorem twistorLine_inf_ne_bot_iff (x y : Fin 4 → ℂ) :
    twistorLine x ⊓ twistorLine y ≠ ⊥ ↔ qC (x - y) = 0 := by
  rw [qC_eq_two_det, mul_eq_zero, or_iff_right two_ne_zero, show spinorMat (x - y) = spinorMat x - spinorMat y from
    map_sub spinorEquiv x y, ← Matrix.det_transpose, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · intro hne
    obtain ⟨Z, ⟨⟨l, rfl⟩, ⟨l', hl'⟩⟩, hZ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hl : l' = l := by
      have := congrArg lambdaPart hl'
      rwa [lambdaPart_incidence, lambdaPart_incidence] at this
    subst hl
    refine ⟨l', fun h0 => hZ (by simp [h0]), ?_⟩
    have e := hl'
    rw [incidence_apply, incidence_apply] at e
    ext b
    fin_cases b
    · have := congrFun e 0
      simp at this
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -this
    · have := congrFun e 1
      simp at this
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -this
  · rintro ⟨l, hl0, hl⟩
    intro hbot
    have hmem : incidence x l ∈ twistorLine x ⊓ twistorLine y := by
      refine ⟨LinearMap.mem_range_self _ l, l, ?_⟩
      rw [incidence_apply, incidence_apply]
      have h0 := congrFun hl 0
      have h1 := congrFun hl 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      ext i
      fin_cases i
      · simp
        linear_combination -h0
      · simp
        linear_combination -h1
      · simp
      · simp
    rw [hbot, Submodule.mem_bot] at hmem
    exact hl0 (incidence_injective x (by rw [hmem, map_zero]))

/-! ## The Klein quadric -/

/-- The Plücker coordinates `X^{AB} = Z₁^A Z₂^B − Z₂^A Z₁^B` of the plane spanned by `Z₁, Z₂` (the bi-twistor
`Z₁ ∧ Z₂`, Adamo's exercise p. 11 and (2.25)). -/
def plucker (Z₁ Z₂ : Fin 4 → ℂ) (A B : Fin 4) : ℂ := Z₁ A * Z₂ B - Z₂ A * Z₁ B

/-- **Plücker coordinates lie on the Klein quadric** `X⁰¹X²³ − X⁰²X¹³ + X⁰³X¹² = 0` (`ε_{ABCD} X^{AB} X^{CD} = 0`,
Adamo footnote 2, p. 20; `ε_{ABCD} X^{AB} X^{CD}` is `8` times this Pfaffian). -/
theorem plucker_klein (Z₁ Z₂ : Fin 4 → ℂ) :
    plucker Z₁ Z₂ 0 1 * plucker Z₁ Z₂ 2 3 - plucker Z₁ Z₂ 0 2 * plucker Z₁ Z₂ 1 3 +
      plucker Z₁ Z₂ 0 3 * plucker Z₁ Z₂ 1 2 = 0 := by
  unfold plucker
  ring

/-- The Plücker relation for a skew `4 × 4` matrix with vanishing Pfaffian:
`X_ab X_AB = X_aA X_bB − X_bA X_aB` for all indices. -/
theorem plucker_identity (X : Fin 4 → Fin 4 → ℂ) (hskew : ∀ A B, X B A = -X A B)
    (hPf : X 0 1 * X 2 3 - X 0 2 * X 1 3 + X 0 3 * X 1 2 = 0) (a b A B : Fin 4) :
    X a b * X A B = X a A * X b B - X b A * X a B := by
  have d : ∀ i, X i i = 0 := fun i => by have := hskew i i; linear_combination this / 2
  have h10 := hskew 0 1
  have h20 := hskew 0 2
  have h30 := hskew 0 3
  have h21 := hskew 1 2
  have h31 := hskew 1 3
  have h32 := hskew 2 3
  have d0 := d 0
  have d1 := d 1
  have d2 := d 2
  have d3 := d 3
  fin_cases a <;> fin_cases b <;> fin_cases A <;> fin_cases B <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h10, h20, h30, h21, h31, h32, d0, d1, d2, d3] <;>
    first | linear_combination hPf | linear_combination -hPf | ring

/-- **Every nonzero point of the Klein quadric is a decomposable bivector** (the converse of `plucker_klein`): a
nonzero skew `X` with vanishing Pfaffian is `Z₁ ∧ Z₂`, with `Z₁` the row `a` divided by `X_ab` and `Z₂` the row `b`, for
any nonzero entry `X_ab`. So the Klein quadric is the image of the Plücker map of 2-planes of `ℂ⁴`. -/
theorem klein_decomposable (X : Fin 4 → Fin 4 → ℂ) (hskew : ∀ A B, X B A = -X A B)
    (hPf : X 0 1 * X 2 3 - X 0 2 * X 1 3 + X 0 3 * X 1 2 = 0) (hX : X ≠ 0) :
    ∃ Z₁ Z₂ : Fin 4 → ℂ, ∀ A B, X A B = plucker Z₁ Z₂ A B := by
  obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hX (funext fun a => funext fun b => h a b)
  refine ⟨fun A => X a A / X a b, fun B => X b B, fun A B => ?_⟩
  have key := plucker_identity X hskew hPf a b A B
  unfold plucker
  field_simp
  linear_combination key

/-- **The bi-twistor of a point** (Adamo (2.25)): for the twistor line of `x` spanned by `λ = (1, 0)` and `λ = (0, 1)`,
`X²³ = 1` (the infinity twistor pairing `I_{AB} X^{AB} = ⟨λ₁λ₂⟩`, (2.29)) and `X⁰¹ = det x^{αα̇} = qC x / 2` (the entry
`½ x²` of (2.25)). -/
theorem plucker_twistorLine (x : Fin 4 → ℂ) :
    plucker (incidence x ![1, 0]) (incidence x ![0, 1]) 2 3 = 1 ∧
      plucker (incidence x ![1, 0]) (incidence x ![0, 1]) 0 1 = qC x / 2 := by
  refine ⟨by simp [plucker, incidence_apply], ?_⟩
  rw [qC_eq_two_det, Matrix.det_fin_two]
  simp [plucker, incidence_apply]
  ring

/-! ## Trust checks -/

/-- A null vector: `(1, 1, 0, 0)`, so the twistor lines of `0` and `(1, 1, 0, 0)` meet. -/
theorem qC_null_example : qC ![1, 1, 0, 0] = 0 := by simp [qC]

/-- A timelike vector is not null: `qC (1, 0, 0, 0) = 1`, so the twistor lines of `0` and `(1, 0, 0, 0)` are disjoint
(`twistorLine_inf_ne_bot_iff`). -/
theorem qC_timelike_example : qC ![1, 0, 0, 0] = 1 := by simp [qC]

theorem twistorLine_disjoint_example : twistorLine ![1, 0, 0, 0] ⊓ twistorLine 0 = ⊥ := by
  by_contra h
  have := (twistorLine_inf_ne_bot_iff ![1, 0, 0, 0] 0).1 h
  simp [qC] at this

end Lightlike

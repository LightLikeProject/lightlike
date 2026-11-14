import Lightlike.SU2.SpinRep
import Lightlike.Spin4.Burnside

/-!
# The irreducible representations `(j₊, j₋)` of Spin(4) = SU(2) × SU(2)

The group Spin(4), the double cover of SO(4), is isomorphic to `SU(2) × SU(2)` (unit quaternions
acting on `ℍ ≅ ℝ⁴` by `x ↦ p x q⁻¹`). We take `Spin4 := SU2 × SU2` as the definition. Its
representation of spin `(j₊, j₋) = (n/2, m/2)` is the tensor product of the spin-`n/2`
representation of the first factor and the spin-`m/2` representation of the second, both from
`Lightlike/SU2/SpinRep.lean`.

Spins are doubled, as everywhere in this library: `n = 2j₊`, `m = 2j₋ ∈ ℕ`.

## Two forms of the same representation

* **Tensor form** `spin4Tensor n m`: Mathlib's tensor product `ℂ^{n+1} ⊗ ℂ^{m+1}` with
  `(g₊, g₋) ↦ D^{n/2}(g₊) ⊗ D^{m/2}(g₋)` (the external tensor product `extTprod` of
  `spinRepresentation n` and `spinRepresentation m`). This is the definition in the roadmap.
* **Matrix form** `spin4Mat n m g = spinMat n g₊ ⊗ₖ spinMat m g₋`, the Kronecker product, acting
  on `ℂ^{(n+1)(m+1)}` indexed by pairs; as a group homomorphism into the unitary group,
  `spin4Rep n m`, and as a Mathlib representation, `spin4Representation n m`. This is the
  concrete form for computations.

`spin4Equiv` is an equivalence of representations between the two forms: the product basis of the
tensor product goes to the standard basis indexed by pairs.

## Proven here (standard axioms only)

* **Homomorphism, unitary, continuous:** `spin4Mat_mul`, `spin4Mat_one`,
  `spin4Mat_mem_unitaryGroup`, `spin4Rep`, `continuous_spin4Rep`.
* **Dimension `(2j₊+1)(2j₋+1)`:** `finrank_tensorSpace`, `finrank_idx` (both `(n+1)(m+1)`).
* **Irreducible:** `spin4Tensor_isIrreducible`, `spin4Representation_isIrreducible`, from
  Burnside's theorem (`Lightlike/Spin4/Burnside.lean`) and the irreducibility of the SU(2) factors.
* **Equivalence of the two forms:** `spin4Equiv`.
* **Centre:** `spin4Mat_negOne_negOne` (`(-1, -1) ↦ (-1)^{n+m}`) and `spin4Mat_negOne_one`
  (`(-1, 1) ↦ (-1)^n`), `spin4Mat_one_negOne` (`(1, -1) ↦ (-1)^m`).
* **Weights:** `spin4Mat_torus` (the maximal torus acts diagonally by `e^{i((n-2k)α + (m-2l)β)}`).
* **The labels are faithful:** `spin4Representation_equiv_iff` (`(n, m) ≅ (n', m')` exactly when
  `n = n'` and `m = m'`), by comparing torus eigenvalues at a root of unity of large order.
* **Unitary in tensor form:** `spin4Unitary` (into the linear isometries of the Hilbert space
  `ℂ^{n+1} ⊗ ℂ^{m+1}` with the tensor-product inner product), equal to `spin4Tensor` on the
  underlying vector space (`hilbertEquiv_spin4Isometry`); `inner_spin4Unitary`.

## Companion files

* `Lightlike/Spin4/SO4.lean`: `Spin4` is the double cover of SO(4) (`toSO4`, surjective, kernel
  `±(1,1)`).
* `Lightlike/Spin4/Clifford.lean`: `Spin4` is Mathlib's Clifford-algebra `spinGroup` of `ℝ⁴`
  (`spinEquiv`), compatibly with the action on vectors.
* `Lightlike/Spin4/Completeness.lean`: every continuous irreducible representation is some `(n, m)`
  (`spin4Rep_complete`).
* `Lightlike/Spin4/ClebschGordan.lean`: restricted to the diagonal SU(2), `(n/2, m/2)` splits into
  the spins `(n+m)/2 - k`, `k ≤ min(n, m)` (`spin4_diag_clebschGordan`).

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics 129,
  Springer (1991), Lectures 11 and 18–20 (representations of sl₂; so₄ ≅ sl₂ × sl₂).
* J. C. Baez, *Spin foam models*, Class. Quantum Grav. 15 (1998) 1827, arXiv:gr-qc/9709052
  (the representations (j₊, j₋) of Spin(4) in 4D spin foam models).
-/

open Matrix TensorProduct
open scoped Kronecker

namespace Lightlike

/-- **The group Spin(4)**, defined as `SU(2) × SU(2)` (the left and right unit quaternions). -/
abbrev Spin4 := SU2 × SU2

namespace Spin4

open SU2

variable {n m : ℕ}

/-! ## A. Tensor form -/

/-- The representation space of spin `(n/2, m/2)` in tensor-product form,
`ℂ^{n+1} ⊗ ℂ^{m+1}`. -/
abbrev TensorSpace (n m : ℕ) := (Fin (n + 1) → ℂ) ⊗[ℂ] (Fin (m + 1) → ℂ)

/-- **The spin-`(n/2, m/2)` representation of Spin(4)**, tensor form: the external tensor product
of the spin-`n/2` representation of the first SU(2) factor and the spin-`m/2` representation of
the second. -/
noncomputable def spin4Tensor (n m : ℕ) : Representation ℂ Spin4 (TensorSpace n m) :=
  extTprod (spinRepresentation n) (spinRepresentation m)

lemma spin4Tensor_apply_tmul (g : Spin4) (v : Fin (n + 1) → ℂ) (w : Fin (m + 1) → ℂ) :
    spin4Tensor n m g (v ⊗ₜ w) = (spinMat n g.1 *ᵥ v) ⊗ₜ (spinMat m g.2 *ᵥ w) := rfl

/-- **Irreducibility, tensor form.** -/
theorem spin4Tensor_isIrreducible (n m : ℕ) : (spin4Tensor n m).IsIrreducible := by
  have := spinRepresentation_isIrreducible (n := n)
  have := spinRepresentation_isIrreducible (n := m)
  exact isIrreducible_extTprod _ _

/-- **Dimension, tensor form:** `(2j₊ + 1)(2j₋ + 1) = (n + 1)(m + 1)`. -/
theorem finrank_tensorSpace (n m : ℕ) :
    Module.finrank ℂ (TensorSpace n m) = (n + 1) * (m + 1) := by
  simp [Module.finrank_tensorProduct]

/-! ## B. Matrix form -/

/-- Basis labels of the matrix form: pairs `(k, l)` of an SU(2)₊ label and an SU(2)₋ label. -/
abbrev Idx (n m : ℕ) := Fin (n + 1) × Fin (m + 1)

/-- The spin-`(n/2, m/2)` matrix of `g = (g₊, g₋)`: the Kronecker product
`D^{n/2}(g₊) ⊗ₖ D^{m/2}(g₋)`. -/
noncomputable def spin4Mat (n m : ℕ) (g : Spin4) : Matrix (Idx n m) (Idx n m) ℂ :=
  spinMat n g.1 ⊗ₖ spinMat m g.2

lemma spin4Mat_apply (g : Spin4) (p q : Idx n m) :
    spin4Mat n m g p q = spinMat n g.1 p.1 q.1 * spinMat m g.2 p.2 q.2 := rfl

theorem spin4Mat_mul (g h : Spin4) : spin4Mat n m (g * h) = spin4Mat n m g * spin4Mat n m h := by
  simp only [spin4Mat, Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, spinMat_mul,
    mul_kronecker_mul]

theorem spin4Mat_one : spin4Mat n m 1 = 1 := by
  simp only [spin4Mat, Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, spinMat_one,
    one_kronecker_one]

/-- **Unitarity.** -/
theorem spin4Mat_mem_unitaryGroup (g : Spin4) :
    spin4Mat n m g ∈ Matrix.unitaryGroup (Idx n m) ℂ := by
  have h1 := Matrix.mem_unitaryGroup_iff.mp (spinRep n g.1).2
  have h2 := Matrix.mem_unitaryGroup_iff.mp (spinRep m g.2).2
  simp only [spinRep_apply] at h1 h2
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, spin4Mat, conjTranspose_kronecker,
    ← mul_kronecker_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose, h1, h2,
    one_kronecker_one]

/-- **The spin-`(n/2, m/2)` unitary representation of Spin(4)**, matrix form, as a homomorphism
into the unitary group of `ℂ^{(n+1)(m+1)}`. -/
noncomputable def spin4Rep (n m : ℕ) : Spin4 →* Matrix.unitaryGroup (Idx n m) ℂ where
  toFun g := ⟨spin4Mat n m g, spin4Mat_mem_unitaryGroup g⟩
  map_one' := Subtype.ext spin4Mat_one
  map_mul' g h := Subtype.ext (spin4Mat_mul g h)

@[simp] lemma spin4Rep_apply (g : Spin4) :
    (spin4Rep n m g : Matrix (Idx n m) (Idx n m) ℂ) = spin4Mat n m g := rfl

/-- **Continuity.** -/
theorem continuous_spin4Rep :
    Continuous fun g : Spin4 => (spin4Rep n m g : Matrix (Idx n m) (Idx n m) ℂ) := by
  have h1 : Continuous fun g : Spin4 => spinMat n (g.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_spinMat.comp (continuous_subtype_val.comp continuous_fst)
  have h2 : Continuous fun g : Spin4 => spinMat m (g.2 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_spinMat.comp (continuous_subtype_val.comp continuous_snd)
  exact continuous_matrix fun p q =>
    (h1.matrix_elem p.1 q.1).mul (h2.matrix_elem p.2 q.2)

/-- The matrix form as a Mathlib `Representation` on `ℂ^{(n+1)(m+1)}`. -/
noncomputable def spin4Representation (n m : ℕ) : Representation ℂ Spin4 (Idx n m → ℂ) where
  toFun g := Matrix.toLin' (spin4Mat n m g)
  map_one' := by simp [spin4Mat_one]; rfl
  map_mul' g h := by simp only [spin4Mat_mul, Matrix.toLin'_mul]; rfl

lemma spin4Representation_apply (g : Spin4) (v : Idx n m → ℂ) :
    spin4Representation n m g v = spin4Mat n m g *ᵥ v := rfl

/-- **Dimension, matrix form:** `(n + 1)(m + 1)`. -/
theorem finrank_idx (n m : ℕ) : Module.finrank ℂ (Idx n m → ℂ) = (n + 1) * (m + 1) := by
  simp

/-! ## C. The two forms are equivalent -/

/-- The product basis of `ℂ^{n+1} ⊗ ℂ^{m+1}`, indexed by pairs. -/
noncomputable def tensorBasis (n m : ℕ) : Module.Basis (Idx n m) ℂ (TensorSpace n m) :=
  (Pi.basisFun ℂ (Fin (n + 1))).tensorProduct (Pi.basisFun ℂ (Fin (m + 1)))

/-- Coordinates in the product basis: `ℂ^{n+1} ⊗ ℂ^{m+1} ≃ ℂ^{(n+1)(m+1)}`. -/
noncomputable def tensorEquiv (n m : ℕ) : TensorSpace n m ≃ₗ[ℂ] (Idx n m → ℂ) :=
  (tensorBasis n m).equivFun

lemma tensorEquiv_tmul (v : Fin (n + 1) → ℂ) (w : Fin (m + 1) → ℂ) :
    tensorEquiv n m (v ⊗ₜ w) = fun p => v p.1 * w p.2 := by
  funext ⟨i, j⟩
  simp [tensorEquiv, tensorBasis, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]

/-- A Kronecker product acts on a product vector `v ⊗ w` factorwise. -/
lemma kronecker_mulVec_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℂ)
    (B : Matrix κ κ ℂ) (v : ι → ℂ) (w : κ → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun p : ι × κ => v p.1 * w p.2) = fun p => (A *ᵥ v) p.1 * (B *ᵥ w) p.2 := by
  funext p
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The coordinate map intertwines the tensor form with the matrix form. -/
theorem tensorEquiv_spin4Tensor (g : Spin4) (x : TensorSpace n m) :
    tensorEquiv n m (spin4Tensor n m g x) = spin4Mat n m g *ᵥ tensorEquiv n m x := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    rw [spin4Tensor_apply_tmul, tensorEquiv_tmul, tensorEquiv_tmul, spin4Mat,
      kronecker_mulVec_prod]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mulVec_add]

/-- **The tensor form and the matrix form are equivalent representations.** -/
noncomputable def spin4Equiv (n m : ℕ) :
    (spin4Tensor n m).Equiv (spin4Representation n m) :=
  Representation.Equiv.mk (tensorEquiv n m) fun g =>
    LinearMap.ext fun x => tensorEquiv_spin4Tensor g x

/-- **Irreducibility, matrix form.** -/
theorem spin4Representation_isIrreducible (n m : ℕ) :
    (spin4Representation n m).IsIrreducible := by
  have := spin4Tensor_isIrreducible n m
  exact IsIrreducible.of_equiv (spin4Equiv n m)

/-- Irreducibility, matrix form, stated for subspaces: a subspace of `ℂ^{(n+1)(m+1)}` invariant
under every `spin4Mat n m g` is `0` or everything. -/
theorem isInvariant_eq_bot_or_eq_top {W : Submodule ℂ (Idx n m → ℂ)}
    (hW : ∀ g : Spin4, ∀ v ∈ W, spin4Mat n m g *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have := spin4Representation_isIrreducible n m
  rcases IsSimpleOrder.eq_bot_or_eq_top
      (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (spin4Representation n m)) with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-! ## D. The centre `{(±1, ±1)}` -/

/-- `(-1, -1)` acts as `(-1)^{n+m} = (-1)^{2(j₊+j₋)}`: trivially exactly when `j₊ + j₋` is an
integer, i.e. when the representation descends to `SO(4) = Spin(4)/{±(1,1)}`. -/
theorem spin4Mat_negOne_negOne :
    spin4Mat n m (negOne, negOne) = (-1 : ℂ) ^ (n + m) • (1 : Matrix (Idx n m) (Idx n m) ℂ) := by
  rw [spin4Mat, spinMat_negOne, spinMat_negOne, smul_kronecker, kronecker_smul,
    one_kronecker_one, smul_smul, pow_add, mul_comm]

/-- `(-1, 1)` acts as `(-1)^n`. -/
theorem spin4Mat_negOne_one :
    spin4Mat n m (negOne, 1) = (-1 : ℂ) ^ n • (1 : Matrix (Idx n m) (Idx n m) ℂ) := by
  rw [spin4Mat, spinMat_negOne, OneMemClass.coe_one, spinMat_one, smul_kronecker,
    one_kronecker_one]

/-- `(1, -1)` acts as `(-1)^m`. -/
theorem spin4Mat_one_negOne :
    spin4Mat n m (1, negOne) = (-1 : ℂ) ^ m • (1 : Matrix (Idx n m) (Idx n m) ℂ) := by
  rw [spin4Mat, spinMat_negOne, OneMemClass.coe_one, spinMat_one, kronecker_smul,
    one_kronecker_one]

/-! ## E. Weights -/

/-- The torus element `diag(e^{iθ}, e^{-iθ})` of SU(2). -/
noncomputable def torusExp (θ : ℝ) : SU2 :=
  torus (Complex.exp (θ * Complex.I)) (by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal])

/-- **Weights of `(j₊, j₋)`.** The torus acts on the basis vector `(k, l)` by
`e^{i((n - 2k)α + (m - 2l)β)}`, i.e. weights `(2m₊, 2m₋)` with `m₊ = j₊ - k`, `m₋ = j₋ - l`. -/
theorem spin4Mat_torus (α β : ℝ) :
    spin4Mat n m (torusExp α, torusExp β) = diagonal fun p : Idx n m =>
      Complex.exp ((((n : ℝ) - 2 * (p.1 : ℕ)) * α + ((m : ℝ) - 2 * (p.2 : ℕ)) * β : ℝ) *
        Complex.I) := by
  unfold torusExp
  rw [spin4Mat]
  dsimp only
  rw [spinMat_torus_exp, spinMat_torus_exp, diagonal_kronecker_diagonal]
  congr 1
  funext p
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## F. Distinct labels give inequivalent representations -/

/-- An isomorphism intertwining two diagonal matrices carries eigenvalues: every diagonal entry
`d i` of the first is a diagonal entry `d' j` of the second. -/
lemma exists_eq_of_intertwines_diagonal {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (e : (ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ)) (d : ι → ℂ) (d' : ι' → ℂ)
    (he : ∀ v, e (diagonal d *ᵥ v) = diagonal d' *ᵥ e v) (i : ι) : ∃ j, d' j = d i := by
  set v : ι → ℂ := Pi.single i 1 with hv_def
  have hv : v ≠ 0 := fun h0 => by simpa [v] using congrFun h0 i
  have hw : e v ≠ 0 := (LinearEquiv.map_ne_zero_iff e).mpr hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  refine ⟨j, ?_⟩
  have hdv : diagonal d *ᵥ v = d i • v := by
    rw [hv_def, diagonal_mulVec_single, mul_one]
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  have h := congrFun (he v) j
  rw [hdv, map_smul, mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
  exact (mul_right_cancel₀ hj h).symm

/-- If `e^{iaθ} = e^{ibθ}` for integers `a`, `b` with `θ = 2π/M` and `|a - b| < M`, then
`a = b`. -/
lemma int_eq_of_exp_eq {M : ℕ} (hM : 0 < M) {a b : ℤ} (h1 : a - b < M) (h2 : b - a < M)
    (h : Complex.exp (((a : ℝ) * (2 * Real.pi / M) : ℝ) * Complex.I) =
      Complex.exp (((b : ℝ) * (2 * Real.pi / M) : ℝ) * Complex.I)) : a = b := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI := Complex.I_ne_zero
  have hab : ((a - b : ℤ) : ℂ) = ((k * M : ℤ) : ℂ) := by
    push_cast at hk ⊢
    linear_combination (norm := (field_simp; ring)) (M / (2 * Real.pi * Complex.I)) * hk
  have hab' : a - b = k * M := by exact_mod_cast hab
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · nlinarith
  · rw [hk0, zero_mul] at hab'; linarith
  · nlinarith

/-- An equivalence `(n, m) ≅ (n', m')` forces `n ≤ n'` and `m ≤ m'`: the highest weight `e^{inθ}`
of `(n, m)` on the torus must be a weight `e^{i(n' - 2k)θ}` of `(n', m')`; at `θ = 2π/(n+n'+1)`
this forces `n = n' - 2k`. -/
lemma le_of_equiv {n m n' m' : ℕ}
    (φ : (spin4Representation n m).Equiv (spin4Representation n' m')) : n ≤ n' ∧ m ≤ m' := by
  let e := φ.toLinearEquiv
  have hint : ∀ g v, e (spin4Mat n m g *ᵥ v) = spin4Mat n' m' g *ᵥ e v := fun g v =>
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v
  constructor
  · set M := n + n' + 1 with hM
    have h := hint (torusExp (2 * Real.pi / M), torusExp 0)
    rw [spin4Mat_torus, spin4Mat_torus] at h
    obtain ⟨j, hj⟩ := exists_eq_of_intertwines_diagonal e _ _ h (0, 0)
    have e1 : ((n' : ℝ) - 2 * ((j.1 : ℕ) : ℝ)) * (2 * Real.pi / M) +
        ((m' : ℝ) - 2 * ((j.2 : ℕ) : ℝ)) * 0 =
        (((n' : ℤ) - 2 * ((j.1 : ℕ) : ℤ) : ℤ) : ℝ) * (2 * Real.pi / M) := by push_cast; ring
    have e2 : ((n : ℝ) - 2 * ((((0, 0) : Idx n m).1 : ℕ) : ℝ)) * (2 * Real.pi / M) +
        ((m : ℝ) - 2 * ((((0, 0) : Idx n m).2 : ℕ) : ℝ)) * 0 =
        (((n : ℤ) : ℤ) : ℝ) * (2 * Real.pi / M) := by simp
    rw [e1, e2] at hj
    have hj1 : ((j.1 : ℕ) : ℤ) ≤ n' := by have := j.1.2; omega
    have key := int_eq_of_exp_eq (M := M) (by omega) (by omega) (by omega) hj
    omega
  · set M := m + m' + 1 with hM
    have h := hint (torusExp 0, torusExp (2 * Real.pi / M))
    rw [spin4Mat_torus, spin4Mat_torus] at h
    obtain ⟨j, hj⟩ := exists_eq_of_intertwines_diagonal e _ _ h (0, 0)
    have e1 : ((n' : ℝ) - 2 * ((j.1 : ℕ) : ℝ)) * 0 +
        ((m' : ℝ) - 2 * ((j.2 : ℕ) : ℝ)) * (2 * Real.pi / M) =
        (((m' : ℤ) - 2 * ((j.2 : ℕ) : ℤ) : ℤ) : ℝ) * (2 * Real.pi / M) := by push_cast; ring
    have e2 : ((n : ℝ) - 2 * ((((0, 0) : Idx n m).1 : ℕ) : ℝ)) * 0 +
        ((m : ℝ) - 2 * ((((0, 0) : Idx n m).2 : ℕ) : ℝ)) * (2 * Real.pi / M) =
        (((m : ℤ) : ℤ) : ℝ) * (2 * Real.pi / M) := by simp
    rw [e1, e2] at hj
    have hj2 : ((j.2 : ℕ) : ℤ) ≤ m' := by have := j.2.2; omega
    have key := int_eq_of_exp_eq (M := M) (by omega) (by omega) (by omega) hj
    omega

/-- **The labels `(j₊, j₋)` are faithful:** the spin-`(n/2, m/2)` and spin-`(n'/2, m'/2)`
representations of Spin(4) are equivalent exactly when `n = n'` and `m = m'`. -/
theorem spin4Representation_equiv_iff {n m n' m' : ℕ} :
    Nonempty ((spin4Representation n m).Equiv (spin4Representation n' m')) ↔
      n = n' ∧ m = m' := by
  constructor
  · rintro ⟨φ⟩
    obtain ⟨h1, h2⟩ := le_of_equiv φ
    obtain ⟨h3, h4⟩ := le_of_equiv φ.symm
    omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨Representation.Equiv.refl _⟩

/-! ## G. Unitarity of the tensor form -/

/-- A unitary matrix acting on `EuclideanSpace ℂ ι` (the standard inner product) as a linear
isometry. -/
noncomputable def unitaryIsometry {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  have h1 : U * Uᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinearMap (Matrix.toEuclideanLin U) (Matrix.toEuclideanLin Uᴴ)
      (by rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.toLin_mul, h1, Matrix.toLin_one])
      (by rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.toLin_mul, h2,
        Matrix.toLin_one]))
    (fun x y => by
      change inner ℂ (Matrix.toEuclideanLin U x) (Matrix.toEuclideanLin U y) = inner ℂ x y
      rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        ← LinearMap.comp_apply, Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.toLin_mul,
        h2, Matrix.toLin_one, LinearMap.id_apply])

lemma unitaryIsometry_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (x : EuclideanSpace ℂ ι) :
    unitaryIsometry U hU x = Matrix.toEuclideanLin U x := rfl

/-- The representation space as a Hilbert space: the tensor product of the Euclidean spaces
`ℂ^{n+1}` and `ℂ^{m+1}`, with Mathlib's tensor-product inner product
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ ⟪b, d⟫`. -/
abbrev HilbertSpace (n m : ℕ) :=
  EuclideanSpace ℂ (Fin (n + 1)) ⊗[ℂ] EuclideanSpace ℂ (Fin (m + 1))

/-- The action of `g = (g₊, g₋)` on the Hilbert space: the tensor product of the unitaries
`D^{n/2}(g₊)` and `D^{m/2}(g₋)`, a linear isometry. -/
noncomputable def spin4Isometry (n m : ℕ) (g : Spin4) : HilbertSpace n m ≃ₗᵢ[ℂ] HilbertSpace n m :=
  TensorProduct.congrIsometry (unitaryIsometry _ (spinRep n g.1).2)
    (unitaryIsometry _ (spinRep m g.2).2)

/-- The Hilbert space and the tensor form's space `(Fin (n+1) → ℂ) ⊗ (Fin (m+1) → ℂ)` are the
same vector space (`EuclideanSpace` only adds the inner product). -/
noncomputable def hilbertEquiv (n m : ℕ) : HilbertSpace n m ≃ₗ[ℂ] TensorSpace n m :=
  TensorProduct.congr (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → ℂ))
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ))

/-- On the underlying vector space, `spin4Isometry` is the tensor form `spin4Tensor`. -/
theorem hilbertEquiv_spin4Isometry (g : Spin4) (x : HilbertSpace n m) :
    hilbertEquiv n m (spin4Isometry n m g x) = spin4Tensor n m g (hilbertEquiv n m x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [spin4Isometry, hilbertEquiv, unitaryIsometry_apply, spin4Tensor_apply_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Unitarity, tensor form.** The tensor form `spin4Tensor` is a unitary representation for the
tensor-product inner product: `g ↦ spin4Isometry n m g` is a group homomorphism from Spin(4) into
the linear isometries of the Hilbert space `ℂ^{n+1} ⊗ ℂ^{m+1}`, and it is `spin4Tensor` on the
underlying vector space (`hilbertEquiv_spin4Isometry`). -/
noncomputable def spin4Unitary (n m : ℕ) : Spin4 →* (HilbertSpace n m ≃ₗᵢ[ℂ] HilbertSpace n m) where
  toFun := spin4Isometry n m
  map_one' := by
    ext x
    apply (hilbertEquiv n m).injective
    rw [hilbertEquiv_spin4Isometry, map_one]
    rfl
  map_mul' g h := by
    ext x
    apply (hilbertEquiv n m).injective
    rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, hilbertEquiv_spin4Isometry,
      hilbertEquiv_spin4Isometry, hilbertEquiv_spin4Isometry, map_mul, Module.End.mul_apply]

/-- **Unitarity, tensor form:** every group element preserves the tensor-product inner
product. -/
theorem inner_spin4Unitary (g : Spin4) (x y : HilbertSpace n m) :
    inner ℂ (spin4Unitary n m g x) (spin4Unitary n m g y) = inner ℂ x y :=
  (spin4Unitary n m g).inner_map_map x y

end Spin4

end Lightlike

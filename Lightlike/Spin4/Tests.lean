import Lightlike.Spin4.Rep
import Lightlike.Tests.SU2
import Lightlike.Spin4.ClebschGordan
import Lightlike.Spin4.SO4
import Lightlike.Spin4.Completeness

/-!
# Trust checks for the Spin(4) representations (`Lightlike/Spin4/Rep.lean`)

Known values from the literature, and wrong inputs shown to give different answers.

* **Lowest spins.** `spin4Mat_zero_zero`: `(0, 0)` is the trivial representation.
  `spin4Mat_one_zero`, `spin4Mat_zero_one`: `(½, 0)` and `(0, ½)` are the defining representations
  of the two SU(2) factors (the left- and right-handed spinors).
* **Dimensions** `(2j₊+1)(2j₋+1)`: `4` for `(½, ½)`, `3` for `(1, 0)`, `9` for `(1, 1)`, `8` for
  `(3/2, ½)` (`finrank_half_half` and the following).
* **Weights** (`spin4Mat_torus`, in `Rep.lean`): the maximal torus
  `(diag(e^{iα}, e^{-iα}), diag(e^{iβ}, e^{-iβ}))` acts diagonally with eigenvalues
  `e^{i(2m₊α + 2m₋β)}`, `m± = j±, j± - 1, …, -j±`.
* **`(½, ½)` is the vector representation of SO(4).** `half_half_equiv_vector`: it is equivalent
  to the complexification of the rotation representation `toSO4Mat` of Spin(4) on `ℝ⁴`.
  `trace_spin4Mat_half_half_torus`: its character on the torus is `2 cos(α + β) + 2 cos(α - β)`,
  the trace of the rotation `x ↦ p x q⁻¹` of `ℝ⁴ ≅ ℍ` (`p = e^{iα}`, `q = e^{iβ}`), which rotates
  the planes `ℂ` and `ℂj` by `α - β` and `α + β`.
* **Centre.** `spin4Mat_negOne_negOne_eq_one_iff`: `(-1, -1)` acts trivially exactly when
  `j₊ + j₋` is an integer (these are the representations of SO(4)).
* **Wrong input: the two factors are not interchangeable.** `not_equiv_half_zero_zero_half`: the
  left- and right-handed spinors `(½, 0)` and `(0, ½)` have the same dimension but are not
  equivalent (`(-1, 1)` acts as `-1` on one, `+1` on the other); `neg_one_pow_eq_of_equiv` is
  the general parity obstruction.
* **Wrong model: the diagonal SU(2) instead of SU(2) × SU(2).** `spin4Mat_diag_singlet`,
  `diag_reducible`: restricted to pairs `(g, g)`, `(½, ½)` is reducible (the singlet spans an
  invariant line, spin `½ ⊗ ½ = 0 ⊕ 1`); `singlet_line_not_invariant`: under the full Spin(4) the
  same line is not invariant, as the irreducibility theorem requires.
* **Wrong model for Clebsch–Gordan: one block instead of several.** `card_cgIdx`: the blocks of
  `spin4_diag_clebschGordan` have total dimension `(n+1)(m+1)`.
  `not_equiv_diag_half_half_threeHalves`: on the diagonal, `(½, ½)` has the dimension 4 of spin
  3/2 but is not equivalent to it (it contains the invariant singlet line).
* **Wrong field for the tensor theorem.** `rot90_isIrreducible`, `not_isIrreducible_rot90_tensor`:
  over `ℝ`, rotation by `π/2` gives an irreducible representation of `ℤ` on `ℝ²` whose external
  tensor square (a representation of `ℤ × ℤ` on `ℝ² ⊗ ℝ²`) is reducible, so
  `isIrreducible_extTprod` needs an algebraically closed field.
* **Completeness is not vacuous.** `spin4Rep_complete_nonvacuous`: the trivial representation on
  `ℂ¹` satisfies the hypotheses of `spin4Rep_complete`, which identifies it as `(0, 0)`.
  `spin4_complete_nonvacuous`: `spin4_complete` applies to every `(n, m)` and returns `(n, m)`.
* **The hypotheses of completeness are needed.** `spin4Rep_complete_needs_pos`: for `d = 0` every
  other hypothesis holds and no `(n, m)` matches. `spin4Rep_complete_needs_continuity`: with a
  wild automorphism `σ` of `ℂ` (`exists_wild_ringEquiv`), `(g₊, g₋) ↦ σ(g₊)` is an irreducible
  representation on `ℂ²` that is not equivalent to any `(n, m)`.
-/

open Matrix
open scoped Kronecker

namespace Lightlike.Spin4.Test

open Lightlike.SU2 Lightlike.SU2.Test

/-! ### Lowest spins -/

/-- `(0, 0)` is the trivial representation. -/
theorem spin4Mat_zero_zero (g : Spin4) : spin4Mat 0 0 g = 1 := by
  rw [spin4Mat, spinMat_zero, spinMat_zero, one_kronecker_one]

/-- `(½, 0)` is the defining representation of the first factor (left-handed spinor). -/
theorem spin4Mat_one_zero (g : Spin4) :
    spin4Mat 1 0 g = (g.1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [spin4Mat, spinMat_one_eq, spinMat_zero]

/-- `(0, ½)` is the defining representation of the second factor (right-handed spinor). -/
theorem spin4Mat_zero_one (g : Spin4) :
    spin4Mat 0 1 g = (1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ (g.2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [spin4Mat, spinMat_one_eq, spinMat_zero]

/-! ### Dimensions -/

/-- `(½, ½)` has dimension 4. -/
theorem finrank_half_half : Module.finrank ℂ (TensorSpace 1 1) = 4 := by
  rw [finrank_tensorSpace]

/-- `(1, 0)` has dimension 3. -/
theorem finrank_one_zero : Module.finrank ℂ (TensorSpace 2 0) = 3 := by
  rw [finrank_tensorSpace]

/-- `(1, 1)` has dimension 9. -/
theorem finrank_one_one : Module.finrank ℂ (TensorSpace 2 2) = 9 := by
  rw [finrank_tensorSpace]

/-- `(3/2, ½)` has dimension 8. -/
theorem finrank_threeHalves_half : Module.finrank ℂ (TensorSpace 3 1) = 8 := by
  rw [finrank_tensorSpace]

/-! ### Weights and the character of `(½, ½)` -/

/-- **`(½, ½)` has the character of the vector representation of SO(4)**: the torus element
`(e^{iα}, e^{iβ})` acts on `ℝ⁴ ≅ ℍ` by `x ↦ p x q⁻¹`, a rotation by `α - β` in the plane `ℂ` and by
`α + β` in the plane `ℂj`, whose trace is `2 cos(α + β) + 2 cos(α - β)`. -/
theorem trace_spin4Mat_half_half_torus (α β : ℝ) :
    trace (spin4Mat 1 1 (torusExp α, torusExp β)) =
      ((2 * Real.cos (α + β) + 2 * Real.cos (α - β) : ℝ) : ℂ) := by
  rw [spin4Mat_torus, trace_diagonal, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.cast_zero,
    zero_add, add_zero, Nat.cast_one]
  push_cast
  simp only [Complex.cos]
  ring_nf

/-! ### The centre -/

/-- **`(-1, -1)` acts trivially exactly when `j₊ + j₋` is an integer**, i.e. `n + m` is even. -/
theorem spin4Mat_negOne_negOne_eq_one_iff {n m : ℕ} :
    spin4Mat n m (negOne, negOne) = 1 ↔ Even (n + m) := by
  rw [spin4Mat_negOne_negOne]
  constructor
  · intro h
    have h00 := congrFun (congrFun h (0, 0)) (0, 0)
    simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h00
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h00
  · intro h
    rw [h.neg_one_pow, one_smul]

/-! ### Wrong input: the two factors are not interchangeable -/

/-- **Parity obstruction.** Equivalent representations `(n, m)` and `(n', m')` have the same
parities: `(-1, 1)` and `(1, -1)` act by the scalars `(-1)^n` and `(-1)^m`. -/
theorem neg_one_pow_eq_of_equiv {n m n' m' : ℕ}
    (φ : (spin4Representation n m).Equiv (spin4Representation n' m')) :
    (-1 : ℂ) ^ n = (-1) ^ n' ∧ (-1 : ℂ) ^ m = (-1) ^ m' := by
  let e := φ.toLinearEquiv
  have key : ∀ (g : Spin4) (c c' : ℂ), spin4Mat n m g = c • 1 → spin4Mat n' m' g = c' • 1 →
      c = c' := by
    intro g c c' h h'
    let v : Idx n m → ℂ := Pi.single (0, 0) 1
    have hv : v ≠ 0 := fun hv0 => by
      have := congrFun hv0 (0, 0)
      simp [v] at this
    have hint := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v
    change e (spin4Mat n m g *ᵥ v) = spin4Mat n' m' g *ᵥ e v at hint
    rw [h, h', smul_mulVec, smul_mulVec, one_mulVec, one_mulVec, map_smul] at hint
    have hev : e v ≠ 0 := (LinearEquiv.map_ne_zero_iff e).mpr hv
    by_contra hcc
    have : (c - c') • e v = 0 := by rw [sub_smul, hint, sub_self]
    exact hev ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hcc))
  exact ⟨key (negOne, 1) _ _ spin4Mat_negOne_one spin4Mat_negOne_one,
    key (1, negOne) _ _ spin4Mat_one_negOne spin4Mat_one_negOne⟩

/-- **Chirality.** The left- and right-handed spinors `(½, 0)` and `(0, ½)` are not equivalent,
although both have dimension 2. -/
theorem not_equiv_half_zero_zero_half :
    IsEmpty ((spin4Representation 1 0).Equiv (spin4Representation 0 1)) :=
  ⟨fun φ => by
    have := (neg_one_pow_eq_of_equiv φ).1
    norm_num at this⟩

/-! ### Wrong model: the diagonal SU(2) -/

/-- The singlet `|↑↓⟩ - |↓↑⟩` in `ℂ² ⊗ ℂ²`, in the coordinates of the matrix form. -/
def singlet : Idx 1 1 → ℂ := fun p =>
  if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- On the diagonal `(g, g)`, the `(½, ½)` matrix multiplies the singlet by `det g`. -/
theorem spin4Mat_diag_singlet (g : SU2) :
    spin4Mat 1 1 (g, g) *ᵥ singlet = (g : Matrix (Fin 2) (Fin 2) ℂ).det • singlet := by
  rw [spin4Mat, spinMat_one_eq]
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply,
      det_fin_two, singlet] <;> ring

lemma singlet_ne_zero : singlet ≠ 0 := fun h => by
  have := congrFun h (0, 1)
  simp [singlet] at this

/-- The line spanned by the singlet. -/
def singletLine : Submodule ℂ (Idx 1 1 → ℂ) := Submodule.span ℂ {singlet}

lemma singletLine_ne_bot : singletLine ≠ ⊥ := by
  rw [singletLine, Ne, Submodule.span_singleton_eq_bot]
  exact singlet_ne_zero

lemma singletLine_ne_top : singletLine ≠ ⊤ := by
  intro htop
  have hmem : (Pi.single (0, 0) 1 : Idx 1 1 → ℂ) ∈ singletLine := htop ▸ trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have := congrFun hc (0, 0)
  simp [singlet] at this

/-- **Wrong model: the diagonal SU(2).** Restricted to pairs `(g, g)`, the `(½, ½)`
representation is reducible: the singlet line is invariant, nonzero and proper. -/
theorem diag_reducible :
    singletLine ≠ ⊥ ∧ singletLine ≠ ⊤ ∧
      ∀ g : SU2, ∀ v ∈ singletLine, spin4Mat 1 1 (g, g) *ᵥ v ∈ singletLine := by
  refine ⟨singletLine_ne_bot, singletLine_ne_top, fun g v hv => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [mulVec_smul, spin4Mat_diag_singlet, (mem_specialUnitaryGroup_iff.mp g.2).2, one_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Under the full Spin(4) the singlet line is not invariant**, as irreducibility
(`isInvariant_eq_bot_or_eq_top`) demands: independent rotations of the two factors move it. -/
theorem singlet_line_not_invariant :
    ¬ ∀ g : Spin4, ∀ v ∈ singletLine, spin4Mat 1 1 g *ᵥ v ∈ singletLine := fun h => by
  rcases isInvariant_eq_bot_or_eq_top h with h' | h'
  · exact singletLine_ne_bot h'
  · exact singletLine_ne_top h'

/-! ### Clebsch–Gordan -/

/-- The Clebsch–Gordan blocks have total dimension `(n+1)(m+1)`:
`Σ_{k ≤ min(n,m)} (n + m - 2k + 1) = (n+1)(m+1)`. -/
theorem card_cgIdx (n m : ℕ) : Fintype.card (CGIdx n m) = (n + 1) * (m + 1) :=
  PhyslibAlpha.Sl2.card_stringIndex

/-- **Wrong model: the diagonal `(½, ½)` is not spin 3/2**, although both have dimension 4: an
equivalence would carry the invariant singlet line to an invariant line of the irreducible spin
3/2. -/
theorem not_equiv_diag_half_half_threeHalves :
    ¬ ∃ T : (Idx 1 1 → ℂ) ≃ₗ[ℂ] (Fin (3 + 1) → ℂ),
      ∀ (g : SU2) (v : Idx 1 1 → ℂ), T (spin4Mat 1 1 (g, g) *ᵥ v) = spinMat 3 g *ᵥ T v := by
  rintro ⟨T, hT⟩
  obtain ⟨-, -, hinv⟩ := diag_reducible
  have hW : SU2.IsInvariant 3 (singletLine.map T.toLinearMap) := by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, hinv g u hu, hT g u⟩
  have h1 : Module.finrank ℂ (singletLine.map T.toLinearMap) = 1 := by
    rw [LinearEquiv.finrank_map_eq, singletLine, finrank_span_singleton singlet_ne_zero]
  rcases SU2.isInvariant_eq_bot_or_eq_top hW with h | h
  · rw [h, finrank_bot] at h1
    exact absurd h1 (by norm_num)
  · rw [h, finrank_top, Module.finrank_fin_fun] at h1
    exact absurd h1 (by norm_num)

/-! ### The hypotheses of completeness are needed -/

open Cardinal in
/-- **A wild automorphism of `ℂ`**: a ring automorphism other than the identity and complex
conjugation. It swaps two elements of a transcendence basis of `ℂ` over `ℤ` (which is infinite,
since `ℂ` is uncountable); being neither `id` nor `conj`, it is not continuous
(`Complex.ringHom_eq_id_or_conj_of_continuous`). -/
theorem exists_wild_ringEquiv :
    ∃ σ : ℂ ≃+* ℂ, (σ : ℂ →+* ℂ) ≠ RingHom.id ℂ ∧ (σ : ℂ →+* ℂ) ≠ starRingEnd ℂ := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ ℂ
  let v : s → ℂ := Subtype.val
  have hcard : #ℂ = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' v hs
    Cardinal.mk_le_aleph0 (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  have hinf : Infinite s := by
    rw [Cardinal.infinite_iff, ← hcard, Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum.le
  obtain ⟨i₀⟩ : Nonempty s := inferInstance
  have hfin : ({i₀} ∪ {i | v i = starRingEnd ℂ (v i₀)} : Set s).Finite :=
    (Set.finite_singleton _).union (Set.Subsingleton.finite fun a ha b hb =>
      Subtype.ext ((show v a = _ from ha).trans (show v b = _ from hb).symm))
  obtain ⟨i₁, hi₁⟩ := hfin.exists_notMem
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, not_or] at hi₁
  let S := Algebra.adjoin ℤ (Set.range v)
  let _ : IsAlgClosure S ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let e : s ≃ s := Equiv.swap i₀ i₁
  let ρ : MvPolynomial s ℤ ≃ₐ[ℤ] MvPolynomial s ℤ :=
    AlgEquiv.ofAlgHom (MvPolynomial.rename e) (MvPolynomial.rename e.symm)
      (by ext; simp) (by ext; simp)
  let e' : S ≃+* S :=
    hs.1.aevalEquiv.symm.toRingEquiv.trans (ρ.toRingEquiv.trans hs.1.aevalEquiv.toRingEquiv)
  let σ : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ e'
  have hσ : σ (v i₀) = v i₁ := by
    have hx : (⟨v i₀, Algebra.subset_adjoin ⟨i₀, rfl⟩⟩ : S) =
        hs.1.aevalEquiv (MvPolynomial.X i₀) := by
      apply Subtype.ext
      have := hs.1.algebraMap_aevalEquiv (MvPolynomial.X i₀)
      rw [MvPolynomial.aeval_X] at this
      exact this.symm
    have h1 : σ (algebraMap S ℂ ⟨v i₀, Algebra.subset_adjoin ⟨i₀, rfl⟩⟩) =
        algebraMap S ℂ (e' ⟨v i₀, Algebra.subset_adjoin ⟨i₀, rfl⟩⟩) :=
      IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ e' _
    have h2 : (e' ⟨v i₀, Algebra.subset_adjoin ⟨i₀, rfl⟩⟩ : ℂ) = v i₁ := by
      rw [hx]
      simp only [e', RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.symm_apply_apply]
      simp [ρ, e]
      rfl
    exact h1.trans h2
  refine ⟨σ, fun h => hi₁.1 ?_, fun h => hi₁.2 ?_⟩
  · have := congrArg (fun f : ℂ →+* ℂ => f (v i₀)) h
    simp only [RingEquiv.coe_toRingHom, hσ, RingHom.id_apply] at this
    exact Subtype.ext this
  · have := congrArg (fun f : ℂ →+* ℂ => f (v i₀)) h
    simp only [RingEquiv.coe_toRingHom, hσ] at this
    exact this

/-- **`d ≥ 1` is needed in `spin4Rep_complete`.** The representation on `ℂ⁰` is continuous and
has no invariant subspace other than `0 = ℂ⁰`, but is equivalent to no `(n, m)`. -/
theorem spin4Rep_complete_needs_pos :
    ∃ ρ : Spin4 →* Matrix (Fin 0) (Fin 0) ℂ, Continuous ρ ∧
      (∀ W : Submodule ℂ (Fin 0 → ℂ), (∀ g : Spin4, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ¬ ∃ n m : ℕ, ∃ T : (Fin 0 → ℂ) ≃ₗ[ℂ] (Idx n m → ℂ),
        ∀ (g : Spin4) (v : Fin 0 → ℂ), T (ρ g *ᵥ v) = spin4Mat n m g *ᵥ T v := by
  refine ⟨1, continuous_const, fun W _ => Or.inl (Subsingleton.elim _ _), ?_⟩
  rintro ⟨n, m, T, -⟩
  have h := T.finrank_eq
  rw [Module.finrank_fin_fun, finrank_idx] at h
  have : 0 < (n + 1) * (m + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  omega

/-- Equivalent matrix representations have equal traces. -/
lemma trace_eq_of_intertwine {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (T : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hT : ∀ v, T (A *ᵥ v) = B *ᵥ T v) : trace B = trace A := by
  have h : Matrix.toLin' B = T.conj (Matrix.toLin' A) := LinearMap.ext fun x => by
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply]
    rw [hT, LinearEquiv.apply_symm_apply]
  rw [← Matrix.trace_toLin'_eq, h, LinearMap.trace_conj', Matrix.trace_toLin'_eq]

/-- The trace of `diag(e^{iθ}, e^{-iθ})` is `2 cos θ`. -/
lemma trace_torusExp (θ : ℝ) :
    trace (torusExp θ : Matrix (Fin 2) (Fin 2) ℂ) = ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [torusExp, torus, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.star_def, Complex.add_conj, Complex.exp_ofReal_mul_I_re]

/-- **Continuity is needed in `spin4Rep_complete`.** For a wild automorphism `σ` of `ℂ`,
`(g₊, g₋) ↦ σ(g₊)` (`σ` applied to the entries) is a representation of Spin(4) on `ℂ²` with no
invariant subspace other than `0` and `ℂ²` that is equivalent to no `(n, m)`. -/
theorem spin4Rep_complete_needs_continuity :
    ∃ ρ : Spin4 →* Matrix (Fin 2) (Fin 2) ℂ,
      (∀ W : Submodule ℂ (Fin 2 → ℂ), (∀ g : Spin4, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ¬ ∃ n m : ℕ, ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Idx n m → ℂ),
        ∀ (g : Spin4) (v : Fin 2 → ℂ), T (ρ g *ᵥ v) = spin4Mat n m g *ᵥ T v := by
  obtain ⟨σ, hid, hconj⟩ := exists_wild_ringEquiv
  let ρ : Spin4 →* Matrix (Fin 2) (Fin 2) ℂ :=
    (σ : ℂ →+* ℂ).mapMatrix.toMonoidHom.comp
      ((Submonoid.subtype _).comp (MonoidHom.fst SU2 SU2))
  have hρ : ∀ g : Spin4, ρ g = (g.1 : Matrix (Fin 2) (Fin 2) ℂ).map σ := fun _ => rfl
  have hΦ : ∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (y : Fin 2 → ℂ),
      (fun i => σ ((A *ᵥ y) i)) = A.map σ *ᵥ fun i => σ (y i) := by
    intro A y; funext i; simp [mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨ρ, fun W hW => ?_, ?_⟩
  · let W' : Submodule ℂ (Fin 2 → ℂ) :=
      { carrier := {y | (fun i => σ (y i)) ∈ W}
        add_mem' := fun {a b} ha hb => by
          change (fun i => σ (a i + b i)) ∈ W
          convert W.add_mem ha hb using 1
          funext i; simp [map_add]
        zero_mem' := by
          change (fun i => σ ((0 : Fin 2 → ℂ) i)) ∈ W
          convert W.zero_mem using 1
          funext i; simp
        smul_mem' := fun c y hy => by
          change (fun i => σ (c * y i)) ∈ W
          convert W.smul_mem (σ c) hy using 1
          funext i; simp [map_mul] }
    have hW' : SU2.IsInvariant 1 W' := fun g y hy => by
      change (fun i => σ ((spinMat 1 g *ᵥ y) i)) ∈ W
      rw [spinMat_one_eq, hΦ]
      exact hW (g, 1) _ hy
    have hpre : ∀ w : Fin 2 → ℂ, w ∈ W ↔ (fun i => σ.symm (w i)) ∈ W' := fun w => by
      change w ∈ W ↔ (fun i => σ (σ.symm (w i))) ∈ W
      simp
    rcases SU2.isInvariant_eq_bot_or_eq_top hW' with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      rw [hpre, h, Submodule.mem_bot] at hw
      rw [Submodule.mem_bot]
      funext i
      have := congrArg σ (congrFun hw i)
      simpa using this
    · right
      rw [eq_top_iff]
      intro w _
      rw [hpre, h]
      trivial
  · rintro ⟨n, m, T, hT⟩
    have htr : ∀ g : Spin4, trace (spin4Mat n m g) = σ (trace (g.1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
      fun g => by
        rw [trace_eq_of_intertwine T (hT g), hρ, ← AddMonoidHom.map_trace]
    have hdim : (n + 1) * (m + 1) = 2 := by
      have h := T.finrank_eq
      rw [Module.finrank_fin_fun, finrank_idx] at h
      exact h.symm
    have hnm : (n = 1 ∧ m = 0) ∨ (n = 0 ∧ m = 1) := by
      rcases n with _ | _ | n <;> rcases m with _ | _ | m <;> simp at hdim ⊢; nlinarith
    rcases hnm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `(½, 0)`: `σ` fixes every trace `2 cos θ`, hence every real number
      have hfix : ∀ g : SU2, σ (trace (g : Matrix (Fin 2) (Fin 2) ℂ)) =
          trace (g : Matrix (Fin 2) (Fin 2) ℂ) := fun g => by
        rw [← htr (g, 1), spin4Mat_one_zero, Matrix.trace_kronecker, Matrix.trace_one]
        simp
      have hint : ∀ s : ℝ, |s| ≤ 2 → σ (s : ℂ) = s := fun s hs => by
        have h1 : 2 * Real.cos (Real.arccos (s / 2)) = s := by
          rw [Real.cos_arccos (by rw [abs_le] at hs; linarith) (by rw [abs_le] at hs; linarith)]
          ring
        have := hfix (torusExp (Real.arccos (s / 2)))
        rwa [trace_torusExp, h1] at this
      have hreal : ∀ r : ℝ, σ (r : ℂ) = r := fun r => by
        set N : ℕ := ⌈|r|⌉₊ + 1
        have hN : (0 : ℝ) < N := by positivity
        have hle : |r| ≤ N := by
          have := Nat.le_ceil |r|
          simp only [N, Nat.cast_add, Nat.cast_one]; linarith
        have hs : |r / N| ≤ 2 := by
          rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]; linarith
        have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
        have hrN : (r : ℂ) = (N : ℂ) * ((r / N : ℝ) : ℂ) := by
          push_cast; field_simp
        rw [hrN, map_mul, map_natCast, hint _ hs]
      let f : ℂ →ₐ[ℝ] ℂ := AlgHom.mk (σ : ℂ →+* ℂ) fun r => by
        change σ (r : ℂ) = (r : ℂ)
        exact hreal r
      rcases Complex.real_algHom_eq_id_or_conj f with h | h
      · exact hid (RingHom.ext fun z => congrArg (fun φ : ℂ →ₐ[ℝ] ℂ => φ z) h)
      · exact hconj (RingHom.ext fun z => congrArg (fun φ : ℂ →ₐ[ℝ] ℂ => φ z) h)
    · -- `(0, ½)`: at `(-1, 1)` the traces are `2` and `σ(-2) = -2`
      have h := htr (negOne, 1)
      rw [spin4Mat_zero_one, Matrix.trace_kronecker, Matrix.trace_one, negOne_coe] at h
      simp [Matrix.trace_neg, Matrix.trace_one] at h
      rw [map_ofNat] at h
      norm_num at h


/-! ### `(½, ½)` is the vector representation of SO(4) -/

open Quaternion

/-- The intertwiner from the complexified `ℝ⁴ = ℍ` to `ℂ² ⊗ ℂ²`: `c ↦ Φ(c) J` with
`Φ(c) = Σ_k c_k toMat(e_k)` (`e_k = 1, i, j, k`) and `J = [[0, 1], [-1, 0]]`, as a matrix. -/
noncomputable def vecIntertwiner : Matrix (Idx 1 1) (Fin 4) ℂ := fun ab k =>
  ![![![0, 0, -1, -Complex.I], ![1, Complex.I, 0, 0]],
    ![![-1, Complex.I, 0, 0], ![0, 0, -1, Complex.I]]] ab.1 ab.2 k

/-- The inverse of `vecIntertwiner`. -/
noncomputable def vecIntertwinerInv : Matrix (Fin 4) (Idx 1 1) ℂ := fun k ab =>
  ![![![0, 1 / 2], ![-1 / 2, 0]], ![![0, -Complex.I / 2], ![-Complex.I / 2, 0]],
    ![![-1 / 2, 0], ![0, -1 / 2]], ![![Complex.I / 2, 0], ![0, -Complex.I / 2]]] k ab.1 ab.2

lemma vecIntertwiner_mul_inv : vecIntertwiner * vecIntertwinerInv = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [vecIntertwiner, vecIntertwinerInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    apply Complex.ext <;> simp <;> norm_num

lemma vecIntertwinerInv_mul : vecIntertwinerInv * vecIntertwiner = 1 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [vecIntertwiner, vecIntertwinerInv, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp <;> norm_num

set_option maxHeartbeats 1000000 in
/-- `vecIntertwiner` intertwines `x ↦ p x q̄` on `ℍ` (complexified) with `toMat p ⊗ₖ toMat q`. -/
lemma vecIntertwiner_mul (p q : ℍ) :
    vecIntertwiner * (LinearMap.toMatrix basisH basisH
      ((LinearMap.mulLeft ℝ p).comp (LinearMap.mulRight ℝ (star q)))).map (fun r : ℝ => (r : ℂ)) =
      (toMat p ⊗ₖ toMat q) * vecIntertwiner := by
  ext ⟨a, b⟩ k
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    simp [vecIntertwiner, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_four,
      Fin.sum_univ_two, LinearMap.toMatrix_apply, basisH_apply, toMat_apply, quatMat] <;>
    apply Complex.ext <;> simp <;> ring

/-- **`(½, ½)` is the complexified vector representation of SO(4)**: an equivalence carries
`spin4Mat 1 1 g` to the rotation matrix `toSO4Mat g` of `ℝ⁴`, viewed as a complex matrix. -/
theorem half_half_equiv_vector :
    ∃ T : (Idx 1 1 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ), ∀ (g : Spin4) (v : Idx 1 1 → ℂ),
      T (spin4Mat 1 1 g *ᵥ v) =
        (toSO4Mat g : Matrix (Fin 4) (Fin 4) ℝ).map (fun r : ℝ => (r : ℂ)) *ᵥ T v := by
  let T : (Idx 1 1 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' vecIntertwinerInv) (Matrix.toLin' vecIntertwiner)
      (by rw [← Matrix.toLin'_mul, vecIntertwinerInv_mul, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, vecIntertwiner_mul_inv, Matrix.toLin'_one])
  refine ⟨T, fun g v => ?_⟩
  set p := (quatEquiv.symm g.1 : ℍ)
  set q := (quatEquiv.symm g.2 : ℍ)
  have hK : spin4Mat 1 1 g = toMat p ⊗ₖ toMat q := by
    rw [spin4Mat, spinMat_one_eq, spinMat_one_eq, ← coe_quatEquiv, ← coe_quatEquiv,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hR : (toSO4Mat g : Matrix (Fin 4) (Fin 4) ℝ) = LinearMap.toMatrix basisH basisH
      ((LinearMap.mulLeft ℝ p).comp (LinearMap.mulRight ℝ (star q))) := by
    change LinearMap.toMatrix basisH basisH (toSO4 g : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv.toLinearMap = _
    congr 1
    exact LinearMap.ext fun x => mul_assoc _ _ _
  have hkey : vecIntertwiner * (toSO4Mat g : Matrix (Fin 4) (Fin 4) ℝ).map (fun r : ℝ => (r : ℂ)) =
      spin4Mat 1 1 g * vecIntertwiner := by
    rw [hR, hK]; exact vecIntertwiner_mul p q
  set R := (toSO4Mat g : Matrix (Fin 4) (Fin 4) ℝ).map (fun r : ℝ => (r : ℂ))
  set K := spin4Mat 1 1 g
  have hinv : vecIntertwinerInv * K = R * vecIntertwinerInv := by
    calc vecIntertwinerInv * K = vecIntertwinerInv * K * (vecIntertwiner * vecIntertwinerInv) := by
          rw [vecIntertwiner_mul_inv, Matrix.mul_one]
      _ = vecIntertwinerInv * (K * vecIntertwiner) * vecIntertwinerInv := by
          simp only [Matrix.mul_assoc]
      _ = R * vecIntertwinerInv := by
          rw [← hkey, ← Matrix.mul_assoc, vecIntertwinerInv_mul, Matrix.one_mul]
  change vecIntertwinerInv *ᵥ (K *ᵥ v) = R *ᵥ (vecIntertwinerInv *ᵥ v)
  rw [mulVec_mulVec, mulVec_mulVec, hinv]

/-! ### Wrong field: the tensor theorem needs an algebraically closed field -/

/-- Rotation of `ℝ²` by `π/2`. -/
def rot90 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

lemma rot90_mul_self : rot90 * rot90 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot90, Matrix.mul_apply, Fin.sum_univ_two]

/-- The rotation as a unit of `End ℝ ℝ²`. -/
noncomputable def rot90Unit : (Module.End ℝ (Fin 2 → ℝ))ˣ where
  val := Matrix.toLin' rot90
  inv := Matrix.toLin' (-rot90)
  val_inv := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.mul_neg, rot90_mul_self, neg_neg,
      Matrix.toLin'_one]; rfl
  inv_val := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.neg_mul, rot90_mul_self, neg_neg,
      Matrix.toLin'_one]; rfl

/-- The representation `k ↦ (rotation by π/2)^k` of `ℤ` on `ℝ²`. -/
noncomputable def rotRep : Representation ℝ (Multiplicative ℤ) (Fin 2 → ℝ) :=
  (Units.coeHom _).comp (zpowersHom _ rot90Unit)

lemma rotRep_one : rotRep (Multiplicative.ofAdd 1) = Matrix.toLin' rot90 := by
  simp [rotRep, rot90Unit]

lemma rotRep_comm (a : Multiplicative ℤ) :
    rotRep a * rotRep (Multiplicative.ofAdd 1) = rotRep (Multiplicative.ofAdd 1) * rotRep a := by
  rw [← map_mul, ← map_mul, mul_comm]

/-- **Rotation by `π/2` is irreducible over `ℝ`** (it has no real eigenvector). -/
theorem rot90_isIrreducible : rotRep.IsIrreducible := by
  have : Nontrivial (Subrepresentation rotRep) :=
    ⟨⊥, ⊤, fun h => by
      have h' := congrArg Subrepresentation.toSubmodule h
      have hmem : (Pi.single 0 1 : Fin 2 → ℝ) ∈ (⊤ : Subrepresentation rotRep).toSubmodule :=
        trivial
      rw [← h'] at hmem
      have := congrFun ((Submodule.mem_bot ℝ).mp hmem) 0
      simp at this⟩
  refine { eq_bot_or_eq_top := fun S => ?_ }
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  right
  apply Subrepresentation.toSubmodule_injective
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hRv := S.apply_mem_toSubmodule (Multiplicative.ofAdd 1) hv
  rw [rotRep_one, Matrix.toLin'_apply] at hRv
  have hN : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
    intro h
    apply hv0
    funext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  change S.toSubmodule = ⊤
  rw [eq_top_iff]
  intro w _
  have hw : w = ((w 0 * v 0 + w 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) • v +
      ((w 1 * v 0 - w 0 * v 1) / (v 0 ^ 2 + v 1 ^ 2)) • (rot90 *ᵥ v) := by
    funext i
    fin_cases i <;> simp [rot90, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  rw [hw]
  exact S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ hv) (S.toSubmodule.smul_mem _ hRv)

/-- **Its external tensor square is reducible**: the `+1` eigenspace of `R ⊗ R` is a proper,
nonzero subrepresentation of `ℤ × ℤ` on `ℝ² ⊗ ℝ²`. So `isIrreducible_extTprod` fails over `ℝ`. -/
theorem not_isIrreducible_rot90_tensor : ¬ (extTprod rotRep rotRep).IsIrreducible := by
  intro hirr
  set R : Module.End ℝ (Fin 2 → ℝ) := Matrix.toLin' rot90
  set RR := TensorProduct.map R R
  have hcomm : ∀ g : Multiplicative ℤ × Multiplicative ℤ,
      RR ∘ₗ extTprod rotRep rotRep g = extTprod rotRep rotRep g ∘ₗ RR := fun g => by
    have hR : R = rotRep (Multiplicative.ofAdd 1) := rotRep_one.symm
    simp only [RR, extTprod_apply, ← TensorProduct.map_comp]
    rw [hR, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
      ← Module.End.mul_eq_comp, rotRep_comm g.1, rotRep_comm g.2]
  let W : Subrepresentation (extTprod rotRep rotRep) :=
    { toSubmodule := LinearMap.ker (RR - LinearMap.id)
      apply_mem_toSubmodule := fun g x hx => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
        rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hx] }
  let e : Fin 2 → (Fin 2 → ℝ) := fun i => Pi.single i 1
  have hR0 : R (e 0) = e 1 := by
    funext i; fin_cases i <;> simp [R, e, rot90, mulVec, dotProduct, Fin.sum_univ_two]
  have hR1 : R (e 1) = -e 0 := by
    funext i; fin_cases i <;> simp [R, e, rot90, mulVec, dotProduct, Fin.sum_univ_two]
  let b := (Pi.basisFun ℝ (Fin 2)).tensorProduct (Pi.basisFun ℝ (Fin 2))
  have hb : ∀ i j, b.repr (e i ⊗ₜ e j) (0, 0) = if i = 0 ∧ j = 0 then 1 else 0 := fun i j => by
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    fin_cases i <;> fin_cases j <;> simp [e]
  let t := e 0 ⊗ₜ[ℝ] e 0 + e 1 ⊗ₜ[ℝ] e 1
  let s := e 0 ⊗ₜ[ℝ] e 0 - e 1 ⊗ₜ[ℝ] e 1
  have ht : t ∈ W.toSubmodule := by
    change RR t - t = 0
    simp only [t, RR, map_add, TensorProduct.map_tmul, hR0, hR1, TensorProduct.neg_tmul,
      TensorProduct.tmul_neg, neg_neg]
    abel
  have ht0 : t ≠ 0 := fun h => by
    have := congrArg (fun x => b.repr x (0, 0)) h
    simp only [t, map_add, Finsupp.add_apply, hb, map_zero, Finsupp.zero_apply] at this
    norm_num at this
  have hs : s ∉ W.toSubmodule := fun h => by
    change RR s - s = 0 at h
    simp only [s, RR, map_sub, TensorProduct.map_tmul, hR0, hR1, TensorProduct.neg_tmul,
      TensorProduct.tmul_neg, neg_neg] at h
    have := congrArg (fun x => b.repr x (0, 0)) h
    simp only [map_sub, Finsupp.sub_apply, hb, map_zero, Finsupp.zero_apply] at this
    norm_num at this
  rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
  · apply ht0
    have : t ∈ (⊥ : Subrepresentation (extTprod rotRep rotRep)).toSubmodule := h ▸ ht
    exact (Submodule.mem_bot ℝ).mp this
  · apply hs
    rw [h]
    trivial

/-! ### Completeness is not vacuous -/

/-- **`spin4Rep_complete` is not vacuous**: the trivial representation on `ℂ¹` is continuous and
irreducible, and the theorem identifies it as `(0, 0)`. -/
theorem spin4Rep_complete_nonvacuous :
    ∃ n m : ℕ, n = 0 ∧ m = 0 ∧ ∃ T : (Fin 1 → ℂ) ≃ₗ[ℂ] (Idx n m → ℂ),
      ∀ (g : Spin4) (v : Fin 1 → ℂ),
        T ((1 : Spin4 →* Matrix (Fin 1) (Fin 1) ℂ) g *ᵥ v) = spin4Mat n m g *ᵥ T v := by
  have hirr : ∀ W : Submodule ℂ (Fin 1 → ℂ),
      (∀ g : Spin4, ∀ v ∈ W, (1 : Spin4 →* Matrix (Fin 1) (Fin 1) ℂ) g *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
    intro W _
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hv00 : v 0 ≠ 0 := fun h => hv0 (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
    rw [eq_top_iff]
    intro w _
    have : w = (w 0 / v 0) • v := funext fun i => by
      rw [Subsingleton.elim i 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hv00]
    rw [this]
    exact W.smul_mem _ hv
  obtain ⟨n, m, T, hT⟩ := spin4Rep_complete 1 continuous_const hirr
  have h := T.finrank_eq
  rw [Module.finrank_fin_fun, finrank_idx] at h
  have hn : n = 0 := by
    rcases n with _ | n
    · rfl
    · nlinarith
  have hm : m = 0 := by
    rcases m with _ | m
    · rfl
    · nlinarith
  exact ⟨n, m, hn, hm, T, hT⟩

/-- **`spin4_complete` is not vacuous**: it applies to every `spin4Representation n m` (which is
irreducible with continuous matrix coefficients) and returns the labels `(n, m)`. -/
theorem spin4_complete_nonvacuous (n m : ℕ) :
    ∃ n' m', Nonempty ((spin4Representation n m).Equiv (spin4Representation n' m')) ∧
      n' = n ∧ m' = m := by
  have := spin4Representation_isIrreducible n m
  have hc : ∀ (v : Idx n m → ℂ) (f : Module.Dual ℂ (Idx n m → ℂ)),
      Continuous fun g => f (spin4Representation n m g v) := fun v f =>
    (LinearMap.continuous_of_finiteDimensional f).comp
      ((continuous_spin4Rep (n := n) (m := m)).matrix_mulVec continuous_const)
  obtain ⟨n', m', ⟨φ⟩⟩ := spin4_complete (spin4Representation n m) hc
  obtain ⟨h1, h2⟩ := spin4Representation_equiv_iff.mp ⟨φ⟩
  exact ⟨n', m', ⟨φ⟩, h1.symm, h2.symm⟩

end Lightlike.Spin4.Test

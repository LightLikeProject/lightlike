module

public import Lightlike.SU2.SpinRep
public import Lightlike.SU2.LieBridge
public import Lightlike.SU2.Completeness

/-!
# Audit of the SU(2) spin representations (`Lightlike/SU2/SpinRep.lean`)

As for the curvature and 6j definitions, we check the construction against independently known
values and include a test that a *wrong* construction gives a different answer.

* `spinMat_zero` - spin 0 is the trivial representation.
* `spinMat_one_eq` - spin ½ is the defining representation `g ↦ g`.
* `spinMat_two_rotY` - spin 1 at the rotation by `β = π/2` about `y` is the textbook Wigner
  matrix `d¹(π/2)` (e.g. Varshalovich et al., *Quantum Theory of Angular Momentum*, table 4.3;
  rows/columns `m = 1, 0, -1`): `[[1/2, -1/√2, 1/2], [1/√2, 0, -1/√2], [1/2, 1/√2, 1/2]]`,
  including the vanishing entry `d¹₀₀(π/2) = cos(π/2) = 0`.
* `kron_two_singlet`, `singlet_not_isSym` - **wrong-input test**: without symmetrisation,
  `(ℂ²)^{⊗2}` is *reducible*: the antisymmetric singlet spans an invariant line (`g^{⊗2} ψ =
  det g · ψ`). So the symmetrisation in `spinMat` is what makes the representations irreducible.
* `spinMat_one_negOne`, `spinMat_two_negOne` - `-1 ∈ SU(2)` acts as `-1` on spin ½ and as `+1` on
  spin 1.
-/

@[expose] public section

open Matrix Finset

namespace Lightlike.SU2.Test

/-! ### Sums over strings of length 1 and 2 -/

lemma sum_str_one (f : Str 1 → ℂ) : ∑ s, f s = f ![0] + f ![1] := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp, Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

lemma sum_str_two (f : Str 2 → ℂ) :
    ∑ s, f s = f ![0, 0] + f ![0, 1] + (f ![1, 0] + f ![1, 1]) := by
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm f, Fintype.sum_prod_type,
    Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two]
  rfl

lemma str_one_eq (s : Str 1) : s = ![s 0] := by funext i; fin_cases i; rfl

lemma str_two_eq (s : Str 2) : s = ![s 0, s 1] := by funext i; fin_cases i <;> rfl

/-! ### Spin 0 and spin ½ -/

/-- Spin 0 is the trivial representation (for every `2 × 2` matrix, in fact). -/
theorem spinMat_zero (g : Matrix (Fin 2) (Fin 2) ℂ) : spinMat 0 g = 1 := by
  have hk : kron 0 g = 1 := by
    ext s t
    rw [Subsingleton.elim s t, one_apply_eq, kron_apply, univ_eq_empty, prod_empty]
  rw [spinMat, hk, Matrix.mul_one, emb_conjTranspose_mul_emb]

@[simp] lemma downs_one_0 : downs (n := 1) ![0] = 0 := by decide
@[simp] lemma downs_one_1 : downs (n := 1) ![1] = 1 := by decide
@[simp] lemma clsCard_one_0 : clsCard 1 0 = 1 := by decide
@[simp] lemma clsCard_one_1 : clsCard 1 1 = 1 := by decide

lemma nrm_one (k : ℕ) (hk : clsCard 1 k = 1) : nrm 1 k = 1 := by simp [nrm, hk]

/-- Spin ½ is the defining representation of SU(2). -/
theorem spinMat_one_eq (g : Matrix (Fin 2) (Fin 2) ℂ) : spinMat 1 g = g := by
  have h0 := nrm_one 0 clsCard_one_0
  have h1 := nrm_one 1 clsCard_one_1
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [spinMat, mul_apply, sum_str_one, conjTranspose_apply, emb_apply, kron_apply, h0, h1]

/-! ### Spin 1: the Wigner matrix `d¹(π/2)` -/

@[simp] lemma downs_two_00 : downs (n := 2) ![0, 0] = 0 := by decide
@[simp] lemma downs_two_01 : downs (n := 2) ![0, 1] = 1 := by decide
@[simp] lemma downs_two_10 : downs (n := 2) ![1, 0] = 1 := by decide
@[simp] lemma downs_two_11 : downs (n := 2) ![1, 1] = 2 := by decide
@[simp] lemma clsCard_two_0 : clsCard 2 0 = 1 := by decide
@[simp] lemma clsCard_two_1 : clsCard 2 1 = 2 := by decide
@[simp] lemma clsCard_two_2 : clsCard 2 2 = 1 := by decide

lemma nrm_two_0 : nrm 2 0 = 1 := by simp [nrm]
lemma nrm_two_1 : nrm 2 1 = c2 := by simp [nrm, c2]
lemma nrm_two_2 : nrm 2 2 = 1 := by simp [nrm]

lemma rotY_coe : (rotY : Matrix (Fin 2) (Fin 2) ℂ) = !![c2, -c2; c2, c2] := rfl

/-- **Spin 1 at `β = π/2`** equals the textbook Wigner small-d matrix `d¹(π/2)`. -/
theorem spinMat_two_rotY :
    spinMat 2 rotY = !![1 / 2, -c2, 1 / 2; c2, 0, -c2; 1 / 2, c2, 1 / 2] := by
  have h := c2_mul_self
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [spinMat, mul_apply, sum_str_two, conjTranspose_apply, emb_apply, kron_apply,
      Fin.prod_univ_two, rotY_coe, nrm_two_0, nrm_two_1, nrm_two_2, conj_c2] <;>
    first
      | linear_combination h
      | linear_combination 2 * c2 * h
      | linear_combination -2 * c2 * h

/-! ### Wrong-input test: the unsymmetrised product `(ℂ²)^{⊗2}` is reducible -/

/-- The singlet `|↑↓⟩ - |↓↑⟩` in `(ℂ²)^{⊗2}`. -/
def singlet : Str 2 → ℂ := fun s => if s = ![0, 1] then 1 else if s = ![1, 0] then -1 else 0

/-- `g^{⊗2}` multiplies the singlet by `det g`. -/
theorem kron_two_singlet (g : Matrix (Fin 2) (Fin 2) ℂ) :
    kron 2 g *ᵥ singlet = g.det • singlet := by
  funext s
  rw [str_two_eq s]
  generalize s 0 = a
  generalize s 1 = b
  simp only [mulVec, dotProduct, sum_str_two, kron_apply, Fin.prod_univ_two, singlet,
    det_fin_two, Pi.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> simp (config := { decide := true }) <;> ring

/-- The singlet is not symmetric, so it lies outside the spin-1 subspace. -/
theorem singlet_not_isSym : ¬ IsSym singlet := by
  intro h
  have := h (Equiv.swap 0 1) ![0, 1]
  have hs : (![0, 1] : Str 2) ∘ (Equiv.swap (0 : Fin 2) 1) = ![1, 0] := by
    funext i; fin_cases i <;> rfl
  rw [hs] at this
  simp (config := { decide := true }) [singlet] at this
  norm_num at this

/-- **Reducibility of the unsymmetrised product.** The singlet spans a nonzero, proper subspace of
`(ℂ²)^{⊗2}` invariant under every `g^{⊗2}`, `g ∈ SU(2)`. Contrast `spinRepresentation_isIrreducible`:
the symmetrisation in `spinMat` is essential. -/
theorem kron_two_reducible :
    ∃ W : Submodule ℂ (Str 2 → ℂ), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : SU2, ∀ v ∈ W, kron 2 (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v ∈ W := by
  refine ⟨Submodule.span ℂ {singlet}, ?_, ?_, ?_⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]
    intro h
    have := congrFun h ![0, 1]
    simp (config := { decide := true }) [singlet] at this
  · intro htop
    have hmem : (Pi.single ![0, 0] 1 : Str 2 → ℂ) ∈ Submodule.span ℂ {singlet} := htop ▸ trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrFun hc ![0, 0]
    simp (config := { decide := true }) [singlet] at this
  · intro g v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [mulVec_smul, kron_two_singlet, (mem_specialUnitaryGroup_iff.mp g.2).2, one_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-! ### The centre: half-integer vs integer spin -/

/-- `-1 ∈ SU(2)` acts as `-1` in the spin-½ representation. -/
theorem spinMat_one_negOne : spinMat 1 negOne = -1 := by
  rw [spinMat_negOne]; simp

/-- `-1 ∈ SU(2)` acts as `1` in the spin-1 representation. -/
theorem spinMat_two_negOne : spinMat 2 negOne = 1 := by
  rw [spinMat_negOne]; simp

/-! ### The differential (`Lightlike/SU2/LieBridge.lean`) -/

/-- Spin 0: the differential of the trivial representation is zero. -/
theorem dSpin_zero (X : Matrix (Fin 2) (Fin 2) ℂ) : dSpin 0 X = 0 := by
  have hk : dkron 0 X = 0 := by ext s t; simp [dkron]
  rw [dSpin, hk, Matrix.mul_zero, Matrix.zero_mul]

/-- Spin ½: the differential of the defining representation is `X ↦ X`. -/
theorem dSpin_one_eq (X : Matrix (Fin 2) (Fin 2) ℂ) : dSpin 1 X = X := by
  have h0 := nrm_one 0 clsCard_one_0
  have h1 := nrm_one 1 clsCard_one_1
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [dSpin, dkron, mul_apply, sum_str_one, conjTranspose_apply, emb_apply, h0, h1]

/-! ### Group-level completeness (`Lightlike/SU2/Completeness.lean`) -/

/-- The hypotheses of `spinRep_complete` are satisfiable: they hold for `spinRep n` itself
(irreducibility from `isInvariant_eq_bot_or_eq_top`), which is then equivalent to a spin
representation. -/
theorem spinRep_complete_applies (n : ℕ) :
    ∃ m : ℕ, ∃ T : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ), ∀ (g : SU2) v,
      T (σ n g *ᵥ v) = (spinRep m g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *ᵥ T v :=
  spinRep_complete (σ n) (continuous_σ n) fun _ hW => isInvariant_eq_bot_or_eq_top hW

end Lightlike.SU2.Test

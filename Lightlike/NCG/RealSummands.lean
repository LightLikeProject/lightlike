import Lightlike.NCG.Complexification

/-!
# Real summands `Mₙ(ℝ)`

T. Krajewski, arXiv:hep-th/9701081, Section 2, p. 2 (`A = ⊕ Mₙᵢ(K)`, `K = ℝ, ℂ, ℍ`) and Section 3.1, p. 10 (read): "`Mₙ(ℝ)`
and `Mₙ(ℍ)` have only one irreducible representation, the fundamental one ... all our formulae remain valid, provided
the indices `i` and `j` label irreducible representations of `A`". For `A = ⊕ Mₙᵢ(ℝ)` the irreducible representations are
the fundamental ones on `ℂⁿⁱ`: a real-linear `π` extends to the complex-linear `σ(x) = π(Re x) + i π(Im x)` of
`⊕ Mₙᵢ(ℂ) = A ⊗_ℝ ℂ`, faithful because `E₀α x Eβ₀ = x_αβ E₀₀` and `π(E₀₀) ≠ 0`. So `(σ, φ)`, with `φ` the inclusion,
is a complexification, and the uniqueness theorem applies.

* `MatSumR`, `reM`, `imM`, `ofRealM` and their algebra (`reM_mul`, `imM_mul`, `reM_star`, `imM_star`, ...);
* `phiR`: `⊕ Mₙᵢ(ℝ) → ⊕ Mₙᵢ(ℂ)`, a real `*`-homomorphism;
* `sigmaR`, `sigmaR_phiR`, `sigmaR_injective`: the complexified representation;
* `realComplexification`, `exists_unitary_realSummands`: uniqueness for real summands.
-/

namespace Lightlike.NCG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (n : ι → ℕ) in
/-- `⊕ᵢ Mₙᵢ(ℝ)`. -/
abbrev MatSumR := ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℝ

variable {n : ι → ℕ}

/-- The entrywise real part. -/
def reM (x : MatSum n) : MatSumR n := fun i => (x i).map Complex.re

/-- The entrywise imaginary part. -/
def imM (x : MatSum n) : MatSumR n := fun i => (x i).map Complex.im

/-- A real matrix as a complex one. -/
def ofRealM (a : MatSumR n) : MatSum n := fun i => (a i).map (↑)

/-- The real part is additive. -/
lemma reM_add (x y : MatSum n) : reM (x + y) = reM x + reM y := by
  funext i; ext α β; simp [reM]

/-- The imaginary part is additive. -/
lemma imM_add (x y : MatSum n) : imM (x + y) = imM x + imM y := by
  funext i; ext α β; simp [imM]

/-- `Re(xy) = Re x Re y - Im x Im y`. -/
lemma reM_mul (x y : MatSum n) : reM (x * y) = reM x * reM y - imM x * imM y := by
  funext i; ext α β
  simp [reM, imM, Matrix.mul_apply, Complex.re_sum, Finset.sum_sub_distrib]

/-- `Im(xy) = Re x Im y + Im x Re y`. -/
lemma imM_mul (x y : MatSum n) : imM (x * y) = reM x * imM y + imM x * reM y := by
  funext i; ext α β
  simp [reM, imM, Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]

/-- `Re(x*) = (Re x)*`. -/
lemma reM_star (x : MatSum n) : reM (star x) = star (reM x) := by
  funext i; ext α β; simp [reM, Matrix.star_apply]

/-- `Im(x*) = -(Im x)*`. -/
lemma imM_star (x : MatSum n) : imM (star x) = -star (imM x) := by
  funext i; ext α β; simp [imM, Matrix.star_apply]

/-- `Re 1 = 1`. -/
lemma reM_one : reM (1 : MatSum n) = 1 := by
  funext i; ext α β; simp [reM, Matrix.one_apply, apply_ite]

/-- `Im 1 = 0`. -/
lemma imM_one : imM (1 : MatSum n) = 0 := by
  funext i; ext α β; simp [imM, Matrix.one_apply, apply_ite]

/-- `Re 0 = 0`. -/
lemma reM_zero : reM (0 : MatSum n) = 0 := by
  funext i; ext α β; simp [reM]

/-- `Im 0 = 0`. -/
lemma imM_zero : imM (0 : MatSum n) = 0 := by
  funext i; ext α β; simp [imM]

/-- `Re(c 1) = (Re c) 1`. -/
lemma reM_smul_one (c : ℂ) : reM (c • (1 : MatSum n)) = c.re • 1 := by
  funext i; ext α β
  by_cases h : α = β <;> simp [reM, Matrix.one_apply, h]

/-- `Im(c 1) = (Im c) 1`. -/
lemma imM_smul_one (c : ℂ) : imM (c • (1 : MatSum n)) = c.im • 1 := by
  funext i; ext α β
  by_cases h : α = β <;> simp [imM, Matrix.one_apply, h]

/-- The real part of a real matrix is itself. -/
lemma reM_ofRealM (a : MatSumR n) : reM (ofRealM a) = a := by
  funext i; ext α β; simp [reM, ofRealM]

/-- The imaginary part of a real matrix is `0`. -/
lemma imM_ofRealM (a : MatSumR n) : imM (ofRealM a) = 0 := by
  funext i; ext α β; simp [imM, ofRealM]

/-- **The inclusion `⊕ Mₙᵢ(ℝ) → ⊕ Mₙᵢ(ℂ)`**, a real `*`-homomorphism. -/
def phiR : MatSumR n →⋆ₐ[ℝ] MatSum n where
  toFun := ofRealM
  map_one' := by funext i; ext α β; simp [ofRealM, Matrix.one_apply, apply_ite]
  map_mul' a b := by funext i; ext α β; simp [ofRealM, Matrix.mul_apply]
  map_zero' := by funext i; ext α β; simp [ofRealM]
  map_add' a b := by funext i; ext α β; simp [ofRealM]
  commutes' r := by
    funext i; ext α β
    by_cases h : α = β <;> simp [ofRealM, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, h]
  map_star' a := by funext i; ext α β; simp [ofRealM, Matrix.star_apply]

/-- `phiR` is `ofRealM`. -/
lemma phiR_apply (a : MatSumR n) : phiR a = ofRealM a := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable (T : FiniteSpectralTriple (MatSumR n) H)

/-- `π(r a) = r π(a)` with the real scalar acting as a complex one. -/
lemma pi_rsmul (r : ℝ) (a : MatSumR n) : T.π (r • a) = (r : ℂ) • T.π a := by
  rw [map_smul]; rfl

/-- **The complexified representation** `σ(x) = π(Re x) + i π(Im x)`. -/
def sigmaR : MatSum n →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun x := T.π (reM x) + Complex.I • T.π (imM x)
  map_one' := by simp only [reM_one, imM_one, map_one, map_zero, smul_zero, add_zero]
  map_mul' x y := by
    simp only [reM_mul, imM_mul, map_sub, map_add, map_mul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, Complex.I_mul_I, neg_one_smul, smul_add]
    abel
  map_zero' := by simp only [reM_zero, imM_zero, map_zero, smul_zero, add_zero]
  map_add' x y := by
    simp only [reM_add, imM_add, map_add, smul_add]
    abel
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, reM_smul_one, imM_smul_one, pi_rsmul, map_one, smul_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_comm Complex.I]
  map_star' x := by
    simp only [reM_star, imM_star, map_neg, map_star, star_add, star_smul, Complex.star_def, Complex.conj_I,
      smul_neg, neg_smul]

/-- `σ(x) = π(Re x) + i π(Im x)`. -/
lemma sigmaR_apply (x : MatSum n) : sigmaR T x = T.π (reM x) + Complex.I • T.π (imM x) := rfl

/-- **`σ ∘ φ = π`.** -/
lemma sigmaR_phiR (a : MatSumR n) : sigmaR T (phiR a) = T.π a := by
  rw [sigmaR_apply, phiR_apply, reM_ofRealM, imM_ofRealM, map_zero, smul_zero, add_zero]

/-- The real matrix unit `E^i_{αβ}`. -/
def unitR (i : ι) (α β : Fin (n i)) : MatSumR n := Pi.single i (Matrix.single α β 1)

/-- The complex matrix unit `E^i_{αβ}`. -/
def unitC (i : ι) (α β : Fin (n i)) : MatSum n := Pi.single i (Matrix.single α β 1)

/-- The inclusion maps the real matrix units to the complex ones. -/
lemma phiR_unitR (i : ι) (α β : Fin (n i)) : phiR (unitR i α β) = unitC i α β := by
  funext k
  by_cases hk : k = i
  · subst hk; ext γ δ; simp [phiR_apply, ofRealM, unitR, unitC, Matrix.single_apply, apply_ite]
  · ext γ δ; simp [phiR_apply, ofRealM, unitR, unitC, Pi.single_eq_of_ne hk]

/-- `E^i_{αα} x E^i_{βα} = x^i_{αβ} E^i_{αα}`. -/
lemma unitC_mul_mul_unitC (x : MatSum n) (i : ι) (α β : Fin (n i)) :
    unitC i α α * x * unitC i β α = (x i α β) • unitC i α α := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.mul_apply, Pi.smul_apply, unitC, Pi.single_eq_same, Matrix.single_mul_mul_single, one_mul,
      mul_one, Matrix.smul_single, smul_eq_mul]
  · simp [unitC, Pi.single_eq_of_ne hk]

/-- **`σ` is faithful**: `σ(x) = 0` gives `x^i_{αβ} π(E^i_{αα}) = σ(E^i_{αα} x E^i_{βα}) = 0`, and `π(E^i_{αα}) ≠ 0`. -/
theorem sigmaR_injective : Function.Injective (sigmaR T) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext i; ext α β
  have h1 : sigmaR T (unitC i α α * x * unitC i β α) = 0 := by rw [map_mul, map_mul, hx, mul_zero, zero_mul]
  rw [unitC_mul_mul_unitC, map_smul, ← phiR_unitR, sigmaR_phiR] at h1
  have hne : T.π (unitR i α α) ≠ 0 := by
    intro h
    have h0 : unitR i α α = 0 := T.injective_π (h.trans (map_zero T.π).symm)
    have := congrFun (congrFun (congrFun h0 i) α) α
    simp [unitR] at this
  rw [Pi.zero_apply, Matrix.zero_apply]
  exact (smul_eq_zero.mp h1).resolve_right hne

/-- **The complexification of a triple over `⊕ Mₙᵢ(ℝ)`.** -/
def realComplexification : Complexification T n where
  σ := sigmaR T
  injective_σ := sigmaR_injective T
  φ := phiR
  pi_eq a := (sigmaR_phiR T a).symm
  mem_span x := by
    rw [sigmaR_apply]
    exact add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

/-- **Uniqueness for real summands** (Krajewski, Section 3.1, p. 10, with Section 3.2, p. 13): a real finite spectral
triple over `⊕ Mₙᵢ(ℝ)` is unitarily equivalent to the model `⊕ ℂⁿⁱ ⊗ ℂʳⁱʲ ⊗ ℂⁿʲ` of its multiplicity matrix, with `π(a)`
acting as the real matrices `a` on the fundamental representations. -/
theorem exists_unitary_realSummands [∀ i, NeZero (n i)] (R : RealStructure T) :
    ∃ U : H ≃ₗᵢ[ℂ] HK n (fun i j => multiplicity ((realComplexification T).realStructure R) i j),
      (∀ a x, U (T.π a x) = piK (phiR a) (U x)) ∧
        ∀ x, U (R.J x) = JK (multiplicity_symm ((realComplexification T).realStructure R)) (U x) :=
  (realComplexification T).exists_unitary R

end

end Lightlike.NCG

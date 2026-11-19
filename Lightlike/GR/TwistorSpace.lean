import Lightlike.GR.TwistorConformal
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Twistor space: the form of signature (2, 2), PT, PN, PT±, and the incidence relation `ω = i x π`

Twistors in Penrose's coordinates `Z = (ω, π)` (`Fin 2 ⊕ Fin 2 → ℂ`) carry the Hermitian form
`Σ(Z) = ω · π̄ + ω̄ · π` (`penroseNorm`, matrix `penroseHerm = [[0, 1], [1, 0]]`). It has signature
`(2, 2)`: a unitary `U` brings it to `diag(1, 1, -1, -1)` (`penroseHerm_signature`, and the same for
the form `twistorHerm` of `TwistorConformal.lean`, `twistorHerm_signature`).

The incidence relation of the row, `ω^A = i x^{AA'} π_{A'}` (`incidencePenrose`), is the incidence
relation `μ = Xᵀ λ` of `TwistorConformal.lean` followed by `(μ, λ) ↦ (i μ, λ)` (`toPenrose`), with
`x = Xᵀ` (`incidencePenrose_eq`); the forms agree, `Σ(toPenrose Z) = twistorNorm Z`
(`penroseNorm_toPenrose`). For the points of `ComplexMinkowski.lean` it is ADM's (2.7)
(`incidencePenrose_spinorMat`). The twistor line of `x` is null iff `x` is Hermitian
(`penroseNorm_incidence_eq_zero_iff`).

On the projective twistor space `CP3 = ℙ ℂ (Fin 2 ⊕ Fin 2 → ℂ)` the sign of `Σ` is well defined
(`Σ(c Z) = |c|² Σ(Z)`, `Σ` real), so `PTplus`, `PN`, `PTminus` partition `CP3`
(`mem_PTplus_mk`, ..., `cp3_partition`), each is nonempty, and `PT = {π ≠ 0}` is ADM's
`CP³ - CP¹`. The lines of real points lie in `PN ∩ PT` (`mk_incidencePenrose_mem`).

## References

* M. Atiyah, M. Dunajski, L. Mason, *Twistor theory at fifty*, arXiv:1704.07464, §2.1, p. 7: `PT`
  is `CP³ - CP¹` with `(Z², Z³) ≠ (0, 0)`; the incidence relation (2.7)
  `(Z⁰, Z¹) = (i/√2) [[ct + z, x + iy], [x - iy, ct - z]] (Z², Z³)`; the `(+ + - -)` Hermitian form
  `Σ(Z, Z) = Z⁰ Z̄² + Z¹ Z̄³ + Z² Z̄⁰ + Z³ Z̄¹`; "The twistor space T is divided into three parts
  depending on whether Σ is positive, negative or zero. This partition descends to the projective
  twistor space"; `PN = {[Z] ∈ PT, Σ(Z, Z) = 0}`; "If the coordinates x^μ are real this line lies in
  the hypersurface PN".
* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196: `CP³` (1.21), `PT` an open subset of `CP³`
  (1.22), p. 9; the Lorentzian incidence relation (2.2), p. 13; signature `(+2, -2)` of (2.5) and
  `PN` (2.7), p. 14.
* A. Bette, arXiv:hep-th/0402150, (3.13)–(3.15), p. 15: the twistor "length" `ρ = ω^A η̄_A + λ̄^{A'} π_{A'}`
  and the division of `CP(3)` into twistors of positive, negative and zero norm.

Differences: twistors are `Fin 2 ⊕ Fin 2 → ℂ` (representation); ADM's `x^{AA'}` is
`(spinorMat x)ᵀ` (convention of the spinor matrix); `PT±`, `PN` are subsets of all of `CP3`, and
ADM's `PT` is `PT` here.
-/

open Matrix Complex
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace Lightlike

/-! ## The twistor form in Penrose's coordinates -/

/-- The matrix `[[0, 1], [1, 0]]` of `Σ(ω, π) = ω · π̄ + ω̄ · π`. -/
def penroseHerm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := fromBlocks 0 1 1 0

lemma penroseHerm_isHermitian : penroseHerm.IsHermitian := by
  simp [IsHermitian, penroseHerm, fromBlocks_conjTranspose]

/-- The twistor form `Σ(Z) = Z† H Z` (ADM, p. 7). -/
def penroseNorm (Z : Fin 2 ⊕ Fin 2 → ℂ) : ℂ := star Z ⬝ᵥ (penroseHerm *ᵥ Z)

lemma penroseNorm_sumElim (ω π : Fin 2 → ℂ) :
    penroseNorm (Sum.elim ω π) =
      star (ω 0) * π 0 + star (ω 1) * π 1 + star (π 0) * ω 0 + star (π 1) * ω 1 := by
  simp only [penroseNorm, penroseHerm, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, Pi.star_apply, zero_mulVec, one_mulVec,
    zero_add, add_zero, Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

/-- `Σ` is real. -/
lemma penroseNorm_im (Z : Fin 2 ⊕ Fin 2 → ℂ) : (penroseNorm Z).im = 0 := by
  rw [← Sum.elim_comp_inl_inr Z, penroseNorm_sumElim]
  simp only [add_im, mul_im, star_def, conj_re, conj_im, Function.comp_apply]
  ring

/-- `Σ(c Z) = |c|² Σ(Z)`. -/
lemma penroseNorm_smul (c : ℂ) (Z : Fin 2 ⊕ Fin 2 → ℂ) :
    penroseNorm (c • Z) = (normSq c : ℂ) * penroseNorm Z := by
  rw [← Sum.elim_comp_inl_inr Z]
  have : c • Sum.elim (Z ∘ Sum.inl) (Z ∘ Sum.inr) = Sum.elim (c • (Z ∘ Sum.inl)) (c • (Z ∘ Sum.inr)) := by
    funext s; rcases s with i | i <;> rfl
  rw [this, penroseNorm_sumElim, penroseNorm_sumElim, ← mul_conj]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', Function.comp_apply, star_def]
  ring

/-- From the coordinates `(μ, λ)` of `TwistorConformal.lean` to Penrose's `(ω, π) = (i μ, λ)`. -/
def toPenrose : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := fromBlocks (I • 1) 0 0 1

lemma toPenrose_sumElim (m l : Fin 2 → ℂ) : toPenrose *ᵥ Sum.elim m l = Sum.elim (I • m) l := by
  simp [toPenrose, fromBlocks_mulVec, smul_mulVec]

/-- **The two forms agree**: `Σ(i μ, λ) = i(λ̄ · μ - μ̄ · λ)`. -/
theorem penroseNorm_toPenrose (Z : Fin 2 ⊕ Fin 2 → ℂ) :
    penroseNorm (toPenrose *ᵥ Z) = twistorNorm Z := by
  rw [← Sum.elim_comp_inl_inr Z, toPenrose_sumElim, penroseNorm_sumElim, twistorNorm_sumElim]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_I,
    Function.comp_apply]
  ring

/-- `toPenrose` is unitary. -/
lemma toPenrose_unitary : toPenroseᴴ * toPenrose = 1 ∧ toPenrose * toPenroseᴴ = 1 := by
  constructor <;>
    simp [toPenrose, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul, smul_smul,
      ← fromBlocks_one]

/-- The two form matrices are congruent: `twistorHerm = toPenrose† penroseHerm toPenrose`. -/
lemma twistorHerm_eq : twistorHerm = toPenroseᴴ * penroseHerm * toPenrose := by
  simp [twistorHerm, toPenrose, penroseHerm, fromBlocks_conjTranspose, fromBlocks_multiply,
    conjTranspose_smul]

/-! ## Signature (2, 2) -/

lemma inv_sqrt_two_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  rw [← mul_inv, ← sq, ← Complex.ofReal_pow, Real.sq_sqrt zero_le_two]
  norm_num

/-- The unitary `(1/√2) [[1, 1], [1, -1]]`. -/
def penroseDiag : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • fromBlocks 1 1 1 (-1)

lemma penroseDiag_conjTranspose : penroseDiagᴴ = penroseDiag := by
  have hs : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  simp [penroseDiag, conjTranspose_smul, fromBlocks_conjTranspose, hs]

/-- **The twistor form has signature `(2, 2)`**: `U† Σ U = diag(1, 1, -1, -1)` for the unitary
`U = (1/√2) [[1, 1], [1, -1]]` (ADM p. 7, "(+ + - -)"; Adamo p. 14, "(+2, -2)"). -/
theorem penroseHerm_signature :
    penroseDiagᴴ * penroseDiag = 1 ∧
      penroseDiagᴴ * penroseHerm * penroseDiag = fromBlocks 1 0 0 (-1) := by
  rw [penroseDiag_conjTranspose]
  have h2 := inv_sqrt_two_sq
  constructor
  · simp only [penroseDiag, smul_mul_smul_comm, fromBlocks_multiply, h2]
    rw [← fromBlocks_one]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [fromBlocks, one_apply] <;> norm_num
  · simp only [penroseDiag, penroseHerm, smul_mul_assoc, mul_smul_comm, smul_smul, h2,
      fromBlocks_multiply]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [fromBlocks, one_apply] <;> norm_num

/-- The form `twistorHerm` of `TwistorConformal.lean` has signature `(2, 2)` too. -/
theorem twistorHerm_signature :
    ∃ U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ, Uᴴ * U = 1 ∧
      Uᴴ * twistorHerm * U = fromBlocks 1 0 0 (-1) := by
  obtain ⟨h1, h2⟩ := penroseHerm_signature
  obtain ⟨t1, t2⟩ := toPenrose_unitary
  refine ⟨toPenroseᴴ * penroseDiag, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc toPenrose,
      t2, Matrix.one_mul, h1]
  · rw [twistorHerm_eq, conjTranspose_mul, conjTranspose_conjTranspose]
    calc penroseDiagᴴ * toPenrose * (toPenroseᴴ * penroseHerm * toPenrose) * (toPenroseᴴ * penroseDiag)
        = penroseDiagᴴ * (toPenrose * toPenroseᴴ) * penroseHerm * (toPenrose * toPenroseᴴ) *
            penroseDiag := by simp only [Matrix.mul_assoc]
      _ = fromBlocks 1 0 0 (-1) := by rw [t2, Matrix.mul_one, Matrix.mul_one, h2]

/-! ## The incidence relation `ω = i x π` -/

/-- The incidence relation in the row's form, `ω^A = i x^{AA'} π_{A'}`. -/
def incidencePenrose (x : Matrix (Fin 2) (Fin 2) ℂ) (π : Fin 2 → ℂ) : Fin 2 ⊕ Fin 2 → ℂ :=
  Sum.elim (I • (x *ᵥ π)) π

/-- **`ω = i x π` is `μ = Xᵀ λ` followed by `(μ, λ) ↦ (i μ, λ)`, with `x = Xᵀ`.** -/
theorem incidencePenrose_eq (x : Matrix (Fin 2) (Fin 2) ℂ) (π : Fin 2 → ℂ) :
    incidencePenrose x π = toPenrose *ᵥ twistorInc xᵀ π := by
  rw [twistorInc, toPenrose_sumElim, transpose_transpose, incidencePenrose]

/-- **ADM's (2.7)**: for a point `x` of `ComplexMinkowski.lean`, ADM's matrix is `(spinorMat x)ᵀ`
and the incidence relation is that of `incidence x` followed by `toPenrose`. -/
theorem incidencePenrose_spinorMat (x : Fin 4 → ℂ) (π : Fin 2 → ℂ) :
    incidencePenrose (spinorMat x)ᵀ π = toPenrose *ᵥ (incidence x π ∘ finSumFinEquiv) := by
  rw [incidence_comp_finSumFinEquiv, incidencePenrose_eq, transpose_transpose]

/-- The entries of ADM's matrix. -/
lemma spinorMat_transpose (x : Fin 4 → ℂ) :
    (spinorMat x)ᵀ = ((Real.sqrt 2 : ℂ)⁻¹) • !![x 0 + x 3, x 1 + I * x 2; x 1 - I * x 2, x 0 - x 3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spinorMat]

/-- **The twistor line of `x` is null iff `x` is Hermitian**, i.e. a real point (ADM p. 7 and Adamo
(2.7), p. 14, state "⇐"). -/
theorem penroseNorm_incidence_eq_zero_iff (x : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ π, penroseNorm (incidencePenrose x π) = 0) ↔ x.IsHermitian := by
  simp only [incidencePenrose_eq, penroseNorm_toPenrose]
  rw [twistorNorm_inc_eq_zero_iff]
  constructor
  · intro h; simpa using h.transpose
  · intro h; exact h.transpose

/-! ## Projective twistor space -/

/-- Projective twistor space `CP³`. -/
abbrev CP3 := ℙ ℂ (Fin 2 ⊕ Fin 2 → ℂ)

/-- The real number `Σ(Z)`. -/
def penroseSign (Z : Fin 2 ⊕ Fin 2 → ℂ) : ℝ := (penroseNorm Z).re

lemma penroseNorm_eq_sign (Z : Fin 2 ⊕ Fin 2 → ℂ) : penroseNorm Z = (penroseSign Z : ℂ) :=
  Complex.ext rfl (by simp [penroseSign, penroseNorm_im])

lemma penroseSign_smul (c : ℂ) (Z : Fin 2 ⊕ Fin 2 → ℂ) :
    penroseSign (c • Z) = normSq c * penroseSign Z := by
  simp [penroseSign, penroseNorm_smul]

/-- The sign of `Σ` is a projective invariant. -/
lemma penroseSign_rep_mk (Z : Fin 2 ⊕ Fin 2 → ℂ) (hZ : Z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ penroseSign (Projectivization.mk ℂ Z hZ).rep = c * penroseSign Z := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ Z hZ
  refine ⟨normSq (a : ℂ), normSq_pos.2 a.ne_zero, ?_⟩
  rw [← ha, Units.smul_def, penroseSign_smul]

/-- Twistors of positive norm `PT⁺`. -/
def PTplus : Set CP3 := {p | 0 < penroseSign p.rep}

/-- Twistors of negative norm `PT⁻`. -/
def PTminus : Set CP3 := {p | penroseSign p.rep < 0}

/-- Null twistors `PN`. -/
def PN : Set CP3 := {p | penroseSign p.rep = 0}

/-- ADM's projective twistor space `PT = CP³ - CP¹`: the points with `π ≠ 0`. -/
def PT : Set CP3 := {p | p.rep ∘ Sum.inr ≠ 0}

lemma mem_PTplus_mk (Z : Fin 2 ⊕ Fin 2 → ℂ) (hZ : Z ≠ 0) :
    Projectivization.mk ℂ Z hZ ∈ PTplus ↔ 0 < penroseSign Z := by
  obtain ⟨c, hc, h⟩ := penroseSign_rep_mk Z hZ
  show 0 < penroseSign _ ↔ _
  rw [h]; exact mul_pos_iff_of_pos_left hc

lemma mem_PTminus_mk (Z : Fin 2 ⊕ Fin 2 → ℂ) (hZ : Z ≠ 0) :
    Projectivization.mk ℂ Z hZ ∈ PTminus ↔ penroseSign Z < 0 := by
  obtain ⟨c, hc, h⟩ := penroseSign_rep_mk Z hZ
  show penroseSign _ < 0 ↔ _
  rw [h]
  constructor <;> intro h' <;> nlinarith

lemma mem_PN_mk (Z : Fin 2 ⊕ Fin 2 → ℂ) (hZ : Z ≠ 0) :
    Projectivization.mk ℂ Z hZ ∈ PN ↔ penroseSign Z = 0 := by
  obtain ⟨c, hc, h⟩ := penroseSign_rep_mk Z hZ
  show penroseSign _ = 0 ↔ _
  rw [h]; exact mul_eq_zero_iff_left hc.ne'

lemma mem_PT_mk (Z : Fin 2 ⊕ Fin 2 → ℂ) (hZ : Z ≠ 0) :
    Projectivization.mk ℂ Z hZ ∈ PT ↔ Z ∘ Sum.inr ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ Z hZ
  show (Projectivization.mk ℂ Z hZ).rep ∘ Sum.inr ≠ 0 ↔ _
  rw [← ha]
  constructor
  · intro h h0; apply h; funext i
    have h1 : Z (Sum.inr i) = 0 := congrFun h0 i
    simp [Units.smul_def, h1]
  · intro h h0; apply h; funext i
    have := congrFun h0 i
    simpa [Units.smul_def, a.ne_zero] using this

/-- **`PT⁺`, `PN`, `PT⁻` partition `CP³`** (ADM p. 7, Bette p. 15). -/
theorem cp3_partition :
    PTplus ∪ PN ∪ PTminus = Set.univ ∧ Disjoint PTplus PN ∧ Disjoint PTplus PTminus ∧
      Disjoint PN PTminus := by
  refine ⟨Set.eq_univ_of_forall fun p => ?_, ?_, ?_, ?_⟩
  · rcases lt_trichotomy 0 (penroseSign p.rep) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr h
  · exact Set.disjoint_left.2 fun p (h1 : 0 < penroseSign p.rep) (h2 : penroseSign p.rep = 0) =>
      h1.ne' h2
  · exact Set.disjoint_left.2 fun p (h1 : 0 < penroseSign p.rep) (h2 : penroseSign p.rep < 0) =>
      lt_asymm h1 h2
  · exact Set.disjoint_left.2 fun p (h1 : penroseSign p.rep = 0) (h2 : penroseSign p.rep < 0) =>
      h2.ne h1

/-! ### Trust checks: each part is nonempty -/

lemma penroseSign_sumElim (ω π : Fin 2 → ℂ) :
    penroseSign (Sum.elim ω π) = (star (ω 0) * π 0 + star (ω 1) * π 1 + star (π 0) * ω 0 +
      star (π 1) * ω 1).re := by
  rw [penroseSign, penroseNorm_sumElim]

lemma sumElim_ne_zero {ω π : Fin 2 → ℂ} (h : π ≠ 0) : (Sum.elim ω π : Fin 2 ⊕ Fin 2 → ℂ) ≠ 0 := by
  intro h0; apply h; funext i; exact congrFun h0 (Sum.inr i)

theorem PTplus_nonempty : PTplus.Nonempty := by
  refine ⟨Projectivization.mk ℂ (Sum.elim ![1, 0] ![1, 0]) (sumElim_ne_zero (by simp)), ?_⟩
  rw [mem_PTplus_mk, penroseSign_sumElim]
  norm_num

theorem PTminus_nonempty : PTminus.Nonempty := by
  refine ⟨Projectivization.mk ℂ (Sum.elim ![-1, 0] ![1, 0]) (sumElim_ne_zero (by simp)), ?_⟩
  rw [mem_PTminus_mk, penroseSign_sumElim]
  norm_num

theorem PN_nonempty : PN.Nonempty := by
  refine ⟨Projectivization.mk ℂ (Sum.elim ![0, 0] ![1, 0]) (sumElim_ne_zero (by simp)), ?_⟩
  rw [mem_PN_mk, penroseSign_sumElim]
  norm_num

/-- **The lines of real points lie in `PN ∩ PT`** (ADM p. 7): for Hermitian `x` and `π ≠ 0`. -/
theorem mk_incidencePenrose_mem {x : Matrix (Fin 2) (Fin 2) ℂ} (hx : x.IsHermitian) {π : Fin 2 → ℂ}
    (hπ : π ≠ 0) :
    Projectivization.mk ℂ (incidencePenrose x π) (sumElim_ne_zero hπ) ∈ PN ∩ PT := by
  refine ⟨(mem_PN_mk _ _).2 ?_, (mem_PT_mk _ _).2 ?_⟩
  · rw [penroseSign, (penroseNorm_incidence_eq_zero_iff x).2 hx π, zero_re]
  · simpa [incidencePenrose] using hπ

end Lightlike

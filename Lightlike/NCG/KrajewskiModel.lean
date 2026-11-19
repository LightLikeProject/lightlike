import Lightlike.NCG.Classification
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The real finite spectral triple of a symmetric multiplicity matrix

T. Krajewski, arXiv:hep-th/9701081, Section 3.2, p. 13 (read): "Conversely, if the matrix of multiplicities `m` is
symmetric, it is possible to define `J` as above and such a antilinear operator fulfills all conditions imposed to
charge conjugation", with `J (e_a ⊗ ψ_p ⊗ e_b) = e_b ⊗ ψ̄_p ⊗ e_a` on `Hᵢⱼ = ℂⁿⁱ ⊗ ℂᵐⁱʲ ⊗ ℂⁿʲ` (p. 13).

For `A = ⊕ᵢ Mₙᵢ(ℂ)` and a symmetric `r : ι → ι → ℕ`, the Hilbert space is `H = ⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ`
(`EuclideanSpace` over `Σ (i, j), Fin rᵢⱼ × Fin nᵢ × Fin nⱼ`), `π(a)` is block diagonal with blocks `1 ⊗ aᵢ ⊗ 1`, and
`J ψ (i, j, ρ, α, β) = conj ψ (j, i, ρ, β, α)`.

* `KIdx`, `HK`, `blk`, `blockHom` (a `*`-homomorphism into the block-diagonal matrices), `piK`;
* `swapIdx`, `JK`;
* `krajewskiTriple`, `krajewskiReal`: the finite spectral triple `(⊕ Mₙᵢ(ℂ), H, 0)` with its real structure;
* `gammaK`, `krajewskiGrading`: the grading `sᵢⱼ` on `Hᵢⱼ` for symmetric signs;
* `lU_rU_apply`, `e00`, `Vsub_krajewski`, `multiplicity_krajewskiReal`: the multiplicity matrix of the triple is `r`.
-/

open Matrix WithLp
open scoped Kronecker

namespace Lightlike.NCG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (r : ι → ι → ℕ)

/-- The index set `Σ (i, j), Fin rᵢⱼ × Fin nᵢ × Fin nⱼ`. -/
abbrev KIdx := Σ p : ι × ι, Fin (r p.1 p.2) × (Fin (n p.1) × Fin (n p.2))

/-- The Hilbert space `⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ`. -/
abbrev HK := EuclideanSpace ℂ (KIdx n r)

variable {n r}

/-- The block `1 ⊗ aᵢ ⊗ 1` of `π(a)` on `Hᵢⱼ`. -/
def blk (a : MatSum n) (p : ι × ι) :
    Matrix (Fin (r p.1 p.2) × (Fin (n p.1) × Fin (n p.2))) (Fin (r p.1 p.2) × (Fin (n p.1) × Fin (n p.2))) ℂ :=
  (1 : Matrix (Fin (r p.1 p.2)) (Fin (r p.1 p.2)) ℂ) ⊗ₖ (a p.1 ⊗ₖ (1 : Matrix (Fin (n p.2)) (Fin (n p.2)) ℂ))

lemma blk_one (p : ι × ι) : blk (r := r) (1 : MatSum n) p = 1 := by
  simp only [blk, Pi.one_apply, one_kronecker_one]

lemma blk_mul (a b : MatSum n) (p : ι × ι) : blk (r := r) (a * b) p = blk a p * blk b p := by
  simp only [blk, Pi.mul_apply, ← mul_kronecker_mul, mul_one]

lemma blk_add (a b : MatSum n) (p : ι × ι) : blk (r := r) (a + b) p = blk a p + blk b p := by
  simp only [blk, Pi.add_apply, add_kronecker, kronecker_add]

lemma blk_zero (p : ι × ι) : blk (r := r) (0 : MatSum n) p = 0 := by
  simp only [blk, Pi.zero_apply, zero_kronecker, kronecker_zero]

lemma blk_smul (c : ℝ) (a : MatSum n) (p : ι × ι) : blk (r := r) (c • a) p = c • blk a p := by
  simp only [blk, Pi.smul_apply, smul_kronecker, kronecker_smul]

lemma blk_star (a : MatSum n) (p : ι × ι) : blk (r := r) (star a) p = (blk a p)ᴴ := by
  simp only [blk, Pi.star_apply, star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

/-- **`π` in matrix form**: `a ↦ blockDiagonal' (1 ⊗ aᵢ ⊗ 1)`, a real `*`-algebra homomorphism. -/
def blockHom : MatSum n →⋆ₐ[ℝ] Matrix (KIdx n r) (KIdx n r) ℂ where
  toFun a := blockDiagonal' (blk a)
  map_one' := by
    rw [show blk (r := r) (1 : MatSum n) = 1 from funext blk_one, blockDiagonal'_one]
  map_mul' a b := by
    rw [show blk (r := r) (a * b) = fun p => blk a p * blk b p from funext (blk_mul a b), blockDiagonal'_mul]
  map_zero' := by
    rw [show blk (r := r) (0 : MatSum n) = 0 from funext blk_zero, blockDiagonal'_zero]
  map_add' a b := by
    rw [show blk (r := r) (a + b) = blk a + blk b from funext (blk_add a b), blockDiagonal'_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [show blk (r := r) (c • (1 : MatSum n)) = c • blk 1 from funext (blk_smul c 1),
      blockDiagonal'_smul, show blk (r := r) (1 : MatSum n) = 1 from funext blk_one, blockDiagonal'_one]
  map_star' a := by
    show blockDiagonal' (blk (star a)) = star (blockDiagonal' (blk a))
    rw [show blk (r := r) (star a) = fun p => (blk a p)ᴴ from funext (blk_star a), star_eq_conjTranspose,
      blockDiagonal'_conjTranspose]

/-- `(π(a) ψ)(i, j, ρ, α, β) = ∑_γ (aᵢ)_{αγ} ψ(i, j, ρ, γ, β)`. -/
lemma blockHom_mulVec (a : MatSum n) (v : KIdx n r → ℂ) (i j : ι) (ρ : Fin (r i j)) (α : Fin (n i))
    (β : Fin (n j)) :
    (blockHom (r := r) a *ᵥ v) ⟨(i, j), (ρ, (α, β))⟩ = ∑ γ, a i α γ * v ⟨(i, j), (ρ, (γ, β))⟩ := by
  show (blockDiagonal' (blk a) *ᵥ v) ⟨(i, j), (ρ, (α, β))⟩ = _
  simp only [mulVec, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single (i, j) fun q hq => Finset.sum_eq_zero fun y _ => by
    rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hq), zero_mul]]
  simp only [blockDiagonal'_apply_eq, blk, kronecker_apply, one_apply, Fintype.sum_prod_type]
  simp [ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- `Matrix.toEuclideanCLM`, as a real `*`-homomorphism. -/
def toECLM : Matrix (KIdx n r) (KIdx n r) ℂ →⋆ₐ[ℝ] (HK n r →L[ℂ] HK n r) :=
  { ((Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ)).toStarAlgHom :
      Matrix (KIdx n r) (KIdx n r) ℂ →ₐ[ℂ] (HK n r →L[ℂ] HK n r)).restrictScalars ℝ with
    map_star' := fun M => (Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ)).toStarAlgHom.map_star' M }

/-- **`π(a)` on `H`**: the block-diagonal matrix as an operator, a real `*`-homomorphism. -/
def piK : MatSum n →⋆ₐ[ℝ] (HK n r →L[ℂ] HK n r) := toECLM.comp blockHom

lemma piK_apply (a : MatSum n) (ψ : HK n r) (i j : ι) (ρ : Fin (r i j)) (α : Fin (n i)) (β : Fin (n j)) :
    piK a ψ ⟨(i, j), (ρ, (α, β))⟩ = ∑ γ, a i α γ * ψ ⟨(i, j), (ρ, (γ, β))⟩ := by
  show ofLp (Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ) (blockHom a) ψ) ⟨(i, j), (ρ, (α, β))⟩ = _
  rw [ofLp_toEuclideanCLM, blockHom_mulVec]

/-- `π` is faithful when every summand acts on some vertex, `∀ i, ∃ j, rᵢⱼ > 0`. -/
lemma piK_injective [∀ i, NeZero (n i)] (hpos : ∀ i, ∃ j, 0 < r i j) :
    Function.Injective (piK (n := n) (r := r)) := by
  intro a b hab
  funext i
  obtain ⟨j, hj⟩ := hpos i
  ext α γ
  have := congrArg (fun T : HK n r →L[ℂ] HK n r =>
    T (toLp 2 (Pi.single ⟨(i, j), (⟨0, hj⟩, (γ, ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩))⟩ (1 : ℂ)))
      ⟨(i, j), (⟨0, hj⟩, (α, ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩))⟩) hab
  simp only [piK_apply, Pi.single_apply, Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq, true_and,
    and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
  exact this

variable (hr : ∀ i j, r i j = r j i)

/-- The involution `(i, j, ρ, α, β) ↦ (j, i, ρ, β, α)` of the index set. -/
def swapIdx : KIdx n r → KIdx n r
  | ⟨(i, j), (ρ, (α, β))⟩ => ⟨(j, i), (Fin.cast (hr i j) ρ, (β, α))⟩

lemma swapIdx_swapIdx (x : KIdx n r) : swapIdx hr (swapIdx hr x) = x := by
  obtain ⟨⟨i, j⟩, ρ, α, β⟩ := x
  rfl

/-- `swapIdx` as an equivalence. -/
def swapEquiv : KIdx n r ≃ KIdx n r := Function.Involutive.toPerm _ (swapIdx_swapIdx hr)

/-- **The charge conjugation** `J ψ (i, j, ρ, α, β) = conj ψ (j, i, ρ, β, α)` (Krajewski, Section 3.2, p. 13). -/
def JK : HK n r →ₗ⋆[ℂ] HK n r where
  toFun ψ := toLp 2 (fun x => star (ψ (swapIdx hr x)))
  map_add' ψ φ := by
    ext x
    simp [star_add]
  map_smul' c ψ := by
    ext x
    simp [mul_comm]

lemma JK_apply (ψ : HK n r) (x : KIdx n r) : JK hr ψ x = star (ψ (swapIdx hr x)) := rfl

lemma isSelfAdjoint_zero_HK : IsSelfAdjoint (0 : HK n r →L[ℂ] HK n r) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, map_zero]

omit hr in
/-- **The finite spectral triple** `(⊕ᵢ Mₙᵢ(ℂ), ⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ, 0)`. -/
def krajewskiTriple [∀ i, NeZero (n i)] (hpos : ∀ i, ∃ j, 0 < r i j) :
    FiniteSpectralTriple (MatSum n) (HK n r) where
  π := piK
  injective_π := piK_injective hpos
  D := 0
  isSelfAdjoint_D := isSelfAdjoint_zero_HK

lemma JK_JK (ψ : HK n r) : JK hr (JK hr ψ) = ψ := by
  ext x
  simp only [JK_apply, star_star, swapIdx_swapIdx]

open scoped InnerProductSpace in
lemma inner_JK (x y : HK n r) : ⟪JK hr x, JK hr y⟫_ℂ = ⟪y, x⟫_ℂ := by
  simp only [PiLp.inner_apply, JK_apply, RCLike.inner_apply, starRingEnd_apply, star_star]
  calc ∑ k, star (y (swapIdx hr k)) * x (swapIdx hr k) = ∑ k, star (y k) * x k :=
        (swapEquiv hr).sum_comp (fun k => star (y k) * x k)
    _ = ∑ k, x k * star (y k) := Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **The real structure** of `krajewskiTriple`: `J` as in Krajewski, Section 3.2, p. 13. -/
def krajewskiReal [∀ i, NeZero (n i)] (hpos : ∀ i, ∃ j, 0 < r i j) : RealStructure (krajewskiTriple (n := n) hpos) where
  J := JK hr
  inner_J := inner_JK hr
  J_J := JK_JK hr
  order_zero a b x := by
    show piK a (JK hr (piK b (JK hr x))) = JK hr (piK b (JK hr (piK a x)))
    ext ⟨⟨i, j⟩, ρ, α, β⟩
    simp only [piK_apply, JK_apply, swapIdx, Fin.cast_cast, Fin.cast_refl, id_eq, star_sum, star_mul', star_star,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun γ _ => by ring
  first_order a b x := by
    have hD : (krajewskiTriple (n := n) (r := r) hpos).D = 0 := rfl
    simp [FiniteSpectralTriple.comm, hD]
  D_J x := by
    show (0 : HK n r →L[ℂ] HK n r) (JK hr x) = JK hr ((0 : HK n r →L[ℂ] HK n r) x)
    simp

omit hr in
/-- The diagonal of the grading, `sᵢⱼ` on `Hᵢⱼ`. -/
def gdiag (s : ι → ι → ℝ) (x : KIdx n r) : ℂ := (s x.1.1 x.1.2 : ℂ)

omit hr in
/-- **The grading** `γ = sᵢⱼ` on `Hᵢⱼ`. -/
def gammaK (s : ι → ι → ℝ) : HK n r →L[ℂ] HK n r := Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ) (diagonal (gdiag s))

omit hr in
lemma gammaK_apply (s : ι → ι → ℝ) (ψ : HK n r) (x : KIdx n r) : gammaK s ψ x = gdiag s x * ψ x := by
  show ofLp (Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ) (diagonal (gdiag s)) ψ) x = _
  rw [ofLp_toEuclideanCLM, mulVec_diagonal]

omit hr in
lemma diagonal_gdiag_mul_blockHom (s : ι → ι → ℝ) (a : MatSum n) :
    diagonal (gdiag (r := r) s) * blockHom a = blockHom a * diagonal (gdiag s) := by
  ext x y
  rw [diagonal_mul, mul_diagonal]
  show gdiag s x * blockDiagonal' (blk a) x y = blockDiagonal' (blk a) x y * gdiag s y
  by_cases h : x.1 = y.1
  · rw [show gdiag (r := r) s x = gdiag s y from by simp only [gdiag, h], mul_comm]
  · simp [blockDiagonal'_apply, h]

/-- **The grading** of `krajewskiTriple` for symmetric signs `sᵢⱼ = sⱼᵢ = ±1` (Krajewski, Section 3.3, p. 13:
`χ = ⊕ χᵢⱼ`, `χᵢⱼ = ±1`, `χᵢⱼ = χⱼᵢ`). -/
def krajewskiGrading [∀ i, NeZero (n i)] (hpos : ∀ i, ∃ j, 0 < r i j) (s : ι → ι → ℝ)
    (hs : ∀ i j, s i j * s i j = 1) (hsym : ∀ i j, s i j = s j i) :
    Grading (krajewskiTriple (n := n) hpos) (krajewskiReal (n := n) hr hpos) where
  γ := gammaK s
  isSelfAdjoint_γ := by
    rw [IsSelfAdjoint, gammaK, ← map_star, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 2
    funext x
    simp [gdiag, Complex.conj_ofReal]
  γ_γ := by
    rw [gammaK, ← map_mul, diagonal_mul_diagonal, ← map_one (Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ)),
      ← diagonal_one]
    congr 2
    funext x
    simp only [gdiag, ← Complex.ofReal_mul, hs, Complex.ofReal_one]
  γ_J x := by
    show gammaK s (JK hr x) = JK hr (gammaK s x)
    ext ⟨⟨i, j⟩, ρ, α, β⟩
    simp only [gammaK_apply, JK_apply, swapIdx, gdiag, star_mul', Complex.star_def, Complex.conj_ofReal, hsym i j]
  γ_π a := by
    show gammaK s * Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ) (blockHom a) =
      Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ) (blockHom a) * gammaK s
    rw [gammaK, ← map_mul, ← map_mul, diagonal_gdiag_mul_blockHom]
  D_γ := by
    show (0 : HK n r →L[ℂ] HK n r) * gammaK s = -(gammaK s * 0)
    simp

/-- **`π(Eᵢ,₀₀) J π(Eⱼ,₀₀) J` in coordinates**: the projection onto the vectors at `(i, j, ρ, 0, 0)`. -/
lemma lU_rU_apply [∀ i, NeZero (n i)] (hpos : ∀ i, ∃ j, 0 < r i j) (i j : ι) (ψ : HK n r) (i' j' : ι)
    (ρ : Fin (r i' j')) (α : Fin (n i')) (β : Fin (n j')) :
    lU (krajewskiTriple (n := n) hpos) i 0 0 (rU (krajewskiReal (n := n) hr hpos) j 0 0 ψ) ⟨(i', j'), (ρ, (α, β))⟩ =
      if i' = i ∧ j' = j ∧ α = 0 ∧ β = 0 then ψ ⟨(i', j'), (ρ, (0, 0))⟩ else 0 := by
  show piK (unit n i 0 0) (JK hr (piK (unit n j 0 0) (JK hr ψ))) ⟨(i', j'), (ρ, (α, β))⟩ = _
  simp only [piK_apply, JK_apply, swapIdx, Fin.cast_cast, Fin.cast_refl, id_eq, star_sum, star_mul', star_star]
  by_cases hi : i' = i
  · subst hi
    by_cases hj : j' = j
    · subst hj
      simp only [unit, Pi.single_eq_same, Matrix.single_apply, true_and, and_true]
      by_cases hα : α = 0 <;> by_cases hβ : β = 0 <;>
        simp [hα, hβ, eq_comm, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [unit, Pi.single_eq_of_ne hj, hj]
  · simp [unit, Pi.single_eq_of_ne hi, hi]

/-- The basis vector at `(i, j, ρ, 0, 0)`. -/
def e00 [∀ i, NeZero (n i)] (i j : ι) (ρ : Fin (r i j)) : HK n r :=
  EuclideanSpace.single (⟨(i, j), (ρ, (0, 0))⟩ : KIdx n r) (1 : ℂ)

lemma e00_apply [∀ i, NeZero (n i)] (i j : ι) (ρ : Fin (r i j)) (x : KIdx n r) :
    e00 i j ρ x = if x = ⟨(i, j), (ρ, (0, 0))⟩ then 1 else 0 := by
  simp only [e00, PiLp.single_apply]

/-- **`Vᵢⱼ` is spanned by the basis vectors at `(i, j, ρ, 0, 0)`.** -/
lemma Vsub_krajewski [∀ i, NeZero (n i)] (hpos : ∀ i, ∃ j, 0 < r i j) (i j : ι) :
    Vsub (krajewskiReal (n := n) hr hpos) i j = Submodule.span ℂ (Set.range (e00 (n := n) (r := r) i j)) := by
  apply le_antisymm
  · rintro _ ⟨ψ, rfl⟩
    have hψ : (lU (krajewskiTriple (n := n) hpos) i 0 0 ∘ₗ rU (krajewskiReal (n := n) hr hpos) j 0 0) ψ =
        ∑ ρ, ψ ⟨(i, j), (ρ, (0, 0))⟩ • e00 i j ρ := by
      ext ⟨⟨i', j'⟩, ρ', α, β⟩
      rw [LinearMap.comp_apply, lU_rU_apply]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, e00_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero]
      by_cases h : i' = i ∧ j' = j ∧ α = 0 ∧ β = 0
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, and_true, if_true, Finset.sum_ite_eq,
          Finset.sum_ite_eq', Finset.mem_univ]
      · rw [if_neg h]
        refine (Finset.sum_eq_zero fun ρ _ => ?_).symm
        rw [if_neg]
        intro hx
        simp only [Sigma.mk.inj_iff, Prod.mk.injEq] at hx
        obtain ⟨⟨rfl, rfl⟩, hx⟩ := hx
        simp only [heq_eq_eq, Prod.mk.injEq] at hx
        exact h ⟨rfl, rfl, hx.2.1, hx.2.2⟩
    rw [hψ]
    exact Submodule.sum_mem _ fun ρ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ρ, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨ρ, rfl⟩
    refine ⟨e00 i j ρ, ?_⟩
    ext ⟨⟨i', j'⟩, ρ', α, β⟩
    rw [LinearMap.comp_apply, lU_rU_apply, e00_apply, e00_apply]
    by_cases h : i' = i ∧ j' = j ∧ α = 0 ∧ β = 0
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp
    · rw [if_neg h, if_neg]
      intro hx
      simp only [Sigma.mk.inj_iff, Prod.mk.injEq] at hx
      obtain ⟨⟨rfl, rfl⟩, hx⟩ := hx
      simp only [heq_eq_eq, Prod.mk.injEq] at hx
      exact h ⟨rfl, rfl, hx.2.1, hx.2.2⟩

/-- **The multiplicity matrix of `krajewskiReal` is `r`**: every symmetric `r` is the multiplicity matrix of a real
finite spectral triple (Krajewski, Section 3.2, p. 13). -/
theorem multiplicity_krajewskiReal [∀ i, NeZero (n i)] (hpos : ∀ i, ∃ j, 0 < r i j) (i j : ι) :
    multiplicity (krajewskiReal (n := n) hr hpos) i j = r i j := by
  rw [multiplicity, Vsub_krajewski, finrank_span_eq_card, Fintype.card_fin]
  have hinj : Function.Injective fun ρ : Fin (r i j) => (⟨(i, j), (ρ, (0, 0))⟩ : KIdx n r) := by
    intro ρ ρ' h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
    exact h.1
  exact EuclideanSpace.orthonormal_single.linearIndependent.comp _ hinj

end

end Lightlike.NCG

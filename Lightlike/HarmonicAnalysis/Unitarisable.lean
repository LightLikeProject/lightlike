import Lightlike.HarmonicAnalysis.SU2Complete
import Lightlike.HarmonicAnalysis.PeterWeylClassFunctions

/-!
# Every continuous finite-dimensional representation of a compact group is unitarisable

Let `G` be a compact group with its Haar probability measure `μ` and `ρ` a continuous finite-dimensional complex
matrix representation of `G` (`MatrixRep`, not assumed unitary). Averaging the standard inner product over `G`,
`⟨u, v⟩' = ∫ ⟨ρ(g) u, ρ(g) v⟩ dμ(g)`, gives the Gram matrix `H = ∫ ρ(g)ᴴ ρ(g) dμ(g)` (`gram`), which is positive
definite (`posDef_gram`) and invariant, `ρ(g)ᴴ H ρ(g) = H` (`gram_invariant`): `⟨ , ⟩'` is an invariant inner product
(`exists_invariant_inner_product`). Writing `H = Tᴴ T` (spectral theorem), `T ρ T⁻¹` is a continuous unitary matrix
representation (`exists_unitary_conj`).

For `SU(2)` this extends the classification of the irreducible unitary representations
(`su2_irreducible_classification`) to every continuous irreducible representation: each is equivalent to a spin
representation `spinRep n` and has dimension `n + 1` (`su2_irreducible_classification_continuous`).

**Difference from the source (kind: representation).** Representations are matrix representations
`G →* Matrix ι ι ℂ` with continuous entries, as in the rest of the harmonic-analysis files; a representation on a
finite-dimensional space is one of these after a choice of basis.

## References

* C. Teleman, *Representation Theory* (lecture notes, Cambridge, Lent 2005), Lecture 3, Theorem 3.10 (Weyl's
  unitary trick, by averaging the inner product) and Remark 3.11 (the same for continuous representations of compact
  groups, with the Haar measure), PDF page 7; Lecture 19, Proposition 19.4 ("Every finite-dimensional representation
  of a compact group is unitarisable"), PDF page 44; Lecture 21, Theorem 21.1, PDF page 50.
-/

open MeasureTheory Matrix
open scoped ComplexOrder

namespace Lightlike.HarmonicAnalysis

noncomputable section

/-- A **continuous finite-dimensional complex matrix representation** of `G` (not necessarily unitary). -/
structure MatrixRep (G : Type*) [Group G] [TopologicalSpace G] (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- The homomorphism into the matrices. -/
  toHom : G →* Matrix ι ι ℂ
  /-- Continuity of the matrix entries. -/
  continuous_toHom : Continuous fun g => (toHom g : Matrix ι ι ℂ)

namespace MatrixRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma continuous_apply (ρ : MatrixRep G ι) (i j : ι) : Continuous fun g => ρ.toHom g i j :=
  (_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp ρ.continuous_toHom)

/-- A unitary matrix representation as a matrix representation. -/
def ofUnitary (σ : UnitaryMatrixRep G ι) : MatrixRep G ι where
  toHom := (Submonoid.subtype _).comp σ.toHom
  continuous_toHom := σ.continuous_toHom

/-- Irreducibility: a nonzero space with no invariant subspace except `0` and the whole space. -/
def IsIrreducible (ρ : MatrixRep G ι) : Prop :=
  Nonempty ι ∧ ∀ W : Submodule ℂ (ι → ℂ), (∀ g, ∀ w ∈ W, (ρ.toHom g).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤

/-- Equivalence of representations: an intertwining linear isomorphism. -/
def Equivalent (ρ : MatrixRep G ι) (σ : MatrixRep G κ) : Prop :=
  ∃ e : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ), ∀ g w, e ((σ.toHom g).mulVec w) = (ρ.toHom g).mulVec (e w)

variable [MeasurableSpace G] (μ : Measure G)

/-- The **averaged Gram matrix** `H = ∫ ρ(g)ᴴ ρ(g) dμ(g)`. -/
def gram (ρ : MatrixRep G ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∫ g, ((ρ.toHom g)ᴴ * ρ.toHom g) i j ∂μ

omit [MeasurableSpace G] in
lemma continuous_gram_integrand (ρ : MatrixRep G ι) (i j : ι) :
    Continuous fun g => ((ρ.toHom g)ᴴ * ρ.toHom g) i j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((ρ.continuous_apply k i).star).mul (ρ.continuous_apply k j)

omit [Group G] [TopologicalSpace G] [DecidableEq ι] in
/-- Constant matrices pass through the entrywise integral. -/
lemma mul_integral_mul (F : G → Matrix ι ι ℂ) (hF : ∀ i j, Integrable (fun g => F g i j) μ)
    (A B : Matrix ι ι ℂ) (i j : ι) :
    (A * Matrix.of (fun a b => ∫ g, F g a b ∂μ) * B) i j = ∫ g, (A * F g * B) i j ∂μ := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [integral_finsetSum _ fun b _ => ?_]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun a _ => ?_]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_mul_const, integral_const_mul]
    · exact ((hF a b).const_mul _).mul_const _
  · exact integrable_finsetSum _ fun a _ => ((hF a b).const_mul _).mul_const _

variable [CompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

lemma integrable_gram_integrand (ρ : MatrixRep G ι) (i j : ι) :
    Integrable (fun g => ((ρ.toHom g)ᴴ * ρ.toHom g) i j) μ :=
  (ρ.continuous_gram_integrand i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The quadratic form of the Gram matrix is the average of `‖ρ(g) v‖²`. -/
lemma dotProduct_gram (ρ : MatrixRep G ι) (v : ι → ℂ) :
    star v ⬝ᵥ (gram μ ρ *ᵥ v) = ((∫ g, ∑ i, ‖(ρ.toHom g *ᵥ v) i‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hpt : ∀ g, ((∑ i, ‖(ρ.toHom g *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, star (v i) * (((ρ.toHom g)ᴴ * ρ.toHom g) i j * v j) := by
    intro g
    have h1 : ((∑ i, ‖(ρ.toHom g *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) = star (ρ.toHom g *ᵥ v) ⬝ᵥ (ρ.toHom g *ᵥ v) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  rw [← integral_complex_ofReal]
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((ρ.integrable_gram_integrand μ i j).mul_const _).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((ρ.integrable_gram_integrand μ i j).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]
  simp only [gram, Matrix.of_apply, Pi.star_apply]

omit [CompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] in
lemma gram_isHermitian (ρ : MatrixRep G ι) : (gram μ ρ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [gram, Matrix.of_apply, Complex.star_def]
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simpa [Complex.star_def] using (Matrix.isHermitian_conjTranspose_mul_self (ρ.toHom g)).apply i j

/-- **The averaged Gram matrix is positive definite.** -/
theorem posDef_gram (ρ : MatrixRep G ι) : (gram μ ρ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gram_isHermitian μ ρ) fun v hv => ?_
  rw [dotProduct_gram]
  have hcont : Continuous fun g => ∑ i, ‖(ρ.toHom g *ᵥ v) i‖ ^ 2 := by
    have : ∀ i, Continuous fun g => (ρ.toHom g *ᵥ v) i := fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ fun j _ => (ρ.continuous_apply i j).mul continuous_const
    exact continuous_finsetSum _ fun i _ => ((this i).norm).pow 2
  have hne : (∑ i, ‖(ρ.toHom 1 *ᵥ v) i‖ ^ 2) ≠ 0 := by
    rw [map_one, Matrix.one_mulVec]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    have hi' : v i ≠ 0 := by simpa using hi
    exact (Finset.sum_pos' (fun j _ => by positivity)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi') 2⟩).ne'
  have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := (1 : G)) hcont
    (HasCompactSupport.of_compactSpace _) (fun g => by positivity) hne
  exact Complex.zero_lt_real.2 hpos

variable [IsTopologicalGroup G] [T2Space G] [IsProbabilityMeasure μ]

/-- **Invariance**: `ρ(h)ᴴ H ρ(h) = H`. -/
theorem gram_invariant (ρ : MatrixRep G ι) (h : G) :
    (ρ.toHom h)ᴴ * gram μ ρ * ρ.toHom h = gram μ ρ := by
  ext i j
  rw [gram, mul_integral_mul μ _ (ρ.integrable_gram_integrand μ)]
  have e : ∀ g, ((ρ.toHom h)ᴴ * ((ρ.toHom g)ᴴ * ρ.toHom g) * ρ.toHom h) i j =
      ((ρ.toHom (g * h))ᴴ * ρ.toHom (g * h)) i j := fun g => by
    rw [map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [e, Matrix.of_apply]
  exact integral_mul_right_eq_self (fun g => ((ρ.toHom g)ᴴ * ρ.toHom g) i j) h

include μ in
/-- **An invariant inner product** (Teleman, Theorem 3.10, Remark 3.11, Proposition 19.4): the positive definite
form `⟨u, v⟩' = ⟨u, H v⟩` with `H = gram μ ρ` satisfies `⟨ρ(g) u, ρ(g) v⟩' = ⟨u, v⟩'`. -/
theorem exists_invariant_inner_product (ρ : MatrixRep G ι) :
    ∃ H : Matrix ι ι ℂ, H.PosDef ∧ ∀ g u v, star (ρ.toHom g *ᵥ u) ⬝ᵥ (H *ᵥ (ρ.toHom g *ᵥ v)) = star u ⬝ᵥ (H *ᵥ v) := by
  refine ⟨gram μ ρ, posDef_gram μ ρ, fun g u v => ?_⟩
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    gram_invariant]

omit [CompactSpace G] [BorelSpace G] [IsTopologicalGroup G] [T2Space G] in
/-- A square root `H = Tᴴ T` of a positive definite matrix, with an inverse. -/
lemma exists_sqrt_of_posDef {H : Matrix ι ι ℂ} (hH : H.PosDef) :
    ∃ T Tinv : Matrix ι ι ℂ, Tᴴ * T = H ∧ T * Tinv = 1 ∧ Tinv * T = 1 := by
  set U := hH.1.eigenvectorUnitary
  set ev := hH.1.eigenvalues
  have hev : ∀ i, 0 < ev i := hH.eigenvalues_pos
  have hspec : H = (U : Matrix ι ι ℂ) * diagonal (fun i => ((ev i : ℝ) : ℂ)) * (star (U : Matrix ι ι ℂ)) := by
    conv_lhs => rw [hH.1.spectral_theorem]
    rfl
  set s : ι → ℂ := fun i => ((Real.sqrt (ev i) : ℝ) : ℂ)
  set si : ι → ℂ := fun i => (((Real.sqrt (ev i))⁻¹ : ℝ) : ℂ)
  have hD : (diagonal s)ᴴ = diagonal s := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [s, Complex.conj_ofReal]
  have hDD : diagonal s * diagonal s = diagonal (fun i => ((ev i : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [s]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hev i).le]
  have hsi : diagonal s * diagonal si = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [s, si]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 (hev i)).ne', Complex.ofReal_one]
  have his : diagonal si * diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [s, si]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.2 (hev i)).ne', Complex.ofReal_one]
  have hUs : (star (U : Matrix ι ι ℂ))ᴴ = (U : Matrix ι ι ℂ) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have hsU : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self U
  have hUs' : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 := Unitary.coe_mul_star_self U
  refine ⟨diagonal s * star (U : Matrix ι ι ℂ), (U : Matrix ι ι ℂ) * diagonal si, ?_, ?_, ?_⟩
  · calc (diagonal s * star (U : Matrix ι ι ℂ))ᴴ * (diagonal s * star (U : Matrix ι ι ℂ))
        = (U : Matrix ι ι ℂ) * (diagonal s * diagonal s) * star (U : Matrix ι ι ℂ) := by
          rw [Matrix.conjTranspose_mul, hD, hUs]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hDD, hspec]
  · calc diagonal s * star (U : Matrix ι ι ℂ) * ((U : Matrix ι ι ℂ) * diagonal si)
        = diagonal s * (star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)) * diagonal si := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsU, Matrix.mul_one, hsi]
  · calc (U : Matrix ι ι ℂ) * diagonal si * (diagonal s * star (U : Matrix ι ι ℂ))
        = (U : Matrix ι ι ℂ) * (diagonal si * diagonal s) * star (U : Matrix ι ι ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [his, Matrix.mul_one, hUs']

include μ in
/-- **Unitarisation** (Teleman, Proposition 19.4): every continuous finite-dimensional representation of a compact
group is conjugate to a continuous unitary matrix representation, `σ(g) = T ρ(g) T⁻¹`. -/
theorem exists_unitary_conj (ρ : MatrixRep G ι) :
    ∃ (T Tinv : Matrix ι ι ℂ) (σ : UnitaryMatrixRep G ι), T * Tinv = 1 ∧ Tinv * T = 1 ∧
      ∀ g, σ.mat g = T * ρ.toHom g * Tinv := by
  obtain ⟨T, Tinv, hTT, h1, h2⟩ := exists_sqrt_of_posDef (posDef_gram μ ρ)
  have hmem : ∀ g, T * ρ.toHom g * Tinv ∈ Matrix.unitaryGroup ι ℂ := fun g => by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul]
    calc Tinvᴴ * ((ρ.toHom g)ᴴ * Tᴴ) * (T * ρ.toHom g * Tinv)
        = Tinvᴴ * ((ρ.toHom g)ᴴ * (Tᴴ * T) * ρ.toHom g) * Tinv := by simp only [Matrix.mul_assoc]
      _ = Tinvᴴ * (Tᴴ * T) * Tinv := by rw [hTT, gram_invariant]
      _ = (T * Tinv)ᴴ * (T * Tinv) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
  let σhom : G →* Matrix.unitaryGroup ι ℂ :=
    { toFun := fun g => ⟨T * ρ.toHom g * Tinv, hmem g⟩
      map_one' := by apply Subtype.ext; simp [h1]
      map_mul' := fun g h => by
        apply Subtype.ext
        change T * ρ.toHom (g * h) * Tinv = (T * ρ.toHom g * Tinv) * (T * ρ.toHom h * Tinv)
        rw [map_mul]
        calc T * (ρ.toHom g * ρ.toHom h) * Tinv = T * ρ.toHom g * (Tinv * T) * ρ.toHom h * Tinv := by
              rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hcont : Continuous fun g => ((σhom g : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) := by
    change Continuous fun g => T * ρ.toHom g * Tinv
    exact (continuous_const.matrix_mul ρ.continuous_toHom).matrix_mul continuous_const
  exact ⟨T, Tinv, ⟨σhom, hcont⟩, h1, h2, fun g => rfl⟩

end MatrixRep

open MatrixRep

/-- **The spin representations are all the continuous irreducible representations of `SU(2)`** (Teleman,
Theorem 21.1, with Proposition 19.4): every continuous irreducible matrix representation of `SU(2)`, unitary or not, is
equivalent to `spinRep n` for some `n`, and has dimension `n + 1`. -/
theorem su2_irreducible_classification_continuous {κ : Type} [Fintype κ] [DecidableEq κ]
    {ρ : MatrixRep SU2 κ} (hρ : ρ.IsIrreducible) :
    ∃ n : ℕ, MatrixRep.Equivalent (ofUnitary (su2Spin n)) ρ ∧ Fintype.card κ = n + 1 := by
  have := isProbabilityMeasure_haarMeasure_top SU2
  obtain ⟨T, Tinv, σ, h1, h2, hσ⟩ := exists_unitary_conj (Measure.haarMeasure ⊤) ρ
  -- `σ` is irreducible
  have hσirr : σ.IsIrreducible := by
    refine ⟨hρ.1, fun W hW => ?_⟩
    let V : Submodule ℂ (κ → ℂ) := W.comap T.mulVecLin
    have hV : ∀ g, ∀ v ∈ V, (ρ.toHom g).mulVec v ∈ V := fun g v hv => by
      change T *ᵥ (ρ.toHom g *ᵥ v) ∈ W
      have : T *ᵥ (ρ.toHom g *ᵥ v) = σ.mat g *ᵥ (T *ᵥ v) := by
        rw [hσ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (T * ρ.toHom g) Tinv T, h2,
          Matrix.mul_one]
      rw [this]
      exact hW g _ hv
    have hTTinv : ∀ w : κ → ℂ, T *ᵥ (Tinv *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rcases hρ.2 V hV with h | h
    · left
      rw [Submodule.eq_bot_iff] at h ⊢
      intro w hw
      have : Tinv *ᵥ w ∈ V := by change T *ᵥ (Tinv *ᵥ w) ∈ W; rw [hTTinv]; exact hw
      have h0 := h _ this
      rw [← hTTinv w, h0, Matrix.mulVec_zero]
    · right
      rw [Submodule.eq_top_iff'] at h ⊢
      intro w
      have : Tinv *ᵥ w ∈ V := h _
      change T *ᵥ (Tinv *ᵥ w) ∈ W at this
      rwa [hTTinv] at this
  obtain ⟨n, ⟨e, he⟩, hcard⟩ := su2_irreducible_classification hσirr
  -- compose the intertwiner with `T`
  let eT : (κ → ℂ) ≃ₗ[ℂ] (κ → ℂ) := LinearEquiv.ofLinearMap T.mulVecLin Tinv.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, h1, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h2, Matrix.mulVecLin_one])
  refine ⟨n, ⟨eT.trans e, fun g w => ?_⟩, hcard⟩
  have hT : T *ᵥ (ρ.toHom g *ᵥ w) = σ.mat g *ᵥ (T *ᵥ w) := by
    rw [hσ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (T * ρ.toHom g) Tinv T, h2,
      Matrix.mul_one]
  change e (T *ᵥ (ρ.toHom g *ᵥ w)) = _
  rw [hT, he]
  rfl

end

end Lightlike.HarmonicAnalysis

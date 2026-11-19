import Lightlike.HarmonicAnalysis.MatrixCoefficient

/-!
# Schur's lemma and the orthogonality relations for matrix coefficients

For irreducible continuous unitary matrix representations `ρ`, `σ` of a compact group with a Haar probability
measure `μ`:

* `∫ ρ_{ij} · conj σ_{lk} dμ = 0` if `ρ` and `σ` are not equivalent (`schur_orthogonality_ne`);
* `∫ ρ_{ij} · conj ρ_{lk} dμ = δ_{il} δ_{jk} / dim ρ` (`schur_orthogonality_eq`).

The proof averages `g ↦ ρ(g) X σ(g)ᴴ` to an intertwiner and applies Schur's lemma.

## References

* T. Bröcker and T. tom Dieck, *Representations of compact Lie groups*, Springer (1985), Chapter II/III.
-/

open MeasureTheory Matrix

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace UnitaryMatrixRep

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The matrix of `ρ(g)`. -/
def mat (ρ : UnitaryMatrixRep G ι) (g : G) : Matrix ι ι ℂ := (ρ.toHom g : Matrix.unitaryGroup ι ℂ)

lemma mat_mul (ρ : UnitaryMatrixRep G ι) (g h : G) : ρ.mat (g * h) = ρ.mat g * ρ.mat h := by
  simp [mat]

lemma mat_one (ρ : UnitaryMatrixRep G ι) : ρ.mat 1 = 1 := by simp [mat]

lemma star_mat_mul_mat (ρ : UnitaryMatrixRep G ι) (g : G) : (ρ.mat g)ᴴ * ρ.mat g = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.1 (ρ.toHom g).2
  simpa [mat, Matrix.star_eq_conjTranspose] using this

lemma mat_mul_star_mat (ρ : UnitaryMatrixRep G ι) (g : G) : ρ.mat g * (ρ.mat g)ᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.1 (ρ.toHom g).2
  simpa [mat, Matrix.star_eq_conjTranspose] using this

lemma continuous_mat_apply (ρ : UnitaryMatrixRep G ι) (i j : ι) : Continuous fun g => ρ.mat g i j :=
  (continuous_apply j).comp ((continuous_apply i).comp ρ.continuous_toHom)

/-- Irreducibility: a nonzero space with no invariant subspace except `0` and the whole space. -/
def IsIrreducible (ρ : UnitaryMatrixRep G ι) : Prop :=
  Nonempty ι ∧ ∀ W : Submodule ℂ (ι → ℂ), (∀ g, ∀ w ∈ W, (ρ.mat g).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤

/-- Equivalence of representations: an intertwining linear isomorphism. -/
def Equivalent (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) : Prop :=
  ∃ e : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ), ∀ g w, e ((σ.mat g).mulVec w) = (ρ.mat g).mulVec (e w)

/-- The kernel of an intertwiner out of an irreducible representation is `0` or everything. -/
lemma ker_eq_bot_or_eq_top {ρ : UnitaryMatrixRep G ι} {σ : UnitaryMatrixRep G κ}
    (hσ : σ.IsIrreducible) (M : Matrix ι κ ℂ) (hM : ∀ g, ρ.mat g * M = M * σ.mat g) :
    LinearMap.ker M.mulVecLin = ⊥ ∨ LinearMap.ker M.mulVecLin = ⊤ := by
  refine hσ.2 _ fun g w hw => ?_
  rw [LinearMap.mem_ker] at hw ⊢
  simp only [Matrix.mulVecLin_apply] at hw ⊢
  rw [Matrix.mulVec_mulVec, ← hM g, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]

/-- **Schur's lemma.** An intertwiner between irreducible representations is zero or an isomorphism. -/
lemma schur_zero_or_equivalent {ρ : UnitaryMatrixRep G ι} {σ : UnitaryMatrixRep G κ}
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (M : Matrix ι κ ℂ)
    (hM : ∀ g, ρ.mat g * M = M * σ.mat g) : M = 0 ∨ Equivalent ρ σ := by
  rcases ker_eq_bot_or_eq_top hσ M hM with hk | hk
  · -- injective; the range is invariant
    right
    have hrange : LinearMap.range M.mulVecLin = ⊥ ∨ LinearMap.range M.mulVecLin = ⊤ := by
      refine hρ.2 _ fun g w hw => ?_
      obtain ⟨u, rfl⟩ := hw
      refine ⟨(σ.mat g).mulVec u, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, ← hM g, ← Matrix.mulVec_mulVec]
    rcases hrange with hr | hr
    · exfalso
      obtain ⟨k⟩ := hσ.1
      have h0 : M.mulVecLin = 0 := LinearMap.range_eq_bot.1 hr
      have : LinearMap.ker M.mulVecLin = ⊤ := by rw [h0]; exact LinearMap.ker_zero
      rw [hk] at this
      have h1 : (Pi.single k (1 : ℂ) : κ → ℂ) ∈ (⊤ : Submodule ℂ (κ → ℂ)) := Submodule.mem_top
      rw [← this] at h1
      simp at h1
    · have hbij : Function.Bijective M.mulVecLin :=
        ⟨LinearMap.ker_eq_bot.1 hk, LinearMap.range_eq_top.1 hr⟩
      refine ⟨LinearEquiv.ofBijective M.mulVecLin hbij, fun g w => ?_⟩
      simp only [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM g]
  · left
    ext i k
    have := congrArg (fun f => f (Pi.single k (1 : ℂ))) (LinearMap.ker_eq_top.1 hk)
    have h2 := congrFun this i
    simpa [Matrix.mulVec_single_one] using h2

/-- **Schur's lemma, scalar form.** An endomorphism commuting with an irreducible representation is a
scalar. -/
lemma schur_scalar {ρ : UnitaryMatrixRep G ι} (hρ : ρ.IsIrreducible) (M : Matrix ι ι ℂ)
    (hM : ∀ g, ρ.mat g * M = M * ρ.mat g) : ∃ c : ℂ, M = c • (1 : Matrix ι ι ℂ) := by
  haveI : Nonempty ι := hρ.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (M.mulVecLin)
  refine ⟨c, ?_⟩
  set M' : Matrix ι ι ℂ := M - c • 1 with hM'
  have hM'int : ∀ g, ρ.mat g * M' = M' * ρ.mat g := fun g => by
    simp [hM', Matrix.mul_sub, Matrix.sub_mul, hM g]
  have hker_ne : LinearMap.ker M'.mulVecLin ≠ ⊥ := by
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    intro hbot
    have hv0 : M'.mulVecLin v = 0 := by
      have h1 : M.mulVec v = c • v := hv.apply_eq_smul
      rw [Matrix.mulVecLin_apply, hM', Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1,
        sub_self]
    have : v ∈ LinearMap.ker M'.mulVecLin := hv0
    rw [hbot] at this
    exact hv.2 (by simpa using this)
  have htop := (ker_eq_bot_or_eq_top hρ M' hM'int).resolve_left hker_ne
  have hzero : M' = 0 := by
    ext i k
    have := congrArg (fun f => f (Pi.single k (1 : ℂ))) (LinearMap.ker_eq_top.1 htop)
    have h2 := congrFun this i
    simpa [Matrix.mulVec_single_one] using h2
  exact sub_eq_zero.1 hzero

variable [MeasurableSpace G]

/-- The average `∫ ρ(g) X σ(g)ᴴ dμ`, entrywise. -/
def avg (μ : Measure G) (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) (X : Matrix ι κ ℂ) :
    Matrix ι κ ℂ :=
  Matrix.of fun i l => ∫ g, (ρ.mat g * X * (σ.mat g)ᴴ) i l ∂μ

lemma continuous_conj_apply (σ : UnitaryMatrixRep G κ) (l k : κ) :
    Continuous fun g => ((σ.mat g)ᴴ) k l := by
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.comp (σ.continuous_mat_apply l k)

lemma continuous_integrand (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) (X : Matrix ι κ ℂ)
    (i : ι) (l : κ) : Continuous fun g => (ρ.mat g * X * (σ.mat g)ᴴ) i l := by
  simp only [Matrix.mul_apply]
  refine continuous_finsetSum _ fun a _ => ?_
  refine (continuous_finsetSum _ fun b _ => ?_).mul (continuous_conj_apply σ l a)
  exact (ρ.continuous_mat_apply i b).mul continuous_const

variable [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The average is an intertwiner. -/
lemma avg_intertwines (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) (X : Matrix ι κ ℂ) (h : G) :
    ρ.mat h * avg μ ρ σ X = avg μ ρ σ X * σ.mat h := by
  ext i l
  have hint : ∀ a b, Integrable (fun g => (ρ.mat g * X * (σ.mat g)ᴴ) a b) μ := fun a b =>
    (continuous_integrand ρ σ X a b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- left side
  have hL : (ρ.mat h * avg μ ρ σ X) i l = ∫ g, (ρ.mat h * (ρ.mat g * X * (σ.mat g)ᴴ)) i l ∂μ := by
    rw [Matrix.mul_apply]
    simp only [avg, Matrix.of_apply]
    have hexp : ∀ g, (ρ.mat h * (ρ.mat g * X * (σ.mat g)ᴴ)) i l =
        ∑ j, ρ.mat h i j * (ρ.mat g * X * (σ.mat g)ᴴ) j l := fun g => Matrix.mul_apply
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ => (hint j l).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
  have hR : (avg μ ρ σ X * σ.mat h) i l = ∫ g, ((ρ.mat g * X * (σ.mat g)ᴴ) * σ.mat h) i l ∂μ := by
    rw [Matrix.mul_apply]
    simp only [avg, Matrix.of_apply]
    have hexp : ∀ g, ((ρ.mat g * X * (σ.mat g)ᴴ) * σ.mat h) i l =
        ∑ j, (ρ.mat g * X * (σ.mat g)ᴴ) i j * σ.mat h j l := fun g => Matrix.mul_apply
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ => (hint i j).mul_const _]
    exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
  rw [hL, hR]
  have hshift : ∀ g, (ρ.mat h * (ρ.mat g * X * (σ.mat g)ᴴ)) =
      ((ρ.mat (h * g) * X * (σ.mat (h * g))ᴴ) * σ.mat h) := by
    intro g
    rw [ρ.mat_mul, σ.mat_mul, Matrix.conjTranspose_mul]
    have e := σ.star_mat_mul_mat h
    calc ρ.mat h * (ρ.mat g * X * (σ.mat g)ᴴ)
        = ρ.mat h * ρ.mat g * X * ((σ.mat g)ᴴ * ((σ.mat h)ᴴ * σ.mat h)) := by
          rw [e, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = ρ.mat h * ρ.mat g * X * ((σ.mat g)ᴴ * (σ.mat h)ᴴ) * σ.mat h := by
          simp only [Matrix.mul_assoc]
  simp_rw [hshift]
  exact integral_mul_left_eq_self (fun g => ((ρ.mat g * X * (σ.mat g)ᴴ) * σ.mat h) i l) h

/-- The entry of `ρ(g) E_{jk} σ(g)ᴴ`. -/
lemma entry_single (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) (g : G) (i j : ι) (k l : κ) :
    (ρ.mat g * Matrix.single j k (1 : ℂ) * (σ.mat g)ᴴ) i l = ρ.mat g i j * starRingEnd ℂ (σ.mat g l k) := by
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, mul_ite, mul_one,
    mul_zero, Complex.star_def]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨rfl, rfl⟩] <;> rfl
    · intro b _ hb
      exact if_neg fun h => hb h.1.symm
    · simp
  · intro b _ hb
    rw [Finset.sum_eq_zero fun a _ => if_neg fun h => hb h.2.symm, zero_mul]
  · simp

variable [IsProbabilityMeasure μ]

/-- **Schur orthogonality, inequivalent case.** -/
theorem schur_orthogonality_ne {ρ : UnitaryMatrixRep G ι} {σ : UnitaryMatrixRep G κ}
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (hne : ¬ Equivalent ρ σ) (i j : ι) (k l : κ) :
    ∫ g, ρ.mat g i j * starRingEnd ℂ (σ.mat g l k) ∂μ = 0 := by
  have h := (schur_zero_or_equivalent hρ hσ (avg μ ρ σ (Matrix.single j k 1))
    fun g => avg_intertwines μ ρ σ _ g).resolve_right hne
  have := congrFun (congrFun h i) l
  simp only [avg, Matrix.of_apply, Matrix.zero_apply, entry_single] at this
  exact this

/-- **Schur orthogonality, equal case.** -/
theorem schur_orthogonality_eq {ρ : UnitaryMatrixRep G ι} (hρ : ρ.IsIrreducible) (i j k l : ι) :
    ∫ g, ρ.mat g i j * starRingEnd ℂ (ρ.mat g l k) ∂μ =
      if i = l ∧ j = k then 1 / (Fintype.card ι : ℂ) else 0 := by
  obtain ⟨c, hc⟩ := schur_scalar hρ (avg μ ρ ρ (Matrix.single j k 1)) fun g => avg_intertwines μ ρ ρ _ g
  have hint : ∀ a b, Integrable (fun g => (ρ.mat g * Matrix.single j k (1 : ℂ) * (ρ.mat g)ᴴ) a b) μ :=
    fun a b => (continuous_integrand ρ ρ _ a b).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- the trace of the average is the trace of `E_{jk}`
  have htr : Matrix.trace (avg μ ρ ρ (Matrix.single j k 1)) = if j = k then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, avg, Matrix.of_apply]
    rw [← integral_finsetSum _ fun a _ => hint a a]
    have : ∀ g, ∑ a, (ρ.mat g * Matrix.single j k (1 : ℂ) * (ρ.mat g)ᴴ) a a =
        if j = k then 1 else 0 := by
      intro g
      have h1 := Matrix.trace_mul_cycle (ρ.mat g) (Matrix.single j k (1 : ℂ)) (ρ.mat g)ᴴ
      rw [ρ.star_mat_mul_mat g, Matrix.one_mul] at h1
      simp only [Matrix.trace, Matrix.diag] at h1
      rw [h1]
      by_cases hjk : j = k
      · subst hjk
        rw [if_pos rfl, Finset.sum_eq_single j]
        · simp [Matrix.single_apply]
        · intro b _ hb
          rw [Matrix.single_apply, if_neg]
          rintro ⟨rfl, -⟩
          exact hb rfl
        · simp
      · rw [if_neg hjk]
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact hjk rfl
    simp_rw [this]
    simp
  have hc_tr : Matrix.trace (avg μ ρ ρ (Matrix.single j k 1)) = c * (Fintype.card ι : ℂ) := by
    rw [hc]; simp [Matrix.trace]; ring
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    haveI := hρ.1
    exact_mod_cast Fintype.card_ne_zero
  have hc' : c = (if j = k then 1 else 0) / (Fintype.card ι : ℂ) := by
    rw [eq_div_iff hn, ← htr, hc_tr]
  have := congrFun (congrFun hc i) l
  simp only [avg, Matrix.of_apply, entry_single] at this
  rw [this, hc']
  by_cases hil : i = l <;> by_cases hjk : j = k <;> simp [hil, hjk, Matrix.one_apply]

end UnitaryMatrixRep

end

end Lightlike.HarmonicAnalysis

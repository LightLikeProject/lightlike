import Lightlike.HarmonicAnalysis.PeterWeylHilbert
import Lightlike.HarmonicAnalysis.CharacterOrthogonality

/-!
# The characters form a Hilbert basis of the class functions

For a compact Hausdorff group `G` with a Haar probability measure `μ`:

* `conjTr μ s`: the conjugation `f ↦ f(s⁻¹ · s)` on `L²(G, μ)`; `classFunctions μ`: the closed subspace of the
  conjugation-invariant classes, `L²(G)^G`.
* `inner_coeff_classFunction`: for a class function `f` and an irreducible `ρ`,
  `⟪ρ_ij, f⟫ = δ_ij ⟪χ_ρ, f⟫ / dim ρ` (the Fourier coefficient of a class function is a scalar matrix, by
  Schur's lemma).
* `eq_zero_of_classFunction_of_orthogonal_characters`: a class function orthogonal to all irreducible
  characters is zero.
* `classFunctions_hilbertBasis`: the characters of the irreducible representations (one for each class) form
  a Hilbert basis of `classFunctions μ`.

The conjugation operators need right invariance of `μ`; for a Haar probability measure on a compact group
it holds (`isMulRightInvariant_of_isProbabilityMeasure`), so the final statements carry no such hypothesis.

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), §2 "Nonabelian Fourier analysis", the unnumbered passage after Remark 9: a function is a
  class function iff each Fourier coefficient is conjugation invariant, hence a scalar by Corollary 5, and
  "the `χ_ξ` form an orthonormal basis" of the space `L²(G)^G` of class functions.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

open UnitaryMatrixRep

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- **A Haar probability measure on a compact group is right invariant** (uniqueness of the Haar probability
measure, Mathlib's `isHaarMeasure_eq_of_isProbabilityMeasure`). -/
instance (priority := 50) isMulRightInvariant_of_isProbabilityMeasure [IsProbabilityMeasure μ] :
    μ.IsMulRightInvariant :=
  ⟨fun g => by
    have : IsProbabilityMeasure (Measure.map (· * g) μ) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_mul_const g).aemeasurable).2 inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.map (· * g) μ) μ⟩

section RightInvariant

variable [μ.IsMulRightInvariant]

/-- Conjugation by `s` preserves a left and right invariant measure. -/
lemma measurePreserving_conj (s : G) : MeasurePreserving (fun x : G => s⁻¹ * x * s) μ μ :=
  (measurePreserving_mul_right μ s).comp (measurePreserving_mul_left μ s⁻¹)

/-- The conjugation `ψ ↦ ψ(s⁻¹ · s)` on `L²`, an isometry. -/
def conjTr (s : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => s⁻¹ * x * s) (measurePreserving_conj μ s)

/-- Conjugation of a continuous function. -/
def conjC (s : G) (a : C(G, ℂ)) : C(G, ℂ) := a.comp ⟨fun x => s⁻¹ * x * s, by fun_prop⟩

lemma conjC_apply (s : G) (a : C(G, ℂ)) (x : G) : conjC s a x = a (s⁻¹ * x * s) := rfl

lemma conjTr_toLp (s : G) (a : C(G, ℂ)) :
    conjTr μ s (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a) = ContinuousMap.toLp (E := ℂ) 2 μ ℂ (conjC s a) := by
  refine Lp.ext ?_
  have h1 := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a)
    (measurePreserving_conj μ s)
  have h2 := (measurePreserving_conj μ s).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) a)
  filter_upwards [h1, h2, ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (conjC s a)]
    with x hx1 hx2 hx3
  rw [hx3]
  exact hx1.trans hx2

/-- The **class functions** in `L²(G, μ)`: the classes invariant under all conjugations. -/
def classFunctions : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | ∀ s, conjTr μ s f = f}
  add_mem' := fun ha hb s => by rw [map_add, ha s, hb s]
  zero_mem' := fun s => map_zero _
  smul_mem' := fun c f hf s => by rw [map_smul, hf s]

lemma mem_classFunctions {f : Lp ℂ 2 μ} : f ∈ classFunctions μ ↔ ∀ s, conjTr μ s f = f := Iff.rfl

lemma isClosed_classFunctions : IsClosed (classFunctions μ : Set (Lp ℂ 2 μ)) := by
  have h : (classFunctions μ : Set (Lp ℂ 2 μ)) = ⋂ s, {f | conjTr μ s f = f} := by
    ext f
    simp only [SetLike.mem_coe, mem_classFunctions, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact isClosed_iInter fun s => isClosed_eq (conjTr μ s).continuous continuous_id

instance : CompleteSpace (classFunctions μ) := (isClosed_classFunctions μ).completeSpace_coe

/-- The character `g ↦ tr ρ(g)` of an irreducible representation as a continuous function. -/
def charFun (ρ : IrrRep G) : C(G, ℂ) :=
  ⟨fun g => ρ.ρ.character g, by
    show Continuous fun g => ∑ i, ρ.ρ.mat g i i
    exact continuous_finsetSum _ fun i _ => ρ.ρ.continuous_mat_apply i i⟩

lemma charFun_eq_sum (ρ : IrrRep G) : charFun ρ = ∑ i, coeffFun ρ i i := by
  ext g
  simp only [ContinuousMap.coe_sum, Finset.sum_apply]
  rfl

/-- Conjugation of a matrix coefficient: `ρ(s⁻¹ g s)_{ij} = ∑ k l, ρ(s⁻¹)_{ik} ρ(s)_{lj} ρ(g)_{kl}`. -/
lemma conjC_coeffFun (ρ : IrrRep G) (s : G) (i j : ρ.ι) :
    conjC s (coeffFun ρ i j) = ∑ k, ∑ l, (ρ.ρ.mat s⁻¹ i k * ρ.ρ.mat s l j) • coeffFun ρ k l := by
  ext g
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  show ρ.ρ.mat (s⁻¹ * g * s) i j = ∑ k, ∑ l, ρ.ρ.mat s⁻¹ i k * ρ.ρ.mat s l j * ρ.ρ.mat g k l
  rw [ρ.ρ.mat_mul, ρ.ρ.mat_mul, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- The characters are class functions. -/
lemma toLp_charFun_mem (ρ : IrrRep G) :
    ContinuousMap.toLp (E := ℂ) 2 μ ℂ (charFun ρ) ∈ classFunctions μ := by
  intro s
  rw [conjTr_toLp]
  congr 1
  ext g
  show (ρ.ρ.mat (s⁻¹ * g * s)).trace = (ρ.ρ.mat g).trace
  rw [ρ.ρ.mat_mul, ρ.ρ.mat_mul, Matrix.trace_mul_cycle, ← ρ.ρ.mat_mul, mul_inv_cancel, ρ.ρ.mat_one,
    Matrix.one_mul]

/-- **The Fourier coefficient of a class function is a scalar matrix**: for a class function `f` and an
irreducible `ρ`, `⟪ρ_ij, f⟫ = δ_ij ⟪χ_ρ, f⟫ / dim ρ`. -/
theorem inner_coeff_classFunction (ρ : IrrRep G) {f : Lp ℂ 2 μ} (hf : f ∈ classFunctions μ)
    (i j : ρ.ι) :
    inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ i j)) f =
      if i = j then inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (charFun ρ)) f / (Fintype.card ρ.ι : ℂ)
      else 0 := by
  classical
  obtain ⟨C, hCe⟩ : ∃ C : Matrix ρ.ι ρ.ι ℂ,
      ∀ a b, C a b = inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ a b)) f :=
    ⟨Matrix.of fun a b => inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ a b)) f,
      fun _ _ => rfl⟩
  have hC : ∀ s, C = ρ.ρ.conj.mat s⁻¹ * C * ρ.ρ.conj.mat s := by
    intro s
    ext a b
    have h1 : inner ℂ (conjTr μ s (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ a b))) f =
        inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ a b)) f := by
      have h2 := (conjTr μ s).inner_map_map (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ a b)) f
      rw [hf s] at h2
      exact h2
    rw [conjTr_toLp, conjC_coeffFun] at h1
    simp only [map_sum, map_smul, sum_inner, inner_smul_left, map_mul] at h1
    rw [hCe, ← h1]
    simp only [Matrix.mul_apply, conj_mat, Matrix.map_apply, hCe, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  have hcomm : ∀ s, ρ.ρ.conj.mat s * C = C * ρ.ρ.conj.mat s := by
    intro s
    have h := hC s
    calc ρ.ρ.conj.mat s * C = ρ.ρ.conj.mat s * (ρ.ρ.conj.mat s⁻¹ * C * ρ.ρ.conj.mat s) := by rw [← h]
      _ = (ρ.ρ.conj.mat s * ρ.ρ.conj.mat s⁻¹) * C * ρ.ρ.conj.mat s := by simp only [Matrix.mul_assoc]
      _ = C * ρ.ρ.conj.mat s := by rw [← mat_mul, mul_inv_cancel, mat_one, Matrix.one_mul]
  obtain ⟨c, hc⟩ := schur_scalar ρ.irr.conj C hcomm
  have htr : inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (charFun ρ)) f = c * (Fintype.card ρ.ι : ℂ) := by
    rw [charFun_eq_sum, map_sum, sum_inner]
    simp_rw [← hCe, hc]
    simp [Matrix.smul_apply, mul_comm]
  have hn : (Fintype.card ρ.ι : ℂ) ≠ 0 := by
    have := ρ.irr.1
    exact_mod_cast Fintype.card_ne_zero
  have hij := congrFun (congrFun hc i) j
  rw [hCe] at hij
  rw [hij, htr]
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, hn]
  · simp [Matrix.smul_apply, h]

end RightInvariant

variable [IsProbabilityMeasure μ]

/-- The character of the representative of a class, as a class function in `L²`. -/
def charClass (π : IrrClass G) : classFunctions μ :=
  ⟨ContinuousMap.toLp (E := ℂ) 2 μ ℂ (charFun (Quotient.out π)), toLp_charFun_mem μ _⟩

/-- The irreducible characters are orthonormal in the space of class functions. -/
theorem orthonormal_charClass : Orthonormal ℂ (charClass μ) := by
  classical
  rw [orthonormal_iff_ite]
  intro π π'
  show inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (charFun (Quotient.out π)))
    (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (charFun (Quotient.out π'))) = _
  rw [inner_toLp_toLp]
  by_cases h : π = π'
  · subst h
    rw [if_pos rfl]
    exact character_orthogonality_eq μ (Quotient.out π : IrrRep G).irr
  · rw [if_neg h]
    have hne : ¬ Equivalent (Quotient.out π' : IrrRep G).ρ (Quotient.out π : IrrRep G).ρ := by
      intro he
      apply h
      have h2 : (⟦Quotient.out π'⟧ : IrrClass G) = ⟦Quotient.out π⟧ := Quotient.sound he
      rw [Quotient.out_eq, Quotient.out_eq] at h2
      exact h2.symm
    exact character_orthogonality_ne μ (Quotient.out π' : IrrRep G).irr (Quotient.out π : IrrRep G).irr hne

/-- **Completeness of the characters.** A class function orthogonal to all irreducible characters is zero. -/
theorem eq_zero_of_classFunction_of_orthogonal_characters {f : Lp ℂ 2 μ} (hf : f ∈ classFunctions μ)
    (h : ∀ π : IrrClass G,
      inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (charFun (Quotient.out π))) f = 0) : f = 0 := by
  refine eq_zero_of_orthogonal_coeffFamily μ fun a => ?_
  obtain ⟨π, i, j⟩ := a
  have h1 := inner_coeff_classFunction μ (Quotient.out π) hf i j
  rw [h π] at h1
  have h2 : inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun (Quotient.out π) i j)) f = 0 := by
    rw [h1]
    simp
  simp only [coeffFamily, inner_smul_right]
  rw [← inner_conj_symm, h2]
  simp

/-- **The irreducible characters form a Hilbert basis of the class functions** `L²(G)^G`. -/
theorem classFunctions_hilbertBasis :
    ∃ b : HilbertBasis (IrrClass G) ℂ (classFunctions μ), ∀ π, b π = charClass μ π := by
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range (charClass μ))).topologicalClosure := by
    rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff]
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    have h0 : (v : Lp ℂ 2 μ) = 0 := by
      refine eq_zero_of_classFunction_of_orthogonal_characters μ v.2 fun π => ?_
      exact (Submodule.mem_orthogonal _ _).1 hv _ (Submodule.subset_span ⟨π, rfl⟩)
    exact Subtype.ext h0
  exact ⟨HilbertBasis.mk (orthonormal_charClass μ) hsp, fun π => by simp⟩

end

end Lightlike.HarmonicAnalysis

import Lightlike.HarmonicAnalysis.ConvolutionEigen

/-!
# The unitary representation on a finite-dimensional left-invariant subspace

A finite-dimensional subspace `V ⊆ L²(G)` of classes of continuous functions that is invariant under all left
translations carries a continuous unitary matrix representation `ρ(s)_{ij} = ⟪b_i, L_s b_j⟫` for an orthonormal
basis `b`, and `s ↦ c_j(s⁻¹)` lies in the span of its matrix coefficients (`inv_mem_matrixCoeffSpan`).

Supporting lemmas for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

lemma continuous_trC (c : C(G, ℂ)) : Continuous fun s : G => trC s c :=
  (ContinuousMap.curry (⟨fun p : G × G => c (p.1⁻¹ * p.2), by fun_prop⟩ : C(G × G, ℂ))).continuous

lemma continuous_leftTr_toLp (c : C(G, ℂ)) :
    Continuous fun s : G => leftTr μ s (ContinuousMap.toLp (E := ℂ) 2 μ ℂ c) := by
  have : (fun s : G => leftTr μ s (ContinuousMap.toLp (E := ℂ) 2 μ ℂ c)) =
      fun s => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (trC s c) := funext fun s => leftTr_toLp μ s c
  rw [this]
  exact (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp (continuous_trC c)

lemma leftTr_mul (s t : G) (ψ : Lp ℂ 2 μ) :
    leftTr μ (s * t) ψ = leftTr μ s (leftTr μ t ψ) := by
  refine Lp.ext ?_
  have h1 : (leftTr μ (s * t) ψ : G → ℂ) =ᵐ[μ] fun x => ψ ((s * t)⁻¹ * x) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_mul_left μ (s * t)⁻¹)
  have h2 : (leftTr μ s (leftTr μ t ψ) : G → ℂ) =ᵐ[μ] fun x => (leftTr μ t ψ) (s⁻¹ * x) :=
    Lp.coeFn_compMeasurePreserving (leftTr μ t ψ) (measurePreserving_mul_left μ s⁻¹)
  have h3 : (leftTr μ t ψ : G → ℂ) =ᵐ[μ] fun x => ψ (t⁻¹ * x) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_mul_left μ t⁻¹)
  have h4 := (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving.ae_eq_comp h3
  filter_upwards [h1, h2, h4] with x hx1 hx2 hx4
  rw [hx1, hx2]
  have hx4' : (leftTr μ t ψ : G → ℂ) (s⁻¹ * x) = ψ (t⁻¹ * (s⁻¹ * x)) := hx4
  rw [hx4']
  simp [mul_assoc]

lemma leftTr_one (ψ : Lp ℂ 2 μ) : leftTr μ 1 ψ = ψ := by
  refine Lp.ext ?_
  have h1 : (leftTr μ 1 ψ : G → ℂ) =ᵐ[μ] fun x => ψ ((1 : G)⁻¹ * x) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_mul_left μ (1 : G)⁻¹)
  filter_upwards [h1] with x hx
  rw [hx]; simp

section Rep

variable (V : Submodule ℂ (Lp ℂ 2 μ)) (hinv : ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V)

/-- The restriction of a left translation to an invariant subspace. -/
def restrTr (s : G) : V →ₗᵢ[ℂ] V where
  toLinearMap := (leftTr μ s).toLinearMap.restrict (fun v hv => hinv s v hv)
  norm_map' := fun v => (leftTr μ s).norm_map (v : Lp ℂ 2 μ)

lemma restrTr_coe (s : G) (v : V) : ((restrTr μ V hinv s v : V) : Lp ℂ 2 μ) = leftTr μ s v := rfl

lemma restrTr_mul (s t : G) (v : V) :
    restrTr μ V hinv (s * t) v = restrTr μ V hinv s (restrTr μ V hinv t v) :=
  Subtype.ext (leftTr_mul μ s t v)

lemma restrTr_one (v : V) : restrTr μ V hinv 1 v = v := Subtype.ext (leftTr_one μ v)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ V)

/-- The matrix `ρ(s)_{ij} = ⟪b_i, L_s b_j⟫`. -/
def repMatrix (s : G) : Matrix ι ι ℂ :=
  Matrix.of fun i j => inner ℂ (b i) (restrTr μ V hinv s (b j))

lemma repMatrix_mem_unitaryGroup (s : G) : repMatrix μ V hinv b s ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have h : (star (repMatrix μ V hinv b s) * repMatrix μ V hinv b s) i j =
      inner ℂ (restrTr μ V hinv s (b i)) (restrTr μ V hinv s (b j)) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, repMatrix, Matrix.of_apply, RCLike.star_def]
    rw [← b.sum_inner_mul_inner (restrTr μ V hinv s (b i)) (restrTr μ V hinv s (b j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact inner_conj_symm (𝕜 := ℂ) (restrTr μ V hinv s (b i)) (b k)
  rw [h, LinearIsometry.inner_map_map, b.inner_eq_ite, Matrix.one_apply]

lemma repMatrix_one : repMatrix μ V hinv b 1 = 1 := by
  ext i j
  simp [repMatrix, restrTr_one, b.inner_eq_ite, Matrix.one_apply]

lemma repMatrix_mul (s t : G) :
    repMatrix μ V hinv b (s * t) = repMatrix μ V hinv b s * repMatrix μ V hinv b t := by
  ext i j
  simp only [repMatrix, Matrix.of_apply, Matrix.mul_apply, restrTr_mul]
  have hx := b.sum_repr' (restrTr μ V hinv t (b j))
  conv_lhs => rw [← hx]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (inner_smul_right (𝕜 := ℂ) (b i) (restrTr μ V hinv s (b k)) _).trans (mul_comm _ _)

/-- The unitary representation on an invariant subspace, in an orthonormal basis. -/
def invRep (hcont : ∀ v ∈ V, ∃ c : C(G, ℂ), v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c) :
    UnitaryMatrixRep G ι where
  toHom :=
    { toFun := fun s => ⟨repMatrix μ V hinv b s, repMatrix_mem_unitaryGroup μ V hinv b s⟩
      map_one' := Subtype.ext (repMatrix_one μ V hinv b)
      map_mul' := fun s t => Subtype.ext (repMatrix_mul μ V hinv b s t) }
  continuous_toHom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    obtain ⟨c, hc⟩ := hcont (b j) (b j).2
    show Continuous fun s : G => inner ℂ (b i : Lp ℂ 2 μ) (leftTr μ s (b j : Lp ℂ 2 μ))
    rw [hc]
    exact continuous_const.inner (continuous_leftTr_toLp μ c)

end Rep

section Coeff

variable (V : Submodule ℂ (Lp ℂ 2 μ)) (hinv : ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V)
  {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ V)

lemma isMatrixCoeff_repMatrix (hcont : ∀ v ∈ V, ∃ c : C(G, ℂ), v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c)
    (k j : ι) : IsMatrixCoeff G (fun g => repMatrix μ V hinv b g k j) :=
  ⟨ι, inferInstance, inferInstance, invRep μ V hinv b hcont, k, j, fun g => rfl⟩

lemma toLp_injective' {f g : C(G, ℂ)}
    (h : ContinuousMap.toLp (E := ℂ) 2 μ ℂ f = ContinuousMap.toLp (E := ℂ) 2 μ ℂ g) : f = g :=
  (ContinuousMap.toLp_inj (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ)).1 h

/-- **Expansion of the inverse-composed function.** `c(g⁻¹)` is a combination of the entries of `ρ(g)`. -/
theorem inv_eq_sum_entries
    (hinv : ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V) (b : OrthonormalBasis ι ℂ V)
    (hcont : ∀ v ∈ V, ∃ c : C(G, ℂ), v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c)
    (c : C(G, ℂ)) (hc : ContinuousMap.toLp (E := ℂ) 2 μ ℂ c ∈ V) :
    ∃ d : ι → ι → ℂ, ∀ g : G, c g⁻¹ = ∑ k, ∑ j, d k j * repMatrix μ V hinv b g k j := by
  choose cc hcc using fun j => hcont (b j) (b j).2
  let v : V := ⟨ContinuousMap.toLp (E := ℂ) 2 μ ℂ c, hc⟩
  let a : ι → ℂ := fun j => inner ℂ (b j) v
  have hv : v = ∑ j, a j • b j := (b.sum_repr' v).symm
  have hcoef : ∀ g : G, ∀ k : ι, inner ℂ (b k) (restrTr μ V hinv g v) =
      ∑ j, a j * repMatrix μ V hinv b g k j := by
    intro g k
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, inner_sum, repMatrix, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => inner_smul_right (𝕜 := ℂ) (b k) (restrTr μ V hinv g (b i)) (a i)
  have key : ∀ g : G, trC g c = ∑ k, (∑ j, a j * repMatrix μ V hinv b g k j) • cc k := by
    intro g
    refine toLp_injective' μ ?_
    rw [← leftTr_toLp, map_sum]
    simp only [map_smul]
    have h1 : (leftTr μ g (ContinuousMap.toLp (E := ℂ) 2 μ ℂ c) : Lp ℂ 2 μ) =
        ((restrTr μ V hinv g v : V) : Lp ℂ 2 μ) := rfl
    rw [h1, ← b.sum_repr' (restrTr μ V hinv g v)]
    simp only [Submodule.coe_sum, Submodule.coe_smul, hcoef]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcc k]
  refine ⟨fun k j => a j * cc k 1, fun g => ?_⟩
  have h1 : c g⁻¹ = trC g c 1 := by simp [trC_apply]
  rw [h1, key g]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The inverse-composed functions of `V` are in the span of the matrix coefficients.** -/
theorem inv_mem_matrixCoeffSpan
    (hinv : ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V) (b : OrthonormalBasis ι ℂ V)
    (hcont : ∀ v ∈ V, ∃ c : C(G, ℂ), v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c)
    (c : C(G, ℂ)) (hc : ContinuousMap.toLp (E := ℂ) 2 μ ℂ c ∈ V) :
    (⟨fun g => c g⁻¹, by fun_prop⟩ : C(G, ℂ)) ∈ matrixCoeffSpan G := by
  obtain ⟨d, hd⟩ := inv_eq_sum_entries μ V hinv b hcont c hc
  have hfun : (⟨fun g => c g⁻¹, by fun_prop⟩ : C(G, ℂ)) =
      ∑ k, ∑ j, d k j • (⟨fun g => repMatrix μ V hinv b g k j,
        (continuous_apply j).comp ((continuous_apply k).comp
          (invRep μ V hinv b hcont).continuous_toHom)⟩ : C(G, ℂ)) := by
    ext g
    rw [show (⟨fun g => c g⁻¹, _⟩ : C(G, ℂ)) g = c g⁻¹ from rfl, hd g]
    simp
    rfl
  rw [hfun]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (isMatrixCoeff_repMatrix μ V hinv b hcont k j)

open scoped Matrix in
/-- Inversion in the group turns an entry of `ρ(g⁻¹)` into the conjugate of an entry of `ρ(g)`. -/
lemma repMatrix_inv (hinv : ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V) (b : OrthonormalBasis ι ℂ V)
    (x : G) (k j : ι) :
    repMatrix μ V hinv b x⁻¹ k j = starRingEnd ℂ (repMatrix μ V hinv b x j k) := by
  have h1 : repMatrix μ V hinv b x⁻¹ * repMatrix μ V hinv b x = 1 := by
    rw [← repMatrix_mul, inv_mul_cancel, repMatrix_one]
  have h2 : (repMatrix μ V hinv b x)ᴴ * repMatrix μ V hinv b x = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 (repMatrix_mem_unitaryGroup μ V hinv b x)
    simpa [Matrix.star_eq_conjTranspose] using this
  have h3 : repMatrix μ V hinv b x * (repMatrix μ V hinv b x)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 (repMatrix_mem_unitaryGroup μ V hinv b x)
    simpa [Matrix.star_eq_conjTranspose] using this
  have h4 : repMatrix μ V hinv b x⁻¹ = (repMatrix μ V hinv b x)ᴴ := by
    calc repMatrix μ V hinv b x⁻¹ = repMatrix μ V hinv b x⁻¹ * (repMatrix μ V hinv b x * (repMatrix μ V hinv b x)ᴴ) := by
          rw [h3, Matrix.mul_one]
      _ = (repMatrix μ V hinv b x⁻¹ * repMatrix μ V hinv b x) * (repMatrix μ V hinv b x)ᴴ := by
          rw [Matrix.mul_assoc]
      _ = (repMatrix μ V hinv b x)ᴴ := by rw [h1, Matrix.one_mul]
  rw [h4]; simp [Matrix.conjTranspose_apply]

/-- Every continuous function in `V` is a combination of the entries of the conjugate representation. -/
theorem eq_sum_conj_entries
    (hinv : ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V) (b : OrthonormalBasis ι ℂ V)
    (hcont : ∀ v ∈ V, ∃ c : C(G, ℂ), v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c)
    (c : C(G, ℂ)) (hc : ContinuousMap.toLp (E := ℂ) 2 μ ℂ c ∈ V) :
    ∃ d : ι → ι → ℂ, ∀ x, c x = ∑ k, ∑ j, d k j * starRingEnd ℂ (repMatrix μ V hinv b x j k) := by
  obtain ⟨d, hd⟩ := inv_eq_sum_entries μ V hinv b hcont c hc
  refine ⟨d, fun x => ?_⟩
  have := hd x⁻¹
  rw [inv_inv] at this
  rw [this]
  simp only [repMatrix_inv μ V hinv b x]

end Coeff

end

end Lightlike.HarmonicAnalysis

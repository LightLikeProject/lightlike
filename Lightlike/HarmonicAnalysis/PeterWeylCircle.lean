import Lightlike.HarmonicAnalysis.PeterWeylChecks

/-!
# Check of the Peter–Weyl theorem on the circle group `U(1)`

* `UnitaryMatrixRep.ofCircleHom`: the one-dimensional unitary representation of a continuous homomorphism
  `G →* Circle`; `isIrreducible_of_unique`: one-dimensional representations are irreducible.
* `circleChar n`: the character `z ↦ zⁿ` of the circle, `n : ℤ`; these are pairwise inequivalent
  (`circleChar_not_equivalent`).
* `circle_hilbertBasis`: the characters `z ↦ zⁿ` form a Hilbert basis of `L²(U(1), μ)` for the Haar probability
  measure `μ`. Orthonormality is Schur orthogonality (`schur_orthogonality_eq`, `schur_orthogonality_ne`);
  completeness is the Stone–Weierstrass theorem. Compare Mathlib's `fourierBasis` on `AddCircle T`.
* `circle_irreducible_classification`: every irreducible continuous unitary matrix representation of the
  circle is one-dimensional and equal to `z ↦ zⁿ` for some `n : ℤ`. So the Hilbert basis of
  `peterWeyl_hilbertBasis` for `G = U(1)` is the Fourier basis.

Checks of the milestone; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

namespace UnitaryMatrixRep

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The one-dimensional unitary representation of a continuous homomorphism into the circle group. -/
def ofCircleHom (f : G →* Circle) (hf : Continuous f) : UnitaryMatrixRep G Unit where
  toHom :=
    { toFun := fun g => ⟨Matrix.of fun _ _ => ((f g : Circle) : ℂ), by
        rw [Matrix.mem_unitaryGroup_iff]
        ext i j
        simp [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Complex.mul_conj]⟩
      map_one' := Subtype.ext (by ext i j; simp [Matrix.one_apply])
      map_mul' := fun g h => Subtype.ext (by ext i j; simp [Matrix.mul_apply]) }
  continuous_toHom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun g => ((f g : Circle) : ℂ)
    exact continuous_subtype_val.comp hf

lemma ofCircleHom_mat (f : G →* Circle) (hf : Continuous f) (g : G) (i j : Unit) :
    (ofCircleHom f hf).mat g i j = ((f g : Circle) : ℂ) := rfl

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A one-dimensional representation is irreducible. -/
lemma isIrreducible_of_unique [Unique ι] (ρ : UnitaryMatrixRep G ι) : ρ.IsIrreducible := by
  refine ⟨inferInstance, fun W _ => ?_⟩
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 h
    have hd : w default ≠ 0 := fun h0 => hw0 (funext fun i => by
      rw [Unique.eq_default i]; exact h0)
    refine (Submodule.eq_top_iff').2 fun v => ?_
    have hv : v = (v default / w default) • w := by
      funext i
      rw [Unique.eq_default i]
      simp [div_mul_cancel₀ _ hd]
    rw [hv]
    exact W.smul_mem _ hw

/-- Equivalent one-dimensional representations have the same coefficient. -/
lemma entry_eq_of_equivalent_of_unique [Unique ι] [Unique κ] {ρ : UnitaryMatrixRep G ι}
    {σ : UnitaryMatrixRep G κ} (h : Equivalent ρ σ) (g : G) :
    ρ.mat g default default = σ.mat g default default := by
  obtain ⟨e, he⟩ := h
  have hσ : ∀ w : κ → ℂ, (σ.mat g).mulVec w = σ.mat g default default • w := by
    intro w
    funext i
    rw [Unique.eq_default i]
    simp [Matrix.mulVec, dotProduct]
  have hρ : ∀ w : ι → ℂ, (ρ.mat g).mulVec w = ρ.mat g default default • w := by
    intro w
    funext i
    rw [Unique.eq_default i]
    simp [Matrix.mulVec, dotProduct]
  have h1 := he g (fun _ => 1)
  rw [hσ, hρ, map_smul] at h1
  have hw : e (fun _ => (1 : ℂ)) ≠ 0 := by
    intro h0
    have h2 : (fun _ : κ => (1 : ℂ)) = 0 := e.injective (by rw [h0, map_zero])
    have h3 := congrFun h2 default
    simp at h3
  have h2 : (σ.mat g default default - ρ.mat g default default) • e (fun _ => (1 : ℂ)) = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact (sub_eq_zero.1 h3).symm
  · exact absurd h3 hw

end UnitaryMatrixRep

open UnitaryMatrixRep

/-- The character `z ↦ zⁿ` of the circle group, as a one-dimensional unitary representation. -/
def circleChar (n : ℤ) : UnitaryMatrixRep Circle Unit :=
  ofCircleHom (zpowGroupHom n) (continuous_zpow n)

lemma circleChar_mat (n : ℤ) (z : Circle) (i j : Unit) :
    (circleChar n).mat z i j = ((z ^ n : Circle) : ℂ) := rfl

/-- The characters `z ↦ zⁿ` are pairwise inequivalent. -/
lemma circleChar_not_equivalent {n m : ℤ} (h : n ≠ m) : ¬ Equivalent (circleChar n) (circleChar m) := by
  intro he
  have hk : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 h
  have h1 := entry_eq_of_equivalent_of_unique he (Circle.exp (Real.pi / ((n - m : ℤ) : ℝ)))
  have h2 : Circle.exp (Real.pi / ((n - m : ℤ) : ℝ)) ^ n = Circle.exp (Real.pi / ((n - m : ℤ) : ℝ)) ^ m :=
    Circle.coe_injective h1
  have h3 : Circle.exp (Real.pi / ((n - m : ℤ) : ℝ)) ^ (n - m) = 1 := by
    rw [zpow_sub, h2, mul_inv_cancel]
  have h4 : ((n - m : ℤ) : ℝ) * (Real.pi / ((n - m : ℤ) : ℝ)) = Real.pi := by field_simp
  rw [← Circle.exp_intCast_mul, h4] at h3
  exact Circle.exp_pi_ne_one h3

/-- The monomial `z ↦ zⁿ` as a continuous function on the circle. -/
def circleMono (n : ℤ) : C(Circle, ℂ) :=
  ⟨fun z => ((z ^ n : Circle) : ℂ), continuous_subtype_val.comp (continuous_zpow n)⟩

lemma circleMono_mul (n m : ℤ) : circleMono n * circleMono m = circleMono (n + m) := by
  ext z
  show ((z ^ n : Circle) : ℂ) * ((z ^ m : Circle) : ℂ) = ((z ^ (n + m) : Circle) : ℂ)
  rw [zpow_add, Circle.coe_mul]

lemma circleMono_zero : circleMono 0 = 1 := by
  ext z
  show ((z ^ (0 : ℤ) : Circle) : ℂ) = 1
  rw [zpow_zero, Circle.coe_one]

lemma star_circleMono (n : ℤ) : star (circleMono n) = circleMono (-n) := by
  ext z
  show star ((z ^ n : Circle) : ℂ) = ((z ^ (-n) : Circle) : ℂ)
  rw [zpow_neg, Circle.coe_inv_eq_conj]
  rfl

/-- The span of the monomials `z ↦ zⁿ`, `n : ℤ`. -/
def circleMonoSpan : Submodule ℂ C(Circle, ℂ) := Submodule.span ℂ (Set.range circleMono)

/-- The trigonometric polynomials on the circle, as a star subalgebra of `C(U(1), ℂ)`. -/
def circleMonoAlgebra : StarSubalgebra ℂ C(Circle, ℂ) where
  carrier := circleMonoSpan
  mul_mem' := by
    intro a b ha hb
    have h1 : a * b ∈ circleMonoSpan * circleMonoSpan := Submodule.mul_mem_mul ha hb
    rw [circleMonoSpan, Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨n, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact ⟨n + m, (circleMono_mul n m).symm⟩
  one_mem' := Submodule.subset_span ⟨0, circleMono_zero⟩
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun c => by
    have : algebraMap ℂ C(Circle, ℂ) c = c • (1 : C(Circle, ℂ)) := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, circleMono_zero⟩)
  star_mem' := by
    intro a ha
    refine Submodule.span_induction (p := fun x _ => star x ∈ circleMonoSpan) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨n, rfl⟩
      exact Submodule.subset_span ⟨-n, (star_circleMono n).symm⟩
    · simpa using Submodule.zero_mem _
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem _ hx hy
    · intro c x _ hx
      simpa using Submodule.smul_mem _ (starRingEnd ℂ c) hx

/-- The trigonometric polynomials are dense in `C(U(1), ℂ)` (Stone–Weierstrass). -/
theorem circleMonoSpan_topologicalClosure : circleMonoSpan.topologicalClosure = ⊤ := by
  have hS : circleMonoAlgebra.SeparatesPoints := by
    intro z w hzw
    refine ⟨_, ⟨circleMono 1, Submodule.subset_span ⟨1, rfl⟩, rfl⟩, ?_⟩
    show ((z ^ (1 : ℤ) : Circle) : ℂ) ≠ ((w ^ (1 : ℤ) : Circle) : ℂ)
    rw [zpow_one, zpow_one]
    exact fun h => hzw (Circle.ext h)
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hS
  refine (Submodule.eq_top_iff').2 fun f => ?_
  have hf : f ∈ circleMonoAlgebra.topologicalClosure := by rw [h]; exact StarSubalgebra.mem_top
  exact hf

variable (μ : Measure Circle) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- The class of `z ↦ zⁿ` in `L²(U(1), μ)`. -/
def circleMonoLp (n : ℤ) : Lp ℂ 2 μ := ContinuousMap.toLp (E := ℂ) 2 μ ℂ (circleMono n)

/-- **Check: the characters of `U(1)` are orthonormal**, by Schur orthogonality. -/
theorem orthonormal_circleMonoLp : Orthonormal ℂ (circleMonoLp μ) := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [circleMonoLp]
  rw [inner_toLp_toLp]
  by_cases h : n = m
  · subst h
    rw [if_pos rfl]
    have h1 := schur_orthogonality_eq μ (isIrreducible_of_unique (circleChar n)) () () () ()
    rw [if_pos ⟨rfl, rfl⟩] at h1
    exact h1.trans (by simp)
  · rw [if_neg h]
    exact schur_orthogonality_ne μ (isIrreducible_of_unique (circleChar m))
      (isIrreducible_of_unique (circleChar n)) (circleChar_not_equivalent (Ne.symm h)) () () () ()

/-- The characters of `U(1)` span a dense subspace of `L²(U(1), μ)`. -/
theorem span_circleMonoLp_topologicalClosure :
    (Submodule.span ℂ (Set.range (circleMonoLp μ))).topologicalClosure = ⊤ := by
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 μ ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ) (p := 2) (μ := μ) (by norm_num)
  have h := hd.topologicalClosure_map_submodule circleMonoSpan_topologicalClosure
  rw [circleMonoSpan, Submodule.map_span, ← Set.range_comp] at h
  exact h

/-- **Check: for `U(1)` the characters `z ↦ zⁿ` (that is `e^{inθ}`) form an orthonormal basis of `L²`.** -/
theorem circle_hilbertBasis : ∃ b : HilbertBasis ℤ ℂ (Lp ℂ 2 μ), ∀ n, b n = circleMonoLp μ n :=
  ⟨HilbertBasis.mk (orthonormal_circleMonoLp μ) (span_circleMonoLp_topologicalClosure μ).ge,
    fun n => by simp⟩

include μ in
/-- An irreducible unitary representation of the circle is a character `z ↦ zⁿ` (with a Haar probability
measure as a parameter). -/
lemma circle_irreducible_classification_aux {κ : Type} [Fintype κ] [DecidableEq κ]
    {σ : UnitaryMatrixRep Circle κ} (hσ : σ.IsIrreducible) :
    Fintype.card κ = 1 ∧ ∃ n : ℤ, ∀ z k l, σ.mat z k l = ((z ^ n : Circle) : ℂ) := by
  have hcard := card_eq_one_of_commutative hσ mul_comm
  refine ⟨hcard, ?_⟩
  obtain ⟨k0, hk0⟩ := Fintype.card_eq_one_iff.1 hcard
  haveI : Unique κ := ⟨⟨k0⟩, hk0⟩
  by_contra hno
  push_neg at hno
  have hne : ∀ n, ¬ Equivalent (circleChar n) σ := by
    intro n he
    obtain ⟨z, k, l, hz⟩ := hno n
    apply hz
    rw [Unique.eq_default k, Unique.eq_default l]
    exact (entry_eq_of_equivalent_of_unique he z).symm
  obtain ⟨f, hf⟩ : ∃ f : C(Circle, ℂ), ∀ z, f z = σ.mat z default default :=
    ⟨⟨_, σ.continuous_mat_apply default default⟩, fun _ => rfl⟩
  have horth : ∀ n, inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f) (circleMonoLp μ n) = 0 := by
    intro n
    simp only [circleMonoLp]
    rw [inner_toLp_toLp]
    simp_rw [hf]
    exact schur_orthogonality_ne μ (isIrreducible_of_unique (circleChar n)) hσ (hne n) () () default default
  have hK : Submodule.span ℂ (Set.range (circleMonoLp μ)) ≤
      LinearMap.ker (innerSL ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f)).toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    exact LinearMap.mem_ker.2 (by simpa using horth n)
  have hv : ContinuousMap.toLp (E := ℂ) 2 μ ℂ f ∈ (Submodule.span ℂ (Set.range (circleMonoLp μ)))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    simpa using hK hu
  rw [(Submodule.topologicalClosure_eq_top_iff).1 (span_circleMonoLp_topologicalClosure μ)] at hv
  have hv0 : ContinuousMap.toLp (E := ℂ) 2 μ ℂ f = 0 := (Submodule.mem_bot ℂ).1 hv
  have hnorm : inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f) (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f) = 1 := by
    rw [inner_toLp_toLp]
    simp_rw [hf]
    have h1 := schur_orthogonality_eq μ hσ default default default default
    rw [if_pos ⟨rfl, rfl⟩, hcard] at h1
    exact h1.trans (by simp)
  rw [hv0] at hnorm
  simp at hnorm

/-- **Check: the irreducible unitary representations of `U(1)` are the characters `z ↦ zⁿ`.** Every
irreducible continuous unitary matrix representation of the circle group is one-dimensional and equal to
`z ↦ zⁿ` for some `n : ℤ`. -/
theorem circle_irreducible_classification {κ : Type} [Fintype κ] [DecidableEq κ]
    {σ : UnitaryMatrixRep Circle κ} (hσ : σ.IsIrreducible) :
    Fintype.card κ = 1 ∧ ∃ n : ℤ, ∀ z k l, σ.mat z k l = ((z ^ n : Circle) : ℂ) := by
  haveI : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Circle)) :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle))⟩
  exact circle_irreducible_classification_aux (Measure.haarMeasure ⊤) hσ

end

end Lightlike.HarmonicAnalysis

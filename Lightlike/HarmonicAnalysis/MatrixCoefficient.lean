import Mathlib

/-!
# Matrix coefficients of finite-dimensional unitary representations

For a topological group `G`, a *unitary matrix representation* is a continuous homomorphism into the
unitary group `U(ι)` of a finite index type `ι`, and a *matrix coefficient* is one of its entries
`g ↦ ρ(g)_{ij}`. The span `matrixCoeffSpan G` of the matrix coefficients of all such representations, as a
submodule of `C(G, ℂ)`, is a star subalgebra: the product of two coefficients is a coefficient of the tensor
(Kronecker) product, the conjugate one of the conjugate representation, and the constant `1` that of the
trivial representation (`matrixCoeffAlgebra`).

Peter–Weyl theorem (Bröcker–tom Dieck, *Representations of compact Lie groups*, Chapter III): for a compact
Hausdorff group this span is dense in `C(G, ℂ)` (`T-HA5`).

## References

* T. Bröcker and T. tom Dieck, *Representations of compact Lie groups*, Springer (1985), Chapter III.
-/

open Matrix

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- A **continuous unitary matrix representation** of `G` of finite dimension, indexed by a finite type `ι`. -/
structure UnitaryMatrixRep (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- The homomorphism into the unitary group. -/
  toHom : G →* Matrix.unitaryGroup ι ℂ
  /-- Continuity of the matrix entries. -/
  continuous_toHom : Continuous fun g => ((toHom g : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)

/-- A function `f : G → ℂ` is a **matrix coefficient** if it is an entry `g ↦ ρ(g)_{ij}` of a continuous
finite-dimensional unitary matrix representation `ρ`. -/
def IsMatrixCoeff (f : G → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (ρ : UnitaryMatrixRep G ι) (i j : ι),
    ∀ g, f g = (ρ.toHom g : Matrix ι ι ℂ) i j

/-- The span of the matrix coefficients inside the continuous functions `C(G, ℂ)`. -/
def matrixCoeffSpan : Submodule ℂ C(G, ℂ) :=
  Submodule.span ℂ {f : C(G, ℂ) | IsMatrixCoeff G (f : G → ℂ)}

variable {G}

/-- The trivial representation has the constant function `1` as coefficient. -/
lemma isMatrixCoeff_one : IsMatrixCoeff G (fun _ => (1 : ℂ)) :=
  ⟨Unit, inferInstance, inferInstance, ⟨1, by simpa using continuous_const⟩, (), (), fun g => by simp⟩

namespace UnitaryMatrixRep

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The complex conjugate of a representation. -/
def conj (ρ : UnitaryMatrixRep G ι) : UnitaryMatrixRep G ι where
  toHom :=
    { toFun := fun g => ⟨((ρ.toHom g : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ).map (starRingEnd ℂ), by
        rw [Matrix.mem_unitaryGroup_iff]
        have hA := Matrix.mem_unitaryGroup_iff.1 (ρ.toHom g).2
        have hstar : star (((ρ.toHom g : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ).map (starRingEnd ℂ)) =
            (star ((ρ.toHom g : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)).map (starRingEnd ℂ) := by
          ext i j
          simp [Matrix.star_apply]
        rw [hstar, ← Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp [Matrix.map_mul]) }
  continuous_toHom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Complex.continuous_conj.comp
      ((continuous_apply j).comp ((continuous_apply i).comp ρ.continuous_toHom))

open Kronecker in
/-- The tensor product of two representations. -/
def tensor (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) : UnitaryMatrixRep G (ι × κ) where
  toHom :=
    { toFun := fun g => ⟨((ρ.toHom g : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ⊗ₖ
          ((σ.toHom g : Matrix.unitaryGroup κ ℂ) : Matrix κ κ ℂ), by
        rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
          ← Matrix.mul_kronecker_mul]
        have h1 := Matrix.mem_unitaryGroup_iff.1 (ρ.toHom g).2
        have h2 := Matrix.mem_unitaryGroup_iff.1 (σ.toHom g).2
        rw [Matrix.star_eq_conjTranspose] at h1 h2
        rw [h1, h2, Matrix.one_kronecker_one]⟩
      map_one' := Subtype.ext (by simp [Matrix.one_kronecker_one])
      map_mul' := fun g h => Subtype.ext (by
        simp [← Matrix.mul_kronecker_mul]) }
  continuous_toHom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun g => (((ρ.toHom g : Matrix ι ι ℂ) ⊗ₖ (σ.toHom g : Matrix κ κ ℂ)) i j)
    simp only [Matrix.kroneckerMap_apply]
    exact ((continuous_apply j.1).comp ((continuous_apply i.1).comp ρ.continuous_toHom)).mul
      ((continuous_apply j.2).comp ((continuous_apply i.2).comp σ.continuous_toHom))

end UnitaryMatrixRep

/-- The conjugate of a coefficient is a coefficient (of the conjugate representation). -/
lemma IsMatrixCoeff.conj {f : G → ℂ} (hf : IsMatrixCoeff G f) :
    IsMatrixCoeff G (fun g => starRingEnd ℂ (f g)) := by
  obtain ⟨ι, _, _, ρ, i, j, hf⟩ := hf
  exact ⟨ι, inferInstance, inferInstance, ρ.conj, i, j, fun g => by simp [UnitaryMatrixRep.conj, hf g]⟩

/-- The product of two coefficients is a coefficient (of the tensor product). -/
lemma IsMatrixCoeff.mul {f h : G → ℂ} (hf : IsMatrixCoeff G f) (hh : IsMatrixCoeff G h) :
    IsMatrixCoeff G (fun g => f g * h g) := by
  obtain ⟨ι, _, _, ρ, i, j, hf⟩ := hf
  obtain ⟨κ, _, _, σ, k, l, hh⟩ := hh
  exact ⟨ι × κ, inferInstance, inferInstance, ρ.tensor σ, (i, k), (j, l), fun g => by
    simp [UnitaryMatrixRep.tensor, hf g, hh g]⟩

/-- **The span of the matrix coefficients is a star subalgebra of `C(G, ℂ)`.** -/
def matrixCoeffAlgebra (G : Type*) [Group G] [TopologicalSpace G] : StarSubalgebra ℂ C(G, ℂ) where
  carrier := matrixCoeffSpan G
  mul_mem' := by
    intro a b ha hb
    have h1 : a * b ∈ matrixCoeffSpan G * matrixCoeffSpan G := Submodule.mul_mem_mul ha hb
    rw [matrixCoeffSpan, Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact IsMatrixCoeff.mul hx hy
  one_mem' := Submodule.subset_span isMatrixCoeff_one
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun c => by
    have : algebraMap ℂ C(G, ℂ) c = c • (1 : C(G, ℂ)) := by simp [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span isMatrixCoeff_one)
  star_mem' := by
    intro a ha
    refine Submodule.span_induction (p := fun x _ => star x ∈ matrixCoeffSpan G) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact Submodule.subset_span (IsMatrixCoeff.conj hx)
    · simpa using Submodule.zero_mem _
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem _ hx hy
    · intro c x _ hx
      simpa using Submodule.smul_mem _ (starRingEnd ℂ c) hx

/-- **Peter–Weyl, from the separation of points**: if the matrix coefficients separate the points of a
compact group, they are dense in `C(G, ℂ)` (Stone–Weierstrass). -/
theorem dense_matrixCoeffSpan_of_separates [CompactSpace G]
    (hsep : ∀ g h : G, g ≠ h → ∃ f ∈ matrixCoeffSpan G, f g ≠ f h) :
    Dense (matrixCoeffSpan G : Set C(G, ℂ)) := by
  have hS : (matrixCoeffAlgebra G).SeparatesPoints := by
    intro g h hgh
    obtain ⟨f, hf, hfg⟩ := hsep g h hgh
    exact ⟨f, ⟨f, hf, rfl⟩, hfg⟩
  have := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hS
  rw [dense_iff_closure_eq]
  have h2 : closure ((matrixCoeffAlgebra G : StarSubalgebra ℂ C(G, ℂ)) : Set C(G, ℂ)) = Set.univ := by
    have := congrArg (fun A : StarSubalgebra ℂ C(G, ℂ) => (A : Set C(G, ℂ))) this
    simpa [StarSubalgebra.topologicalClosure_coe] using this
  exact h2

end

end Lightlike.HarmonicAnalysis

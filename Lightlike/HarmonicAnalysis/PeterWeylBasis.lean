import Lightlike.HarmonicAnalysis.IrrClasses

/-!
# The orthonormal family of normalised irreducible matrix coefficients

Let `Ĝ` be the set of equivalence classes of irreducible continuous finite-dimensional unitary matrix
representations of `G`, with a chosen representative `π.out` of each class. For a Haar probability measure `μ`
the functions `√(dim π) · π.out_{ij}` form an orthonormal family in `L²(G, μ)` indexed by
`Σ π, (index of π.out) × (index of π.out)` (`orthonormal_coeffFamily`); completeness is in `PeterWeyl`-basis form.

Supporting definitions for the Peter–Weyl theorem.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

open UnitaryMatrixRep

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An irreducible continuous finite-dimensional unitary matrix representation, on some finite index type. -/
structure IrrRep where
  /-- The index type. -/
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  /-- The representation. -/
  ρ : UnitaryMatrixRep G ι
  /-- Irreducibility. -/
  irr : ρ.IsIrreducible

attribute [instance] IrrRep.fin IrrRep.dec

/-- Equivalence of irreducible representations, as a setoid. -/
def irrSetoid : Setoid (IrrRep G) where
  r a b := UnitaryMatrixRep.Equivalent a.ρ b.ρ
  iseqv := ⟨fun a => UnitaryMatrixRep.Equivalent.refl a.ρ, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The set of equivalence classes of irreducible representations. -/
abbrev IrrClass := Quotient (irrSetoid G)

variable {G}

/-- The index of the orthonormal family: a class and a pair of indices of its representative. -/
abbrev CoeffIdx (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  Σ π : IrrClass G, (Quotient.out π : IrrRep G).ι × (Quotient.out π : IrrRep G).ι

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The coefficient `g ↦ ρ(g)_{ij}` as a continuous function. -/
def coeffFun (ρ : IrrRep G) (i j : ρ.ι) : C(G, ℂ) := ⟨fun g => ρ.ρ.mat g i j, ρ.ρ.continuous_mat_apply i j⟩

/-- The normalised coefficient `√(dim ρ) · ρ_{ij}` as an element of `L²`. -/
def coeffFamily (a : CoeffIdx G) : Lp ℂ 2 μ :=
  ((Real.sqrt (Fintype.card (Quotient.out a.1 : IrrRep G).ι) : ℝ) : ℂ) •
    ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun (Quotient.out a.1) a.2.1 a.2.2)

lemma inner_toLp_toLp (f g : C(G, ℂ)) :
    inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f) (ContinuousMap.toLp (E := ℂ) 2 μ ℂ g) =
      ∫ x, g x * starRingEnd ℂ (f x) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) f,
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) g] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

variable [IsProbabilityMeasure μ]

/-- **Orthonormality** of the normalised irreducible coefficients (Schur orthogonality). -/
theorem orthonormal_coeffFamily : Orthonormal ℂ (coeffFamily μ) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨π, i, j⟩ ⟨π', l, k⟩
  simp only [coeffFamily]
  rw [inner_smul_left, inner_smul_right, inner_toLp_toLp]
  by_cases hπ : π = π'
  · subst hπ
    have hn : (Fintype.card (Quotient.out π : IrrRep G).ι : ℝ) ≠ 0 := by
      haveI := (Quotient.out π : IrrRep G).irr.1
      exact_mod_cast Fintype.card_ne_zero
    have hs := schur_orthogonality_eq μ (Quotient.out π : IrrRep G).irr l k j i
    have h1 : ∫ x, coeffFun (Quotient.out π : IrrRep G) l k x *
        starRingEnd ℂ (coeffFun (Quotient.out π : IrrRep G) i j x) ∂μ =
        if l = i ∧ k = j then 1 / (Fintype.card (Quotient.out π : IrrRep G).ι : ℂ) else 0 := hs
    rw [h1]
    by_cases hij : i = l ∧ j = k
    · obtain ⟨rfl, rfl⟩ := hij
      rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
      have hsq : ((Real.sqrt (Fintype.card (Quotient.out π : IrrRep G).ι) : ℝ) : ℂ) *
          ((Real.sqrt (Fintype.card (Quotient.out π : IrrRep G).ι) : ℝ) : ℂ) =
          (Fintype.card (Quotient.out π : IrrRep G).ι : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        simp
      have hn' : (Fintype.card (Quotient.out π : IrrRep G).ι : ℂ) ≠ 0 := by exact_mod_cast hn
      simp only [Complex.conj_ofReal]
      rw [← mul_assoc, hsq, mul_one_div, div_self hn']
    · have hij' : ¬ (l = i ∧ k = j) := fun h => hij ⟨h.1.symm, h.2.symm⟩
      have hne : ¬ ((⟨π, (i, j)⟩ : CoeffIdx G) = ⟨π, (l, k)⟩) := by
        intro h
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at h
        exact hij h
      rw [if_neg hij', if_neg hne]
      simp
  · have hne : ¬ ((⟨π, (i, j)⟩ : CoeffIdx G) = ⟨π', (l, k)⟩) := fun h => hπ (by
      simpa using congrArg Sigma.fst h)
    rw [if_neg hne]
    have hnequiv : ¬ UnitaryMatrixRep.Equivalent (Quotient.out π : IrrRep G).ρ (Quotient.out π' : IrrRep G).ρ := by
      intro h
      apply hπ
      have : (⟦Quotient.out π⟧ : IrrClass G) = ⟦Quotient.out π'⟧ := Quotient.sound h
      rw [Quotient.out_eq, Quotient.out_eq] at this
      exact this
    have h0 := schur_orthogonality_ne μ (Quotient.out π : IrrRep G).irr (Quotient.out π' : IrrRep G).irr hnequiv i j k l
    have h1 : ∫ x, coeffFun (Quotient.out π' : IrrRep G) l k x *
        starRingEnd ℂ (coeffFun (Quotient.out π : IrrRep G) i j x) ∂μ = 0 := by
      have : ∀ x, coeffFun (Quotient.out π' : IrrRep G) l k x *
          starRingEnd ℂ (coeffFun (Quotient.out π : IrrRep G) i j x) =
          starRingEnd ℂ ((Quotient.out π : IrrRep G).ρ.mat x i j *
            starRingEnd ℂ ((Quotient.out π' : IrrRep G).ρ.mat x l k)) := by
        intro x; simp [coeffFun, mul_comm]
      simp_rw [this]
      rw [integral_conj, h0]; simp
    rw [h1]; simp

end

end Lightlike.HarmonicAnalysis

import Lightlike.HarmonicAnalysis.InvariantRep
import Lightlike.HarmonicAnalysis.SchurOrthogonality

/-!
# Decomposition of left-invariant subspaces into irreducible ones

A finite-dimensional left-invariant subspace `V` of `L²(G)` of classes of continuous functions is a finite
orthogonal sum of minimal invariant subspaces (`exists_minimal_decomposition`), and the unitary matrix
representation of a minimal invariant subspace is irreducible (`invRep_isIrreducible`).

Supporting lemmas for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A subspace of `L²(G)` is left invariant if all left translations map it into itself. -/
def IsLeftInvariant (V : Submodule ℂ (Lp ℂ 2 μ)) : Prop := ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V

/-- A minimal left-invariant subspace: invariant, nonzero, with no left-invariant subspace strictly between. -/
def IsMinimalInvariant (V : Submodule ℂ (Lp ℂ 2 μ)) : Prop :=
  IsLeftInvariant μ V ∧ V ≠ ⊥ ∧
    ∀ W : Submodule ℂ (Lp ℂ 2 μ), W ≤ V → IsLeftInvariant μ W → W = ⊥ ∨ W = V

/-- The orthogonal complement of an invariant subspace inside an invariant subspace is invariant. -/
lemma isLeftInvariant_orth_inf {V W : Submodule ℂ (Lp ℂ 2 μ)} (hV : IsLeftInvariant μ V)
    (hW : IsLeftInvariant μ W) : IsLeftInvariant μ (Wᗮ ⊓ V) := by
  intro s v ⟨hvW, hvV⟩
  refine ⟨?_, hV s v hvV⟩
  intro w hw
  have hinv : leftTr μ s⁻¹ w ∈ W := hW s⁻¹ w hw
  have h1 : inner ℂ w (leftTr μ s v) = inner ℂ (leftTr μ s⁻¹ w) v := by
    have := LinearIsometry.inner_map_map (leftTr μ s) (leftTr μ s⁻¹ w) v
    rw [← this, ← leftTr_mul, mul_inv_cancel, leftTr_one]
  rw [h1]
  exact hvW _ hinv

/-- **Decomposition into minimal invariant subspaces.** A finite-dimensional invariant subspace is the
supremum of finitely many minimal invariant subspaces. -/
theorem exists_minimal_decomposition (n : ℕ) :
    ∀ V : Submodule ℂ (Lp ℂ 2 μ), FiniteDimensional ℂ V → IsLeftInvariant μ V → Module.finrank ℂ V ≤ n →
      ∃ F : Finset (Submodule ℂ (Lp ℂ 2 μ)),
        (∀ W ∈ F, IsMinimalInvariant μ W ∧ W ≤ V) ∧ V = F.sup id := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V hfd hV hdim
    by_cases hbot : V = ⊥
    · exact ⟨∅, by simp, by simp [hbot]⟩
    by_cases hmin : IsMinimalInvariant μ V
    · exact ⟨{V}, fun W hW => by rw [Finset.mem_singleton.1 hW]; exact ⟨hmin, le_rfl⟩, by simp⟩
    -- there is a proper nonzero invariant subspace
    have hex : ∃ W : Submodule ℂ (Lp ℂ 2 μ), W ≤ V ∧ IsLeftInvariant μ W ∧ W ≠ ⊥ ∧ W ≠ V := by
      by_contra hno
      push Not at hno
      exact hmin ⟨hV, hbot, fun W hWV hWi => by
        by_cases hW0 : W = ⊥
        · exact Or.inl hW0
        · exact Or.inr (hno W hWV hWi hW0)⟩
    obtain ⟨W, hWV, hWi, hW0, hWV'⟩ := hex
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWV
    set W' : Submodule ℂ (Lp ℂ 2 μ) := Wᗮ ⊓ V with hW'
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_right
    have hW'i : IsLeftInvariant μ W' := isLeftInvariant_orth_inf μ hV hWi
    have hsup : W ⊔ W' = V := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hWV
    have hlt1 : Module.finrank ℂ W < Module.finrank ℂ V :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWV hWV')
    have hW'lt : W' < V := by
      refine lt_of_le_of_ne inf_le_right fun h => hW0 ?_
      have hWo : W ≤ Wᗮ := by
        intro w hw
        have : w ∈ W' := by rw [h]; exact hWV hw
        exact this.1
      exact (Submodule.eq_bot_iff _).2 fun w hw => inner_self_eq_zero.1 (hWo hw w hw)
    have hlt2 : Module.finrank ℂ W' < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hW'lt
    obtain ⟨F1, hF1, hF1s⟩ := ih (Module.finrank ℂ W) (lt_of_lt_of_le hlt1 hdim) W inferInstance hWi le_rfl
    obtain ⟨F2, hF2, hF2s⟩ := ih (Module.finrank ℂ W') (lt_of_lt_of_le hlt2 hdim) W' inferInstance hW'i le_rfl
    refine ⟨F1 ∪ F2, fun X hX => ?_, ?_⟩
    · rcases Finset.mem_union.1 hX with h | h
      · exact ⟨(hF1 X h).1, (hF1 X h).2.trans hWV⟩
      · exact ⟨(hF2 X h).1, (hF2 X h).2.trans inf_le_right⟩
    · rw [Finset.sup_union, ← hF1s, ← hF2s, hsup]

section Irreducible

variable (V : Submodule ℂ (Lp ℂ 2 μ)) (hinv : ∀ (s : G), ∀ v ∈ V, leftTr μ s v ∈ V)
  {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ V)

/-- The coordinates-to-vector isomorphism of an orthonormal basis. -/
def coordIso : (ι → ℂ) ≃ₗ[ℂ] V := b.toBasis.equivFun.symm

lemma coordIso_apply (x : ι → ℂ) : coordIso μ V b x = ∑ a, x a • b a := by
  show b.toBasis.equivFun.symm x = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [OrthonormalBasis.coe_toBasis]

/-- The restricted translation acts on coordinates through the matrix `ρ(s)`. -/
lemma restrTr_coordIso (s : G) (x : ι → ℂ) :
    restrTr μ V hinv s (coordIso μ V b x) = coordIso μ V b ((repMatrix μ V hinv b s).mulVec x) := by
  rw [coordIso_apply, coordIso_apply, map_sum]
  simp only [map_smul]
  have h1 : ∀ a, restrTr μ V hinv s (b a) = ∑ c, repMatrix μ V hinv b s c a • b c :=
    fun a => (b.sum_repr' _).symm
  simp_rw [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- **A minimal invariant subspace gives an irreducible representation.** -/
theorem invRep_isIrreducible [FiniteDimensional ℂ V]
    (hcont : ∀ v ∈ V, ∃ c : C(G, ℂ), v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c)
    (hmin : IsMinimalInvariant μ V) :
    (invRep μ V hinv b hcont).IsIrreducible := by
  refine ⟨?_, ?_⟩
  · by_contra hne
    rw [not_nonempty_iff] at hne
    apply hmin.2.1
    have : Module.finrank ℂ V = 0 := by
      rw [Module.finrank_eq_card_basis b.toBasis]; simp
    exact Submodule.finrank_eq_zero.1 this
  · intro X hX
    let W : Submodule ℂ (Lp ℂ 2 μ) := (X.map (coordIso μ V b).toLinearMap).map V.subtype
    have hWV : W ≤ V := Submodule.map_subtype_le _ _
    have hWinv : IsLeftInvariant μ W := by
      rintro s _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨_, ⟨(repMatrix μ V hinv b s).mulVec x, hX s x hx, rfl⟩, ?_⟩
      show ((coordIso μ V b ((repMatrix μ V hinv b s).mulVec x) : V) : Lp ℂ 2 μ) = leftTr μ s _
      rw [← restrTr_coordIso μ V hinv b s x]; rfl
    rcases hmin.2.2 W hWV hWinv with h | h
    · left
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have : ((coordIso μ V b x : V) : Lp ℂ 2 μ) ∈ W := ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [h] at this
      have h0 : coordIso μ V b x = 0 := Subtype.ext (by simpa using this)
      exact (coordIso μ V b).injective (by simpa using h0)
    · right
      refine (Submodule.eq_top_iff').2 fun y => ?_
      have : ((coordIso μ V b y : V) : Lp ℂ 2 μ) ∈ W := by rw [h]; exact (coordIso μ V b y).2
      obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := this
      have : coordIso μ V b x = coordIso μ V b y := Subtype.ext hxy
      rw [← (coordIso μ V b).injective this]; exact hx

end Irreducible

end

end Lightlike.HarmonicAnalysis

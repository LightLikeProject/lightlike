import Lightlike.OperatorAlgebras.Spectral.Cyclic

/-!
# Decomposition of a Hilbert space into cyclic subspaces of a projection-valued measure

`cyclicSubspace μ ψ` is the range of `cycIso`, the closure of `{∫ f dμ ψ}`. It is invariant under every
`μ.integral g`, and so is its orthogonal complement (`integral_mem_orthogonal`). By Zorn's lemma there is a family
of vectors whose cyclic subspaces are pairwise orthogonal and span a dense subspace
(`exists_cyclic_family`).

Supporting results for the converse of the Wigner classification; no catalogue entry.
-/

open scoped InnerProductSpace
open MeasureTheory

namespace Lightlike.OperatorAlgebras.Spectral

noncomputable section

variable {X : Type*} [MeasurableSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The cyclic subspace** of `ψ`: the range of `cycIso`. -/
def cyclicSubspace (μ : ProjectionValuedMeasure X H) (ψ : H) : Submodule ℂ H :=
  LinearMap.range (cycIso μ ψ).toLinearMap

lemma mem_cyclicSubspace_integral (μ : ProjectionValuedMeasure X H) (ψ : H) {f : X → ℂ} (hf : f ∈ BddMeasurable X) :
    μ.integral f ψ ∈ cyclicSubspace μ ψ :=
  ⟨toL2 (μ.assoc ψ) ⟨f, hf⟩, cycIso_toL2 μ ψ ⟨f, hf⟩⟩

lemma self_mem_cyclicSubspace (μ : ProjectionValuedMeasure X H) (ψ : H) : ψ ∈ cyclicSubspace μ ψ := by
  have := mem_cyclicSubspace_integral μ ψ (f := 1) (by rw [mem_bddMeasurable]; exact ⟨measurable_const, 1, by simp⟩)
  rwa [μ.integral_one] at this

/-- The cyclic subspace is closed. -/
lemma isClosed_cyclicSubspace (μ : ProjectionValuedMeasure X H) (ψ : H) :
    IsClosed (cyclicSubspace μ ψ : Set H) := by
  have := (cycIso μ ψ).isometry.isClosedEmbedding.isClosed_range
  exact this

/-- **The orthogonal complement of an invariant subspace is invariant**: if `v ⊥ S` and `S` is invariant under
`∫ ḡ`, then `∫ g v ⊥ S`. -/
lemma integral_mem_orthogonal (μ : ProjectionValuedMeasure X H) {S : Submodule ℂ H}
    (hS : ∀ f ∈ BddMeasurable X, ∀ z ∈ S, μ.integral f z ∈ S) {v : H} (hv : v ∈ Sᗮ) {g : X → ℂ}
    (hg : g ∈ BddMeasurable X) : μ.integral g v ∈ Sᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro z hz
  have hgc : (fun x => (starRingEnd ℂ) (g x)) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    rcases hg with ⟨hm, C, hC⟩
    exact ⟨by simpa [Function.comp_def] using (Complex.continuous_conj.measurable.comp hm), C, fun x => by
      simpa using hC x⟩
  have : ⟪z, μ.integral g v⟫_ℂ = ⟪μ.integral (fun x => (starRingEnd ℂ) (g x)) z, v⟫_ℂ := by
    rw [μ.integral_conj hg, ← ContinuousLinearMap.adjoint_inner_left]
  rw [this]
  exact hv _ (hS _ hgc z hz)

/-- **The cyclic subspace is invariant**: `∫ g` maps it into itself. -/
lemma integral_mem_cyclicSubspace (μ : ProjectionValuedMeasure X H) (ψ : H) {g : X → ℂ} (hg : g ∈ BddMeasurable X)
    {z : H} (hz : z ∈ cyclicSubspace μ ψ) : μ.integral g z ∈ cyclicSubspace μ ψ := by
  obtain ⟨F, rfl⟩ := hz
  have hcl : IsClosed {F : Lp ℂ 2 (μ.assoc ψ) | μ.integral g (cycIso μ ψ F) ∈ cyclicSubspace μ ψ} :=
    (isClosed_cyclicSubspace μ ψ).preimage ((μ.integral g).continuous.comp (cycIso μ ψ).continuous)
  refine (denseRange_toL2 (μ.assoc ψ)).induction_on F hcl ?_
  intro h
  have hgh : (g : X → ℂ) * h ∈ BddMeasurable X := by
    rw [mem_bddMeasurable] at hg ⊢
    obtain ⟨hm1, C1, h1⟩ := hg
    obtain ⟨hm2, C2, h2⟩ := h.2
    exact ⟨hm1.mul hm2, C1 * C2, fun x => by
      simpa [norm_mul] using mul_le_mul (h1 x) (h2 x) (norm_nonneg _) ((norm_nonneg _).trans (h1 x))⟩
  have := integral_cycIso_toL2 μ ψ ⟨g, hg⟩ h hgh
  show μ.integral g (cycIso μ ψ (toL2 (μ.assoc ψ) h)) ∈ _
  rw [show μ.integral g (cycIso μ ψ (toL2 (μ.assoc ψ) h)) = _ from this]
  exact ⟨_, rfl⟩

/-- The family of vectors whose cyclic subspaces are pairwise orthogonal. -/
def IsOrthoCyclic (μ : ProjectionValuedMeasure X H) (S : Set H) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ x ∈ cyclicSubspace μ a, ∀ y ∈ cyclicSubspace μ b, ⟪x, y⟫_ℂ = 0

/-- **Decomposition into cyclic subspaces.** There is a set `S` of vectors with pairwise orthogonal cyclic subspaces
whose sum is dense. -/
theorem exists_cyclic_family (μ : ProjectionValuedMeasure X H) :
    ∃ S : Set H, IsOrthoCyclic μ S ∧ (⨆ a : S, cyclicSubspace μ a).topologicalClosure = ⊤ := by
  obtain ⟨S, hS, hmax⟩ := zorn_subset {S : Set H | IsOrthoCyclic μ S} (fun c hc hchain => by
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    intro a ha b hb hab
    obtain ⟨s, hs, has⟩ := ha
    obtain ⟨t, ht, hbt⟩ := hb
    rcases hchain.total hs ht with h | h
    · exact hc ht a (h has) b hbt hab
    · exact hc hs a has b (h hbt) hab)
  refine ⟨S, hS, ?_⟩
  set T : Submodule ℂ H := ⨆ a : S, cyclicSubspace μ a with hT
  have hTinv : ∀ f ∈ BddMeasurable X, ∀ z ∈ T, μ.integral f z ∈ T := by
    intro f hf z hz
    induction hz using Submodule.iSup_induction' with
    | mem a z hz => exact Submodule.mem_iSup_of_mem a (integral_mem_cyclicSubspace μ a hf hz)
    | zero => simpa using Submodule.zero_mem T
    | add x y _ _ hx hy => rw [map_add]; exact T.add_mem hx hy
  by_contra hne
  have hTc : T.topologicalClosure ≠ ⊤ := hne
  have hortho : Tᗮ ≠ ⊥ := by
    intro h
    apply hTc
    rw [← Submodule.orthogonal_orthogonal_eq_closure, h]
    exact Submodule.bot_orthogonal_eq_top
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hortho
  have hφS : φ ∉ S := by
    intro hφS
    have : φ ∈ T := Submodule.mem_iSup_of_mem ⟨φ, hφS⟩ (self_mem_cyclicSubspace μ φ)
    exact hφ0 (inner_self_eq_zero.1 (hφ φ this))
  have hZφ : ∀ z ∈ cyclicSubspace μ φ, z ∈ Tᗮ := by
    rintro _ ⟨F, rfl⟩
    have hcl : IsClosed {F : Lp ℂ 2 (μ.assoc φ) | cycIso μ φ F ∈ Tᗮ} :=
      (Submodule.isClosed_orthogonal T).preimage (cycIso μ φ).continuous
    refine (denseRange_toL2 (μ.assoc φ)).induction_on F hcl ?_
    intro h
    show cycIso μ φ (toL2 (μ.assoc φ) h) ∈ Tᗮ
    rw [cycIso_toL2]
    exact integral_mem_orthogonal μ hTinv hφ h.2
  have hS' : IsOrthoCyclic μ (insert φ S) := by
    intro a ha b hb hab x hx y hy
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact by
        have hyT : y ∈ T := Submodule.mem_iSup_of_mem ⟨b, hb⟩ hy
        rw [← inner_conj_symm]
        have := (Submodule.mem_orthogonal _ _).1 (hZφ x hx) y hyT
        rw [this, map_zero]
    · exact by
        have hxT : x ∈ T := Submodule.mem_iSup_of_mem ⟨a, ha⟩ hx
        exact (Submodule.mem_orthogonal _ _).1 (hZφ y hy) x hxT
    · exact hS a ha b hb hab x hx y hy
  exact hφS (hmax hS' (Set.subset_insert φ S) (Set.mem_insert φ S))

end

end Lightlike.OperatorAlgebras.Spectral

import Lightlike.Canonical.ProjectiveLimitIntegral.Limit

/-!
# Cylindrical functions on a projective limit (row G2-008)

For an inverse system of compact Hausdorff spaces over a directed set, the *cylindrical functions*
are the continuous functions `φ ∘ proj i` with `φ ∈ C(X i, ℝ)`.  They form a subalgebra
`cylSubalgebra` of `C(lim X, ℝ)` (directedness is used to bring two cylindrical functions to a
common index), it separates points, and by Stone–Weierstrass it is dense
(`cylSubalgebra_topologicalClosure`).  This density is the input for building the limit measure
by the Riesz–Markov theorem.
-/

noncomputable section

open Set

namespace Lightlike.Canonical.ProjectiveLimitIntegral

namespace InvSystem

variable {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
variable (S : InvSystem ι X)

/-- The pull-back `φ ∘ proj i` of a continuous function on `X i`, as a continuous function on the
limit. -/
def cyl (i : ι) (φ : C(X i, ℝ)) : C(S.Limit, ℝ) :=
  φ.comp ⟨S.proj i, S.continuous_proj i⟩

@[simp] lemma cyl_apply (i : ι) (φ : C(X i, ℝ)) (x : S.Limit) : S.cyl i φ x = φ (S.proj i x) :=
  rfl

/-- A cylindrical function based at `i` is also based at any `k ≥ i`. -/
lemma cyl_eq_of_le {i k : ι} (h : i ≤ k) (φ : C(X i, ℝ)) :
    S.cyl i φ = S.cyl k (φ.comp ⟨S.f h, S.continuous_f h⟩) := by
  ext x
  simp [S.f_proj h x]

/-- The **cylindrical functions**: continuous functions on the limit of the form `φ ∘ proj i`. -/
def cylSubalgebra [Nonempty ι] [IsDirectedOrder ι] : Subalgebra ℝ C(S.Limit, ℝ) where
  carrier := {F | ∃ i, ∃ φ : C(X i, ℝ), F = S.cyl i φ}
  mul_mem' := by
    rintro _ _ ⟨i, φ, rfl⟩ ⟨j, ψ, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, (φ.comp ⟨S.f hik, S.continuous_f hik⟩) * (ψ.comp ⟨S.f hjk, S.continuous_f hjk⟩), ?_⟩
    rw [S.cyl_eq_of_le hik φ, S.cyl_eq_of_le hjk ψ]
    ext x
    simp
  add_mem' := by
    rintro _ _ ⟨i, φ, rfl⟩ ⟨j, ψ, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, (φ.comp ⟨S.f hik, S.continuous_f hik⟩) + (ψ.comp ⟨S.f hjk, S.continuous_f hjk⟩), ?_⟩
    rw [S.cyl_eq_of_le hik φ, S.cyl_eq_of_le hjk ψ]
    ext x
    simp
  algebraMap_mem' := by
    intro r
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, algebraMap ℝ C(X i, ℝ) r, by ext x; simp⟩

lemma mem_cylSubalgebra [Nonempty ι] [IsDirectedOrder ι] (i : ι) (φ : C(X i, ℝ)) :
    S.cyl i φ ∈ S.cylSubalgebra :=
  ⟨i, φ, rfl⟩

/-- The cylindrical functions separate the points of a projective limit of compact Hausdorff
spaces. -/
lemma cylSubalgebra_separatesPoints [Nonempty ι] [IsDirectedOrder ι]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] :
    S.cylSubalgebra.SeparatesPoints := by
  intro x y hxy
  have : ∃ i, S.proj i x ≠ S.proj i y := by
    by_contra hcon
    exact hxy (Subtype.ext (funext fun i => by_contra fun h => hcon ⟨i, h⟩))
  obtain ⟨i, hi⟩ := this
  obtain ⟨g, hg, hg0, hg1⟩ :=
    CompletelyRegularSpace.completely_regular (S.proj i x) {S.proj i y} isClosed_singleton
      (by simpa using hi)
  refine ⟨_, ⟨S.cyl i ⟨fun z => (g z : ℝ), continuous_subtype_val.comp hg⟩,
    S.mem_cylSubalgebra i _, rfl⟩, ?_⟩
  simp only [cyl_apply, ContinuousMap.coe_mk, hg0]
  have := hg1 (show S.proj i y ∈ ({S.proj i y} : Set (X i)) from rfl)
  simp [this]

/-- **The cylindrical functions are dense in `C(lim X, ℝ)`** (Stone–Weierstrass). -/
theorem cylSubalgebra_topologicalClosure [Nonempty ι] [IsDirectedOrder ι]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] :
    S.cylSubalgebra.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    S.cylSubalgebra_separatesPoints

end InvSystem

end Lightlike.Canonical.ProjectiveLimitIntegral

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.cyl := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.cyl
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.cylSubalgebra := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.cylSubalgebra
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.cylSubalgebra_separatesPoints := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.cylSubalgebra_separatesPoints
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.cylSubalgebra_topologicalClosure := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.cylSubalgebra_topologicalClosure
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.cyl_apply := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.cyl_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.cyl_eq_of_le := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.cyl_eq_of_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.mem_cylSubalgebra := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.mem_cylSubalgebra

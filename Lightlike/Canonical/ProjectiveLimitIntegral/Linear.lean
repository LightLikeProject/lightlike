import Lightlike.Canonical.ProjectiveLimitIntegral.Functional

/-!
# The integral as a linear functional on cylindrical functions (row G2-008)

For a cylindrically consistent family of probability measures `μ i` (surjective bonding maps), the
well-defined map `φ ∘ proj i ↦ ∫ φ dμ i` is a linear functional `lam` on the algebra of cylindrical
functions (`lam_cyl`), it sends `1` to `1` and is bounded by the sup norm (`abs_lam_le`).
-/

noncomputable section

open MeasureTheory Set

namespace Lightlike.Rows.G2_008

namespace InvSystem

variable {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
variable (S : InvSystem ι X)

lemma exists_cyl [Nonempty ι] [IsDirectedOrder ι] (F : S.cylSubalgebra) :
    ∃ i, ∃ φ : C(X i, ℝ), (F : C(S.Limit, ℝ)) = S.cyl i φ := F.2

variable [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]

/-- The (choice-based) integral of the base function of a cylindrical function. -/
def lamFun [Nonempty ι] [IsDirectedOrder ι] (μ : ∀ i, Measure (X i)) (F : S.cylSubalgebra) : ℝ :=
  ∫ x, (S.exists_cyl F).choose_spec.choose x ∂(μ (S.exists_cyl F).choose)

variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
variable (hS : ∀ {i j : ι} (h : i ≤ j), Function.Surjective (S.f h))
variable {μ : ∀ i, Measure (X i)} (hμ : S.IsConsistent μ) (hp : ∀ i, IsProbabilityMeasure (μ i))

include hS hμ in
/-- `lamFun` computes `∫ φ dμ i` on `φ ∘ proj i`. -/
lemma lamFun_cyl (i : ι) (φ : C(X i, ℝ)) :
    S.lamFun μ ⟨S.cyl i φ, S.mem_cylSubalgebra i φ⟩ = ∫ x, φ x ∂(μ i) :=
  S.integral_eq_of_cyl_eq hS hμ
    ((S.exists_cyl ⟨S.cyl i φ, S.mem_cylSubalgebra i φ⟩).choose_spec.choose_spec.symm)

omit [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [∀ i, T2Space (X i)] in
include hp in
lemma integrable_cont {i : ι} (φ : C(X i, ℝ)) : Integrable φ (μ i) := by
  have := hp i
  exact φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hS hμ hp in
/-- The integral functional on the cylindrical functions. -/
def lam : S.cylSubalgebra →ₗ[ℝ] ℝ where
  toFun := S.lamFun μ
  map_add' F G := by
    obtain ⟨i, φ, hF⟩ := S.exists_cyl F
    obtain ⟨j, ψ, hG⟩ := S.exists_cyl G
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have eF : F = ⟨S.cyl i φ, S.mem_cylSubalgebra i φ⟩ := Subtype.ext hF
    have eG : G = ⟨S.cyl j ψ, S.mem_cylSubalgebra j ψ⟩ := Subtype.ext hG
    have eFG : F + G = ⟨S.cyl k ((φ.comp ⟨S.f hik, S.continuous_f hik⟩) +
        (ψ.comp ⟨S.f hjk, S.continuous_f hjk⟩)), S.mem_cylSubalgebra _ _⟩ := by
      apply Subtype.ext
      show (F : C(S.Limit, ℝ)) + G = _
      rw [hF, hG, S.cyl_eq_of_le hik φ, S.cyl_eq_of_le hjk ψ]
      ext x
      simp
    rw [eFG, eF, eG, S.lamFun_cyl hS hμ, S.lamFun_cyl hS hμ, S.lamFun_cyl hS hμ]
    show ∫ x, ((φ.comp ⟨S.f hik, S.continuous_f hik⟩) x +
        (ψ.comp ⟨S.f hjk, S.continuous_f hjk⟩) x) ∂(μ k) = _
    rw [integral_add (integrable_cont hp _) (integrable_cont hp _),
      S.integral_comp_f hμ hik φ, S.integral_comp_f hμ hjk ψ]
  map_smul' c F := by
    obtain ⟨i, φ, hF⟩ := S.exists_cyl F
    have eF : F = ⟨S.cyl i φ, S.mem_cylSubalgebra i φ⟩ := Subtype.ext hF
    have ecF : c • F = ⟨S.cyl i (c • φ), S.mem_cylSubalgebra i _⟩ := by
      apply Subtype.ext
      show c • (F : C(S.Limit, ℝ)) = _
      rw [hF]
      ext x
      simp
    rw [RingHom.id_apply, ecF, eF]
    have h1 := S.lamFun_cyl hS hμ i (c • φ)
    have h2 := S.lamFun_cyl hS hμ i φ
    show S.lamFun μ _ = c * S.lamFun μ _
    rw [h1, h2]
    show ∫ x, c * φ x ∂(μ i) = _
    exact integral_const_mul c _

include hS hμ hp in
/-- `lam` computes `∫ φ dμ i` on `φ ∘ proj i`. -/
lemma lam_cyl (i : ι) (φ : C(X i, ℝ)) :
    S.lam hS hμ hp ⟨S.cyl i φ, S.mem_cylSubalgebra i φ⟩ = ∫ x, φ x ∂(μ i) :=
  S.lamFun_cyl hS hμ i φ

include hS hμ hp in
/-- **The integral functional is bounded by the sup norm** (`‖lam F‖ ≤ ‖F‖`). -/
lemma abs_lam_le (F : S.cylSubalgebra) : |S.lam hS hμ hp F| ≤ ‖(F : C(S.Limit, ℝ))‖ := by
  obtain ⟨i, φ, hF⟩ := S.exists_cyl F
  have eF : F = ⟨S.cyl i φ, S.mem_cylSubalgebra i φ⟩ := Subtype.ext hF
  rw [eF, S.lam_cyl hS hμ hp]
  have := hp i
  have hb : ∀ y, ‖φ y‖ ≤ ‖S.cyl i φ‖ := by
    intro y
    obtain ⟨x, rfl⟩ := S.proj_surjective hS i y
    exact (S.cyl i φ).norm_coe_le_norm x
  have := norm_integral_le_of_norm_le_const (μ := μ i) (f := fun y => φ y)
    (Filter.Eventually.of_forall hb)
  simpa using this

end InvSystem

end Lightlike.Rows.G2_008

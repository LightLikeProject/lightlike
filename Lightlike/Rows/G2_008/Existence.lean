import Lightlike.Rows.G2_008.Linear

/-!
# Extension of the integral functional to all continuous functions (row G2-008)

The functional `lam` on cylindrical functions is bounded by the sup norm and cylindrical functions
are dense in `C(lim X, ℝ)`; hence `lam` extends to a continuous linear functional `lamL` on
`C(lim X, ℝ)` (`lamL_cyl`).  Positivity of `lamL` and the Riesz–Markov step come in later files.
-/

noncomputable section

open MeasureTheory Set

namespace Lightlike.Rows.G2_008

namespace InvSystem

variable {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
variable (S : InvSystem ι X)
variable [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]

omit [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] in
/-- The inclusion of the cylindrical functions into all continuous functions has dense range. -/
lemma denseRange_cylSubalgebra_val : DenseRange S.cylSubalgebra.val.toLinearMap := by
  have h : Dense (S.cylSubalgebra : Set C(S.Limit, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
      S.cylSubalgebra_topologicalClosure]
    rfl
  simpa [DenseRange] using h

variable (hS : ∀ {i j : ι} (h : i ≤ j), Function.Surjective (S.f h))
variable {μ : ∀ i, Measure (X i)} (hμ : S.IsConsistent μ) (hp : ∀ i, IsProbabilityMeasure (μ i))

include hS hμ hp in
/-- The integral functional extended to a continuous linear functional on `C(lim X, ℝ)`. -/
def lamL : C(S.Limit, ℝ) →L[ℝ] ℝ :=
  (S.lam hS hμ hp).extendOfNorm S.cylSubalgebra.val.toLinearMap

include hS hμ hp in
/-- `lamL` computes `∫ φ dμ i` on `φ ∘ proj i`. -/
lemma lamL_cyl (i : ι) (φ : C(X i, ℝ)) : S.lamL hS hμ hp (S.cyl i φ) = ∫ x, φ x ∂(μ i) := by
  have h := LinearMap.extendOfNorm_eq (f := S.lam hS hμ hp) (e := S.cylSubalgebra.val.toLinearMap)
    S.denseRange_cylSubalgebra_val ⟨1, fun F => by
      simpa using S.abs_lam_le hS hμ hp F⟩ ⟨S.cyl i φ, S.mem_cylSubalgebra i φ⟩
  exact h.trans (S.lam_cyl hS hμ hp i φ)

end InvSystem

end Lightlike.Rows.G2_008

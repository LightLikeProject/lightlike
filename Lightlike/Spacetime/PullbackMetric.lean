import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.Lorentzian

/-!
# The metric induced by an immersion into a space with a bilinear form

For a smooth map `ι : M → V` into a normed space with a symmetric bilinear form `L` (any signature), the pullback
`L(dι ·, dι ·)` (`pullbackForm`) is a metric of `M` as soon as it is nondegenerate on every tangent space
(`NondegMetric.pullback`). For a quadric `{x | L(x, x) = c}`, `c ≠ 0`, nondegeneracy is linear algebra
(`pullback_nondeg_of_quadric`): `L` is nondegenerate on `x^⊥` when it is nondegenerate on `V` and `L(x, x) ≠ 0`, and the
differential of an immersion onto the quadric is injective with image `x^⊥`.
-/

open Manifold Bundle
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The metric induced by an immersion**: the pullback of a symmetric bilinear form `L` by a smooth map `ι`, when it
is nondegenerate on every tangent space. -/
def NondegMetric.pullback (L : V →L[ℝ] V →L[ℝ] ℝ) (hL : ∀ a b, L a b = L b a) (ι : M → V)
    (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι)
    (hnd : ∀ (p : M) (v : TangentSpace I p),
      (∀ w : TangentSpace I p, L (dι (I := I) ι p v) (dι (I := I) ι p w) = 0) → v = 0) :
    NondegMetric I M where
  g := pullbackForm (I := I) L ι
  symm := pullbackForm_symm hL ι
  nondegenerate p v h := hnd p v fun w => by rw [← pullbackForm_apply]; exact h w
  contMDiff := contMDiff_pullbackForm L hι

/-- The value of the induced metric: `L(dι v, dι w)`. -/
theorem NondegMetric.pullback_apply (L : V →L[ℝ] V →L[ℝ] ℝ) (hL : ∀ a b, L a b = L b a) (ι : M → V)
    (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι) (hnd) (p : M) (v w : TangentSpace I p) :
    (NondegMetric.pullback L hL ι hι hnd).g p v w = L (dι (I := I) ι p v) (dι (I := I) ι p w) := rfl

omit [FiniteDimensional ℝ E] in
/-- **The form is nondegenerate on the tangent space of a quadric.** If `L` is symmetric and nondegenerate,
`L(x, x) ≠ 0`, and the linear map `D` is injective with image exactly the `L`-orthogonal complement of `x`, then the
pullback `L(D ·, D ·)` is nondegenerate. -/
theorem pullback_nondeg_of_quadric {L : V →L[ℝ] V →L[ℝ] ℝ} (hL : ∀ a b, L a b = L b a)
    (hLnd : ∀ u, (∀ z, L u z = 0) → u = 0) {x : V} (hx : L x x ≠ 0) {D : E →L[ℝ] V}
    (hinj : Function.Injective D) (hDperp : ∀ w, L x (D w) = 0)
    (hDsurj : ∀ z, L x z = 0 → ∃ w, D w = z) (v : E) (hv : ∀ w, L (D v) (D w) = 0) : v = 0 := by
  have hu : ∀ z, L (D v) z = 0 := by
    intro z
    set c := L x z / L x x
    have hz : L x (z - c • x) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul]
      simp only [c]
      field_simp
      ring
    obtain ⟨w, hw⟩ := hDsurj _ hz
    have h1 : L (D v) (z - c • x) = 0 := by rw [← hw]; exact hv w
    have h2 : L (D v) x = 0 := by rw [hL]; exact hDperp v
    have : L (D v) z = L (D v) (z - c • x) + c * L (D v) x := by
      rw [map_sub, map_smul, smul_eq_mul]; ring
    rw [this, h1, h2, mul_zero, add_zero]
  exact hinj ((hLnd _ hu).trans (map_zero D).symm)


/-- **Non-vacuity of `NondegMetric.pullback`**: the inner product pulled back by the identity of a Euclidean space
is a metric whose value is the inner product. -/
theorem exists_pullback_euclidean (n : ℕ) :
    ∃ g : NondegMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      ∀ p (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p),
        g.g p v w = inner ℝ (v : EuclideanSpace ℝ (Fin n)) w := by
  have hd : ∀ p : EuclideanSpace ℝ (Fin n),
      dι (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (id : EuclideanSpace ℝ (Fin n) → _) p =
        ContinuousLinearMap.id ℝ _ := fun p => mfderiv_id
  refine ⟨NondegMetric.pullback (innerSL ℝ) (fun a b => by show inner ℝ a b = inner ℝ b a; exact real_inner_comm b a) id contMDiff_id
    (fun p v h => ?_), fun p v w => ?_⟩
  · have h0 := h v
    rw [hd p] at h0
    exact inner_self_eq_zero.1 h0
  · show innerSL ℝ (dι (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) id p v)
      (dι (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) id p w) = _
    rw [hd p]
    rfl

/-- **Non-vacuity of `pullback_nondeg_of_quadric`**: the unit circle of the Euclidean plane at `e₀`, whose tangent line
is the image of `t ↦ t e₁`. -/
theorem pullback_nondeg_of_quadric_circle (v : ℝ)
    (hv : ∀ w : ℝ, innerSL ℝ ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) v)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) w) = 0) : v = 0 := by
  refine pullback_nondeg_of_quadric (L := innerSL ℝ)
    (fun a b => by show inner ℝ a b = inner ℝ b a; exact real_inner_comm b a)
    (fun u hu => inner_self_eq_zero.1 (hu u)) (x := EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    (by show inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) ≠ 0; simp)
    (fun a b h => by simpa using congrArg (fun z => z (1 : Fin 2)) h)
    (fun w => by
      show inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (w • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = 0
      simp [inner_smul_right, EuclideanSpace.inner_single_left])
    (fun z hz => ⟨z (1 : Fin 2), ?_⟩) v hv
  have hz' : inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) z = 0 := hz
  rw [EuclideanSpace.inner_single_left] at hz'
  ext i
  fin_cases i
  · simpa using hz'.symm
  · simp

end Lightlike

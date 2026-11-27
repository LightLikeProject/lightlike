import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.Corners.ChartCurvature
import Lightlike.Spacetime.Corners.LieDerivation
import Lightlike.Spacetime.LieMetric
import Lightlike.Spacetime.Minkowski

/-!
# Killing fields induced by ambient symmetries

For a smooth map `ι : M → V` into a finite-dimensional normed space with a symmetric bilinear form `L`, and an
`L`-skew linear map `A` of `V`, a vector field `X` of `M` that is `ι`-related to the linear field `x ↦ A x`
(`dι (X p) = A (ι p)`) preserves the pulled back form: `L_X (ι* L) = 0`. With the Levi-Civita connection of the
induced metric this makes `X` a Killing field. This gives the Killing fields of de Sitter and anti-de Sitter space as
restrictions of the generators `x_a ∂_b - x_b ∂_a` of the ambient pseudo-orthogonal group.

* `dι_mlieBracket_of_related`: if `dι (X q) = A (ι q)`, then `dι [X, Y] = X (dι Y) - A (dι Y)` (the commutator
  formula `mfderiv_mlieBracketW`, tested against every linear functional of `V`).
* `lieDerivMetric_eq_zero_of_related`: for `g(u, v) = L(dι u, dι v)` and `A` skew for `L`, `L_X g = 0`.
* `isKillingAt_of_related`: such an `X` is a Killing field of every Levi-Civita connection of `g`.
* `isKillingAt_minkowski_boost`: non-vacuity, the boost of `1+1` Minkowski space.

The metric enters only through the identity `g(u, v) = L(dι u, dι v)`, so the theorems apply to
`NondegMetric.pullback` and to any metric equal to it. Any model with corners `I` on a finite-dimensional space is
allowed, in particular the `Fin n → ℝ` models of products such as `ℝ × Sᵐ`.

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), ch. 8 (maximally symmetric spaces).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- **The derivative of a smooth map applied to a differentiable field is differentiable.** -/
theorem mdiffAt_dι_section {ι : M → V} (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι)
    {Z : Π q : M, TangentSpace I q} {p : M}
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) p) :
    MDifferentiableAt I 𝓘(ℝ, V) (fun q => dι (I := I) ι q (Z q)) p := by
  have hA : MDifferentiableAt I 𝓘(ℝ, V).tangent
      (tangentMap I 𝓘(ℝ, V) ι ∘ fun q => (⟨q, Z q⟩ : TangentBundle I M)) p :=
    (((hι.contMDiff_tangentMap (m := 1) (by norm_num)) _).mdifferentiableAt one_ne_zero).comp p hZ
  have hB := ((mdifferentiableAt_totalSpace _ _).1 hA).2
  simp only [Function.comp_apply, trivializationAt_model_space_apply] at hB
  exact hB

omit [FiniteDimensional ℝ V] in
/-- The derivative of `q ↦ ℓ (f q)` for a continuous linear `ℓ` is `ℓ` of the derivative of `f`. -/
theorem mvfderiv_clm_comp_left {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (ℓ : F →L[ℝ] G) {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (u : TangentSpace I x) :
    mvfderiv I (fun q => ℓ (f q)) x u = ℓ (mvfderiv I f x u) := by
  have h := mvfderiv_clm_applyW (fun _ : M => ℓ) f x mdifferentiableAt_const hf u
  rw [h, mvfderiv_const]
  simp

variable [IsManifold I 2 M] [CompleteSpace E]

omit [FiniteDimensional ℝ V] in
/-- **Naturality of the Lie bracket along an ambient linear field.** If `X` is `ι`-related to the linear
field `x ↦ A x` of `V`, then `dι [X, Y] = X (dι Y) - A (dι Y)`, where `X (dι Y)` is the derivative of the
`V`-valued function `q ↦ dι_q (Y q)` along `X`. -/
theorem dι_mlieBracket_of_related {ι : M → V} (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι) (A : V →L[ℝ] V)
    {X Y : Π q : M, TangentSpace I q} (hXA : ∀ q, dι (I := I) ι q (X q) = A (ι q)) {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) x) :
    dι (I := I) ι x (mlieBracket I X Y x) =
      mvfderiv I (fun q => dι (I := I) ι q (Y q)) x (X x) - A (dι (I := I) ι x (Y x)) := by
  have hιd : ∀ q, MDifferentiableAt I 𝓘(ℝ, V) ι q := fun q => (hι q).mdifferentiableAt (by simp)
  have hFY := mdiffAt_dι_section hι hY
  rw [← sub_eq_zero]
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => ?_
  have hd : ∀ (W : Π q : M, TangentSpace I q), dirDerivW (ℓ ∘ ι) W = fun q => ℓ (dι (I := I) ι q (W q)) := by
    intro W; funext q
    exact mvfderiv_clm_comp_left ℓ (hιd q) (W q)
  have hg : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ℓ ∘ ι) y :=
    Eventually.of_forall fun y => (ℓ.contMDiff.contMDiffAt).comp y (hι y)
  have key := mfderiv_mlieBracketW (ℓ ∘ ι) X Y x hg hX hY
  have e1 : (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (ℓ ∘ ι) x (mlieBracket I X Y x)) =
      ℓ (dι (I := I) ι x (mlieBracket I X Y x)) := mvfderiv_clm_comp_left ℓ (hιd x) _
  have e2 : (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (dirDerivW (ℓ ∘ ι) Y) x (X x)) =
      ℓ (mvfderiv I (fun q => dι (I := I) ι q (Y q)) x (X x)) := by
    rw [hd Y]; exact mvfderiv_clm_comp_left ℓ hFY (X x)
  have e3 : (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (dirDerivW (ℓ ∘ ι) X) x (Y x)) =
      ℓ (A (dι (I := I) ι x (Y x))) := by
    have : dirDerivW (ℓ ∘ ι) X = fun q => (ℓ.comp A) (ι q) := by
      rw [hd X]; funext q; simp [hXA q]
    rw [this]; exact mvfderiv_clm_comp_left (ℓ.comp A) (hιd x) (Y x)
  rw [e1, e2, e3] at key
  simp [map_sub, key]

omit [FiniteDimensional ℝ V] in
/-- **A field related to an ambient skew linear field preserves the induced metric**: if
`g(u, v) = L(dι u, dι v)`, `A` is `L`-skew (`L(A u, v) + L(u, A v) = 0`) and `dι (X q) = A (ι q)`, then
`(L_X g)(V, W) = 0` at every point, for all fields `V, W` differentiable there. -/
theorem lieDerivMetric_eq_zero_of_related {g : NondegMetric I M}
    {L : V →L[ℝ] V →L[ℝ] ℝ} {ι : M → V} (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι)
    (hg : ∀ q u v, g.g q u v = L (dι (I := I) ι q u) (dι (I := I) ι q v))
    (A : V →L[ℝ] V) (hA : ∀ u v, L (A u) v + L u (A v) = 0)
    {X : Π q : M, TangentSpace I q} (hXA : ∀ q, dι (I := I) ι q (X q) = A (ι q)) {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) x)
    {Y W : Π q : M, TangentSpace I q}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, W q⟩ : TangentBundle I M)) x) :
    lieDerivMetric g X Y W x = 0 := by
  have hFY := mdiffAt_dι_section hι hY
  have hFW := mdiffAt_dι_section hι hW
  have hgp : gpair g Y W = fun q => L (dι (I := I) ι q (Y q)) (dι (I := I) ι q (W q)) := by
    funext q; exact hg q (Y q) (W q)
  have hprod := mvfderiv_clm_applyW (fun q => L (dι (I := I) ι q (Y q))) (fun q => dι (I := I) ι q (W q)) x
    (L.mdifferentiableAt.comp x hFY) hFW (X x)
  have hL := mvfderiv_clm_comp_left L hFY (X x)
  unfold lieDerivMetric
  rw [hgp, hprod, hL, hg, hg, dι_mlieBracket_of_related hι A hXA hX hY,
    dι_mlieBracket_of_related hι A hXA hX hW]
  have := hA (dι (I := I) ι x (Y x)) (dι (I := I) ι x (W x))
  simp only [map_sub, _root_.sub_apply]
  linarith

omit [FiniteDimensional ℝ V] in
/-- **Killing fields induced by ambient symmetries.** For the Levi-Civita connection of a metric induced by
`ι` from a symmetric form `L`, a smooth field `X` that is `ι`-related to an `L`-skew linear field `x ↦ A x`
is a Killing field at every point. -/
theorem isKillingAt_of_related {g : NondegMetric I M} {cov : Connection I M}
    (hcov : cov.IsLeviCivita g)
    {L : V →L[ℝ] V →L[ℝ] ℝ} {ι : M → V} (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι)
    (hg : ∀ q u v, g.g q u v = L (dι (I := I) ι q u) (dι (I := I) ι q v))
    (A : V →L[ℝ] V) (hA : ∀ u v, L (A u) v + L u (A v) = 0)
    {X : Π q : M, TangentSpace I q} (hXA : ∀ q, dι (I := I) ι q (X q) = A (ι q)) {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) x) :
    IsKillingAt cov g X x :=
  (isKillingAt_iff_lieDerivMetric_eq_zero hcov hX).2 fun _ _ hY hW =>
    lieDerivMetric_eq_zero_of_related hι hg A hA hXA hX hY hW

/-! ## Non-vacuity: the boost of 1+1 Minkowski space -/

/-- The boost generator of `1+1` Minkowski space, `A (t, x) = (x, t)`. -/
def boost2 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearMap.proj 1).smulRight (Pi.single 0 1 : Fin 2 → ℝ) +
    (ContinuousLinearMap.proj 0).smulRight (Pi.single 1 1 : Fin 2 → ℝ)

/-- The boost is skew for the Minkowski form: `η(A u, v) + η(u, A v) = 0`. -/
theorem boost2_skew (u v : Fin 2 → ℝ) : minkowskiForm 2 (boost2 u) v + minkowskiForm 2 u (boost2 v) = 0 := by
  simp [boost2, Fin.sum_univ_two, etaDiag, Pi.single_apply]

/-- **Non-vacuity of `isKillingAt_of_related`**: the boost field `q ↦ A q` of `1+1` Minkowski space (the
inclusion `ι = id`, `L = η`) is a Killing field of the Levi-Civita connection at every point, and it is
not the zero field. -/
theorem isKillingAt_minkowski_boost (x : Fin 2 → ℝ) :
    IsKillingAt (leviCivita (minkowskiMetric 2).toNondegMetric) (minkowskiMetric 2).toNondegMetric
      (fun q => (boost2 q : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) q)) x ∧
    (fun q => (boost2 q : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) q)) ≠ 0 := by
  have hdι : ∀ q, dι (I := 𝓘(ℝ, Fin 2 → ℝ)) (id : (Fin 2 → ℝ) → Fin 2 → ℝ) q = ContinuousLinearMap.id ℝ _ :=
    fun q => mfderiv_id
  refine ⟨isKillingAt_of_related (L := minkowskiForm 2)
    ⟨leviCivita_torsion _, leviCivita_compat _⟩ contMDiff_id ?_ boost2 boost2_skew ?_ ?_, ?_⟩
  · intro q u v; rw [hdι]; rfl
  · intro q; rw [hdι]; rfl
  · refine (mdifferentiableAt_totalSpace _ _).2 ⟨mdifferentiableAt_id, ?_⟩
    simp only [trivializationAt_model_space_apply]
    exact boost2.mdifferentiableAt
  · intro h
    have := congrFun h (Pi.single 0 1)
    have h1 := congrFun this 1
    simp [boost2] at h1

end Lightlike

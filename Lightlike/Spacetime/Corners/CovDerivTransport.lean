import Mathlib
import Lightlike.Spacetime.Connection
import Lightlike.Spacetime.Corners.LieBracketTransport
import Lightlike.Spacetime.Corners.ChartCovariant

/-!
# A connection for a transported model

For `e : E ≃L[ℝ] F` and `I' = I.transContinuousLinearEquiv e`, a connection `cov` on the tangent bundle for `I` gives a connection
`transCov e cov` on the tangent bundle for `I'`, `∇'_v σ = e (∇_{e⁻¹ v} (e⁻¹ ∘ σ))`; and `transCov e cov` of a transported section is the
transport of `cov` (`transCov_transSection`). Used to carry the curvature theorems of the model `Fin n → ℝ` to any finite-dimensional model
space (GE11 m4).
-/

open Bundle Manifold Set VectorField
open scoped Manifold ContDiff
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inverse transport of a section of the tangent bundle for the transported model. -/
def untransSection (e : E ≃L[ℝ] F) (σ : Π y : M, TangentSpace (I.transContinuousLinearEquiv e) y) :
    Π y : M, TangentSpace I y := fun y => e.symm (σ y)

@[simp] theorem transSection_untransSection (e : E ≃L[ℝ] F) (σ : Π y : M, TangentSpace (I.transContinuousLinearEquiv e) y) :
    transSection e (untransSection e σ : Π y : M, TangentSpace I y) = σ :=
  funext fun y => e.apply_symm_apply (σ y)

@[simp] theorem untransSection_transSection (e : E ≃L[ℝ] F) (σ : Π y : M, TangentSpace I y) :
    untransSection e (transSection e σ) = σ :=
  funext fun y => e.symm_apply_apply (σ y)

variable [IsManifold I 1 M] [CompleteSpace E] [CompleteSpace F]

/-- The derivative of a function for the transported model: `d g = (d g) ∘ e⁻¹`. -/
theorem mfderiv_transContinuousLinearEquiv_real (e : E ≃L[ℝ] F) {g : M → ℝ} {x : M} (hg : MDiffAt g x) :
    mfderiv (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) g x =
      (mfderiv I 𝓘(ℝ, ℝ) g x).comp (e.symm : F →L[ℝ] E) :=
  (hasMFDerivAt_transContinuousLinearEquiv e hg.hasMFDerivAt).mfderiv

/-- **The connection transported to the model `I.transContinuousLinearEquiv e`.** -/
def transCov (e : E ≃L[ℝ] F) (cov : Connection I M) : Connection (I.transContinuousLinearEquiv e) M where
  toFun σ x := (e : E →L[ℝ] F).comp ((cov (untransSection e σ) x).comp (e.symm : F →L[ℝ] E))
  isCovariantDerivativeOnUniv :=
    { add := by
        intro σ σ' x hσ hσ' _
        have h1 : MDiffAt (T% (untransSection e σ : Π y : M, TangentSpace I y)) x :=
          (mdifferentiableAt_transSection_iff e _ x).1 (by simpa using hσ)
        have h2 : MDiffAt (T% (untransSection e σ' : Π y : M, TangentSpace I y)) x :=
          (mdifferentiableAt_transSection_iff e _ x).1 (by simpa using hσ')
        have hs : (untransSection e (σ + σ') : Π y : M, TangentSpace I y) =
            untransSection e σ + untransSection e σ' := funext fun y => map_add e.symm _ _
        have := cov.isCovariantDerivativeOn.add h1 h2
        ext v
        change e ((cov (untransSection e (σ + σ')) x) (e.symm v)) =
          e ((cov (untransSection e σ) x) (e.symm v)) + e ((cov (untransSection e σ') x) (e.symm v))
        rw [hs, this]
        exact map_add e _ _
      leibniz := by
        intro σ g x hσ hg _
        have h1 : MDiffAt (T% (untransSection e σ : Π y : M, TangentSpace I y)) x :=
          (mdifferentiableAt_transSection_iff e _ x).1 (by simpa using hσ)
        have hg' : MDiffAt g x := (mdifferentiableAt_transContinuousLinearEquiv_iff e).1 hg
        have hs : (untransSection e (g • σ) : Π y : M, TangentSpace I y) =
            g • untransSection e σ := funext fun y => map_smul e.symm _ _
        have := cov.isCovariantDerivativeOn.leibniz h1 hg'
        ext v
        have hv : (cov (g • untransSection e σ) x) (e.symm v) = g x • (cov (untransSection e σ) x) (e.symm v) +
            (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g x (e.symm v)) • (untransSection e σ x : TangentSpace I x) :=
          congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (e.symm v)) this
        change (show TangentSpace (I.transContinuousLinearEquiv e) x from e ((cov (untransSection e (g • σ)) x) (e.symm v))) =
          (show TangentSpace (I.transContinuousLinearEquiv e) x from g x • (show TangentSpace (I.transContinuousLinearEquiv e) x from e ((cov (untransSection e σ) x) (e.symm v)))) +
            (show TangentSpace (I.transContinuousLinearEquiv e) x from (show ℝ from mfderiv (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) g x v) • (show TangentSpace (I.transContinuousLinearEquiv e) x from σ x))
        rw [mfderiv_transContinuousLinearEquiv_real e hg', hs, hv]
        dsimp only
        refine (map_add e _ _).trans (congrArg₂ (· + ·) (map_smul e _ _) ?_)
        exact (map_smul e (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g x (e.symm v)) (untransSection e σ x : E)).trans <|
          congrArg (fun w : F => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g x (e.symm v)) • w)
          (e.apply_symm_apply (σ x))
        }

theorem transCov_apply (e : E ≃L[ℝ] F) (cov : Connection I M) (σ : Π y : M, TangentSpace I y) (x : M)
    (v : TangentSpace (I.transContinuousLinearEquiv e) x) :
    transCov e cov (transSection e σ) x v = e (cov σ x (e.symm v)) := by
  show e (cov (untransSection e (transSection e σ)) x (e.symm v)) = _
  rw [untransSection_transSection]

variable {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {H₂ : Type*} [TopologicalSpace H₂]
  {J : ModelWithCorners ℝ E₂ H₂} {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N]

theorem contMDiffAt_linEquiv_comp_iff (c : G ≃L[ℝ] G') {n : WithTop ℕ∞} (f : N → G) {p : N} :
    ContMDiffAt J 𝓘(ℝ, G') n (fun b => c (f b)) p ↔ ContMDiffAt J 𝓘(ℝ, G) n f p := by
  constructor
  · intro hf
    have h2 : ContMDiffAt 𝓘(ℝ, G') 𝓘(ℝ, G) n (c.symm : G' → G) (c (f p)) :=
      c.symm.contDiff.contMDiff.contMDiffAt
    exact (by simpa [Function.comp_def] using h2.comp p hf)
  · intro hf
    have h2 : ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, G') n (c : G → G') (f p) :=
      c.contDiff.contMDiff.contMDiffAt
    exact h2.comp p hf

theorem inCoordinates_trans (e : E ≃L[ℝ] F) (x₀ x : M) (hx : x ∈ (chartAt H x₀).source)
    (L : TangentSpace I x →L[ℝ] TangentSpace I x) :
    ContinuousLinearMap.inCoordinates F (TangentSpace (I.transContinuousLinearEquiv e)) F
      (TangentSpace (I.transContinuousLinearEquiv e)) x₀ x x₀ x ((e : E →L[ℝ] F).comp (L.comp (e.symm : F →L[ℝ] E))) =
    (e.arrowCongr e) (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x L) := by
  unfold ContinuousLinearMap.inCoordinates
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
    TangentBundle.symmL_trivializationAt_eq_core hx,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hx,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hx]
  ext v
  have h1 : ∀ a b : M, (tangentBundleCore (I.transContinuousLinearEquiv e) M).coordChange (achart H a) (achart H b) x =
      (tangentCoordChange (I.transContinuousLinearEquiv e) a b x : F →L[ℝ] F) := fun a b => rfl
  have h2 : ∀ a b : M, (tangentBundleCore I M).coordChange (achart H a) (achart H b) x =
      (tangentCoordChange I a b x : E →L[ℝ] E) := fun a b => rfl
  rw [h1, h1, h2, h2]
  change tangentCoordChange (I.transContinuousLinearEquiv e) x x₀ x (e (L (e.symm (tangentCoordChange
      (I.transContinuousLinearEquiv e) x₀ x x v)))) =
    e (tangentCoordChange I x x₀ x (L (tangentCoordChange I x₀ x x (e.symm v))))
  rw [tangentCoordChange_transContinuousLinearEquiv, tangentCoordChange_transContinuousLinearEquiv]
  erw [e.symm_apply_apply, e.symm_apply_apply]

/-- **Smoothness of a field of endomorphisms of the tangent spaces is unchanged by the transport.** -/
theorem contMDiffAt_endSection_trans_iff (e : E ≃L[ℝ] F) {n : WithTop ℕ∞}
    (ψ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) {x : M} :
    ContMDiffAt (I.transContinuousLinearEquiv e) ((I.transContinuousLinearEquiv e).prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y => (⟨y, (e : E →L[ℝ] F).comp ((ψ y).comp (e.symm : F →L[ℝ] E))⟩ :
        TotalSpace (F →L[ℝ] F) (fun y : M => TangentSpace (I.transContinuousLinearEquiv e) y →L[ℝ]
          TangentSpace (I.transContinuousLinearEquiv e) y))) x ↔
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => (⟨y, ψ y⟩ : TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) x := by
  rw [contMDiffAt_hom_bundle, contMDiffAt_hom_bundle]
  refine and_congr ?_ ?_
  · exact ⟨fun _ => contMDiffAt_id, fun _ => contMDiffAt_id⟩
  · have hev : (fun y : M => ContinuousLinearMap.inCoordinates F (TangentSpace (I.transContinuousLinearEquiv e)) F
        (TangentSpace (I.transContinuousLinearEquiv e)) x y x y ((e : E →L[ℝ] F).comp ((ψ y).comp (e.symm : F →L[ℝ] E)))) =ᶠ[nhds x]
        fun y => (e.arrowCongr e) (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x y x y (ψ y)) := by
      filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
      exact inCoordinates_trans e x y hy (ψ y)
    refine (hev.contMDiffAt_iff).trans ?_
    rw [contMDiffAt_linEquiv_comp_iff (e.arrowCongr e) (fun y => ContinuousLinearMap.inCoordinates E (TangentSpace I) E
      (TangentSpace I) x y x y (ψ y)) (J := I.transContinuousLinearEquiv e)]
    exact contMDiffAt_transContinuousLinearEquiv_iff e

/-- **The transported connection is locally smooth when the connection is.** -/
theorem locallySmoothConnectionW_transCov [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 2 M] (e : E ≃L[ℝ] F) (cov : Connection I M)
    [LocallySmoothConnectionW cov] : LocallySmoothConnectionW (transCov e cov) where
  contMDiffAt := by
    intro σ x hσ
    have hσ' : ∀ᶠ y in nhds x, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun q : M => (⟨q, (untransSection e σ : Π y : M, TangentSpace I y) q⟩ : TangentBundle I M)) y := by
      filter_upwards [hσ] with y hy
      have h := (contMDiffAt_transSection_iff e (untransSection e σ : Π y : M, TangentSpace I y) (n := ∞) y).1
      rw [transSection_untransSection] at h
      exact h hy
    have h1 := contMDiffAt_covW cov hσ'
    have h2 := (contMDiffAt_endSection_trans_iff e (n := ∞) (fun y => cov (untransSection e σ : Π y : M, TangentSpace I y) y)
      (x := x)).2 h1
    exact h2

end Lightlike

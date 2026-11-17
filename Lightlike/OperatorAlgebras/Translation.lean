import Lightlike.OperatorAlgebras.UnitaryGroup
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The translation group on `L²(ℝ)`

`(U t ψ)(x) = ψ(x + t)` on `Lp ℂ 2 volume` is a strongly continuous one-parameter unitary group
(`translationGroup`). Its generator is `-i d/dx` on `C²` functions with compact support (`translationGroup_generator_ofCS` in
`Lightlike/OperatorAlgebras/GeneratorTranslation.lean`), so `translationGroup` is the group `exp (i t P)` for
the momentum `P = -i d/dx`.

Strong continuity comes from Mathlib's `Continuous.compMeasurePreservingLp`.
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras

/-- The Hilbert space `L²(ℝ)` of complex functions. -/
abbrev L2R : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- Translation by `t` as a measure-preserving map `x ↦ x + t` of `ℝ`. -/
lemma measurePreserving_shift (t : ℝ) : MeasurePreserving (fun x : ℝ => x + t) volume volume :=
  measurePreserving_add_right volume t

/-- The shift `ψ ↦ ψ(· + t)` on `L²(ℝ)` as a linear isometry. -/
noncomputable def shiftL (t : ℝ) : L2R →ₗᵢ[ℂ] L2R :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + t) (measurePreserving_shift t)

private lemma comp_congr {f g : ℝ → ℝ} (hf : MeasurePreserving f volume volume)
    (hg : MeasurePreserving g volume volume) (h : f = g) (ψ : L2R) :
    Lp.compMeasurePreserving f hf ψ = Lp.compMeasurePreserving g hg ψ := by
  subst h; rfl

private lemma shiftL_apply (t : ℝ) (ψ : L2R) :
    shiftL t ψ = Lp.compMeasurePreserving (fun x : ℝ => x + t) (measurePreserving_shift t) ψ := rfl

private lemma shift_comp (s t : ℝ) (ψ : L2R) :
    shiftL s (shiftL t ψ) = shiftL (s + t) ψ := by
  rw [shiftL_apply, shiftL_apply, shiftL_apply,
    ← Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) ψ (measurePreserving_shift t)
      (measurePreserving_shift s)]
  exact comp_congr _ _ (funext fun x => by simp; ring) ψ

private lemma shift_zero (ψ : L2R) : shiftL 0 ψ = ψ := by
  rw [shiftL_apply, comp_congr (measurePreserving_shift 0) (MeasurePreserving.id volume)
    (funext fun x => by simp) ψ]
  exact Lp.compMeasurePreserving_id_apply ψ

private lemma shift_cancel (s t : ℝ) (h : s + t = 0) (ψ : L2R) :
    shiftL s (shiftL t ψ) = ψ := by
  rw [shift_comp, h]; exact shift_zero ψ

/-- **The translation group on `L²(ℝ)`**: `(U t ψ)(x) = ψ(x + t)`. -/
noncomputable def translationGroup : UnitaryGroup L2R where
  toFun t :=
    { toLinearMap := (shiftL t).toLinearMap
      invFun := fun ψ => shiftL (-t) ψ
      left_inv := fun ψ => shift_cancel (-t) t (by ring) ψ
      right_inv := fun ψ => shift_cancel t (-t) (by ring) ψ
      norm_map' := (shiftL t).norm_map }
  map_zero' := LinearIsometryEquiv.ext fun ψ => shift_zero ψ
  map_add' := fun s t => LinearIsometryEquiv.ext fun ψ => (shift_comp s t ψ).symm
  continuous' := by
    intro ψ
    let g : ℝ → C(ℝ, ℝ) := fun t => ⟨fun x => x + t, continuous_id.add continuous_const⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.add continuous_fst)
    exact Continuous.compMeasurePreservingLp (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (f := fun _ : ℝ => ψ) continuous_const hg (fun t => measurePreserving_shift t) (by norm_num)

end Lightlike.OperatorAlgebras

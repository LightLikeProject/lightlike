import Mathlib
import Lightlike.Rows.G1_059.GreenOperator

/-!
# The `1+1` Minkowski model for the Green operators

Null coordinates `(u, v) = (t + x, t - x)` on `ℝ × ℝ`; the wave operator is `P = ∂_v ∂_u` (up to the
constant factor 4 in `□ = 4 ∂_u ∂_v`), the causal future of a set `S` is
`J⁺ S = {p | ∃ s ∈ S, s.1 ≤ p.1 ∧ s.2 ≤ p.2}` and the causal past `J⁻ S` is the reflected set.
The retarded Green operator is the convolution with the indicator `Q` of the closed quadrant
`{0 ≤ u, 0 ≤ v}`: `(G⁺ f)(u, v) = ∫_{a ≤ u, b ≤ v} f(a, b)`.

## Main definitions

* `Lightlike.Rows.G1_059.smoothFns`, `testFns`: smooth functions, and smooth compactly supported
  functions on `ℝ × ℝ`.
* `Lightlike.Rows.G1_059.wave`: the operator `P = ∂_v ∂_u` on smooth functions.
* `Lightlike.Rows.G1_059.retarded`: the retarded Green operator `f ↦ f ⋆ Q`.
-/

open Function MeasureTheory Set
open scoped ContDiff Convolution

namespace Lightlike.Rows.G1_059

/-- Smooth functions on `ℝ × ℝ` (null coordinates of `1+1` Minkowski space). -/
def smoothFns : Submodule ℝ (ℝ × ℝ → ℝ) where
  carrier := {g | ContDiff ℝ ∞ g}
  add_mem' := fun {a b} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) => ha.add hb
  zero_mem' := (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ × ℝ => (0 : ℝ))
  smul_mem' := fun c g (hg : ContDiff ℝ ∞ g) => (contDiff_const.smul hg : ContDiff ℝ ∞ (c • g))

/-- Smooth compactly supported functions on `ℝ × ℝ` (test functions). -/
def testFns : Submodule ℝ (ℝ × ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun _c _ hg => ⟨contDiff_const.smul hg.1, hg.2.smul_left⟩

theorem testFns_le : testFns ≤ smoothFns := fun _ hf => hf.1

/-- The indicator of the closed quadrant `{0 ≤ u, 0 ≤ v}`. -/
noncomputable def quadrant : ℝ × ℝ → ℝ :=
  Set.indicator {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} 1

theorem quadrant_locInt : LocallyIntegrable quadrant (volume : Measure (ℝ × ℝ)) := by
  have hm : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  exact (locallyIntegrable_const (1 : ℝ)).indicator hm

/-- The retarded convolution `f ↦ f ⋆ Q`, i.e. `(u, v) ↦ ∫_{a ≤ u, b ≤ v} f (a, b)`, on smooth
compactly supported `f`. -/
noncomputable def retardedFun (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℝ] quadrant

theorem retardedFun_smooth {f : ℝ × ℝ → ℝ} (hf : f ∈ testFns) :
    ContDiff ℝ ∞ (retardedFun f) :=
  hf.2.contDiff_convolution_left _ hf.1 quadrant_locInt

/-- The directional derivative `∂_w g = fderiv g · w` of a smooth function is smooth. -/
theorem contDiff_dirDeriv {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (w : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ g p w) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem diffAt_smooth (g : smoothFns) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (g : ℝ × ℝ → ℝ) p :=
  (show ContDiff ℝ ∞ (g : ℝ × ℝ → ℝ) from g.2).differentiable (by simp) p

/-- The directional derivative `∂_w` as a linear map on smooth functions. -/
noncomputable def dirDeriv (w : ℝ × ℝ) : smoothFns →ₗ[ℝ] smoothFns where
  toFun g := ⟨fun p => fderiv ℝ (g : ℝ × ℝ → ℝ) p w, contDiff_dirDeriv g.2 w⟩
  map_add' g h := by
    apply Subtype.ext
    funext p
    have hg := diffAt_smooth g p
    have hh := diffAt_smooth h p
    show fderiv ℝ ((g : ℝ × ℝ → ℝ) + (h : ℝ × ℝ → ℝ)) p w = _
    rw [fderiv_add hg hh]
    rfl
  map_smul' c g := by
    apply Subtype.ext
    funext p
    show fderiv ℝ (c • (g : ℝ × ℝ → ℝ)) p w = _
    rw [fderiv_const_smul (diffAt_smooth g p)]
    rfl

/-- The wave operator `P = ∂_v ∂_u` (the constant `1/4` times the d'Alembertian) on smooth
functions of the null coordinates `(u, v)`. -/
noncomputable def wave : smoothFns →ₗ[ℝ] smoothFns := dirDeriv (0, 1) ∘ₗ dirDeriv (1, 0)

end Lightlike.Rows.G1_059

import Mathlib

/-!
# The flat torus `(ℝ/ℤ)ⁿ` as a smooth manifold modelled on `ℝⁿ`

`FlatTorus n = Fin n → AddCircle 1` with the charts `torusChart a`, the products of the inverses of the quotient map
`ℝ → ℝ/ℤ` on the intervals `(aᵢ, aᵢ + 1)` (`AddCircle.openPartialHomeomorphCoe`). The chart at `x` is centred so
that `x` is half a period away from the cut. The chart changes are, near every point, translations by an integer
vector (`toIcoDiv` is locally constant away from the cut, `eventuallyEq_toIcoDiv_nhds`), so they are smooth and the
torus is a smooth manifold modelled on `𝓘(ℝ, Fin n → ℝ)` (`FlatTorus.isManifold`). It is compact and Hausdorff
(Mathlib's instances for `AddCircle` and finite products).

This is the compact manifold modelled on `Fin n → ℝ` on which the heat-trace layer is checked: Mathlib's `Circle` and
spheres are modelled on `EuclideanSpace ℝ (Fin n)`, which the volume layer (`Lightlike.NondegMetric.volumeMeasure`) does
not use.
-/

open Set Manifold Topology Filter
open scoped ContDiff

noncomputable section

namespace Lightlike

/-- The flat torus `(ℝ/ℤ)ⁿ`. -/
abbrev FlatTorus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

namespace FlatTorus

/-- The period `1` is positive (named, so that it does not clash with the same instance in other files). -/
instance fact_zero_lt_one : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

variable {n : ℕ}

/-- The chart of the circle cut at `a`: the inverse of `ℝ → ℝ/ℤ` on `(a, a + 1)`. -/
def circleChart (a : ℝ) : OpenPartialHomeomorph (AddCircle (1 : ℝ)) ℝ :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).symm

theorem circleChart_source (a : ℝ) : (circleChart a).source = {(a : AddCircle (1 : ℝ))}ᶜ := rfl

theorem circleChart_target (a : ℝ) : (circleChart a).target = Ioo a (a + 1) := rfl

theorem circleChart_symm_apply (a y : ℝ) : (circleChart a).symm y = (y : AddCircle (1 : ℝ)) := rfl

theorem circleChart_coe (a y : ℝ) : circleChart a (y : AddCircle (1 : ℝ)) = toIcoMod one_pos a y := by
  change ((AddCircle.equivIco 1 a (y : AddCircle (1 : ℝ)) : ℝ)) = _
  simp [AddCircle.equivIco, QuotientAddGroup.equivIcoMod_coe]

/-- The chart of the torus cut at `a`. -/
def torusChart (a : Fin n → ℝ) : OpenPartialHomeomorph (FlatTorus n) (Fin n → ℝ) :=
  OpenPartialHomeomorph.pi fun i => circleChart (a i)

/-- The cut of the chart at `x`: half a period away from `x`. -/
def cutAt (x : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco 1 0 x : ℝ) + 1 / 2

theorem ne_cutAt (x : AddCircle (1 : ℝ)) : x ≠ (cutAt x : AddCircle (1 : ℝ)) := by
  intro h
  have h1 : ((AddCircle.equivIco 1 0 x : ℝ) : AddCircle (1 : ℝ)) = x := AddCircle.coe_equivIco
  rw [cutAt, AddCircle.coe_add, h1] at h
  have h2 : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    have := congrArg (· - x) h
    simpa using this.symm
  rw [AddCircle.coe_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  simp only [zsmul_eq_mul, mul_one] at hk
  have : (2 : ℝ) * k = 1 := by linarith
  have hk' : (2 * k : ℤ) = 1 := by exact_mod_cast this
  omega

instance : ChartedSpace (Fin n → ℝ) (FlatTorus n) where
  atlas := range torusChart
  chartAt x := torusChart fun i => cutAt (x i)
  mem_chart_source x := by
    simp only [torusChart, OpenPartialHomeomorph.pi, PartialEquiv.pi, Set.mem_univ_pi]
    intro i
    exact ne_cutAt (x i)
  chart_mem_atlas x := ⟨_, rfl⟩

/-- **The chart changes of the torus are smooth**: near every point of its domain the chart change from the cut `a`
to the cut `b` is the translation `y ↦ y - k` by an integer vector `k`. -/
theorem contDiffOn_chartChange (a b : Fin n → ℝ) :
    ContDiffOn ℝ ∞ ((torusChart a).symm ≫ₕ torusChart b) ((torusChart a).symm ≫ₕ torusChart b).source := by
  intro y hy
  have hyb : ∀ i, (y i : AddCircle (1 : ℝ)) ≠ (b i : AddCircle (1 : ℝ)) := by
    intro i
    have := hy.2
    simp only [mem_preimage, torusChart, OpenPartialHomeomorph.pi, PartialEquiv.pi, Set.mem_univ_pi] at this
    exact this i
  have hmod : ∀ i, ¬ y i ≡ b i [PMOD (1 : ℝ)] := fun i =>
    AddCommGroup.not_modEq_iff_ne_mod_zmultiples.2 (hyb i)
  have hev : ∀ i, (fun z : Fin n → ℝ => toIcoMod one_pos (b i) (z i)) =ᶠ[𝓝 y]
      fun z => z i - (toIcoDiv one_pos (b i) (y i) : ℝ) := by
    intro i
    have h := (eventuallyEq_toIcoDiv_nhds one_pos (b i) (hmod i))
    have hc : Tendsto (fun z : Fin n → ℝ => z i) (𝓝 y) (𝓝 (y i)) := (continuous_apply i).tendsto y
    filter_upwards [hc.eventually h] with z hz
    rw [← self_sub_toIcoDiv_zsmul, hz]
    simp
  have hfun : ((torusChart a).symm ≫ₕ torusChart b) = fun z : Fin n → ℝ => fun i => toIcoMod one_pos (b i) (z i) := by
    funext z i
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, torusChart,
      OpenPartialHomeomorph.pi_symm_apply, OpenPartialHomeomorph.pi_apply, circleChart_symm_apply, circleChart_coe]
  rw [hfun]
  refine ContDiffAt.contDiffWithinAt ?_
  rw [contDiffAt_pi]
  intro i
  refine ContDiffAt.congr_of_eventuallyEq ?_ (hev i)
  exact ((contDiff_apply ℝ (fun _ : Fin n => ℝ) i).sub contDiff_const).contDiffAt

instance isManifold : IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ (FlatTorus n) := by
  refine isManifold_of_contDiffOn 𝓘(ℝ, Fin n → ℝ) ∞ (FlatTorus n) fun e e' he he' => ?_
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  simpa using contDiffOn_chartChange a b

example : CompactSpace (FlatTorus n) := inferInstance
example : T2Space (FlatTorus n) := inferInstance
example : SecondCountableTopology (FlatTorus n) := inferInstance

end FlatTorus

end Lightlike

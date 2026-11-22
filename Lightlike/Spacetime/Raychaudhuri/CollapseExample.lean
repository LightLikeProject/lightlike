import Lightlike.Spacetime.Raychaudhuri.ComovingCov
import Lightlike.Spacetime.Raychaudhuri.DustField
import Lightlike.Spacetime.Raychaudhuri.CollapseDust
import Lightlike.Spacetime.Raychaudhuri.FocusingSEC

/-!
# Non-vacuity of the focusing theorem: the collapsing dust universe on the manifold (GE3)

For `c > 0` the manifold `flrwOpen` over `I = (-∞, c)` with `a t = (c - t)^(2/3)`, `k = 0`, dust of density
`1 / (6 π G (c - t)²)`, satisfies every hypothesis of `raychaudhuri_focusing_strongEC` with the comoving field `V = ∂_t`
and the curve `γ s = (s, 0, 0, 0)` on `[0, c/2)`: Einstein's equations (through `collapse_friedmann`), the strong energy
condition of dust, `∇_V V = 0`, `g(V, V) = -1`, rotation-free, and `Θ = -2/c < 0` at `γ 0`.
`collapse_focusing_example` states the conclusion `c/2 ≤ 3/|Θ| = 3c/2`.

**Limits.** One congruence in one example; the final inequality is the conclusion of the general theorem, not a sharp
value (the actual blow-up is at `s = c`).
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

/-- A curve in an open subset of `ℝ⁴` whose coordinates have a derivative has the same manifold derivative. -/
theorem hasMFDerivAt_opens_of_coe {U : Opens (Fin 4 → ℝ)} {γ : ℝ → U} {s : ℝ} {f' : ℝ →L[ℝ] (Fin 4 → ℝ)}
    (h : HasFDerivAt (fun s => (γ s : Fin 4 → ℝ)) f' s) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s f' := by
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.2 h.continuousAt, ?_⟩
  have e : (extChartAt 𝓘(ℝ, Fin 4 → ℝ) (γ s)) ∘ γ = fun s => (γ s : Fin 4 → ℝ) :=
    funext fun t => opens_extChartAt_apply U (γ s) (γ t)
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.comp_id, PartialEquiv.refl_symm]
  rw [e]
  exact h.hasFDerivWithinAt

namespace Cosmology

variable (c : ℝ)

theorem collapse_contDiffOn : ContDiffOn ℝ ∞ (collapseA c) (Iio c) := fun _ ht =>
  ((contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne (n := ∞) (p := (2 / 3 : ℝ))
    (sub_pos.2 ht).ne').contDiffWithinAt

/-- The point `(min s (c/2), 0, 0, 0)` of the chart domain. -/
def collapsePt (hc : 0 < c) (s : ℝ) : flrwOpen (I := Iio c) isOpen_Iio (k := 0) :=
  ⟨Pi.single 0 (min s (c / 2)), by
    refine ⟨?_, ?_⟩
    · simp only [Pi.single_eq_same, mem_Iio]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · simp [spatialNormSq]⟩

end Cosmology

variable {c : ℝ}

/-- **The collapsing dust universe meets all the hypotheses of the focusing theorem**: `Θ = -2/c` at `γ 0`, and the
conclusion `c/2 ≤ 3/|Θ|` of `raychaudhuri_focusing_strongEC` holds for the curve on `[0, c/2)`. -/
theorem collapse_focusing_example {Gn : ℝ} (hG : 0 < Gn) (hc : 0 < c)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0)))
    [LocallySmoothConnection cov] [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) (fun _ ht => Cosmology.collapseA_pos c ht) 0).toNondegMetric) :
    ∃ γ : ℝ → Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0),
      expansionM cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) (γ 0) = -2 / c ∧
        c / 2 ≤ 3 / |expansionM cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) (γ 0)| := by
  have hcpos := fun t (ht : t ∈ Iio c) => Cosmology.collapseA_pos c ht
  have hE : (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) hcpos 0).toNondegMetric.EinsteinEq cov 0 (8 * Real.pi * Gn)
      (fun x v w => matForm (Matrix.of fun μ ν => Cosmology.perfectFluid (Cosmology.collapseRho Gn c)
        (fun _ => 0) (Cosmology.flrwMetric (Cosmology.collapseA c) 0) μ ν x.1) v w) := by
    rw [Cosmology.flrwManifold_einstein_iff_friedmann isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0 cov h]
    exact fun t ht => Cosmology.collapse_friedmann hG c ht
  have hS := flrwManifold_dust_strongEC isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0
    (Cosmology.collapseRho Gn c) (fun t ht => by
      unfold Cosmology.collapseRho
      have : 0 < c - t := sub_pos.2 ht
      positivity)
  have hΘ : expansionM cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) (Cosmology.collapsePt c hc 0) = -2 / c := by
    rw [flrwManifold_comoving_expansion isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0 cov h]
    have h0 : ((Cosmology.collapsePt c hc 0 : Fin 4 → ℝ) 0) = 0 := by
      simp [Cosmology.collapsePt]
      linarith
    rw [h0, Cosmology.collapseA_hubble c hc]
    field_simp
    ring
  refine ⟨Cosmology.collapsePt c hc, ?_, ?_⟩
  · exact hΘ
  · have hlt : expansionM cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) (Cosmology.collapsePt c hc 0) < 0 := by
      rw [hΘ]; exact div_neg_of_neg_of_pos (by norm_num) hc
    refine raychaudhuri_focusing_strongEC (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) hcpos 0) cov h (κ := 8 * Real.pi * Gn) (by positivity) hE hS
      (V := fun _ => (Pi.single 0 1 : Fin 4 → ℝ))
      (contMDiff_constField (U := Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0)) (Pi.single 0 1))
      (γ := Cosmology.collapsePt c hc) (L := c / 2) ?_ ?_ ?_ ?_ hlt
    · intro s hs
      refine hasMFDerivAt_opens_of_coe ?_
      have h1 : HasFDerivAt (fun s : ℝ => (Pi.single 0 s : Fin 4 → ℝ))
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single 0 1 : Fin 4 → ℝ)) s := by
        have := (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ) 0).hasFDerivAt (x := s)
        have e : (1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single 0 1 : Fin 4 → ℝ) =
            ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ) 0 := by
          ext
          simp
        rw [e]
        exact this
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hs.2] with t ht
      simp [Cosmology.collapsePt, min_eq_left (show t < c / 2 from ht).le]
    · exact fun s _ => Filter.Eventually.of_forall fun q => flrwManifold_comoving_geodesic isOpen_Iio
        (Cosmology.collapse_contDiffOn c) hcpos 0 cov h q
    · exact fun s _ => Filter.Eventually.of_forall fun q => flrwManifold_comoving_unit isOpen_Iio
        (Cosmology.collapse_contDiffOn c) hcpos 0 q
    · exact fun s _ u w => flrwManifold_comoving_rotationFree isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0
        cov h _ u w

end Lightlike

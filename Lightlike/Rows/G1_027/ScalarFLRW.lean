module

public import Lightlike.Cosmology.FLRW

/-!
# The scalar field in FLRW: the stress tensor of a homogeneous field (row G1-027, milestone CO29)

For a scalar field `Φ` with potential `V` on a coordinate metric `g`, the stress-energy tensor is
`T_{μν} = ∂_μ Φ ∂_ν Φ − (½ g^{αβ} ∂_α Φ ∂_β Φ + V(Φ)) g_{μν}`. For a homogeneous field `Φ = φ(t)` on
the FLRW metric of `Lightlike.Cosmology.flrwMetric` it is the perfect fluid at rest with
`ρ = φ̇²/2 + V(φ)` and `p = φ̇²/2 − V(φ)`.

Main results
* `Lightlike.Cosmology.scalarStress`: the stress tensor of a scalar field in a chart.
* `Lightlike.Cosmology.scalarStress_flrw`: for a homogeneous field it is `perfectFluid ρ p`.

Source: Baumann, *TASI lectures on inflation* (`baumann-2009`), eq. (A.140) for the equations of
motion; the tensor is Carroll, gr-qc/9712019, eq. (1.112).
-/

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

namespace Cosmology

/-- The stress-energy tensor of a scalar field `Φ` with potential `V` in a chart with metric `g`:
`T_{μν} = ∂_μ Φ ∂_ν Φ − (½ g^{αβ} ∂_α Φ ∂_β Φ + V(Φ)) g_{μν}`. -/
def scalarStress (Φ : (Fin 4 → ℝ) → ℝ) (V : ℝ → ℝ)
    (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  pd μ Φ x * pd ν Φ x -
    (1 / 2 * ∑ α : Fin 4, ∑ β : Fin 4, (g x)⁻¹ α β * pd α Φ x * pd β Φ x + V (Φ x)) * g x μ ν

/-- The energy density `φ̇²/2 + V(φ)` of a homogeneous scalar field. -/
def scalarRho (φ V : ℝ → ℝ) (t : ℝ) : ℝ := deriv φ t ^ 2 / 2 + V (φ t)

/-- The pressure `φ̇²/2 − V(φ)` of a homogeneous scalar field. -/
def scalarP (φ V : ℝ → ℝ) (t : ℝ) : ℝ := deriv φ t ^ 2 / 2 - V (φ t)

/-- **A homogeneous scalar field on the FLRW metric is a perfect fluid at rest**, with density
`φ̇²/2 + V(φ)` and pressure `φ̇²/2 − V(φ)`, at every point where `φ` is differentiable in time. -/
theorem scalarStress_flrw {φ V : ℝ → ℝ} {a : ℝ → ℝ} {k : ℝ} {x : Fin 4 → ℝ}
    (hφ : DifferentiableAt ℝ φ (x 0)) (ha : a (x 0) ≠ 0)
    (hD : 0 < 1 + k * spatialNormSq x / 4) (μ ν : Fin 4) :
    scalarStress (fun y => φ (y 0)) V (flrwMetric a k) μ ν x =
      perfectFluid (scalarRho φ V) (scalarP φ V) (flrwMetric a k) μ ν x := by
  have hp : ∀ j : Fin 4, pd j (fun y : Fin 4 → ℝ => φ (y 0)) x
      = if j = 0 then deriv φ (x 0) else 0 := fun j => (hasPd_comp0 (j := j) hφ).2
  have hinv : (flrwMetric a k x)⁻¹ = Matrix.diagonal (fun i : Fin 4 =>
      (if i = 0 then (-1 : ℝ) else (a (x 0) / (1 + k * spatialNormSq x / 4)) ^ 2)⁻¹) :=
    inv_diag' _ (fun i => by
      split_ifs
      · norm_num
      · exact pow_ne_zero 2 (div_ne_zero ha hD.ne'))
  unfold scalarStress perfectFluid scalarRho scalarP
  rw [hinv]
  simp only [hp, flrwMetric, Fin.sum_univ_four, Matrix.diagonal_apply]
  fin_cases μ <;> fin_cases ν <;> simp <;> ring

/-- The Klein–Gordon equation `φ̈ + 3Hφ̇ + V′(φ) = 0` for a homogeneous field on the FLRW
background with scale factor `a`, `H = ȧ/a`, at time `t`. -/
def IsKG (a φ V : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (deriv φ) t + 3 * (deriv a t / a t) * deriv φ t + deriv V (φ t) = 0

/-- The time derivative of the energy density `φ̇²/2 + V(φ)` is `φ̇ (φ̈ + V′(φ))`. -/
theorem hasDerivAt_scalarRho {φ V : ℝ → ℝ} {t : ℝ} (hφ : DifferentiableAt ℝ φ t)
    (hφ' : DifferentiableAt ℝ (deriv φ) t) (hV : DifferentiableAt ℝ V (φ t)) :
    HasDerivAt (scalarRho φ V) (deriv φ t * (deriv (deriv φ) t + deriv V (φ t))) t := by
  have h1 := (hφ'.hasDerivAt.pow 2).div_const 2
  have h2 : HasDerivAt (fun s => V (φ s)) (deriv V (φ t) * deriv φ t) t :=
    hV.hasDerivAt.comp t hφ.hasDerivAt
  have := h1.add h2
  unfold scalarRho
  convert this using 1
  norm_num
  ring

/-- **Second Friedmann equation from the first and Klein–Gordon.** On an open set where the first
Friedmann equation holds with `ρ = φ̇²/2 + V(φ)` and the Klein–Gordon equation holds, the second
equation (with `p = φ̇²/2 − V(φ)`) holds at every `t` with `ȧ(t) ≠ 0`. -/
theorem second_of_first_kg {I : Set ℝ} (hI : IsOpen I) {a φ V : ℝ → ℝ} (k Λ Gn : ℝ)
    (hpos : ∀ t ∈ I, 0 < a t) (ha : ∀ t ∈ I, DifferentiableAt ℝ a t)
    (ha' : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t)
    (hφ : ∀ t ∈ I, DifferentiableAt ℝ φ t) (hφ' : ∀ t ∈ I, DifferentiableAt ℝ (deriv φ) t)
    (hV : ∀ t ∈ I, DifferentiableAt ℝ V (φ t))
    (h1 : ∀ t ∈ I, FirstFriedmann a (scalarRho φ V) k Λ Gn t)
    (hkg : ∀ t ∈ I, IsKG a φ V t) {t : ℝ} (ht : t ∈ I) (hadot : deriv a t ≠ 0) :
    SecondFriedmann a (scalarRho φ V) (scalarP φ V) Λ Gn t := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 8 * Real.pi * Gn / 3 := ⟨_, rfl⟩
  have hA : a t ≠ 0 := (hpos t ht).ne'
  have hAt : HasDerivAt a (deriv a t) t := (ha t ht).hasDerivAt
  have hBt : HasDerivAt (deriv a) (deriv (deriv a) t) t := (ha' t ht).hasDerivAt
  have hu : HasDerivAt (fun s => deriv a s / a s)
      ((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2) t := hBt.div hAt hA
  have h3 : HasDerivAt (fun s => (deriv a s / a s) ^ 2)
      (2 * (deriv a t / a t) * ((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2)) t := by
    have := (hasDerivAt_pow 2 (deriv a t / a t)).comp t hu
    exact this.congr_deriv (by simp)
  have hq : HasDerivAt (fun s => k / a s ^ 2) (-(2 * k * deriv a t) / a t ^ 3) t := by
    have := (hasDerivAt_const t k).div (hAt.pow 2) (pow_ne_zero 2 hA)
    convert this using 1
    simp only [Pi.pow_apply]
    field_simp
    try ring
  have hr := h3.add hq
  have hρ := hasDerivAt_scalarRho (hφ t ht) (hφ' t ht) (hV t ht)
  have hcr := hρ.const_mul c
  have hev : (fun s => (deriv a s / a s) ^ 2 + k / a s ^ 2 - Λ / 3) =ᶠ[nhds t]
      fun s => c * scalarRho φ V s := by
    filter_upwards [hI.mem_nhds ht] with s hs
    have := h1 s hs
    simp only [FirstFriedmann] at this
    rw [hc]
    linarith
  have hd := hcr.congr_of_eventuallyEq hev
  have hd2 := hr.sub_const (Λ / 3)
  have key := hd.unique hd2
  have key2 : c * (deriv φ t * (deriv (deriv φ) t + deriv V (φ t))) =
      2 * (deriv a t / a t) * (deriv (deriv a) t / a t - (deriv a t / a t) ^ 2)
        - 2 * k * (deriv a t / a t) / a t ^ 2 := by
    rw [key]; field_simp
    try ring
  have hk : deriv (deriv φ) t + deriv V (φ t) = -3 * (deriv a t / a t) * deriv φ t := by
    have := hkg t ht
    unfold IsKG at this
    linarith
  rw [hk] at key2
  have hH : deriv a t / a t ≠ 0 := div_ne_zero hadot hA
  have e3 : (deriv a t / a t) * (2 * (deriv (deriv a) t / a t - (deriv a t / a t) ^ 2)
      - 2 * k / a t ^ 2 + 3 * c * deriv φ t ^ 2) = 0 := by
    linear_combination (-1 : ℝ) * key2
  have e4 := (mul_eq_zero.1 e3).resolve_left hH
  have e1 := h1 t ht
  simp only [FirstFriedmann, scalarRho] at e1
  unfold SecondFriedmann scalarRho scalarP
  have e5 : 4 * Real.pi * Gn / 3 = c / 2 := by rw [hc]; ring
  rw [e5]
  rw [← hc] at e1
  linear_combination (1 / 2 : ℝ) * e4 + e1

/-- Einstein's equations for the scalar-field stress tensor on the chart are the same as those for
the perfect fluid `(scalarRho, scalarP)`, when `φ` is differentiable and `a > 0` on `I`. -/
theorem isEinsteinSolution_scalar_iff {I : Set ℝ} {a φ V : ℝ → ℝ} (k Λ Gn : ℝ)
    (hpos : ∀ t ∈ I, 0 < a t) (hφ : ∀ t ∈ I, DifferentiableAt ℝ φ t) :
    IsEinsteinSolution Λ Gn (flrwMetric a k)
        (scalarStress (fun y => φ (y 0)) V (flrwMetric a k)) (flrwDomain I k) ↔
      IsEinsteinSolution Λ Gn (flrwMetric a k)
        (perfectFluid (scalarRho φ V) (scalarP φ V) (flrwMetric a k)) (flrwDomain I k) := by
  have h : ∀ x ∈ flrwDomain I k, ∀ μ ν,
      scalarStress (fun y => φ (y 0)) V (flrwMetric a k) μ ν x =
        perfectFluid (scalarRho φ V) (scalarP φ V) (flrwMetric a k) μ ν x := fun x hx μ ν =>
    scalarStress_flrw (hφ _ hx.1) (hpos _ hx.1).ne' hx.2 μ ν
  unfold IsEinsteinSolution
  refine and_congr Iff.rfl (forall₂_congr fun x hx => forall₂_congr fun μ ν => ?_)
  rw [h x hx μ ν]

/-- **CO29.** For a homogeneous scalar field `φ(t)` with potential `V` on the FLRW metric of
`flrwMetric`, with `a > 0`, `a`, `φ` smooth on the open interval `I`, `V` differentiable and
`ȧ ≠ 0` on `I` (the caveat of CO1 for the converse direction), Einstein's equations with the scalar
stress tensor together with the Klein–Gordon equation hold on the chart iff the first Friedmann
equation with `ρ = φ̇²/2 + V(φ)` together with the Klein–Gordon equation hold at every `t ∈ I`.
By `scalarStress_flrw` the field is a perfect fluid with `p = φ̇²/2 − V(φ)`.
Source: `baumann-2009`, eq. (A.140). -/
theorem scalar_einstein_iff {I : Set ℝ} (hI : IsOpen I) {a φ V : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a I) (hφ : ContDiffOn ℝ ∞ φ I) (hV : Differentiable ℝ V)
    (hpos : ∀ t ∈ I, 0 < a t) (hadot : ∀ t ∈ I, deriv a t ≠ 0) (k Λ Gn : ℝ) :
    (IsEinsteinSolution Λ Gn (flrwMetric a k)
        (scalarStress (fun y => φ (y 0)) V (flrwMetric a k)) (flrwDomain I k) ∧
      ∀ t ∈ I, IsKG a φ V t) ↔
    ((∀ t ∈ I, FirstFriedmann a (scalarRho φ V) k Λ Gn t) ∧ ∀ t ∈ I, IsKG a φ V t) := by
  have hda : ∀ t ∈ I, DifferentiableAt ℝ a t := fun t ht =>
    (ha.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have hda' : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t := fun t ht =>
    ((ha.deriv_of_isOpen hI (m := ∞) (by simp)).contDiffAt (hI.mem_nhds ht)).differentiableAt
      (by simp)
  have hdφ : ∀ t ∈ I, DifferentiableAt ℝ φ t := fun t ht =>
    (hφ.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have hdφ' : ∀ t ∈ I, DifferentiableAt ℝ (deriv φ) t := fun t ht =>
    ((hφ.deriv_of_isOpen hI (m := ∞) (by simp)).contDiffAt (hI.mem_nhds ht)).differentiableAt
      (by simp)
  rw [isEinsteinSolution_scalar_iff k Λ Gn hpos hdφ, flrw_einstein_iff_friedmann hI ha hpos]
  constructor
  · rintro ⟨hF, hk⟩
    exact ⟨fun t ht => (hF t ht).1, hk⟩
  · rintro ⟨hF, hk⟩
    exact ⟨fun t ht => ⟨hF t ht, second_of_first_kg hI k Λ Gn hpos hda hda' hdφ hdφ'
      (fun t _ => hV (φ t)) hF hk ht (hadot t ht)⟩, hk⟩

end Cosmology

end Lightlike

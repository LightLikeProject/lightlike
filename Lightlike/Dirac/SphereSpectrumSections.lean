import Mathlib
import Lightlike.Dirac.SphereDirac
import Lightlike.Dirac.SpinorLichnerowicz
import Lightlike.Dirac.SphereSpectrum

/-!
# The Dirac spectrum on the spinor sections of the 2-sphere

The smooth sections of the spinor bundle of `sphereSpinStructure` (`Lightlike/Dirac/SphereSpin.lean`) and their
Dirac operator `SpinorSection.dirac` (`Lightlike/Dirac/SpinorBundle.lean`). This file relates the eigensections
`D σ = λ σ` to the chart eigenspinors of the two-chart spectrum theorem (`SphereEigenspace`,
`Lightlike/Dirac/SphereSpectrum.lean`) through the north chart (work in progress).

## This layer

* `northRep σ`: the representation of `σ` in the north frame, read in the north chart;
* `SpinorSection.eq_zero_of_north`: a smooth section vanishing on `S2 ∖ {N}` vanishes.
-/

open Bundle Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Dirac

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ρ : CliffordRep 2 V}

lemma stereoS_zero_pc : pc (stereoS 0) 2 = 1 := by
  rw [(pc_stereoS 0).2.2]; simp [nsq]

lemma stereoS_ne_north {y : Fin 2 → ℝ} (hy : y ≠ 0) : pc (stereoS y) 2 ≠ 1 := by
  rw [(pc_stereoS y).2.2]
  have hq : 0 < nsq y := by
    unfold nsq
    by_contra h
    push_neg at h
    have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact hy (funext fun i => by fin_cases i <;> simp [h0, h1])
  intro h
  rw [div_eq_one_iff_eq (by positivity)] at h
  linarith

lemma pc_stereoS_ne_south (y : Fin 2 → ℝ) : pc (stereoS y) 2 ≠ -1 := by
  rw [(pc_stereoS y).2.2]
  have hq := nsq_nonneg y
  intro h
  rw [div_eq_iff (by positivity)] at h
  linarith

/-- **A smooth spinor section vanishing away from the north pole vanishes.** -/
theorem SpinorSection.eq_zero_of_north (σ : SpinorSection sphereSpinStructure ρ)
    (h : ∀ p : S2, pc p 2 ≠ 1 → σ p = 0) : σ = 0 := by
  ext p
  by_cases hp : pc p 2 = 1
  · -- `p` is the north pole `stereoS 0`; read `σ` in the south frame along `stereoS`
    have hS : p = stereoS 0 := by
      have hs := pc_sq_sum p
      have h01 : pc p 0 = 0 ∧ pc p 1 = 0 := by
        constructor <;> nlinarith [sq_nonneg (pc p 0), sq_nonneg (pc p 1)]
      apply Subtype.ext
      ext i
      obtain ⟨h0, h1, h2⟩ := pc_stereoS 0
      fin_cases i
      · exact h01.1.trans (by rw [show (0 : Fin (2 + 1)) = 0 from rfl] at h0; simpa [nsq] using h0.symm)
      · exact h01.2.trans (by simpa [nsq] using h1.symm)
      · exact hp.trans (by simpa [nsq] using h2.symm)
    subst hS
    set g : (Fin 2 → ℝ) → V := fun y => σ.toField.rep false (stereoS y)
    have hdom : ∀ y, stereoS y ∈ sphereSpinStructure.dom false := fun y => pc_stereoS_ne_south y
    have hg : ContinuousAt g 0 :=
      ((σ.toField_isSmooth false (stereoS 0) (hdom 0)).continuousAt).comp
        (contMDiff_stereoS 0).continuousAt
    have hg0 : ∀ y, y ≠ 0 → g y = 0 := fun y hy => by
      show σ.toField.rep false (stereoS y) = 0
      rw [show σ.toField.rep false (stereoS y) = σ.rep false (stereoS y) from rfl,
        σ.rep_of_mem (hdom y), h _ (stereoS_ne_north hy)]
      erw [map_zero]
    have hlim : Tendsto g (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hg0 y hy).symm)
    have hg00 : g 0 = 0 := tendsto_nhds_unique (hg.tendsto.mono_left nhdsWithin_le_nhds) hlim
    apply SpinStructure.coordChange_injective (ρ := ρ) (hdom 0)
    simp only
    rw [show ((0 : SpinorSection sphereSpinStructure ρ) (stereoS 0)) = 0 from rfl]
    erw [map_zero, ← σ.rep_of_mem (hdom 0)]
    exact hg00
  · exact h p hp

/-! ## The north representation -/

lemma stereoN_mem_dom (y : Fin 2 → ℝ) : stereoN y ∈ sphereSpinStructure.dom true := pc_stereoN_ne y

lemma pc_ne_one_iff_dom {p : S2} : p ∈ sphereSpinStructure.dom true ↔ pc p 2 ≠ 1 := Iff.rfl

/-- The representation of `σ` in the north frame, read in the north chart (on `E 2`). -/
def northRep (σ : SpinorSection sphereSpinStructure ρ) (x : E 2) : V :=
  σ.toField.rep true (stereoN (modelEquiv2 x))

lemma rep_add (σ τ : SpinorSection sphereSpinStructure ρ) {i : Bool} {p : S2}
    (hp : p ∈ sphereSpinStructure.dom i) :
    (σ + τ).toField.rep i p = σ.toField.rep i p + τ.toField.rep i p := by
  change (σ + τ).rep i p = σ.rep i p + τ.rep i p
  rw [(σ + τ).rep_of_mem hp, σ.rep_of_mem hp, τ.rep_of_mem hp]
  erw [map_add]

lemma rep_smul (c : ℝ) (σ : SpinorSection sphereSpinStructure ρ) {i : Bool} {p : S2}
    (hp : p ∈ sphereSpinStructure.dom i) :
    (c • σ).toField.rep i p = c • σ.toField.rep i p := by
  change (c • σ).rep i p = c • σ.rep i p
  rw [(c • σ).rep_of_mem hp, σ.rep_of_mem hp]
  erw [map_smul]

/-- The north representation as a linear map. -/
def northMap : SpinorSection sphereSpinStructure ρ →ₗ[ℝ] (E 2 → V) where
  toFun := northRep
  map_add' σ τ := funext fun x => rep_add σ τ (stereoN_mem_dom _)
  map_smul' c σ := funext fun x => rep_smul c σ (stereoN_mem_dom _)

/-- A section is determined by its north representation. -/
theorem northMap_injective : Function.Injective (northMap (ρ := ρ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro σ hσ
  refine σ.eq_zero_of_north fun p hp => ?_
  have hx := congrFun hσ (modelEquiv2.symm (invN p))
  simp only [northMap, LinearMap.coe_mk, AddHom.coe_mk, northRep, ContinuousLinearEquiv.apply_symm_apply,
    stereoN_invN hp, Pi.zero_apply] at hx
  apply SpinStructure.coordChange_injective (ρ := ρ) (show p ∈ sphereSpinStructure.dom true from hp)
  simp only
  erw [map_zero, ← σ.rep_of_mem (show p ∈ sphereSpinStructure.dom true from hp)]
  exact hx

/-- **The eigen-equation from the chart.** If the north representation of a smooth section satisfies the chart
eigen-equation `diracF f = λ f`, then `D σ = λ σ`. -/
theorem dirac_eq_of_north (σ : SpinorSection sphereSpinStructure ρ) (lam : ℝ)
    (h : ∀ x, diracF ρ stereoF stereoOmega (northRep σ) x = lam • northRep σ x) :
    σ.dirac = lam • σ := by
  rw [← sub_eq_zero]
  refine (σ.dirac - lam • σ).eq_zero_of_north fun p hp => ?_
  have hd : p ∈ sphereSpinStructure.dom true := hp
  set x := modelEquiv2.symm (invN p)
  have hpx : stereoN (modelEquiv2 x) = p := by
    simp only [x, ContinuousLinearEquiv.apply_symm_apply]; exact stereoN_invN hp
  have hdiff : MDifferentiableAt I2 𝓘(ℝ, V) (σ.toField.rep true) (stereoN (modelEquiv2 x)) := by
    rw [hpx]; exact (σ.toField_isSmooth true p hd).mdifferentiableAt (by simp)
  have key := dirac_sphere_north ρ hdiff
  rw [show (σ.toField.rep true ∘ stereoN ∘ modelEquiv2) = northRep σ from rfl, h x] at key
  rw [hpx] at key
  -- the north representation of `D σ - λ σ` vanishes at `p`
  have h1 : (σ.dirac - lam • σ).toField.rep true p = 0 := by
    rw [sub_eq_add_neg, rep_add _ _ hd, ← neg_smul, rep_smul _ _ hd, σ.toField_dirac hd]
    change sphereSpinStructure.dirac ρ true (σ.toField.rep true) p + _ = 0
    rw [key, neg_smul, show northRep σ x = σ.toField.rep true p by
      simp only [northRep]; rw [hpx]]
    abel
  apply SpinStructure.coordChange_injective (ρ := ρ) hd
  simp only
  erw [map_zero, ← (σ.dirac - lam • σ).rep_of_mem hd]
  exact h1

lemma contDiff_northRep (σ : SpinorSection sphereSpinStructure ρ) : ContDiff ℝ ∞ (northRep σ) := by
  rw [← contMDiff_iff_contDiff]
  intro x
  have h1 := σ.toField_isSmooth true (stereoN (modelEquiv2 x)) (stereoN_mem_dom _)
  have h2 : ContMDiffAt 𝓘(ℝ, E 2) I2 ∞ (fun x : E 2 => stereoN (modelEquiv2 x)) x :=
    (contMDiff_stereoN (modelEquiv2 x)).comp x
      ((modelEquiv2 : E 2 →L[ℝ] Fin 2 → ℝ).contDiff.contMDiff.contMDiffAt)
  exact h1.comp x h2

/-- **The chart eigen-equation from the section.** If `D σ = λ σ`, the north representation satisfies
`diracF ρ stereoF stereoOmega f = λ f` on the whole chart. -/
theorem north_eq_of_dirac {σ : SpinorSection sphereSpinStructure ρ} {lam : ℝ} (h : σ.dirac = lam • σ)
    (x : E 2) : diracF ρ stereoF stereoOmega (northRep σ) x = lam • northRep σ x := by
  have hd := stereoN_mem_dom (modelEquiv2 x)
  have hdiff : MDifferentiableAt I2 𝓘(ℝ, V) (σ.toField.rep true) (stereoN (modelEquiv2 x)) :=
    (σ.toField_isSmooth true _ hd).mdifferentiableAt (by simp)
  have key := dirac_sphere_north ρ hdiff
  rw [show (σ.toField.rep true ∘ stereoN ∘ modelEquiv2) = northRep σ from rfl] at key
  rw [← key]
  change sphereSpinStructure.dirac ρ true (σ.toField.rep true) _ = lam • σ.toField.rep true _
  have e1 : sphereSpinStructure.dirac ρ true (σ.toField.rep true) (stereoN (modelEquiv2 x)) =
      σ.dirac.toField.rep true (stereoN (modelEquiv2 x)) := (σ.toField_dirac hd).symm
  rw [e1, h, rep_smul _ _ hd]

end Lightlike.Dirac

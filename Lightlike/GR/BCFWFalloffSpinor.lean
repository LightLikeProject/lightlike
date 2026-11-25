import Lightlike.GR.BCFWFalloff
import Lightlike.GR.BCFWFactorization

/-!
# The falloff for spinor kinematics

For spinor data `l`, `lt : ℕ → Fin 2 → ℂ`, the `[0, 1⟩` shift `|0̂] = |0] + z|1]`, `|1̂⟩ = |1⟩ − z|0⟩` with the
polarizations `ε₋(0̂; |q])`, `ε₊(1̂; ⟨q'|)` on the shifted legs (constant reference spinors) satisfies the hypotheses of
`FalloffData`: `1/[q 0̂]` and `1/⟨q' 1̂⟩` are `O(1/z)`.
-/

open Filter Topology Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The shifted momenta `p̂_t = −|l̂_t]⟨l̃̂_t|`. -/
def shiftedMom (l lt : ℕ → Fin 2 → ℂ) (z : ℂ) : ℕ → Fin 4 → ℂ := fun t =>
  nullMom (if t = 0 then l 0 + z • l 1 else l t) (if t = 1 then lt 1 - z • lt 0 else lt t)

/-- The polarizations of the gluons with negative helicity at `0` and `j ≥ 2`, reference spinors `qs`, `qa`, on the
shifted kinematics. -/
def shiftedPol (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (j : ℕ) (z : ℂ) : ℕ → Fin 4 → ℂ := fun t =>
  if t = 0 then epsMinus (l 0 + z • l 1) (lt 0) qs
  else if t = 1 then epsPlus (l 1) (lt 1 - z • lt 0) qa
  else if t = j then epsMinus (l t) (lt t) qs
  else epsPlus (l t) (lt t) qa

/-- Auxiliary statement `squareBr_add_smul_right` for the large-z falloff. -/
lemma squareBr_add_smul_right (a b c : Fin 2 → ℂ) (z : ℂ) :
    squareBr a (b + z • c) = squareBr a b + z * squareBr a c := by
  simp only [squareBr_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- Auxiliary statement `angleBr_sub_smul_right` for the large-z falloff. -/
lemma angleBr_sub_smul_right (a b c : Fin 2 → ℂ) (z : ℂ) :
    angleBr a (b - z • c) = angleBr a b + z * (-angleBr a c) := by
  simp only [angleBr_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- **The spinor data satisfy the falloff hypotheses.** -/
theorem falloffData_spinor (m j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (hq1 : squareBr qs (l 1) ≠ 0) (hq0 : angleBr qa (lt 0) ≠ 0)
    (hone : ∀ b, 2 ≤ b → b ≤ m + 1 →
      mdot (momRange (shiftedMom l lt 0) 1 b) (nullMom (l 1) (lt 0)) ≠ 0)
    (hother : ∀ a b, a < b → b ≤ m + 1 → a ≠ 1 → ¬ (a = 0 ∧ b = m + 1) →
      mdot (momRange (shiftedMom l lt 0) a b) (momRange (shiftedMom l lt 0) a b) ≠ 0) :
    FalloffData m (shiftedMom l lt) (shiftedPol l lt qs qa j) (nullMom (l 1) (lt 0)) where
  hp z t := by
    unfold shiftedMom shiftVec
    by_cases h0 : t = 0
    · subst h0
      simp [nullMom_add_smul_left]
    · by_cases h1 : t = 1
      · subst h1
        simp only [if_neg h0, if_true, one_ne_zero, zero_smul, sub_zero, if_false]
        rw [nullMom_sub_smul_right]
        simp [sub_eq_add_neg]
      · simp [h0, h1]
  hr := mdot_nullMom_self _ _
  he0 := by
    have hc := Ord.inv_linear (squareBr qs (l 0)) (squareBr qs (l 1)) hq1
    have hv : Ord (-1) (fun z : ℂ => ((Real.sqrt 2 : ℝ) : ℂ) • (1 / (squareBr qs (l 0) + z * squareBr qs (l 1)))) :=
      hc.const_smul ((Real.sqrt 2 : ℝ) : ℂ)
    have h2 := (hv.smul (Ord.const (momOf (vecMulVec qs (lt 0))))).mono (le_of_eq (by norm_num : (-1 : ℤ) + 0 = -1))
    refine Ord.of_eventuallyEq h2 (Eventually.of_forall fun z => ?_)
    simp only [shiftedPol, if_true, epsMinus, momOf_smul, squareBr_add_smul_right, smul_eq_mul]
    congr 1
    ring
  he1 := by
    have hc := Ord.inv_linear (angleBr qa (lt 1)) (-angleBr qa (lt 0)) (neg_ne_zero.2 hq0)
    have hv : Ord (-1) (fun z : ℂ => ((Real.sqrt 2 : ℝ) : ℂ) • (1 / (angleBr qa (lt 1) + z * (-angleBr qa (lt 0))))) :=
      hc.const_smul ((Real.sqrt 2 : ℝ) : ℂ)
    have h2 := (hv.smul (Ord.const (momOf (vecMulVec (l 1) qa)))).mono (le_of_eq (by norm_num : (-1 : ℤ) + 0 = -1))
    refine Ord.of_eventuallyEq h2 (Eventually.of_forall fun z => ?_)
    simp only [shiftedPol, one_ne_zero, if_false, if_true, epsPlus, momOf_smul, angleBr_sub_smul_right, smul_eq_mul]
    congr 1
    ring
  heo t ht := by
    have h0 : t ≠ 0 := by omega
    have h1 : t ≠ 1 := by omega
    by_cases hj' : t = j
    · have : (fun z => shiftedPol l lt qs qa j z t) = fun _ => epsMinus (l t) (lt t) qs :=
        funext fun z => by rw [shiftedPol, if_neg h0, if_neg h1, if_pos hj']
      rw [this]; exact Ord.const _
    · have : (fun z => shiftedPol l lt qs qa j z t) = fun _ => epsPlus (l t) (lt t) qa :=
        funext fun z => by rw [shiftedPol, if_neg h0, if_neg h1, if_neg hj']
      rw [this]; exact Ord.const _
  hone := hone
  hother := hother

/-- **The BCFW large-`z` falloff for the true amplitudes** (Elvang-Huang (3.11) for the `[−, +⟩` shift of the gluons `0`, `1`,
here with the polarizations (2.49)-(2.50) with constant references): the colour-ordered Feynman amplitude of `m + 3`
gluons tends to `0` as `z → ∞` under `|0̂] = |0] + z|1]`, `|1̂⟩ = |1⟩ − z|0⟩`, for generic kinematics. -/
theorem tendsto_bgAmplitude_shift (m j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (hq1 : squareBr qs (l 1) ≠ 0) (hq0 : angleBr qa (lt 0) ≠ 0)
    (hone : ∀ b, 2 ≤ b → b ≤ m + 1 →
      mdot (momRange (shiftedMom l lt 0) 1 b) (nullMom (l 1) (lt 0)) ≠ 0)
    (hother : ∀ a b, a < b → b ≤ m + 1 → a ≠ 1 → ¬ (a = 0 ∧ b = m + 1) →
      mdot (momRange (shiftedMom l lt 0) a b) (momRange (shiftedMom l lt 0) a b) ≠ 0) :
    Tendsto (fun z => bgAmplitude m (shiftedMom l lt z) (shiftedPol l lt qs qa j z)) (cocompact ℂ) (𝓝 0) :=
  (falloffData_spinor m j hj l lt qs qa hq1 hq0 hone hother).tendsto_amplitude

end Lightlike.SpinorHelicity

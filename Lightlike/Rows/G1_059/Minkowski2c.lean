module

public import Mathlib
public import Lightlike.Rows.G1_059.Minkowski2b

/-!
# The advanced Green operator and the support rules in 1+1 Minkowski (row G1-059)

The advanced operator is the retarded one conjugated by the point reflection `p ↦ -p`, which
commutes with the wave operator `box`.  We prove `box (Gadv f) = f` and `Gadv (box f) = f`
(BGP key `bgp-2007`, Section 3.4), and the support rules: `Gret f` is supported in the future
cone `{p | ∃ q ∈ supp f, q ≤ p}` of `supp f` (coordinatewise order in light-cone coordinates),
`Gadv f` in the past cone.

* `box_comp_neg`: `box (g ∘ neg) = box g ∘ neg`;
* `Gadv`, `box_Gadv`, `Gadv_box`;
* `Jp`, `Jm`: future and past cones; `support_Gret_subset`, `support_Gadv_subset`.
-/

@[expose] public section

open MeasureTheory Set

namespace Lightlike.GreenOps.Mink2

/-- The wave operator commutes with the point reflection `p ↦ -p`. -/
lemma box_comp_neg (g : ℝ × ℝ → ℝ) : box (fun q => g (-q)) = fun p => box g (-p) := by
  funext p
  unfold box
  have h1 : ∀ u : ℝ, deriv (fun v => g (-(u, v))) p.2 =
      -deriv (fun v => g (-u, v)) (-p.2) := by
    intro u
    have := deriv_comp_neg (f := fun v => g (-u, v)) (x := p.2)
    simpa using this
  simp only [Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  have h3 : (fun u : ℝ => deriv (fun v => g (-u, -v)) p.2) =
      fun u => -(fun w => deriv (fun v => g (w, v)) (-p.2)) (-u) := by
    funext u
    simpa using h1 u
  rw [h3]
  have key : ∀ (F : ℝ → ℝ) (x : ℝ), deriv (fun u => -(F (-u))) x = deriv F (-x) := by
    intro F x
    have e : (fun u => -(F (-u))) = -(fun u => F (-u)) := rfl
    rw [e, deriv.neg, deriv_comp_neg]
    simp
  rw [key (fun w => deriv (fun v => g (w, v)) (-p.2)) p.1]

/-- The advanced Green operator in light-cone coordinates: `Gadv f p = Gret (f ∘ neg) (-p)`, i.e.
`1/4 ∫_{b ≥ v} ∫_{a ≥ u} f (a, b)`. -/
noncomputable def Gadv (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := Gret (fun q => f (-q)) (-p)

/-- `box ∘ Gadv = id` on continuous compactly supported functions. -/
theorem box_Gadv {f : ℝ × ℝ → ℝ} (hc : Continuous f) (hcs : HasCompactSupport f) :
    box (Gadv f) = f := by
  have hc' : Continuous fun q => f (-q) := hc.comp continuous_neg
  have hcs' : HasCompactSupport fun q => f (-q) := hcs.comp_homeomorph (Homeomorph.neg _)
  have h := box_Gret hc' hcs'
  funext p
  have h2 := box_comp_neg (Gret fun q => f (-q))
  have h3 : Gadv f = fun q => Gret (fun q => f (-q)) (-q) := rfl
  rw [h3, h2]
  have := congrFun h (-p)
  simpa using this

/-- `Gadv ∘ box = id` on `C²` compactly supported functions. -/
theorem Gadv_box {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hcs : HasCompactSupport f) :
    Gadv (box f) = f := by
  have hf' : ContDiff ℝ 2 fun q => f (-q) := hf.comp contDiff_neg
  have hcs' : HasCompactSupport fun q => f (-q) := hcs.comp_homeomorph (Homeomorph.neg _)
  have h := Gret_box hf' hcs'
  have h2 := box_comp_neg f
  funext p
  unfold Gadv
  have h3 : (fun q => box f (-q)) = box fun q => f (-q) := by rw [h2]
  rw [h3, h]
  simp

/-- The future cone of a set in light-cone coordinates (coordinatewise order). -/
def Jp (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | ∃ q ∈ S, q.1 ≤ p.1 ∧ q.2 ≤ p.2}

/-- The past cone of a set in light-cone coordinates (coordinatewise order). -/
def Jm (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | ∃ q ∈ S, p.1 ≤ q.1 ∧ p.2 ≤ q.2}

/-- `Gret f` is supported in the future cone of the support of `f`. -/
lemma support_Gret_subset (f : ℝ × ℝ → ℝ) : Function.support (Gret f) ⊆ Jp (Function.support f) := by
  intro p hp
  by_contra hn
  apply hp
  have h0 : ∀ a b, a ≤ p.1 → b ≤ p.2 → f (a, b) = 0 := by
    intro a b ha hb
    by_contra hne
    exact hn ⟨(a, b), hne, ha, hb⟩
  unfold Gret
  have : ∫ b in Iic p.2, ∫ a in Iic p.1, f (a, b) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro b hb
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro a ha
    exact h0 a b ha hb
  rw [this]; simp

/-- `Gadv f` is supported in the past cone of the support of `f`. -/
lemma support_Gadv_subset (f : ℝ × ℝ → ℝ) : Function.support (Gadv f) ⊆ Jm (Function.support f) := by
  intro p hp
  obtain ⟨q, hq, h1, h2⟩ := support_Gret_subset (fun q => f (-q)) (show -p ∈ _ from hp)
  refine ⟨-q, hq, ?_, ?_⟩
  · simp at h1 ⊢; linarith
  · simp at h2 ⊢; linarith

end Lightlike.GreenOps.Mink2

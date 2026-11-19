import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The shear that flattens a graph, and its invariance of Lebesgue measure

For `γ : ℝⁿ → ℝ` and a coordinate `i` of `ℝⁿ⁺¹`, `shearFwd γ i x` adds `γ(x')` to the `i`-th coordinate of
`x`, where `x'` are the other coordinates; `shearBwd γ i` subtracts it. They are inverse to each other
(`shearBwd_shearFwd`, `shearFwd_shearBwd`), `shearFwd` maps the half-space `x_i ≥ 0` onto the region above
the graph of `γ`, and for measurable `γ` it preserves Lebesgue measure (`measurePreserving_shearFwd`).

Supporting lemmas for the divergence theorem on a domain bounded by a graph; no catalogue entry.
-/

open MeasureTheory Set

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The shear `x ↦ (x', x_i + γ(x'))`. -/
def shearFwd (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  i.insertNth (x i + γ (i.removeNth x)) (i.removeNth x)

/-- The inverse shear `x ↦ (x', x_i - γ(x'))`. -/
def shearBwd (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  i.insertNth (x i - γ (i.removeNth x)) (i.removeNth x)

@[simp] lemma shearFwd_apply_same (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    shearFwd γ i x i = x i + γ (i.removeNth x) := by
  simp [shearFwd]

@[simp] lemma removeNth_shearFwd (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    i.removeNth (shearFwd γ i x) = i.removeNth x := by
  simp [shearFwd]

@[simp] lemma shearBwd_apply_same (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    shearBwd γ i x i = x i - γ (i.removeNth x) := by
  simp [shearBwd]

@[simp] lemma removeNth_shearBwd (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    i.removeNth (shearBwd γ i x) = i.removeNth x := by
  simp [shearBwd]

lemma shearBwd_shearFwd (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    shearBwd γ i (shearFwd γ i x) = x := by
  unfold shearBwd
  rw [shearFwd_apply_same, removeNth_shearFwd, add_sub_cancel_right]
  exact Fin.insertNth_self_removeNth i x

lemma shearFwd_shearBwd (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    shearFwd γ i (shearBwd γ i x) = x := by
  unfold shearFwd
  rw [shearBwd_apply_same, removeNth_shearBwd, sub_add_cancel]
  exact Fin.insertNth_self_removeNth i x

/-- The shear maps the half-space `x_i ≥ 0` onto the region above the graph. -/
lemma shearFwd_mem_graph_iff (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    γ (i.removeNth (shearFwd γ i x)) ≤ shearFwd γ i x i ↔ 0 ≤ x i := by
  rw [shearFwd_apply_same, removeNth_shearFwd]
  constructor <;> intro h <;> linarith

/-- **The shear preserves Lebesgue measure.** -/
theorem measurePreserving_shearFwd (γ : (Fin n → ℝ) → ℝ) (hγ : Measurable γ) (i : Fin (n + 1)) :
    MeasurePreserving (shearFwd γ i) (volume : Measure (Fin (n + 1) → ℝ)) volume := by
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  -- the skew product on `ℝⁿ × ℝ`
  have hskew : MeasurePreserving (fun q : (Fin n → ℝ) × ℝ => (q.1, q.2 + γ q.1))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) :=
    MeasurePreserving.skew_product (g := fun y t => t + γ y) (MeasurePreserving.id volume)
      ((measurable_snd.add (hγ.comp measurable_fst)))
      (Filter.Eventually.of_forall fun y => map_add_right_eq_self volume (γ y))
  have hs : MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => (p.1 + γ p.2, p.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    (Measure.measurePreserving_swap.comp hskew).comp Measure.measurePreserving_swap
  have hfun : shearFwd γ i = fun x => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
      ((fun p : ℝ × (Fin n → ℝ) => (p.1 + γ p.2, p.2))
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x)) := by
    funext x
    rfl
  rw [hfun]
  exact (he.symm _).comp (hs.comp he)

end Lightlike

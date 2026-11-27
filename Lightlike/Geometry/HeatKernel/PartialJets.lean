import Mathlib
import Lightlike.Spacetime.RiemannSymmetry

/-!
# Iterated partial derivatives along a list of indices

`pdL L f = ∂_{L₁} ∂_{L₂} ⋯ f` for a list `L` of coordinate indices. On an open set where the functions are smooth:
the **Leibniz rule** `pdL L (f h) = Σ_{(A, B) ∈ splits L} pdL A f · pdL B h` (`pdL_mul`), with `splits L` the list of the
`2^|L|` ways of distributing the entries of `L` over the two factors; the rule for finite sums (`pdL_sum`); vanishing of
the derivatives of a function vanishing on the set (`pdL_eq_zero_of_eqOn`); and the symmetry of iterated partial
derivatives (`pdL_perm`). These turn the order-by-order differentiation of an identity at a point into a computation
that `simp` carries out on an explicit list.
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The iterated partial derivative `∂_{L₁} ∂_{L₂} ⋯ ∂_{L_k} f`. -/
def pdL (L : List (Fin n)) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ := L.foldr pd f

@[simp] lemma pdL_nil (f : (Fin n → ℝ) → ℝ) : pdL [] f = f := rfl

@[simp] lemma pdL_cons (a : Fin n) (L : List (Fin n)) (f : (Fin n → ℝ) → ℝ) : pdL (a :: L) f = pd a (pdL L f) := rfl

/-- A partial derivative after the list is the list extended at its end. -/
lemma pdL_pd (L : List (Fin n)) (i : Fin n) (f : (Fin n → ℝ) → ℝ) : pdL L (pd i f) = pdL (L ++ [i]) f := by
  simp [pdL, List.foldr_append]

/-- The ways of distributing the entries of a list over two factors, in order. -/
def splits : List (Fin n) → List (List (Fin n) × List (Fin n))
  | [] => [([], [])]
  | a :: L => (splits L).map (fun AB => (a :: AB.1, AB.2)) ++ (splits L).map (fun AB => (AB.1, a :: AB.2))

variable {U : Set (Fin n → ℝ)}

/-- Iterated partial derivatives of a smooth function on an open set are smooth. -/
lemma contDiffOn_pdL {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (L : List (Fin n)) :
    ContDiffOn ℝ ∞ (pdL L f) U := by
  induction L with
  | nil => exact hf
  | cons a L ih => exact contDiffOn_pd ih hU a

lemma differentiableAt_of_contDiffOn' {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {y : Fin n → ℝ} (hy : y ∈ U) : DifferentiableAt ℝ f y :=
  (hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)

/-- A sum over a list of functions differentiable at `y` is differentiable at `y`. -/
lemma differentiableAt_list_sum {ι : Type*} (l : List ι) (F : ι → (Fin n → ℝ) → ℝ) {y : Fin n → ℝ}
    (hF : ∀ x ∈ l, DifferentiableAt ℝ (F x) y) : DifferentiableAt ℝ (fun z => (l.map fun x => F x z).sum) y := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF x (by simp)).add (ih fun x hx => hF x (by simp [hx]))

/-- `pd` of a sum over a list. -/
lemma pd_list_sum {ι : Type*} (l : List ι) (F : ι → (Fin n → ℝ) → ℝ) (a : Fin n) {y : Fin n → ℝ}
    (hF : ∀ x ∈ l, DifferentiableAt ℝ (F x) y) :
    pd a (fun z => (l.map fun x => F x z).sum) y = (l.map fun x => pd a (F x) y).sum := by
  induction l with
  | nil => simp [pd]
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : DifferentiableAt ℝ (F x) y := hF x (by simp)
    have h2 := differentiableAt_list_sum l F fun x hx => hF x (by simp [hx])
    rw [← ih fun x hx => hF x (by simp [hx])]
    unfold pd
    rw [fderiv_fun_add h1 h2]
    rfl

/-- `pd` of a product. -/
lemma pd_mul' {f h : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (a : Fin n) (hf : DifferentiableAt ℝ f y)
    (hh : DifferentiableAt ℝ h y) : pd a (fun z => f z * h z) y = pd a f y * h y + f y * pd a h y := by
  unfold pd
  rw [fderiv_fun_mul hf hh]
  simp
  ring

/-- `pd` at `y` depends only on the values near `y`. -/
lemma pd_congr_on {f f' : (Fin n → ℝ) → ℝ} (hU : IsOpen U) {y : Fin n → ℝ} (hy : y ∈ U) (h : EqOn f f' U)
    (a : Fin n) : pd a f y = pd a f' y := by
  unfold pd
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) h)]

/-- **The Leibniz rule for iterated partial derivatives.** -/
lemma pdL_mul {f h : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (L : List (Fin n)) : ∀ y ∈ U,
    pdL L (fun z => f z * h z) y = ((splits L).map fun AB => pdL AB.1 f y * pdL AB.2 h y).sum := by
  induction L with
  | nil => intro y _; simp [splits]
  | cons a L ih =>
    intro y hy
    rw [pdL_cons, pd_congr_on hU hy ih a, pd_list_sum]
    · simp only [splits, List.map_append, List.map_map, List.sum_append]
      rw [← List.sum_map_add]
      refine congrArg List.sum (List.map_congr_left fun AB _ => ?_)
      simp only [Function.comp_apply, pdL_cons]
      rw [pd_mul' a (differentiableAt_of_contDiffOn' (contDiffOn_pdL hf hU _) hU hy)
        (differentiableAt_of_contDiffOn' (contDiffOn_pdL hh hU _) hU hy)]
    · intro AB _
      exact ((differentiableAt_of_contDiffOn' (contDiffOn_pdL hf hU _) hU hy).mul
        (differentiableAt_of_contDiffOn' (contDiffOn_pdL hh hU _) hU hy))

/-- **Iterated partial derivatives of a finite sum.** -/
lemma pdL_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin n → ℝ) → ℝ} (hF : ∀ i ∈ s, ContDiffOn ℝ ∞ (F i) U)
    (hU : IsOpen U) (L : List (Fin n)) : ∀ y ∈ U, pdL L (fun z => ∑ i ∈ s, F i z) y = ∑ i ∈ s, pdL L (F i) y := by
  induction L with
  | nil => intro y _; rfl
  | cons a L ih =>
    intro y hy
    rw [pdL_cons, pd_congr_on hU hy ih a]
    unfold pd
    rw [fderiv_fun_sum fun i hi => differentiableAt_of_contDiffOn' (contDiffOn_pdL (hF i hi) hU _) hU hy]
    simp [pd]

/-- Iterated partial derivatives of a function vanishing on an open set vanish there. -/
lemma pdL_eq_zero_of_eqOn {f : (Fin n → ℝ) → ℝ} (hU : IsOpen U) (h : EqOn f 0 U) (L : List (Fin n)) :
    ∀ y ∈ U, pdL L f y = 0 := by
  induction L with
  | nil => exact h
  | cons a L ih =>
    intro y hy
    rw [pdL_cons, pd_congr_on hU hy ih a]
    simp [pd]

/-- Iterated partial derivatives agree for functions agreeing on an open set. -/
lemma pdL_congr_on {f f' : (Fin n → ℝ) → ℝ} (hU : IsOpen U) (h : EqOn f f' U) (L : List (Fin n)) :
    ∀ y ∈ U, pdL L f y = pdL L f' y := by
  induction L with
  | nil => exact h
  | cons a L ih => intro y hy; rw [pdL_cons, pdL_cons, pd_congr_on hU hy ih a]

/-- **Symmetry of iterated partial derivatives**: the order of the list does not matter. -/
lemma pdL_perm {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {L L' : List (Fin n)}
    (hL : L.Perm L') : ∀ y ∈ U, pdL L f y = pdL L' f y := by
  induction hL with
  | nil => intro y _; rfl
  | cons a _ ih => intro y hy; rw [pdL_cons, pdL_cons, pd_congr_on hU hy ih a]
  | swap a b L =>
    intro y hy
    simp only [pdL_cons]
    exact pd_pd_comm (contDiffOn_pdL hf hU L) hU hy b a
  | trans _ _ ih₁ ih₂ => intro y hy; rw [ih₁ y hy, ih₂ y hy]

end Lightlike

import Lightlike.SpinFoam.EPRL
import Lightlike.Spin4.VertexTests

/-!
# Checks of the EPRL state sum

* **A value from the Clebsch–Gordan definition.** On the single 4-simplex `{0,1,2,3,4}` with
  `γ = 1/3`, spin `3/2` on the four triangles opposite the edges `03, 04, 13, 14` (in the vertex positions) and
  intertwiner label `3/2` on the tetrahedra `1` and `3`, the vertex is `2/27` (SymPy: `2/27`,
  `Lightlike.Spin4.VertexTests.eprlVertex_cycle_third`), the four faces weigh `(2+1)(1+1) = 6` each,
  and the weight is `6⁴ · 2/27 = 96`.
* **Wrong inputs.** For `γ = 1/2` the spin `3/2` is not EPRL-admissible, so the same colouring has
  weight `0`; with a wrong intertwiner label the vertex is `0`.
-/

open Finset Lightlike.Spin4 Lightlike.FourD

namespace Lightlike.SpinFoam.EPRL.Tests

/-- The 4-simplex `{0,1,2,3,4}`. -/
def S5 : Finset ℕ := {0, 1, 2, 3, 4}

lemma S5_card : #S5 = 5 := by decide

/-- The single 4-simplex. -/
def K1 : Complex4 ℕ := Complex4.simplex S5 S5_card

/-- Its sorted vertices are `0, …, 4`. -/
lemma orderEmb_S5 (i : Fin 5) : S5.orderEmbOfFin S5_card i = (i : ℕ) := by
  have := Finset.orderEmbOfFin_unique S5_card (f := fun i : Fin 5 => (i : ℕ))
    (fun i => by fin_cases i <;> decide) (fun i j h => by simpa using h)
  exact (congrFun this i).symm

/-- The colouring: spin `3` (doubled) on the triangles `{1,2,4}, {1,2,3}, {0,2,4}, {0,2,3}`
(edges `03, 04, 13, 14` of `K₅`), label `3` on the tetrahedra `{0,2,3,4}` and `{0,1,2,4}`
(nodes `1` and `3`). -/
def colA : Finset ℕ → ℕ := fun f =>
  if f = {1, 2, 4} ∨ f = {1, 2, 3} ∨ f = {0, 2, 4} ∨ f = {0, 2, 3} ∨ f = {0, 2, 3, 4} ∨
    f = {0, 1, 2, 4} then 3 else 0

lemma triSpins_colA : triSpins S5 S5_card colA = ![0, 0, 3, 3, 0, 3, 3, 0, 0, 0] := by
  funext e
  simp only [triSpins, orderEmb_S5]
  fin_cases e <;> decide

lemma tetLabels_colA : tetLabels S5 S5_card colA = ![0, 3, 0, 3, 0] := by
  funext a
  simp only [tetLabels, orderEmb_S5]
  fin_cases a <;> decide

lemma eprlN_third : eprlN (3⁻¹) 3 = 2 := by
  rw [eprlN, Nat.floor_eq_iff (by positivity)]
  norm_num [abs_of_pos]

lemma eprlM_third : eprlM (3⁻¹) 3 = 1 := by
  rw [eprlM, Nat.floor_eq_iff (by positivity)]
  norm_num [abs_of_pos]

lemma eprlAdmissible_third : EPRLAdmissible (3⁻¹) 3 :=
  (eprlAdmissible_iff (by norm_num) (by norm_num)).mpr ⟨1, by norm_num, by decide⟩

lemma eprlAdmissible_zero' : EPRLAdmissible (3⁻¹) 0 := eprlAdmissible_zero _

/-- **Value check.** The vertex of the single simplex is `2/27`. -/
theorem simpE_colA : simpE (1 / 3) colA S5 = ((2 / 27 : ℝ) : ℂ) := by
  have hn : (fun e => eprlN (1 / 3) (triSpins S5 S5_card colA e)) =
      ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] := by
    rw [triSpins_colA]; funext e; fin_cases e <;> simp [eprlN_third, eprlN_zero]
  have hm : (fun e => eprlM (1 / 3) (triSpins S5 S5_card colA e)) =
      ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] := by
    rw [triSpins_colA]; funext e; fin_cases e <;> simp [eprlM_third, eprlM_zero]
  have hadm : ∀ e, EPRLAdmissible (1 / 3) (triSpins S5 S5_card colA e) := by
    intro e; rw [triSpins_colA]; fin_cases e <;>
      simp [eprlAdmissible_third, eprlAdmissible_zero']
  unfold simpE
  rw [dite_eq_left S5_card, hn, hm, tetLabels_colA,
    ite_eq_left ⟨hadm, Lightlike.Spin4.VertexTests.isVertexBoundary_cycle_third⟩]
  exact Lightlike.Spin4.VertexTests.eprlVertex_cycle_third

lemma faceAmp_colA (f : Finset ℕ) :
    faceAmp (3⁻¹) (colA f) = if colA f = 3 then 6 else 1 := by
  have h : colA f = 3 ∨ colA f = 0 := by unfold colA; split_ifs <;> simp
  rcases h with h | h
  · rw [h, ite_eq_left rfl, faceAmp, eprlN_third, eprlM_third]
  · rw [h, ite_eq_right (by norm_num), faceAmp, eprlN_zero, eprlM_zero]

/-- **Value check.** The weight of the colouring on the single simplex is `96 = 6⁴ · 2/27`. -/
theorem weightE_colA : weightE (1 / 3) K1 colA = 96 := by
  have hs : K1.simps = {S5} := rfl
  have ht : K1.tris = S5.powersetCard 3 := Complex4.faces_simplex S5_card 2
  have hf : ∏ f ∈ K1.tris, (faceAmp (1 / 3) (colA f) : ℂ) = 1296 := by
    rw [ht]
    have : ∏ f ∈ S5.powersetCard 3, faceAmp (1 / 3) (colA f) = 1296 := by
      simp only [one_div, faceAmp_colA]
      decide
    exact_mod_cast this
  unfold weightE
  rw [hf, hs, prod_singleton, simpE_colA]
  simp [edgeAmp]
  norm_num

/-- **Wrong input.** For `γ = 1/2` the spin `3/2` is not admissible (`γ J = 3/2` is not an
integer), so the same colouring has vertex `0`. -/
theorem simpE_colA_half : simpE (1 / 2) colA S5 = 0 := by
  refine simpE_eq_zero_of_not_admissible _ _ S5_card 2 ?_
  rw [show triSpins S5 S5_card colA 2 = 3 by rw [triSpins_colA]; rfl,
    eprlAdmissible_iff (by norm_num) (by norm_num)]
  rintro ⟨p, hp, -⟩
  have h1 : (p : ℝ) * 2 = 3 := by rw [← hp]; push_cast; ring
  have h2 : p * 2 = 3 := by exact_mod_cast h1
  omega

end Lightlike.SpinFoam.EPRL.Tests

import Lightlike.SpinFoam.EPRLStateSum.RecouplingTranspose

/-!
# The EPRL node intertwiners in the intrinsic channel of a tetrahedron

A tetrahedron with sorted triangle spins `t₀ t₁ t₂ t₃` appears at the node `a` of a 4-simplex with
its legs rotated by `r = a mod 4` (`NodeBasis.cyc_eq_succAbove`): the legs are
`(t_r, t_{r+1}, t_{r+2}, t_{r+3})` and the label `i` couples the first two. The Ooguri label is
intrinsic: it labels `fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃` (`SNet`, `(02)(13)` channel).

* `nodeCoef t₀ t₁ t₂ t₃ r i l`: the coefficient of the intrinsic channel vector `l` in the node
  intertwiner `i` of rotation `r`;
* `fourJ_node₀`, `fourJ_node₁`, `fourJ_node₂`, `fourJ_node₃`: the tensor identities, for the four
  rotations;
* `nodeCoef_zero`, `nodeCoef_two`: rotations `0` and `2` are the recoupling matrix `fourRecoupling`
  up to the sign `(-1)^i`.
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam.EPRLStateSum

/-- The coefficient of the intrinsic `(02)(13)` vector `l` in the node intertwiner of label `i`
and rotation `r` (taken mod 4) of a tetrahedron with sorted spins `t₀ t₁ t₂ t₃`. -/
noncomputable def nodeCoef (t₀ t₁ t₂ t₃ r i l : ℕ) : ℝ :=
  match r % 4 with
  | 0 => fourRecoupling t₀ t₁ t₂ t₃ i l
  | 1 => ∑ k ∈ range (t₀ + t₁ + 1),
      rot1Recoupling t₀ t₁ t₂ t₃ i k * fourRecoupling t₀ t₁ t₂ t₃ k l
  | 2 => (-1) ^ i * fourRecoupling t₀ t₁ t₂ t₃ i l
  | _ => ∑ k ∈ range (t₂ + t₃ + 1),
      rot1Recoupling t₂ t₃ t₀ t₁ i k * ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l)

/-- Composition of two changes of basis (a finite double sum). -/
lemma sum_comp_basis {S T : Finset ℕ} (a : ℕ → ℝ) (R : ℕ → ℕ → ℝ) (B : ℕ → ℝ) :
    ∑ k ∈ T, a k * ∑ l ∈ S, R k l * B l = ∑ l ∈ S, (∑ k ∈ T, a k * R k l) * B l := by
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => sum_congr rfl fun k _ => by ring

/-- **Rotation 0**: the node intertwiner is the `(01)(23)` one, with the recoupling matrix. -/
theorem fourJ_node₀ (t₀ t₁ t₂ t₃ i : ℕ) (m₀ m₁ m₂ m₃ : ℤ) :
    fourJ t₀ t₁ t₂ t₃ i m₀ m₁ m₂ m₃ = ∑ l ∈ range (t₀ + t₂ + 1),
      nodeCoef t₀ t₁ t₂ t₃ 0 i l * fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃ := by
  rw [fourJ_eq_sum_fourRecoupling]
  rfl

/-- **Rotation 2**: the pair swap gives the sign `(-1)^i`. -/
theorem fourJ_node₂ (t₀ t₁ t₂ t₃ i : ℕ) (m₀ m₁ m₂ m₃ : ℤ) :
    fourJ t₂ t₃ t₀ t₁ i m₂ m₃ m₀ m₁ = ∑ l ∈ range (t₀ + t₂ + 1),
      nodeCoef t₀ t₁ t₂ t₃ 2 i l * fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃ := by
  rw [fourJ_swapPairs, fourJ_eq_sum_fourRecoupling, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  show _ = (-1) ^ i * fourRecoupling t₀ t₁ t₂ t₃ i l * _
  ring

/-- **Rotation 1**: the legs `(t₁ t₂ t₃ t₀)`. -/
theorem fourJ_node₁ (t₀ t₁ t₂ t₃ i : ℕ) (m₀ m₁ m₂ m₃ : ℤ) :
    fourJ t₁ t₂ t₃ t₀ i m₁ m₂ m₃ m₀ = ∑ l ∈ range (t₀ + t₂ + 1),
      nodeCoef t₀ t₁ t₂ t₃ 1 i l * fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃ := by
  rw [fourJ_rot1]
  have h : ∀ k, fourJ t₀ t₁ t₂ t₃ k m₀ m₁ m₂ m₃ = ∑ l ∈ range (t₀ + t₂ + 1),
      fourRecoupling t₀ t₁ t₂ t₃ k l * fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃ := fun k =>
    fourJ_eq_sum_fourRecoupling t₀ t₁ t₂ t₃ k m₀ m₁ m₂ m₃
  simp only [h]
  rw [sum_comp_basis (fun k => rot1Recoupling t₀ t₁ t₂ t₃ i k)
    (fun k l => fourRecoupling t₀ t₁ t₂ t₃ k l) (fun l => fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃)]
  rfl

/-- **Rotation 3**: the legs `(t₃ t₀ t₁ t₂)`. -/
theorem fourJ_node₃ (t₀ t₁ t₂ t₃ i : ℕ) (m₀ m₁ m₂ m₃ : ℤ) :
    fourJ t₃ t₀ t₁ t₂ i m₃ m₀ m₁ m₂ = ∑ l ∈ range (t₀ + t₂ + 1),
      nodeCoef t₀ t₁ t₂ t₃ 3 i l * fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃ := by
  rw [fourJ_rot1 t₂ t₃ t₀ t₁ i m₂ m₃ m₀ m₁]
  have h : ∀ k, fourJ t₂ t₃ t₀ t₁ k m₂ m₃ m₀ m₁ = ∑ l ∈ range (t₀ + t₂ + 1),
      ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l) * fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃ := fun k => by
    rw [fourJ_swapPairs, fourJ_eq_sum_fourRecoupling, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  simp only [h]
  rw [sum_comp_basis (fun k => rot1Recoupling t₂ t₃ t₀ t₁ i k)
    (fun k l => (-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l)
    (fun l => fourJ t₀ t₂ t₁ t₃ l m₀ m₂ m₁ m₃)]
  rfl

/-- The coefficients of rotation `0` are the recoupling matrix. -/
theorem nodeCoef_zero (t₀ t₁ t₂ t₃ i l : ℕ) :
    nodeCoef t₀ t₁ t₂ t₃ 0 i l = fourRecoupling t₀ t₁ t₂ t₃ i l := rfl

/-- The coefficients of rotation `2` are the recoupling matrix times `(-1)^i`. -/
theorem nodeCoef_two (t₀ t₁ t₂ t₃ i l : ℕ) :
    nodeCoef t₀ t₁ t₂ t₃ 2 i l = (-1) ^ i * fourRecoupling t₀ t₁ t₂ t₃ i l := rfl

/-- **Orthogonality for rotation `0`**: `Σ_l N₀(i,l) N₀(i',l) = δ_{ii'}` on admissible `i`. -/
theorem sum_nodeCoef_zero_mul (t₀ t₁ t₂ t₃ i i' : ℕ) :
    ∑ l ∈ range (t₀ + t₂ + 1), nodeCoef t₀ t₁ t₂ t₃ 0 i l * nodeCoef t₀ t₁ t₂ t₃ 0 i' l =
      if i = i' ∧ Pentagon.Tri t₀ t₁ i ∧ Pentagon.Tri i t₂ t₃ then 1 else 0 :=
  sum_fourRecoupling_mul t₀ t₁ t₂ t₃ i i'

/-- **Orthogonality for rotation `2`**: the signs `(-1)^i (-1)^i'` square to one on the diagonal. -/
theorem sum_nodeCoef_two_mul (t₀ t₁ t₂ t₃ i i' : ℕ) :
    ∑ l ∈ range (t₀ + t₂ + 1), nodeCoef t₀ t₁ t₂ t₃ 2 i l * nodeCoef t₀ t₁ t₂ t₃ 2 i' l =
      if i = i' ∧ Pentagon.Tri t₀ t₁ i ∧ Pentagon.Tri i t₂ t₃ then 1 else 0 := by
  have h := sum_fourRecoupling_mul t₀ t₁ t₂ t₃ i i'
  have : ∀ l ∈ range (t₀ + t₂ + 1), nodeCoef t₀ t₁ t₂ t₃ 2 i l * nodeCoef t₀ t₁ t₂ t₃ 2 i' l =
      ((-1 : ℝ) ^ i * (-1) ^ i') * (fourRecoupling t₀ t₁ t₂ t₃ i l * fourRecoupling t₀ t₁ t₂ t₃ i' l) :=
    fun l _ => by rw [nodeCoef_two, nodeCoef_two]; ring
  rw [sum_congr rfl this, ← mul_sum, h]
  by_cases hii : i = i'
  · subst hii
    rw [negOnePow_mul_self]
    simp
  · simp [hii]

/-- The coefficients depend on the rotation only modulo `4`. -/
theorem nodeCoef_mod (t₀ t₁ t₂ t₃ r i l : ℕ) :
    nodeCoef t₀ t₁ t₂ t₃ (r % 4) i l = nodeCoef t₀ t₁ t₂ t₃ r i l := by
  unfold nodeCoef
  rw [Nat.mod_mod]

end Lightlike.SpinFoam.EPRLStateSum

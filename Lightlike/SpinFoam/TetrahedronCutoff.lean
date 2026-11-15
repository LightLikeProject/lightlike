import Lightlike.SpinFoam.TetrahedronSixJ
import Lightlike.SpinFoam.TetrahedronTests

/-!
# The cut-off sum of the tetrahedron

The Ponzano–Regge-type sum of the tetrahedron integral over the six edge spins, with the weights
`Π (s_e + 1)` and the amplitude `(6j)²` (`tetraInt_eq_sixJ_sq`). All spins are doubled. The cut-off
`N` keeps the doubled spins `≤ N`.

## Main results
* `tetraPartition`: the cut-off sum.
* `tetraTerm_nonneg`, `tetraPartition_mono`: the terms are nonnegative, so the sum is monotone.
* `tetraTerm_eq`: the term is the weight times `(tetraInt s).re`.
* `tetraTerm_two`, `tetraPartition_two_ge`: the all-`2` colouring contributes `81/4`, so the sum
  at doubled cut-off `2` is at least `1 + 81/4`.
* `tetraPartition_zero`: at cut-off `0` the sum is `1`.
* `tetraRemovable_iff_bddAbove`: the cut-off can be removed (the sum has a limit) exactly when the
  sum is bounded.
* `TetraUnbounded`: the **hypothesis** that the sum is unbounded, as for the 2-sphere
  (`not_removable_sphere`; the boundary of a tetrahedron is a 2-sphere). **It is not proved here**:
  it needs a growth lower bound for `Σ Π (s+1) (6j)²`.
* `not_tetraRemovable_of_unbounded`: unboundedness excludes a limit.

Numerical evidence only (`scripts/spinfoam/tetra_partition_check.py`, exact SymPy values): the sums
for doubled cut-offs `0, 1, 2, 3` are `1`, `29`, `2393/4`, `488337/100`. They grow fast, but this is
not a proof of unboundedness.
-/

open Finset Filter Topology PhyslibAlpha.Sl2

namespace Lightlike.SpinFoam

/-- The weight `Π (s_e + 1)` times the amplitude `(6j)²` of the six doubled edge spins. -/
noncomputable def tetraTerm (s : Fin 6 → ℕ) : ℝ :=
  (∏ e, ((s e : ℝ) + 1)) * (sixJSym (s 0) (s 1) (s 2) (s 5) (s 4) (s 3)) ^ 2

/-- The cut-off sum of the tetrahedron over the doubled spins `≤ N`. -/
noncomputable def tetraPartition (N : ℕ) : ℝ :=
  ∑ s ∈ Fintype.piFinset (fun _ : Fin 6 => range (N + 1)), tetraTerm s

/-- The term is the weight times the real part of the tetrahedron integral `tetraInt`, which is
`(6j)²` (`tetraInt_eq_sixJ_sq`). -/
lemma tetraTerm_eq (s : Fin 6 → ℕ) :
    tetraTerm s = (∏ e, ((s e : ℝ) + 1)) * (tetraInt s).re := by
  rw [tetraInt_eq_sixJ_sq, tetraTerm, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Every term is nonnegative. -/
lemma tetraTerm_nonneg (s : Fin 6 → ℕ) : 0 ≤ tetraTerm s :=
  mul_nonneg (Finset.prod_nonneg fun e _ => by positivity) (sq_nonneg _)

/-- Raising the cut-off adds nonnegative terms. -/
theorem tetraPartition_mono : Monotone tetraPartition := by
  intro M N hMN
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun s _ _ => tetraTerm_nonneg s
  intro s hs
  simp only [Fintype.mem_piFinset, mem_range] at hs ⊢
  intro i
  have := hs i
  omega

/-- The square of the all-zero `6j` symbol is `1`. -/
lemma sixJ_zero_sq : (sixJSym 0 0 0 0 0 0 : ℝ) ^ 2 = 1 := by
  have h6 : ((sixJSym 0 0 0 0 0 0 : ℝ) : ℂ) ^ 2 = 1 := by
    have := tetraInt_eq_sixJ_sq (fun _ => 0)
    rw [← this]; exact Tests.tetraInt_zero
  exact_mod_cast h6

/-- The zero colouring has term `1`. -/
lemma tetraTerm_zero : tetraTerm (fun _ => 0) = 1 := by
  simp [tetraTerm, sixJ_zero_sq]

/-- At cut-off `0` only the zero colouring survives, with value `1`. -/
theorem tetraPartition_zero : tetraPartition 0 = 1 := by
  have h : Fintype.piFinset (fun _ : Fin 6 => range (0 + 1)) = {fun _ => 0} := by
    ext s
    simp only [Fintype.mem_piFinset, mem_range, mem_singleton]
    constructor
    · intro hs; funext i; have := hs i; omega
    · rintro rfl i; simp
  rw [tetraPartition, h, Finset.sum_singleton, tetraTerm_zero]

/-- The cut-off sum of the tetrahedron is at least `1` at every cut-off. -/
theorem one_le_tetraPartition (N : ℕ) : 1 ≤ tetraPartition N := by
  rw [← tetraPartition_zero]; exact tetraPartition_mono (Nat.zero_le N)

/-- The cut-off of the tetrahedron sum can be removed: the sum has a limit. -/
def TetraRemovable : Prop := ∃ L : ℝ, Tendsto tetraPartition atTop (𝓝 L)

/-- A monotone sequence converges exactly when it is bounded. -/
theorem tetraRemovable_iff_bddAbove : TetraRemovable ↔ BddAbove (Set.range tetraPartition) := by
  constructor
  · rintro ⟨L, hL⟩
    exact hL.bddAbove_range
  · intro hb
    exact ⟨_, tendsto_atTop_ciSup tetraPartition_mono hb⟩

/-- **Hypothesis, not proved here:** the cut-off sum of the tetrahedron is unbounded, as for the
2-sphere. Proving it needs a growth lower bound for `Σ Π (s+1) (6j)²`. -/
def TetraUnbounded : Prop := ¬ BddAbove (Set.range tetraPartition)

/-- If the sum is unbounded, the cut-off cannot be removed. -/
theorem not_tetraRemovable_of_unbounded (h : TetraUnbounded) : ¬ TetraRemovable :=
  fun hr => h (tetraRemovable_iff_bddAbove.1 hr)

/-- The all-spin-`1` colouring (doubled spin `2`) contributes `3⁶ · (1/6)² = 81/4`. -/
lemma tetraTerm_two : tetraTerm (fun _ => 2) = 81 / 4 := by
  have h : (sixJSym 2 2 2 2 2 2 : ℝ) = 1 / 6 := Tests.sixJ_all_two
  simp only [tetraTerm, h]
  norm_num [Finset.prod_const]

/-- At doubled cut-off `2` the sum is at least `1 + 81/4`: the zero colouring and the all-`2` one.
This is a proved lower bound, in line with the exact value `2393/4` (numerical evidence). -/
lemma tetraPartition_two_ge : 1 + 81 / 4 ≤ tetraPartition 2 := by
  have hsub : ({fun _ => 0, fun _ => 2} : Finset (Fin 6 → ℕ)) ⊆
      Fintype.piFinset (fun _ : Fin 6 => range (2 + 1)) := by
    intro s hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [Fintype.mem_piFinset]
  have hne : (fun _ : Fin 6 => (0 : ℕ)) ≠ fun _ => 2 := by
    intro h; have := congrFun h 0; omega
  calc (1 : ℝ) + 81 / 4
      = ∑ s ∈ ({fun _ => 0, fun _ => 2} : Finset (Fin 6 → ℕ)), tetraTerm s := by
        rw [Finset.sum_pair hne, tetraTerm_two]
        rw [tetraTerm_zero]
    _ ≤ tetraPartition 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => tetraTerm_nonneg s

end Lightlike.SpinFoam

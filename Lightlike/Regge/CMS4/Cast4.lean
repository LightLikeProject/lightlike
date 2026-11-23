import Lightlike.Regge.CMS4.Comb4

/-!
# Integer model versus real model of the Kuhn star (dimension 4)

Cast lemmas relating the integer data of `Comb4` (`kvZ`, `vZ`, `cw1`, `inClsB`, `det4Z`) to the real
data of `JetCore4` / `Inc4` (`kv4`, `kpos4`, `clsW1`, `InClass4`, `det4`), and the rewriting of a class
sum `clsSum4` as a sum over a duplicate-free list of incidences.

## Main results

* `kv4_eq_cast`, `kpos4_sub_cast`: the real vertices are the casts of the integer ones.
* `inClass4_iff`, `mem_incsOf_iff`: the class membership tests agree.
* `det4_cast`: the real determinant of integer vectors is the cast of `det4Z`.
* `clsSum4_eq_list_sum`: a class sum over a nodup list of the incidences of the class.
-/

namespace Lightlike.Regge4

/-- The orthoscheme vertices are casts of the integer ones. -/
theorem kv4_eq_cast (k : Fin 5) (j : Fin 4) : kv4 k j = (kvZ k j : ℝ) := by
  fin_cases k <;> fin_cases j <;> simp [kv4, kvZ]

/-- The difference of two vertices of an incidence is the cast of the integer edge vector. -/
theorem kpos4_sub_cast (σ : Fin 24) (h : Fin 10) (t p : Fin 5) :
    kpos4 σ h t - kpos4 σ h p = fun i => (vZ σ t p i : ℝ) := by
  funext i
  simp only [kpos4, vZ, Pi.sub_apply, kv4_eq_cast]
  push_cast
  ring

/-- The first edge vector of a class is the cast of the integer one. -/
theorem clsW1_cast (c : Fin 4 → Fin 3) : clsW1 c = fun i => (cw1 c i : ℝ) := by
  funext i
  simp only [clsW1, cw1]
  split_ifs <;> simp

/-- The second edge vector of a class is the cast of the integer one. -/
theorem clsW2_cast (c : Fin 4 → Fin 3) : clsW2 c = fun i => (cw2 c i : ℝ) := by
  funext i
  simp only [clsW2, cw2]
  split_ifs <;> simp

/-- The two membership tests of a class agree. -/
theorem inClass4_iff (c : Fin 4 → Fin 3) (σ : Fin 24) (h : Fin 10) :
    InClass4 c σ h ↔ inClsB c σ h = true := by
  simp only [InClass4, inClsB, Bool.and_eq_true, decide_eq_true_eq]
  have e1 : (∀ i, kv4 (hQ h) (perms4 σ i) - kv4 (hP h) (perms4 σ i) = clsW1 c i) ↔
      vZ σ (hQ h) (hP h) = cw1 c := by
    rw [funext_iff, clsW1_cast]
    refine forall_congr' fun i => ?_
    simp only [vZ, kv4_eq_cast]
    constructor
    · intro hi; exact_mod_cast hi
    · intro hi; exact_mod_cast hi
  have e2 : (∀ i, kv4 (hR h) (perms4 σ i) - kv4 (hQ h) (perms4 σ i) = clsW2 c i) ↔
      vZ σ (hR h) (hQ h) = cw2 c := by
    rw [funext_iff, clsW2_cast]
    refine forall_congr' fun i => ?_
    simp only [vZ, kv4_eq_cast]
    constructor
    · intro hi; exact_mod_cast hi
    · intro hi; exact_mod_cast hi
  rw [e1, e2]

/-- An incidence is in `incsOf c` exactly when its hinge is in the class. -/
theorem mem_incsOf_iff (c : Fin 4 → Fin 3) (e : Fin 24 × Fin 10) :
    e ∈ incsOf c ↔ InClass4 c e.1 e.2 := by
  rw [inClass4_iff]
  obtain ⟨σ, h⟩ := e
  simp [incsOf]

/-- The real determinant of integer vectors is the cast of the integer determinant. -/
theorem det4_cast (a b c d : Fin 4 → ℤ) :
    det4 (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) (fun i => (c i : ℝ)) (fun i => (d i : ℝ))
      = (det4Z a b c d : ℝ) := by
  rw [det4_expand]
  simp only [det4Z, d3, d3Z]
  push_cast
  ring

open Classical in
/-- A class sum is the sum over any duplicate-free list of the incidences of the class. -/
theorem clsSum4_eq_list_sum (c : Fin 4 → Fin 3) (f : Fin 24 → Fin 10 → ℝ)
    (L : List (Fin 24 × Fin 10)) (hL : L.Nodup) (hm : ∀ e, e ∈ L ↔ InClass4 c e.1 e.2) :
    clsSum4 c f = (L.map fun e => f e.1 e.2).sum := by
  unfold clsSum4
  rw [← Fintype.sum_prod_type' (f := fun σ h => if InClass4 c σ h then f σ h else 0)]
  have : (∑ x : Fin 24 × Fin 10, if InClass4 c x.1 x.2 then f x.1 x.2 else 0)
      = ∑ x ∈ L.toFinset, f x.1 x.2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp [hm]
  rw [this, List.sum_toFinset _ hL]

end Lightlike.Regge4

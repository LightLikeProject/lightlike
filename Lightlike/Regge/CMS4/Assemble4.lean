import Lightlike.Regge.CMS4.Cast4

/-!
# Assembling the angle sum of a class star in dimension 4

Rewriting the dihedral angle of an incidence of a class `c` as the fan angle of the integer
quotient vectors `orient c e`, and the class sum as a sum over the certified chain of `Comb4`.

## Main results

* `fanAng4_symm`: the fan angle is symmetric.
* `incAng4_orient`: for an incidence of the class `c`, `incAng4` is `fanAng4` of `orient c e`.
* `sum_take_getD`: a sum over `l.take n` is a sum over `Finset.range n` of `getD`.
-/

open Real Matrix
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The fan angle is symmetric in its two vectors (for a symmetric matrix). -/
theorem fanAng4_symm {G : Matrix (Fin 4) (Fin 4) ℝ} (hs : Gᵀ = G) (w₁ w₂ x y : Fin 4 → ℝ) :
    fanAng4 G w₁ w₂ x y = fanAng4 G w₁ w₂ y x := by
  unfold fanAng4
  rw [bf2_symm hs w₁ w₂ x y, mul_comm (bf2 G w₁ w₂ x x)]

/-- A sum over the first `n` entries of a list is a sum over `Finset.range n` of `getD`. -/
theorem sum_take_getD {α : Type*} [Inhabited α] (l : List α) (f : α → ℝ) :
    ∀ n, n ≤ l.length → ((l.take n).map f).sum = ∑ i ∈ Finset.range n, f (l.getD i default)
  | 0, _ => by simp
  | n + 1, hn => by
    rw [Finset.sum_range_succ, ← sum_take_getD l f n (by omega), List.take_add_one]
    have : l[n]? = some (l.getD n default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp
    rw [this]
    simp

/-- For an incidence of the class `c`, the dihedral angle is the fan angle of the oriented integer
quotient vectors, with the fixed axis vectors `cw1`, `ax2` of the class. -/
theorem incAng4_orient {m : Fin 4 → ℝ} (hG : (g m).PosDef) (c : Fin 4 → Fin 3)
    (e : Fin 24 × Fin 10) (he : e ∈ incsOf c) :
    incAng4 e.2 (incQ4 g m e.1 e.2) =
      fanAng4 (g m) (fun i => (cw1 c i : ℝ)) (fun i => (ax2 c i : ℝ))
        (fun i => ((orient c e).1 i : ℝ)) (fun i => ((orient c e).2 i : ℝ)) := by
  have hs : (g m)ᵀ = g m := by simpa [Matrix.IsSymm] using hG.1
  obtain ⟨σ, h⟩ := e
  have hin := (inClass4_iff c σ h).1 ((mem_incsOf_iff c (σ, h)).1 he)
  simp only [inClsB, Bool.and_eq_true, decide_eq_true_eq] at hin
  obtain ⟨h1, h2⟩ := hin
  have e1 : kpos4 σ h (hQ h) - kpos4 σ h (hP h) = fun i => (cw1 c i : ℝ) := by
    rw [kpos4_sub_cast, h1]
  have e2 : kpos4 σ h (hR h) - kpos4 σ h (hP h) = fun i => (ax2 c i : ℝ) := by
    funext i
    have a1 := congrFun (kpos4_sub_cast σ h (hR h) (hQ h)) i
    have a2 := congrFun (kpos4_sub_cast σ h (hQ h) (hP h)) i
    have a3 := congrFun (kpos4_sub_cast σ h (hR h) (hP h)) i
    simp only [Pi.sub_apply] at a1 a2 a3
    rw [h2] at a1
    rw [h1] at a2
    simp only [ax2, Pi.sub_apply]
    push_cast
    linarith
  rw [incAng4_eq_fanAng4 g hG σ h, e1, e2, kpos4_sub_cast, kpos4_sub_cast]
  simp only [orient]
  split_ifs
  · rfl
  · exact fanAng4_symm hs _ _ _ _

end Lightlike.Regge4

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

/-- The hinge edge vectors of an incidence of the class `c` are the axis vectors `cw1`, `ax2`. -/
theorem incAxes4 (c : Fin 4 → Fin 3) (σ : Fin 24) (h : Fin 10) (he : (σ, h) ∈ incsOf c) :
    kpos4 σ h (hQ h) - kpos4 σ h (hP h) = (fun i => (cw1 c i : ℝ)) ∧
      kpos4 σ h (hR h) - kpos4 σ h (hP h) = fun i => (ax2 c i : ℝ) := by
  have hin := (inClass4_iff c σ h).1 ((mem_incsOf_iff c (σ, h)).1 he)
  simp only [inClsB, Bool.and_eq_true, decide_eq_true_eq] at hin
  obtain ⟨h1, h2⟩ := hin
  refine ⟨by rw [kpos4_sub_cast, h1], ?_⟩
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

/-- The Gram determinant of the axis vectors of a class with an incidence is positive. -/
theorem gramW_class_pos {m : Fin 4 → ℝ} (hG : (g m).PosDef) (c : Fin 4 → Fin 3)
    (e : Fin 24 × Fin 10) (he : e ∈ incsOf c) :
    0 < gramW (g m) (fun i => (cw1 c i : ℝ)) (fun i => (ax2 c i : ℝ)) := by
  obtain ⟨σ, h⟩ := e
  obtain ⟨e1, e2⟩ := incAxes4 c σ h he
  have := gramW_incidence_pos g hG σ h
  rwa [e1, e2] at this

/-- For an incidence of the class `c`, the dihedral angle is the fan angle of the oriented integer
quotient vectors, with the fixed axis vectors `cw1`, `ax2` of the class. -/
theorem incAng4_orient {m : Fin 4 → ℝ} (hG : (g m).PosDef) (c : Fin 4 → Fin 3)
    (e : Fin 24 × Fin 10) (he : e ∈ incsOf c) :
    incAng4 e.2 (incQ4 g m e.1 e.2) =
      fanAng4 (g m) (fun i => (cw1 c i : ℝ)) (fun i => (ax2 c i : ℝ))
        (fun i => ((orient c e).1 i : ℝ)) (fun i => ((orient c e).2 i : ℝ)) := by
  have hs : (g m)ᵀ = g m := by simpa [Matrix.IsSymm] using hG.1
  obtain ⟨σ, h⟩ := e
  obtain ⟨e1, e2⟩ := incAxes4 c σ h he
  rw [incAng4_eq_fanAng4 g hG σ h, e1, e2, kpos4_sub_cast, kpos4_sub_cast]
  simp only [orient]
  split_ifs
  · rfl
  · exact fanAng4_symm hs _ _ _ _

/-- The class sum of a certified quad class is the sum over the first four incidences of the chain. -/
theorem clsSum4_quad (c : Fin 4 → Fin 3) (hq : quadCert c = true) (f : Fin 24 → Fin 10 → ℝ) :
    clsSum4 c f = ∑ i ∈ Finset.range 4, f (chainOf c |>.getD i default).1
      (chainOf c |>.getD i default).2 := by
  simp only [quadCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq
  obtain ⟨⟨⟨⟨⟨⟨hL, hlen⟩, hnd⟩, hcl⟩, hadj⟩, hLm⟩, hmL⟩ := hq
  have hm : ∀ e, e ∈ (chainOf c).take 4 ↔ InClass4 c e.1 e.2 := by
    intro e
    rw [← mem_incsOf_iff]
    constructor
    · intro h
      simpa using hmL e h
    · intro h
      simpa using hLm e h
  rw [clsSum4_eq_list_sum c f _ hnd hm, sum_take_getD (chainOf c) (fun e => f e.1 e.2) 4 (by omega)]

/-- The chain entries `i < 4` of a certified quad class are incidences of the class. -/
theorem chain_mem_quad (c : Fin 4 → Fin 3) (hq : quadCert c = true) (i : ℕ) (hi : i < 4) :
    (chainOf c).getD i default ∈ incsOf c := by
  simp only [quadCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq
  obtain ⟨⟨⟨⟨⟨⟨hL, hlen⟩, hnd⟩, hcl⟩, hadj⟩, hLm⟩, hmL⟩ := hq
  have h1 : (chainOf c).getD i default ∈ (chainOf c).take 4 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.2 ⟨i, by simp; omega, by simp⟩
  simpa using hmL _ h1

/-- **The angle sum of a quad class.** -/
theorem quad_angle_sum {m : Fin 4 → ℝ} (hG : (g m).PosDef) (c : Fin 4 → Fin 3)
    (hq : quadCert c = true) :
    clsSum4 c (fun σ h => incAng4 h (incQ4 g m σ h)) = 2 * π := by
  have hq' := hq
  simp only [quadCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq'
  obtain ⟨⟨⟨⟨⟨⟨hL, hlen⟩, hnd⟩, hcl⟩, hadj⟩, hLm⟩, hmL⟩ := hq'
  rw [clsSum4_quad c hq]
  set ch := chainOf c with hch
  let v : ℕ → Fin 4 → ℝ := fun i => fun k => (((orient c (ch.getD i default)).1 k : ℤ) : ℝ)
  have hD := gramW_class_pos g hG c _ (chain_mem_quad c hq 0 (by norm_num))
  have hnext : ∀ i < 4, (fun k => (((orient c (ch.getD i default)).2 k : ℤ) : ℝ)) = v (i + 1) := by
    intro i hi
    have := (hadj i (List.mem_range.2 hi)).2
    simp only [adjB, decide_eq_true_eq] at this
    simp only [v, this]
  have hpos : ∀ i < 4, 0 < det4 (fun i => (cw1 c i : ℝ)) (fun i => (ax2 c i : ℝ)) (v i) (v (i + 1)) := by
    intro i hi
    have := (hadj i (List.mem_range.2 hi)).1
    simp only [posB, decide_eq_true_eq] at this
    rw [← hnext i hi]
    simp only [v]
    rw [det4_cast]
    exact_mod_cast this
  have hc : ∃ a b : ℝ, v 4 = v 0 + a • (fun i => (cw1 c i : ℝ)) + b • (fun i => (ax2 c i : ℝ)) := by
    refine ⟨0, 0, ?_⟩
    simp only [v, hcl]
    simp
  have key := quad_fan4 hG hD v hpos hc
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [incAng4_orient g hG c _ (chain_mem_quad c hq i hi'), hnext i hi']

end Lightlike.Regge4

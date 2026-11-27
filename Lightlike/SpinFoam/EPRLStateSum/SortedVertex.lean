import Lightlike.SpinFoam.EPRLStateSum.VertexPerm
import Lightlike.SpinFoam.EPRLStateSum.IntrinsicVertex

/-!
# The intrinsic vertex is the contraction of the sorted-leg intertwiners

The intrinsic vertex `simpEIAux J z` (sorted labels `z`) is the contraction `contract5 J (sortT J z)` of the five intertwiners with
the legs in the sorted order, in the sorted channel `(0 1 | 2 3)` (`simpEIAux_eq_contract5`). The sorted tensor of the node `a` is
`Σ_i nodeT J a z i · cycT J i a`: the transition matrix `nodeT` (with the signs `nodeEta`) expands the sorted intertwiner in the cyclic one
(`sortT_eq_sum_nodeT`), by the change of channel and the exchanges of legs of `Symmetry.lean`.
-/

open Finset Lightlike.Recoupling Lightlike.SpinFoam PhyslibAlpha.Sl2

namespace Lightlike.SpinFoam.EPRLStateSum

/-- The node tensors of the sorted vertex: the intertwiner of node `a` with the legs in the sorted order `a.succAbove 0, …, 3` and the
virtual spin `z a` in the channel `(0 1 | 2 3)`. -/
noncomputable def sortT (j : Fin 5 → Fin 5 → ℕ) (z : Fin 5 → ℕ) : Fin 5 → (Fin 5 → ℤ) → ℝ :=
  fun a μ => fourJ (j a (a.succAbove 0)) (j a (a.succAbove 1)) (j a (a.succAbove 2)) (j a (a.succAbove 3)) (z a)
    (μ (a.succAbove 0)) (μ (a.succAbove 1)) (μ (a.succAbove 2)) (μ (a.succAbove 3))

/-- The channel tensors at the node `1`: the sorted `(t₀ t₂ | t₁ t₃)` and the cyclic `(t₁ t₃ | t₂ t₀)` differ by `(-1)^(l + (t₀+t₂+l)/2)`. -/
lemma eta_one (t₀ t₁ t₂ t₃ l : ℕ) (x₀ x₁ x₂ x₃ : ℤ) :
    fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃ = (-1) ^ (l + (t₀ + t₂ + l) / 2) * fourJ t₁ t₃ t₂ t₀ l x₁ x₃ x₂ x₀ := by
  have h1 := fourJ_swap₃₄ t₁ t₃ t₀ t₂ l x₁ x₃ x₀ x₂
  have h2 := fourJ_swapPairs t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃
  rw [h1, h2]
  have hs : ((-1 : ℝ) ^ ((l + t₀ + t₂) / 2)) * (-1) ^ ((l + t₀ + t₂) / 2) = 1 := by
    rw [← mul_pow]; norm_num
  have hl : ((-1 : ℝ) ^ l) * (-1) ^ l = 1 := by rw [← mul_pow]; norm_num
  have e : (t₀ + t₂ + l) / 2 = (l + t₀ + t₂) / 2 := by rw [show t₀ + t₂ + l = l + t₀ + t₂ by ring]
  rw [e, pow_add]
  linear_combination (-(fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃) * ((-1 : ℝ) ^ ((l + t₀ + t₂) / 2)) *
    ((-1 : ℝ) ^ ((l + t₀ + t₂) / 2))) * hl + (-(fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃)) * hs

/-- Two signs `(-1)^n * (-1)^n` multiply to `1` (used to turn `x = s y` into `y = s x`). -/
lemma neg_one_pow_sq' (n : ℕ) : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num

/-- The channel tensors at the node `2`: the sorted `(t₀ t₂ | t₁ t₃)` and the cyclic `(t₂ t₀ | t₃ t₁)` differ by
`(-1)^((t₀+t₂+l)/2 + (t₁+t₃+l)/2)`. -/
lemma eta_two (t₀ t₁ t₂ t₃ l : ℕ) (x₀ x₁ x₂ x₃ : ℤ) :
    fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃ =
      (-1) ^ ((t₀ + t₂ + l) / 2 + (t₁ + t₃ + l) / 2) * fourJ t₂ t₀ t₃ t₁ l x₂ x₀ x₃ x₁ := by
  have h1 := fourJ_swap₃₄ t₂ t₀ t₁ t₃ l x₂ x₀ x₁ x₃
  have h2 := fourJ_swap₁₂ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃
  rw [h1, h2, pow_add]
  have e1 : (l + t₁ + t₃) / 2 = (t₁ + t₃ + l) / 2 := by rw [show l + t₁ + t₃ = t₁ + t₃ + l by ring]
  rw [e1]
  have ha := neg_one_pow_sq' ((t₀ + t₂ + l) / 2)
  have hb := neg_one_pow_sq' ((t₁ + t₃ + l) / 2)
  linear_combination (-(fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃) * ((-1 : ℝ) ^ ((t₀ + t₂ + l) / 2)) *
    ((-1 : ℝ) ^ ((t₀ + t₂ + l) / 2))) * hb + (-(fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃)) * ha

/-- The channel tensors at the node `3`: the sorted `(t₀ t₂ | t₁ t₃)` and the cyclic `(t₃ t₁ | t₀ t₂)` differ by `(-1)^(l + (t₁+t₃+l)/2)`. -/
lemma eta_three (t₀ t₁ t₂ t₃ l : ℕ) (x₀ x₁ x₂ x₃ : ℤ) :
    fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃ = (-1) ^ (l + (t₁ + t₃ + l) / 2) * fourJ t₃ t₁ t₀ t₂ l x₃ x₁ x₀ x₂ := by
  have h1 := fourJ_swap₁₂ t₁ t₃ t₀ t₂ l x₁ x₃ x₀ x₂
  have h2 := fourJ_swapPairs t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃
  rw [h1, h2, pow_add]
  have ha := neg_one_pow_sq' l
  have hb := neg_one_pow_sq' ((t₁ + t₃ + l) / 2)
  linear_combination (-(fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃) * ((-1 : ℝ) ^ ((t₁ + t₃ + l) / 2)) *
    ((-1 : ℝ) ^ ((t₁ + t₃ + l) / 2))) * ha + (-(fourJ t₀ t₂ t₁ t₃ l x₀ x₂ x₁ x₃)) * hb

/-- The cyclic channel tensor `(c₀ c₂ | c₁ c₃)` of the node `a`: the legs `a+1, a+3, a+2, a+4`, the virtual spin `l`. -/
noncomputable def cycC (j : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (l : ℕ) (μ : Fin 5 → ℤ) : ℝ :=
  fourJ (j a (a + 1)) (j a (a + 3)) (j a (a + 2)) (j a (a + 4)) l (μ (a + 1)) (μ (a + 3)) (μ (a + 2)) (μ (a + 4))

/-- **The sorted channel tensor is the cyclic one times the sign `nodeEta`**, at every node. -/
lemma sorted_channel (j : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (l : ℕ) (μ : Fin 5 → ℤ) :
    fourJ (j a (a.succAbove 0)) (j a (a.succAbove 2)) (j a (a.succAbove 1)) (j a (a.succAbove 3)) l
        (μ (a.succAbove 0)) (μ (a.succAbove 2)) (μ (a.succAbove 1)) (μ (a.succAbove 3)) =
      nodeEta j a l * cycC j a l μ := by
  fin_cases a
  · simp [nodeEta, tetSignExp, cycC, Fin.succAbove]
  · have h := eta_one (j 1 0) (j 1 2) (j 1 3) (j 1 4) l (μ 0) (μ 2) (μ 3) (μ 4)
    simp [nodeEta, tetSignExp, cycC, Fin.succAbove]
    simpa using h
  · have h := eta_two (j 2 0) (j 2 1) (j 2 3) (j 2 4) l (μ 0) (μ 1) (μ 3) (μ 4)
    simp [nodeEta, tetSignExp, cycC, Fin.succAbove]
    simpa using h
  · have h := eta_three (j 3 0) (j 3 1) (j 3 2) (j 3 4) l (μ 0) (μ 1) (μ 2) (μ 4)
    simp [nodeEta, tetSignExp, cycC, Fin.succAbove]
    simpa using h
  · simp [nodeEta, tetSignExp, cycC, Fin.succAbove]

/-- The cyclic-order intertwiner of the node `a` with the virtual spin `k` in the channel `(0 1 | 2 3)` of the cyclic legs. -/
noncomputable def cycNode (j : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (k : ℕ) (μ : Fin 5 → ℤ) : ℝ :=
  fourJ (j a (a + 1)) (j a (a + 2)) (j a (a + 3)) (j a (a + 4)) k (μ (a + 1)) (μ (a + 2)) (μ (a + 3)) (μ (a + 4))

lemma cycT_eq_cycNode (j : Fin 5 → Fin 5 → ℕ) (i : Fin 5 → ℕ) (a : Fin 5) (μ : Fin 5 → ℤ) :
    cycT j i a μ = cycNode j a (i a) μ := rfl

/-- The cyclic intertwiner is the combination `Σ_l nodeP(k, l) ι^{(02|13)}_l` of the channel tensors. -/
lemma cycNode_eq_sum_cycC (j : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (k : ℕ) (μ : Fin 5 → ℤ) :
    cycNode j a k μ = ∑ l ∈ range (j a (a + 1) + j a (a + 3) + 1), nodeP j a k l * cycC j a l μ := by
  unfold cycNode cycC nodeP
  exact fourJ_eq_sum_fourRecoupling _ _ _ _ _ _ _ _ _

/-- The channel tensor of the cyclic legs vanishes outside its box. -/
lemma cycC_eq_zero_of_not_adm (j : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (l : ℕ) (μ : Fin 5 → ℤ)
    (h : ¬ AdmP j a l) : cycC j a l μ = 0 := by
  unfold cycC
  exact fourJ_eq_zero_of_not_adm (by unfold AdmP at h; exact h) _ _ _ _

/-- **The overlap**: the sum over the positional labels `k` of `nodeT(z, k)` times the cyclic intertwiner is
`Σ_m nodeI(z, m) η(m) ι^{(02|13)}_m`, by the orthogonality of the positional matrix. -/
lemma sum_nodeT_cycNode (j : Fin 5 → Fin 5 → ℕ) (hj : ∀ p q, j p q = j q p) (z : ℕ)
    (a : Fin 5) (μ : Fin 5 → ℤ) :
    ∑ k ∈ posBox j a, nodeT j a z k * cycNode j a k μ =
      ∑ m ∈ simpBox j a, nodeI j a z m * nodeEta j a m * cycC j a m μ := by
  classical
  have hbox : simpBox j a = range (j a (a + 1) + j a (a + 3) + 1) := by
    have h10 := hj 1 0
    have h20 := hj 2 0
    have h30 := hj 3 0
    have h31 := hj 3 1
    have h40 := hj 4 0
    have h42 := hj 4 2
    fin_cases a <;> simp [simpBox, h10, h20, h30, h31, h40, h42]
  rw [hbox]
  have step1 : ∀ k : ℕ, nodeT j a z k * cycNode j a k μ =
      ∑ m ∈ range (j a (a + 1) + j a (a + 3) + 1), ∑ l ∈ range (j a (a + 1) + j a (a + 3) + 1),
        (nodeI j a z m * nodeEta j a m * cycC j a l μ) * (nodeP j a k m * nodeP j a k l) := by
    intro k
    unfold nodeT
    rw [hbox, cycNode_eq_sum_cycC, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [Finset.sum_congr rfl fun k _ => step1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_comm]
  have step2 : ∀ l ∈ range (j a (a + 1) + j a (a + 3) + 1),
      ∑ k ∈ posBox j a, (nodeI j a z m * nodeEta j a m * cycC j a l μ) * (nodeP j a k m * nodeP j a k l) =
        (nodeI j a z m * nodeEta j a m * cycC j a l μ) *
          (if m = l ∧ Lightlike.Pentagon.Tri (j a (a + 1)) (j a (a + 3)) m ∧ Lightlike.Pentagon.Tri m (j a (a + 2)) (j a (a + 4)) then 1 else 0) := by
    intro l _
    rw [← Finset.mul_sum, sum_nodeP_mul]
  rw [Finset.sum_congr rfl step2]
  rw [Finset.sum_eq_single_of_mem m hm]
  · by_cases hA : AdmP j a m
    · have : (if m = m ∧ Lightlike.Pentagon.Tri (j a (a + 1)) (j a (a + 3)) m ∧ Lightlike.Pentagon.Tri m (j a (a + 2)) (j a (a + 4)) then (1 : ℝ) else 0) = 1 := by
        rw [if_pos ⟨rfl, hA⟩]
      rw [this, mul_one]
    · rw [cycC_eq_zero_of_not_adm j a m μ hA]
      simp
  · intro l _ hlm
    rw [if_neg (fun h => hlm h.1.symm), mul_zero]

/-- The sorted matrix vanishes above its box: `l ≤ t₀ + t₂`. -/
lemma nodeI_eq_zero_of_gt (j : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (z l : ℕ)
    (h : j a (a.succAbove 0) + j a (a.succAbove 2) < l) : nodeI j a z l = 0 := by
  unfold nodeI fourRecoupling
  by_cases h6 : sixJSym (j a (a.succAbove 0)) (j a (a.succAbove 1)) z (j a (a.succAbove 3)) (j a (a.succAbove 2)) l = 0
  · rw [h6, mul_zero]
  · exfalso
    obtain ⟨-, t2, -, -⟩ := Lightlike.Pentagon.tri_of_sixJSym_ne_zero h6
    unfold Lightlike.Pentagon.Tri at t2
    omega

/-- **The sorted intertwiner is the transition matrix applied to the cyclic ones**: for symmetric `J`,
`sortT J z a μ = Σ_k nodeT J a (z a) k · cycNode J a k μ`. -/
lemma sortT_eq_sum_nodeT (j : Fin 5 → Fin 5 → ℕ) (hj : ∀ p q, j p q = j q p) (z : Fin 5 → ℕ) (a : Fin 5)
    (μ : Fin 5 → ℤ) :
    sortT j z a μ = ∑ k ∈ posBox j a, nodeT j a (z a) k * cycNode j a k μ := by
  rw [sum_nodeT_cycNode j hj (z a) a μ]
  have hbox : simpBox j a = range (j a (a + 1) + j a (a + 3) + 1) := by
    have h10 := hj 1 0
    have h20 := hj 2 0
    have h30 := hj 3 0
    have h31 := hj 3 1
    have h40 := hj 4 0
    have h42 := hj 4 2
    fin_cases a <;> simp [simpBox, h10, h20, h30, h31, h40, h42]
  rw [hbox]
  unfold sortT
  rw [fourJ_eq_sum_fourRecoupling]
  set g : ℕ → ℝ := fun l => nodeI j a (z a) l * nodeEta j a l * cycC j a l μ with hg
  have hg1 : ∀ l ∈ range (j a (a.succAbove 0) + j a (a.succAbove 2) + 1),
      fourRecoupling (j a (a.succAbove 0)) (j a (a.succAbove 1)) (j a (a.succAbove 2)) (j a (a.succAbove 3)) (z a) l *
        fourJ (j a (a.succAbove 0)) (j a (a.succAbove 2)) (j a (a.succAbove 1)) (j a (a.succAbove 3)) l
          (μ (a.succAbove 0)) (μ (a.succAbove 2)) (μ (a.succAbove 1)) (μ (a.succAbove 3)) = g l := by
    intro l _
    rw [sorted_channel j a l μ]
    simp only [hg, nodeI]
    ring
  rw [Finset.sum_congr rfl hg1]
  -- both sums are the sum of `g` over a larger box
  have hz1 : ∀ l, l ∉ range (j a (a.succAbove 0) + j a (a.succAbove 2) + 1) → g l = 0 := by
    intro l hl
    have : j a (a.succAbove 0) + j a (a.succAbove 2) < l := by
      simpa [Finset.mem_range, not_lt] using hl
    simp only [hg, nodeI_eq_zero_of_gt j a (z a) l this, zero_mul]
  have hz2 : ∀ l, l ∉ range (j a (a + 1) + j a (a + 3) + 1) → g l = 0 := by
    intro l hl
    have hlt : j a (a + 1) + j a (a + 3) < l := by simpa [Finset.mem_range, not_lt] using hl
    have hA : ¬ AdmP j a l := by
      intro h
      have := h.1
      unfold Lightlike.Pentagon.Tri at this
      omega
    simp only [hg, cycC_eq_zero_of_not_adm j a l μ hA, mul_zero]
  have hbig1 : ∑ l ∈ range (j a (a.succAbove 0) + j a (a.succAbove 2) + 1), g l =
      ∑ l ∈ range (j a (a.succAbove 0) + j a (a.succAbove 2) + 1 + (j a (a + 1) + j a (a + 3) + 1)), g l := by
    refine Finset.sum_subset (fun l hl => ?_) fun l _ hl => hz1 l hl
    simp only [Finset.mem_range] at hl ⊢; omega
  have hbig2 : ∑ l ∈ range (j a (a + 1) + j a (a + 3) + 1), g l =
      ∑ l ∈ range (j a (a.succAbove 0) + j a (a.succAbove 2) + 1 + (j a (a + 1) + j a (a + 3) + 1)), g l := by
    refine Finset.sum_subset (fun l hl => ?_) fun l _ hl => hz2 l hl
    simp only [Finset.mem_range] at hl ⊢; omega
  rw [hbig1, ← hbig2]

/-- **The intrinsic vertex is the contraction of the sorted-leg intertwiners**: for symmetric triangle spins `J`,
`simpEIAux J z = contract5 J (sortT J z)`. -/
theorem simpEIAux_eq_contract5 (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (z : Fin 5 → ℕ) :
    simpEIAux J z = contract5 J (sortT J z) := by
  have h : sortT J z = fun a μ => ∑ k ∈ posBox J a, nodeT J a (z a) k * cycNode J a k μ :=
    funext fun a => funext fun μ => sortT_eq_sum_nodeT J hJ z a μ
  rw [h, contract5_sum, simpEIAux_eq_sum_nodeT J hJ z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [posF_eq_fifteenJ J hJ i, fifteenJSimplex_eq_contract5 J hJ i]
  rfl

end Lightlike.SpinFoam.EPRLStateSum

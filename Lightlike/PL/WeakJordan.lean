import Lightlike.PL.WeakJordanAssemble

/-!
# The weak Jordan theorem

The complement of a circuit in the plane is not connected.

## Main results

* `weak_jordan_extremal`: two arcs from a highest point `a` to a lowest point `b` that meet only at
  their ends have a disconnected complement (Klazar, arXiv:2604.04296, Section 2, Claim 4).
-/

open Set

namespace Lightlike.PL

/-- An arc has a point other than its ends. -/
lemma IsArc.exists_mid {A : Set (ℝ × ℝ)} {p q : ℝ × ℝ} (h : IsArc A p q) :
    ∃ z ∈ A, z ≠ p ∧ z ≠ q := by
  obtain ⟨γ, -, hi, h0, h1, rfl⟩ := h
  refine ⟨γ (1 / 2), ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩, fun hz => ?_, fun hz => ?_⟩
  · have := hi ⟨by norm_num, by norm_num⟩ ⟨le_rfl, zero_le_one⟩ (hz.trans h0.symm)
    norm_num at this
  · have := hi ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩ (hz.trans h1.symm)
    norm_num at this

/-- A segment splits at an inner point into two segments that meet only there. -/
lemma segment_inter_of_mem {c d e : ℝ × ℝ} (he : e ∈ segment ℝ c d) {z : ℝ × ℝ}
    (h1 : z ∈ segment ℝ c e) (h2 : z ∈ segment ℝ e d) : z = e := by
  have a1 := dist_add_dist_of_mem_segment h1
  have a2 := dist_add_dist_of_mem_segment h2
  have a3 := dist_add_dist_of_mem_segment he
  have a4 := dist_triangle c z d
  have c1 := dist_comm z e
  have c2 := dist_comm e z
  have : dist z e ≤ 0 := by linarith
  exact dist_le_zero.1 this

/-- **The weak Jordan theorem for two arcs between a highest and a lowest point.** -/
theorem weak_jordan_extremal {A₀ A₁ : Set (ℝ × ℝ)} {a b : ℝ × ℝ} (h₀ : IsArc A₀ a b)
    (h₁ : IsArc A₁ a b) (hi : A₀ ∩ A₁ = {a, b}) (hab : b.2 < a.2)
    (hext : ∀ z ∈ A₀ ∪ A₁, b.2 ≤ z.2 ∧ z.2 ≤ a.2) : ¬ IsPreconnected (A₀ ∪ A₁)ᶜ := by
  intro hD
  have hcomp : ∀ {A : Set (ℝ × ℝ)} {p q : ℝ × ℝ}, IsArc A p q → IsCompact A := by
    rintro A p q ⟨γ, hc, -, -, -, rfl⟩
    exact isCompact_Icc.image_of_continuousOn hc
  set K : Set (ℝ × ℝ) := A₀ ∪ A₁ with hK
  have hKc : IsCompact K := (hcomp h₀).union (hcomp h₁)
  have hDo : IsOpen Kᶜ := hKc.isClosed.isOpen_compl
  have haK : a ∈ K := Or.inl h₀.left_mem
  have hbK : b ∈ K := Or.inl h₀.right_mem
  have hne : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  obtain ⟨M, hM⟩ := (hKc.image continuous_fst).bddAbove
  have hKx : ∀ z ∈ K, z.1 < M + 1 := fun z hz => by
    have : z.1 ≤ M := hM ⟨z, hz, rfl⟩
    linarith
  -- the horizontal segment
  set y₀ : ℝ := (a.2 + b.2) / 2 with hy₀
  obtain ⟨c, d, hc, hd, hcy, hdy, hT⟩ := exists_T h₀ h₁ (y₀ := y₀) (by simp only [hy₀]; linarith)
    (by simp only [hy₀]; linarith)
  have hy1 : b.2 < y₀ := by simp only [hy₀]; linarith
  have hy2 : y₀ < a.2 := by simp only [hy₀]; linarith
  have hcK : c ∈ K := Or.inl hc
  have hdK : d ∈ K := Or.inr hd
  have hca : c ≠ a := fun h => by rw [h] at hcy; linarith
  have hcb : c ≠ b := fun h => by rw [h] at hcy; linarith
  have hda : d ≠ a := fun h => by rw [h] at hdy; linarith
  have hdb : d ≠ b := fun h => by rw [h] at hdy; linarith
  have hcd : c ≠ d := fun h => by
    have : c ∈ A₀ ∩ A₁ := ⟨hc, h ▸ hd⟩
    rw [hi] at this
    rcases this with h' | h'
    · exact hca h'
    · exact hcb h'
  set T : Set (ℝ × ℝ) := segment ℝ c d with hTdef
  have hTK : ∀ z ∈ T, z ∈ K → z = c ∨ z = d := fun z hz hzK => by
    rcases hzK with hzK | hzK
    · exact Or.inl ((hT z hz).1 hzK)
    · exact Or.inr ((hT z hz).2 hzK)
  have hTy : ∀ z ∈ T, z.2 = y₀ := fun z hz => by
    obtain ⟨t, -, -, -, e2⟩ := mem_seg_coords hz
    rw [e2, hcy, hdy]; ring
  have hTx : ∀ z ∈ T, z.1 < M + 1 := fun z hz => by
    obtain ⟨t, ht0, ht1, e1, -⟩ := mem_seg_coords hz
    have hcx := hKx c hcK
    have hdx := hKx d hdK
    rw [e1]
    rcases eq_or_lt_of_le ht0 with rfl | hpos
    · linarith
    · nlinarith [mul_pos hpos (sub_pos.2 hdx), mul_nonneg (sub_nonneg.2 ht1) (sub_pos.2 hcx).le]
  have he₀T : midpoint ℝ c d ∈ T := midpoint_mem_segment c d
  have he₀c : midpoint ℝ c d ≠ c := fun h => hcd ((midpoint_eq_left_iff ℝ).1 h)
  have he₀d : midpoint ℝ c d ≠ d := fun h => hcd ((midpoint_eq_right_iff ℝ).1 h)
  have he₀K : midpoint ℝ c d ∉ K := fun h => by
    rcases hTK _ he₀T h with h' | h'
    · exact he₀c h'
    · exact he₀d h'
  -- the outer arc
  obtain ⟨l, hl, hl1, hl2, hFK, hbetw⟩ := exists_outer (K := K) (X := M + 1) hab hext hKx haK hbK
  set F : Set (ℝ × ℝ) := chainSet l with hFdef
  have hFarc : IsArc F a b := IsArc.chain hl hl1 hl2 (two_le_length hl1 hl2 hne)
  have hFT : ∀ z ∈ F, z ∉ T := fun z hz hzT =>
    hbetw z hz ⟨by rw [hTy z hzT]; exact hy1, by rw [hTy z hzT]; exact hy2, hTx z hzT⟩
  obtain ⟨g₀, hg₀F, hg₀a, hg₀b⟩ := hFarc.exists_mid
  have hg₀K : g₀ ∉ K := fun h => by
    rcases hFK ⟨hg₀F, h⟩ with h' | h'
    · exact hg₀a h'
    · exact hg₀b h'
  obtain ⟨e, heT, g, hgF, B, hBD, hBarc, hBT, hBF⟩ := exists_link hDo hD
    (isCompact_segment' ..).isClosed (isClosed_chainSet l)
    (Set.disjoint_left.2 fun z hz hzF => hFT z hzF hz) he₀T hg₀F he₀K hg₀K
  have heB : e ∈ B := hBarc.left_mem
  have hgB : g ∈ B := hBarc.right_mem
  have heK : e ∉ K := hBD heB
  have hgK : g ∉ K := hBD hgB
  have hec : e ≠ c := fun h => heK (h ▸ hcK)
  have hed : e ≠ d := fun h => heK (h ▸ hdK)
  have hga : g ≠ a := fun h => hgK (h ▸ haK)
  have hgb : g ≠ b := fun h => hgK (h ▸ hbK)
  -- the pieces
  obtain ⟨Pac, Pcb, hPac, hPcb, hP0, hP0i⟩ := h₀.split hc hca hcb
  obtain ⟨Pad, Pdb, hPad, hPdb, hP1, hP1i⟩ := h₁.split hd hda hdb
  obtain ⟨Pag, Pgb, hPag, hPgb, hP2, hP2i⟩ := hFarc.split hgF hga hgb
  have hTec : IsArc (segment ℝ c e) e c := (IsArc.of_segment (Ne.symm hec)).symm
  have hTed : IsArc (segment ℝ e d) e d := IsArc.of_segment hed
  have heTc : segment ℝ c e ⊆ T := (convex_segment c d).segment_subset (left_mem_segment ℝ c d) heT
  have heTd : segment ℝ e d ⊆ T := (convex_segment c d).segment_subset heT (right_mem_segment ℝ c d)
  have s0 : ∀ z, z ∈ A₀ ↔ z ∈ Pac ∨ z ∈ Pcb := fun z => by rw [← hP0]; rfl
  have s1 : ∀ z, z ∈ A₁ ↔ z ∈ Pad ∨ z ∈ Pdb := fun z => by rw [← hP1]; rfl
  have s2 : ∀ z, z ∈ F ↔ z ∈ Pag ∨ z ∈ Pgb := fun z => by rw [← hP2]; rfl
  have s0i : ∀ z, z ∈ Pac → z ∈ Pcb → z = c := fun z h h' => by
    have : z ∈ Pac ∩ Pcb := ⟨h, h'⟩
    rw [hP0i] at this; exact this
  have s1i : ∀ z, z ∈ Pad → z ∈ Pdb → z = d := fun z h h' => by
    have : z ∈ Pad ∩ Pdb := ⟨h, h'⟩
    rw [hP1i] at this; exact this
  have s2i : ∀ z, z ∈ Pag → z ∈ Pgb → z = g := fun z h h' => by
    have : z ∈ Pag ∩ Pgb := ⟨h, h'⟩
    rw [hP2i] at this; exact this
  have f_hi : ∀ z, z ∈ A₀ → z ∈ A₁ → z = a ∨ z = b := fun z h h' => by
    have : z ∈ A₀ ∩ A₁ := ⟨h, h'⟩
    rw [hi] at this; exact this
  have f_FK : ∀ z, z ∈ F → (z ∈ A₀ ∨ z ∈ A₁) → z = a ∨ z = b := fun z h h' => hFK ⟨h, h'⟩
  have f_TK : ∀ z, z ∈ T → (z ∈ A₀ ∨ z ∈ A₁) → z = c ∨ z = d := fun z h h' => hTK z h h'
  have f_BK : ∀ z, z ∈ B → ¬ (z ∈ A₀ ∨ z ∈ A₁) := fun z h h' => hBD h h'
  have f_BT : ∀ z, z ∈ B → z ∈ T → z = e := fun z h h' => by
    have : z ∈ B ∩ T := ⟨h, h'⟩
    rw [hBT] at this; exact this
  have f_BF : ∀ z, z ∈ B → z ∈ F → z = g := fun z h h' => by
    have : z ∈ B ∩ F := ⟨h, h'⟩
    rw [hBF] at this; exact this
  have f_c : ∀ z, z ∈ segment ℝ c e → z ∈ T := fun z h => heTc h
  have f_d : ∀ z, z ∈ segment ℝ e d → z ∈ T := fun z h => heTd h
  have f_FT' : ∀ z, z ∈ F → z ∉ T := hFT
  exact false_of_pieces hPac hPad hPag hPcb.symm hPdb.symm hPgb.symm hTec hTed hBarc
    s0i s1i s2i (fun z h h' => segment_inter_of_mem heT h h')
    (fun z h h' => by grind) (fun z h h' => by grind) (fun z h h' => by grind)
    (fun z h => by grind) (fun z h h' => by grind) (fun z h h' => by grind)
    (fun z h h' => by grind) hne hcd hca hcb hda hdb

end Lightlike.PL

import Lightlike.GR.ParkeTaylorBCFW

/-!
# The Parke-Taylor formula for every position of the negative-helicity gluons, by BCFW recursion

Elvang-Huang p. 39 derive the Parke-Taylor formula recursively for adjacent negative-helicity gluons
(`ParkeTaylorBCFW.lean`) and leave the non-adjacent case to the reader ("Try your own hands on the proof for the
non-adjacent case"). Here: for `A_n[1⁻ ⋯ j⁻ ⋯]` with `j ≥ 3` (gluons `0` and `j − 1 ≥ 2` here), the `[1, 2⟩` shift of the
negative gluon `1` and its positive neighbour `2` (a `[−, +⟩` shift of adjacent lines, valid by (3.11), p. 37) keeps a
single diagram, `Â_{n−1}(1̂⁻, P̂^±, 4, …) Â₃(−P̂^∓, 2̂⁺, 3)/P₂₃²`, with the three-point factor `Â₃(−P̂⁻, 2̂⁺, 3⁺)` if `3` is
positive and `Â₃(−P̂⁺, 2̂⁺, 3⁻)` if `3` is the second negative gluon.

* `parkeTaylor_bcfw_far`: the Parke-Taylor amplitudes satisfy these recursions (both three-point factors are
  `[23]/c` for `|P̂] = c|2] + |3]`, `c = ⟨12⟩/⟨13⟩`);
* `IsBCFWFamilyMHV`, `eq_parkeTaylor_of_bcfw_mhv`: a family of MHV amplitudes with the three-point amplitudes (2.77)
  and these recursions is the Parke-Taylor family `⟨1j⟩⁴/(⟨12⟩ ⋯ ⟨n1⟩)` for every position `j`;
* `eq_parkeTaylor_of_bcfw_mhv'`: for negative gluons at any positions `i ≠ j`, relabelled cyclically so that `i` comes
  first (Elvang-Huang p. 25, property 1), `A_n = ⟨ij⟩⁴/(⟨12⟩ ⋯ ⟨n1⟩)`, the formula (2.80).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: (2.77), p. 23; (2.80) and the cyclic property,
  pp. 24–25; (3.11), p. 37; (3.12)–(3.22) and the remark on the non-adjacent case, pp. 37–39.
-/

open Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

variable {m : ℕ}

lemma parkeTaylor_mul_angleBr {n : ℕ} (a b c d : Fin 2 → ℂ) (s : Fin n → Fin 2 → ℂ) :
    parkeTaylor a b s * angleBr c d ^ 4 = parkeTaylor c d s * angleBr a b ^ 4 := by
  unfold parkeTaylor; ring

/-- The three-point factors of the non-adjacent recursion for the choice `|P̂] = c|2] + |3]` (gluons `1, 2` here):
`Â₃(−P̂⁻, 2̂⁺, 3⁺) = [23]/c`. -/
lemma antiMHV3_far (l1 l2 : Fin 2 → ℂ) (c : ℂ) (hs : squareBr l1 l2 ≠ 0) (hc : c ≠ 0) :
    antiMHV3 l1 l2 (c • l1 + l2) = squareBr l1 l2 / c := by
  have hs1 : squareBr l2 (c • l1 + l2) = c * squareBr l2 l1 := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hs2 : squareBr (c • l1 + l2) l1 = squareBr l2 l1 := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hq : squareBr l2 l1 = -squareBr l1 l2 := squareBr_antisymm _ _
  unfold antiMHV3
  rw [hs1, hs2, hq]
  field_simp

/-- `Â₃(−P̂⁺, 2̂⁺, 3⁻) = [23]/c` (gluons `1, 2` here). -/
lemma antiMHV3_two (l1 l2 : Fin 2 → ℂ) (c : ℂ) (hs : squareBr l1 l2 ≠ 0) (hc : c ≠ 0) :
    antiMHV3 (c • l1 + l2) l1 l2 = squareBr l1 l2 / c := by
  have hs1 : squareBr l2 (c • l1 + l2) = c * squareBr l2 l1 := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hs2 : squareBr (c • l1 + l2) l1 = squareBr l2 l1 := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hq : squareBr l2 l1 = -squareBr l1 l2 := squareBr_antisymm _ _
  unfold antiMHV3
  rw [hs1, hs2, hq]
  field_simp

/-- **The Parke-Taylor amplitudes with a non-adjacent second negative gluon satisfy the `[1, 2⟩` recursion**:
for `j ≥ 2` (gluons `0`, `j` here) and the choice `⟨P̂| = ⟨3|`, `|P̂] = c|2] + |3]`,
`⟨1j⟩⁴/(⟨12⟩ ⋯ ⟨n1⟩) = (Parke-Taylor of 1, P̂, 4, …, n) · ([23]/c)/P₂₃²`. -/
theorem parkeTaylor_bcfw_far (l lt : Fin (m + 4) → Fin 2 → ℂ) (j : Fin (m + 4))
    (h01 : angleBr (lt 0) (lt 1) ≠ 0) (h02 : angleBr (lt 0) (lt 2) ≠ 0) (h12 : angleBr (lt 1) (lt 2) ≠ 0)
    (h23 : angleBr (lt 2) (lt 3) ≠ 0) (hR : restProd lt ≠ 0) (hs12 : squareBr (l 1) (l 2) ≠ 0) :
    parkeTaylor (lt 0) (lt j) lt =
      parkeTaylor (lt 0) (lt j) (lt ∘ (1 : Fin (m + 4)).succAbove) *
        (squareBr (l 1) (l 2) / (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2))) /
          (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) := by
  set c := angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2) with hc
  have hc0 : c ≠ 0 := div_ne_zero h01 h02
  have hP0 : vecMulVec (c • l 1 + l 2) (lt 2) ≠ 0 := by
    intro h0
    have hlt2 : lt 2 ≠ 0 := fun e => h02 (by rw [e, angleBr_eq]; simp)
    obtain ⟨b, hb⟩ : ∃ b, lt 2 b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hlt2 (funext hcon)
    have hl : c • l 1 + l 2 ≠ 0 := by
      intro e
      apply hs12
      have : l 2 = -(c • l 1) := eq_neg_of_add_eq_zero_right e
      rw [this, squareBr_eq]
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨a, ha⟩ : ∃ a, (c • l 1 + l 2) a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hl (funext hcon)
    have e := congrFun (congrFun h0 a) b
    simp only [vecMulVec_apply, Matrix.zero_apply] at e
    exact (mul_ne_zero ha hb) e
  have adj := parkeTaylor_bcfw l lt h01 h02 h12 h23 hR hs12 (lP := c • l 1 + l 2) (ltP := lt 2) rfl hP0
  rw [cons_eq_comp_succAbove, mul_div_assoc, antiMHV3_div_channel l lt hs12 h12 c] at adj
  -- the numerators: `⟨1j⟩⁴` against `⟨12⟩⁴` and `⟨13⟩⁴`
  have e1 := parkeTaylor_mul_angleBr (lt 0) (lt j) (lt 0) (lt 1) lt
  have L0 : (lt ∘ (1 : Fin (m + 4)).succAbove) 0 = lt 0 := by
    simp [Fin.succAbove_of_castSucc_lt _ _ (show (Fin.castSucc 0 : Fin (m + 4)) < 1 from by
      rw [Fin.lt_def]; simp)]
  have e2 := parkeTaylor_mul_angleBr (lt 0) (lt j) (lt 0) (lt 2) (lt ∘ (1 : Fin (m + 4)).succAbove)
  have hpt1 : parkeTaylor (lt 0) (lt j) lt =
      parkeTaylor (lt 0) (lt 1) lt * angleBr (lt 0) (lt j) ^ 4 / angleBr (lt 0) (lt 1) ^ 4 := by
    field_simp; linear_combination e1
  have hpt2 : parkeTaylor (lt 0) (lt j) (lt ∘ (1 : Fin (m + 4)).succAbove) =
      parkeTaylor (lt 0) (lt 2) (lt ∘ (1 : Fin (m + 4)).succAbove) * angleBr (lt 0) (lt j) ^ 4 /
        angleBr (lt 0) (lt 2) ^ 4 := by
    field_simp; linear_combination e2
  rw [hpt1, hpt2, adj, hc]
  field_simp

/-- A family of colour-ordered MHV amplitudes `A_n[1⁻ ⋯ j⁻ ⋯]` with the negative-helicity gluons at `0` and `j`
(`n = m + 3`, functions of the angle spinors in colour order), with the three-point amplitudes (2.77) (`j = 1`, and
`j = 2` cyclically relabelled) and the single-diagram BCFW recursions: the `[1, 2⟩` shift of two adjacent negative
gluons for `j = 1` (3.18), and of the negative gluon `0` and its positive neighbour `1` for `j ≥ 2`, for every set of
square spinors and the choice `⟨P̂| = ⟨3|`, `|P̂] = c|2] + |3]`, `c = ⟨12⟩/⟨13⟩` (gluons `1, 2` here). -/
structure IsBCFWFamilyMHV (A : ∀ m : ℕ, Fin (m + 3) → (Fin (m + 3) → Fin 2 → ℂ) → ℂ) : Prop where
  three_one : ∀ lt : Fin 3 → Fin 2 → ℂ, A 0 1 lt =
    angleBr (lt 0) (lt 1) ^ 3 / (angleBr (lt 1) (lt 2) * angleBr (lt 2) (lt 0))
  three_two : ∀ lt : Fin 3 → Fin 2 → ℂ, A 0 2 lt =
    angleBr (lt 2) (lt 0) ^ 3 / (angleBr (lt 0) (lt 1) * angleBr (lt 1) (lt 2))
  rec_one : ∀ (m : ℕ) (l lt : Fin (m + 4) → Fin 2 → ℂ), squareBr (l 1) (l 2) ≠ 0 →
    A (m + 1) 1 lt = A m 1 (lt ∘ (1 : Fin (m + 4)).succAbove) *
      antiMHV3 (l 2) ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (l 1) /
        (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2))
  rec_two : ∀ (m : ℕ) (l lt : Fin (m + 4) → Fin 2 → ℂ), squareBr (l 1) (l 2) ≠ 0 →
    A (m + 1) 2 lt = A m 1 (lt ∘ (1 : Fin (m + 4)).succAbove) *
      antiMHV3 ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (l 1) (l 2) /
        (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2))
  rec_far : ∀ (m : ℕ) (l lt : Fin (m + 4) → Fin 2 → ℂ) (j : Fin (m + 4)) (hj : 3 ≤ (j : ℕ)),
    squareBr (l 1) (l 2) ≠ 0 →
    A (m + 1) j lt = A m ⟨(j : ℕ) - 1, by omega⟩ (lt ∘ (1 : Fin (m + 4)).succAbove) *
      antiMHV3 (l 1) (l 2) ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) /
        (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2))

lemma succAbove_one_of_pos {k : Fin (m + 3)} (hk : 1 ≤ (k : ℕ)) :
    ((1 : Fin (m + 4)).succAbove k : ℕ) = k + 1 := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
  simp

lemma parkeTaylor_three_two (lt : Fin 3 → Fin 2 → ℂ) (hg : GenericAngles lt) :
    angleBr (lt 2) (lt 0) ^ 3 / (angleBr (lt 0) (lt 1) * angleBr (lt 1) (lt 2)) =
      parkeTaylor (lt 0) (lt 2) lt := by
  have h01 := hg 0 1 (by decide)
  have h12 := hg 1 2 (by decide)
  have h20 := hg 2 0 (by decide)
  have r0 : finRotate 3 0 = 1 := by decide
  have r1 : finRotate 3 1 = 2 := by decide
  have r2 : finRotate 3 2 = 0 := by decide
  simp only [parkeTaylor, cycDen, Fin.prod_univ_three, r0, r1, r2]
  rw [angleBr_antisymm (lt 0) (lt 2)]
  field_simp

/-- **The Parke-Taylor formula for every position of the second negative gluon, by BCFW recursion**:
`A_n[1⁻ ⋯ j⁻ ⋯] = ⟨1j⟩⁴/(⟨12⟩ ⋯ ⟨n1⟩)` (gluons `0`, `j` here) for nonvanishing brackets. -/
theorem eq_parkeTaylor_of_bcfw_mhv {A : ∀ m : ℕ, Fin (m + 3) → (Fin (m + 3) → Fin 2 → ℂ) → ℂ}
    (hA : IsBCFWFamilyMHV A) :
    ∀ (m : ℕ) (j : Fin (m + 3)) (lt : Fin (m + 3) → Fin 2 → ℂ), j ≠ 0 → GenericAngles lt →
      A m j lt = parkeTaylor (lt 0) (lt j) lt := by
  -- the adjacent case
  have hadj : ∀ (m : ℕ) (lt : Fin (m + 3) → Fin 2 → ℂ), GenericAngles lt →
      A m 1 lt = parkeTaylor (lt 0) (lt 1) lt :=
    eq_parkeTaylor_of_bcfw ⟨hA.three_one, hA.rec_one⟩
  intro m
  induction m with
  | zero =>
    intro j lt hj hg
    fin_cases j
    · exact absurd rfl hj
    · exact hadj 0 lt hg
    · change A 0 2 lt = parkeTaylor (lt 0) (lt 2) lt
      rw [hA.three_two lt]
      exact parkeTaylor_three_two lt hg
  | succ m ih =>
    intro j lt hj hg
    have v1 : ((1 : Fin (m + 4)) : ℕ) = 1 := by simp
    have v2 : ((2 : Fin (m + 4)) : ℕ) = 2 := by simp
    have v3 : ((3 : Fin (m + 4)) : ℕ) = 3 := by simp
    have ne : ∀ a b : Fin (m + 4), (a : ℕ) ≠ b → a ≠ b := fun a b h e => h (congrArg Fin.val e)
    have h01 := hg 0 1 (ne _ _ (by rw [v1]; simp))
    have h02 := hg 0 2 (ne _ _ (by rw [v2]; simp))
    have h12 := hg 1 2 (ne _ _ (by rw [v1, v2]; simp))
    have h23 := hg 2 3 (ne _ _ (by rw [v2, v3]; simp))
    have n21 : (2 : Fin (m + 4)) ≠ 1 := ne _ _ (by rw [v1, v2]; simp)
    set l : Fin (m + 4) → Fin 2 → ℂ := fun k => if k = 1 then ![1, 0] else ![0, 1] with hl
    have hl1 : l 1 = ![1, 0] := by simp [hl]
    have hl2 : l 2 = ![0, 1] := by simp [hl, n21]
    have hs12 : squareBr (l 1) (l 2) ≠ 0 := by rw [hl1, hl2, squareBr_eq]; simp
    have hc0 : angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2) ≠ 0 := div_ne_zero h01 h02
    have hjv : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    rcases Nat.lt_or_ge (j : ℕ) 3 with hj3 | hj3
    · rcases (show (j : ℕ) = 1 ∨ (j : ℕ) = 2 by omega) with h | h
      · have : j = 1 := Fin.ext (by rw [h, v1])
        subst this
        exact hadj (m + 1) lt hg
      · have : j = 2 := Fin.ext (by rw [h, v2])
        subst this
        rw [hA.rec_two m l lt hs12, hadj m _ (hg.comp_succAbove 1), antiMHV3_two _ _ _ hs12 hc0]
        have hL1 : (lt ∘ (1 : Fin (m + 4)).succAbove) 1 = lt 2 := by
          simp only [Function.comp_apply]
          congr 1
        have hL0 : (lt ∘ (1 : Fin (m + 4)).succAbove) 0 = lt 0 := by
          simp [Fin.succAbove_of_castSucc_lt _ _ (show (Fin.castSucc 0 : Fin (m + 4)) < 1 from by
            rw [Fin.lt_def]; simp)]
        rw [hL0, hL1, parkeTaylor_bcfw_far l lt 2 h01 h02 h12 h23 (restProd_ne_zero hg) hs12]
    · set j' : Fin (m + 3) := ⟨(j : ℕ) - 1, by omega⟩ with hj'
      have hj'0 : j' ≠ 0 := fun h => by have := congrArg Fin.val h; simp [hj'] at this; omega
      rw [hA.rec_far m l lt j hj3 hs12, ih j' _ hj'0 (hg.comp_succAbove 1), antiMHV3_far _ _ _ hs12 hc0]
      have hLj : (lt ∘ (1 : Fin (m + 4)).succAbove) j' = lt j := by
        simp only [Function.comp_apply]
        congr 1
        exact Fin.ext (by rw [succAbove_one_of_pos (by simp [hj']; omega)]; simp [hj']; omega)
      have hL0 : (lt ∘ (1 : Fin (m + 4)).succAbove) 0 = lt 0 := by
        simp [Fin.succAbove_of_castSucc_lt _ _ (show (Fin.castSucc 0 : Fin (m + 4)) < 1 from by
          rw [Fin.lt_def]; simp)]
      rw [hL0, hLj, parkeTaylor_bcfw_far l lt j h01 h02 h12 h23 (restProd_ne_zero hg) hs12]

/-- The cyclic denominator is invariant under cyclic relabelling by any shift. -/
lemma cycDen_add_right (lt : Fin (m + 3) → Fin 2 → ℂ) (i : Fin (m + 3)) :
    cycDen (fun k => lt (k + i)) = cycDen lt := by
  unfold cycDen
  have h : ∀ k : Fin (m + 3), finRotate (m + 3) k + i = finRotate (m + 3) (k + i) := by
    intro k
    rw [finRotate_apply, finRotate_apply]
    abel
  simp only [h]
  exact Equiv.prod_comp (Equiv.addRight i) (fun k => angleBr (lt k) (lt (finRotate (m + 3) k)))

/-- **The Parke-Taylor formula for any positions `i ≠ j` of the two negative-helicity gluons** (Elvang-Huang (2.80)):
relabelling cyclically so that `i` comes first (colour-ordered amplitudes are cyclic, Elvang-Huang p. 25, property 1),
the amplitude of a BCFW family is `⟨ij⟩⁴/(⟨12⟩ ⋯ ⟨n1⟩)`. -/
theorem eq_parkeTaylor_of_bcfw_mhv' {A : ∀ m : ℕ, Fin (m + 3) → (Fin (m + 3) → Fin 2 → ℂ) → ℂ}
    (hA : IsBCFWFamilyMHV A) (m : ℕ) (i j : Fin (m + 3)) (lt : Fin (m + 3) → Fin 2 → ℂ) (hij : i ≠ j)
    (hg : GenericAngles lt) :
    A m (j - i) (fun k => lt (k + i)) = parkeTaylor (lt i) (lt j) lt := by
  have hg' : GenericAngles (fun k => lt (k + i)) := fun a b hab => hg _ _ fun e => hab (add_right_cancel e)
  rw [eq_parkeTaylor_of_bcfw_mhv hA m (j - i) _ (sub_ne_zero.2 (Ne.symm hij)) hg', parkeTaylor,
    parkeTaylor, cycDen_add_right, zero_add, sub_add_cancel]

end Lightlike.SpinorHelicity

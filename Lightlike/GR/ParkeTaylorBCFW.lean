import Lightlike.GR.BCFWFactorization

/-!
# The Parke-Taylor formula by BCFW recursion

Elvang-Huang §3.2 prove the Parke-Taylor formula `A_n[1⁻ 2⁻ 3⁺ ⋯ n⁺] = ⟨12⟩⁴/(⟨12⟩⟨23⟩ ⋯ ⟨n1⟩)` (3.9) by
induction on `n` with the `[1, 2⟩` shift: the recursion (3.7) has a single non-vanishing diagram (3.18),
`A_n = Â_{n−1}(1̂⁻, P̂₂₃⁻, 4⁺, …, n⁺) · (1/P₂₃²) · Â₃(−P̂₂₃⁺, 2̂⁻, 3⁺)`, and with the formula for `n − 1` points
and the anti-MHV three-point amplitude this is (3.9) again ((3.19)–(3.22)).

* **The Parke-Taylor amplitudes satisfy the BCFW recursion** (`parkeTaylor_bcfw`): for every choice of spinors
  `|P̂]`, `⟨P̂|` of the on-shell channel momentum, `A_n = A_{n−1}(1̂, P̂, 4, …, n) A₃(−P̂, 2̂, 3)/P₂₃²`; the proof is
  the residue formula (3.4) applied to the shifted amplitude `Â(z)` (`ptShift_rational`,
  `eval_zero_eq_neg_sum_residues`) and the factorization of its residue (`ptShift_factorization`).
* **The recursion determines the amplitudes** (`eq_parkeTaylor_of_bcfw`): any family of colour-ordered MHV
  amplitudes `A_n` with the three-point amplitude `A₃[1⁻ 2⁻ 3⁺] = ⟨12⟩³/(⟨23⟩⟨31⟩)` (2.77) that satisfies the
  single-diagram recursion (3.18) (`IsBCFWFamily`) is the Parke-Taylor family, for nonvanishing brackets.

Gluons `1, 2, 3, …, n` of the source are `0, 1, 2, …, n − 1` here; a family of MHV amplitudes depends on the angle
spinors of the gluons in colour order. For the choice `⟨P̂| = ⟨3|`, `|P̂] = c|2] + |3]` (`c = ⟨12⟩/⟨13⟩`) of
the spinors of the on-shell `P̂₂₃` (`ptShift_onshell`) the angle spinors of the `(n − 1)`-point amplitude are
those of `1, 3, 4, …, n` (`Fin.succAbove 1`), and `Â₃(−P̂⁺, 2̂⁻, 3⁺)/P₂₃² = c³/⟨23⟩` (`antiMHV3_div_channel`).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: (2.77), p. 23; §3.2, the Parke-Taylor
  amplitude (3.9) and the induction (3.12)–(3.22), pp. 37–39 ("This completes the inductive step … we have then
  proven the Parke-Taylor formula for all n").
-/

open Matrix Polynomial

noncomputable section

namespace Lightlike.SpinorHelicity

variable {m : ℕ}

/-- **The Parke-Taylor amplitudes satisfy the BCFW recursion** (Elvang-Huang (3.18)–(3.22)): for every choice
of spinors `|P̂]`, `⟨P̂|` of the on-shell channel momentum `P̂₂₃` at the pole,
`A_n[1⁻2⁻3⁺⋯n⁺] = Â_{n−1}(1̂⁻, P̂⁻, 4⁺, …, n⁺) Â₃(−P̂⁺, 2̂⁻, 3⁺) / P₂₃²`. -/
theorem parkeTaylor_bcfw (l lt : Fin (m + 4) → Fin 2 → ℂ) (h01 : angleBr (lt 0) (lt 1) ≠ 0)
    (h02 : angleBr (lt 0) (lt 2) ≠ 0) (h12 : angleBr (lt 1) (lt 2) ≠ 0)
    (h23 : angleBr (lt 2) (lt 3) ≠ 0) (hR : restProd lt ≠ 0) (hs12 : squareBr (l 1) (l 2) ≠ 0)
    {lP ltP : Fin 2 → ℂ}
    (hP : vecMulVec lP ltP =
      vecMulVec ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2))
    (hP0 : vecMulVec lP ltP ≠ 0) :
    parkeTaylor (lt 0) (lt 1) lt =
      parkeTaylor (lt 0) ltP
          (Fin.cons (lt 0) (Fin.cons ltP (fun k : Fin (m + 1) => lt k.succ.succ.succ)) :
            Fin (m + 3) → Fin 2 → ℂ) *
        antiMHV3 (l 2) lP (l 1) / (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) := by
  set zs := angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)
  have hzs : (0 : ℂ) ≠ zs := (div_ne_zero h12 h02).symm
  -- `A_n = Â(0)`
  have h0 : ptShift lt 0 = parkeTaylor (lt 0) (lt 1) lt := by
    unfold ptShift
    have : bcfwAngle lt 0 1 0 = lt := by
      funext k
      by_cases hk : k = 1
      · subst hk; simp [bcfwAngle]
      · exact Function.update_of_ne hk _ _
    rw [this]
  -- `Â(0) = −Res_{z*} Â(z)/z`
  have hrat := ptShift_rational lt h01 h02 h23 hR hzs
  have hres := eval_zero_eq_neg_sum_residues (Finset.univ : Finset Unit) (fun _ => zs)
    (Set.injOn_of_subsingleton _ _) (degree_ptShift_numerator lt) (fun _ _ => hzs.symm)
  have hw : residue (Finset.univ : Finset Unit) (fun _ => zs)
      (Polynomial.C (-(angleBr (lt 0) (lt 1) ^ 3 /
        (angleBr (lt 0) (lt 2) * angleBr (lt 2) (lt 3) * restProd lt)))) default =
      -(angleBr (lt 0) (lt 1) ^ 3 / (angleBr (lt 0) (lt 2) * angleBr (lt 2) (lt 3) * restProd lt)) := by
    simp [residue, Lagrange.nodalWeight]
  have key := ptShift_factorization l lt h01 h02 h12 h23 hR hs12 hP hP0
  rw [neg_div, neg_div, neg_inj] at key
  rw [← h0, hrat, hres, Fintype.sum_unique, hw, neg_div, neg_neg]
  exact key

/-- The three-point factor and the propagator for the choice `|P̂] = c|2] + |3]`:
`Â₃(−P̂⁺, 2̂⁻, 3⁺)/P₂₃² = c³/⟨23⟩` (gluons `1, 2` here). -/
lemma antiMHV3_div_channel (l lt : Fin (m + 4) → Fin 2 → ℂ) (hs12 : squareBr (l 1) (l 2) ≠ 0)
    (h12 : angleBr (lt 1) (lt 2) ≠ 0) (c : ℂ) :
    antiMHV3 (l 2) (c • l 1 + l 2) (l 1) / (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) =
      c ^ 3 / angleBr (lt 1) (lt 2) := by
  have hs1 : squareBr (l 2) (c • l 1 + l 2) = c * squareBr (l 2) (l 1) := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hs2 : squareBr (c • l 1 + l 2) (l 1) = squareBr (l 2) (l 1) := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hq : squareBr (l 2) (l 1) = -squareBr (l 1) (l 2) := squareBr_antisymm _ _
  unfold antiMHV3
  rw [hs1, hs2, hq]
  field_simp

/-- The angle spinors of the `(n − 1)`-point amplitude `Â_{n−1}(1̂, P̂, 4, …, n)` for `⟨P̂| = ⟨3|`: those of
`1, 3, 4, …, n`. -/
lemma cons_eq_comp_succAbove (lt : Fin (m + 4) → Fin 2 → ℂ) :
    (Fin.cons (lt 0) (Fin.cons (lt 2) (fun k : Fin (m + 1) => lt k.succ.succ.succ)) :
      Fin (m + 3) → Fin 2 → ℂ) = lt ∘ (1 : Fin (m + 4)).succAbove := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp [Fin.succAbove_of_castSucc_lt _ _ (show (Fin.castSucc 0 : Fin (m + 4)) < 1 from by
      rw [Fin.lt_def]; simp)]
  · simp only [Fin.cons_succ, Fin.cons_zero, Function.comp_apply]
    congr 1
  · simp only [Fin.cons_succ, Function.comp_apply]
    congr 1

/-- A family of colour-ordered MHV amplitudes `A_n[1⁻ 2⁻ 3⁺ ⋯ n⁺]` (`n = m + 3`, functions of the angle
spinors of the gluons in colour order) with the three-point amplitude (2.77) and the single-diagram BCFW
recursion (3.18) with the choice `⟨P̂| = ⟨3|`, `|P̂] = c|2] + |3]`, `c = ⟨12⟩/⟨13⟩`, for every set of square
spinors. -/
structure IsBCFWFamily (A : ∀ m : ℕ, (Fin (m + 3) → Fin 2 → ℂ) → ℂ) : Prop where
  three : ∀ lt : Fin 3 → Fin 2 → ℂ, A 0 lt =
    angleBr (lt 0) (lt 1) ^ 3 / (angleBr (lt 1) (lt 2) * angleBr (lt 2) (lt 0))
  recursion : ∀ (m : ℕ) (l lt : Fin (m + 4) → Fin 2 → ℂ), squareBr (l 1) (l 2) ≠ 0 →
    A (m + 1) lt = A m (lt ∘ (1 : Fin (m + 4)).succAbove) *
      antiMHV3 (l 2) ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (l 1) /
        (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2))

/-- Nonvanishing brackets of distinct gluons. -/
def GenericAngles {k : ℕ} (lt : Fin k → Fin 2 → ℂ) : Prop :=
  ∀ a b, a ≠ b → angleBr (lt a) (lt b) ≠ 0

lemma GenericAngles.comp_succAbove {k : ℕ} {lt : Fin (k + 1) → Fin 2 → ℂ} (h : GenericAngles lt)
    (p : Fin (k + 1)) : GenericAngles (lt ∘ p.succAbove) := fun _ _ hab =>
  h _ _ (fun e => hab (Fin.succAbove_right_injective e))

lemma restProd_ne_zero {lt : Fin (m + 4) → Fin 2 → ℂ} (h : GenericAngles lt) : restProd lt ≠ 0 := by
  unfold restProd
  refine Finset.prod_ne_zero_iff.2 fun k _ => h _ _ fun e => ?_
  have := congrArg Fin.val e
  rw [coe_finRotate] at this
  split_ifs at this with hl
  · simp at this
  · simp at this

lemma parkeTaylor_three (lt : Fin 3 → Fin 2 → ℂ) (hg : GenericAngles lt) :
    angleBr (lt 0) (lt 1) ^ 3 / (angleBr (lt 1) (lt 2) * angleBr (lt 2) (lt 0)) =
      parkeTaylor (lt 0) (lt 1) lt := by
  have h01 := hg 0 1 (by decide)
  have r0 : finRotate 3 0 = 1 := by decide
  have r1 : finRotate 3 1 = 2 := by decide
  have r2 : finRotate 3 2 = 0 := by decide
  simp only [parkeTaylor, cycDen, Fin.prod_univ_three, r0, r1, r2]
  field_simp

/-- The inductive step (Elvang-Huang (3.18)–(3.22)). -/
lemma bcfw_step {A : ∀ m : ℕ, (Fin (m + 3) → Fin 2 → ℂ) → ℂ} (hA : IsBCFWFamily A) (m : ℕ)
    (ih : ∀ lt : Fin (m + 3) → Fin 2 → ℂ, GenericAngles lt → A m lt = parkeTaylor (lt 0) (lt 1) lt)
    (lt : Fin (m + 4) → Fin 2 → ℂ) (hg : GenericAngles lt) :
    A (m + 1) lt = parkeTaylor (lt 0) (lt 1) lt := by
  have v1 : ((1 : Fin (m + 4)) : ℕ) = 1 := by simp
  have v2 : ((2 : Fin (m + 4)) : ℕ) = 2 := by simp
  have v3 : ((3 : Fin (m + 4)) : ℕ) = 3 := by simp
  have ne : ∀ a b : Fin (m + 4), (a : ℕ) ≠ b → a ≠ b := fun a b h e => h (congrArg Fin.val e)
  have h01 := hg 0 1 (ne _ _ (by rw [v1]; simp))
  have h02 := hg 0 2 (ne _ _ (by rw [v2]; simp))
  have h12 := hg 1 2 (ne _ _ (by rw [v1, v2]; simp))
  have h23 := hg 2 3 (ne _ _ (by rw [v2, v3]; simp))
  have n21 : (2 : Fin (m + 4)) ≠ 1 := ne _ _ (by rw [v1, v2]; simp)
  -- square spinors with `[23] ≠ 0` (gluons `1, 2` here)
  set l : Fin (m + 4) → Fin 2 → ℂ := fun k => if k = 1 then ![1, 0] else ![0, 1] with hl
  have hl1 : l 1 = ![1, 0] := by simp [hl]
  have hl2 : l 2 = ![0, 1] := by simp [hl, n21]
  have hs12 : squareBr (l 1) (l 2) ≠ 0 := by rw [hl1, hl2, squareBr_eq]; simp
  set c := angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)
  have hP0 : vecMulVec (c • l 1 + l 2) (lt 2) ≠ 0 := by
    intro h0
    have hlt2 : lt 2 ≠ 0 := fun e => h02 (by rw [e, angleBr_eq]; simp)
    obtain ⟨b, hb⟩ : ∃ b, lt 2 b ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hlt2 (funext hc)
    have e := congrFun (congrFun h0 1) b
    simp [vecMulVec_apply, hl1, hl2] at e
    exact hb e
  rw [hA.recursion m l lt hs12, ih _ (hg.comp_succAbove 1)]
  rw [parkeTaylor_bcfw l lt h01 h02 h12 h23 (restProd_ne_zero hg) hs12 rfl hP0,
    ← cons_eq_comp_succAbove]
  simp only [Fin.cons_zero, Fin.cons_one]

/-- **The Parke-Taylor formula by BCFW recursion** (Elvang-Huang §3.2, (3.9), (3.18)–(3.22)): a family of
colour-ordered MHV amplitudes with the three-point amplitude (2.77) satisfying the single-diagram BCFW
recursion is the Parke-Taylor family, `A_n[1⁻ 2⁻ 3⁺ ⋯ n⁺] = ⟨12⟩⁴/(⟨12⟩⟨23⟩ ⋯ ⟨n1⟩)`, for nonvanishing brackets. -/
theorem eq_parkeTaylor_of_bcfw {A : ∀ m : ℕ, (Fin (m + 3) → Fin 2 → ℂ) → ℂ} (hA : IsBCFWFamily A) :
    ∀ (m : ℕ) (lt : Fin (m + 3) → Fin 2 → ℂ), GenericAngles lt →
      A m lt = parkeTaylor (lt 0) (lt 1) lt := by
  intro m
  induction m with
  | zero => exact fun lt hg => (hA.three lt).trans (parkeTaylor_three lt hg)
  | succ m ih => exact fun lt hg => bcfw_step hA m ih lt hg

end Lightlike.SpinorHelicity

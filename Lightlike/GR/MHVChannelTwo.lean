import Lightlike.GR.MHVChannelZero

/-!
# The channel `[1, 2]` of the recursion for the true amplitudes

The pole of the channel `[1, 2]` sits at `z = ⟨12⟩/⟨02⟩`, where `|1̂⟩ = (⟨01⟩/⟨02⟩) |2⟩` and the channel momentum is
`P = −(c|1] + |2])⟨2|` with `c = ⟨01⟩/⟨02⟩` (Elvang-Huang (3.17)–(3.18)).
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The scalar product of two null momenta in spinor form. -/
lemma mdot_nullMom_two (a b c d : Fin 2 → ℂ) :
    mdot (nullMom a b) (nullMom c d) = (1 / 2) * angleBr b d * squareBr a c := by
  rw [nullMom_eq_momOf_smul, nullMom_eq_momOf_smul, mdot_momOf_smul_vec]; ring

/-- Schouten: the angle spinor of the leg `1` at the pole is proportional to `⟨2|`. -/
lemma sub_smul_eq_smul_two (a b c : Fin 2 → ℂ) (hbc : angleBr b c ≠ 0) :
    a - (angleBr a c / angleBr b c) • b = (angleBr b a / angleBr b c) • c := by
  have hD : c 1 * b 0 - c 0 * b 1 ≠ 0 := by
    intro h; apply hbc; rw [angleBr_eq]; linear_combination h
  ext i
  fin_cases i <;> simp [angleBr_eq] <;> field_simp <;> ring

/-- The two-leg channel momentum before the shift. -/
lemma momRange_two (p : ℕ → Fin 4 → ℂ) : momRange p 1 2 = p 1 + p 2 := by
  simp [momRange, Finset.sum_Ico_succ_top]

/-- The pole of the channel `[1, 2]`. -/
lemma zpole_two (l lt : ℕ → Fin 2 → ℂ) (h02 : angleBr (lt 0) (lt 2) ≠ 0) (h12 : squareBr (l 1) (l 2) ≠ 0) :
    zpole l lt 2 = angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2) := by
  have hP : momRange (shiftedMom l lt 0) 1 2 = nullMom (l 1) (lt 1) + nullMom (l 2) (lt 2) := by
    rw [momRange_two]; simp [shiftedMom]
  unfold zpole
  rw [hP]
  simp only [mdot_add_left, mdot_add_right, mdot_nullMom_two]
  have a1 : angleBr (lt 1) (lt 1) = 0 := by rw [angleBr_eq]; ring
  have a2 : angleBr (lt 2) (lt 2) = 0 := by rw [angleBr_eq]; ring
  have s1 : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
  have s2 : squareBr (l 2) (l 2) = 0 := by rw [squareBr_eq]; ring
  have hs : squareBr (l 2) (l 1) = -squareBr (l 1) (l 2) := squareBr_antisymm _ _
  have ha : angleBr (lt 2) (lt 1) = -angleBr (lt 1) (lt 2) := angleBr_antisymm _ _
  have hb : angleBr (lt 2) (lt 0) = -angleBr (lt 0) (lt 2) := angleBr_antisymm _ _
  rw [a1, a2, s1, s2, hs, ha, hb]
  field_simp
  ring

/-- `nullMom` is linear in the angle spinor. -/
lemma nullMom_smul_right (a b : Fin 2 → ℂ) (c : ℂ) : nullMom a (c • b) = c • nullMom a b := by
  funext μ
  fin_cases μ <;> simp [nullMom, momOf, Matrix.vecMulVec_apply] <;> ring

/-- **The channel momentum at the pole of `[1, 2]`** is `P = −(c|1] + |2])⟨2|`, `c = ⟨01⟩/⟨02⟩`. -/
lemma momRange_pole_two (l lt : ℕ → Fin 2 → ℂ) (h02 : angleBr (lt 0) (lt 2) ≠ 0)
    (h12 : squareBr (l 1) (l 2) ≠ 0) :
    momRange (shiftedMom l lt (zpole l lt 2)) 1 2 =
      nullMom ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) := by
  rw [momRange_two, zpole_two l lt h02 h12]
  have h1 : shiftedMom l lt (angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)) 1 =
      nullMom (l 1) ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • lt 2) := by
    simp only [shiftedMom, if_neg (show (1 : ℕ) ≠ 0 by omega), if_true]
    rw [sub_smul_eq_smul_two (lt 1) (lt 0) (lt 2) h02]
  have h2 : shiftedMom l lt (angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)) 2 = nullMom (l 2) (lt 2) := by
    simp [shiftedMom]
  rw [h1, h2, nullMom_smul_right, add_comm ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1) (l 2),
    nullMom_add_smul_left, add_comm]

/-- **The left three-point amplitude of the channel `[1, 2]`, both gluons positive, the internal leg negative**:
`A₃(1⁺, 2⁺, P⁻) = [12] ⟨q P⟩² / (⟨q 1⟩⟨q 2⟩)`. -/
theorem leftAmp_ppm_two (p ê : ℕ → Fin 4 → ℂ) (lh lth : ℕ → Fin 2 → ℂ) (lP ltP qs qa : Fin 2 → ℂ)
    (ε : Fin 4 → ℂ) (hp1 : p 1 = nullMom (lh 1) (lth 1)) (hp2 : p 2 = nullMom (lh 2) (lth 2))
    (hP : momRange p 1 2 = nullMom lP ltP)
    (he1 : ê 1 = epsPlus (lh 1) (lth 1) qa) (he2 : ê 2 = epsPlus (lh 2) (lth 2) qa)
    (hε : ε = epsMinus lP (-ltP) qs)
    (hy1 : angleBr qa (lth 1) ≠ 0) (hy2 : angleBr qa (lth 2) ≠ 0) (hx : squareBr qs lP ≠ 0) :
    bgAmplitude 0 (leftMom p 1 2 (-momRange p 1 2)) (leftPol ê 1 2 ε) =
      squareBr (lh 1) (lh 2) * angleBr qa (-ltP) ^ 2 / (angleBr qa (lth 1) * angleBr qa (lth 2)) := by
  have hc : Conserved3 ![lh 1, lh 2, lP] ![lth 1, lth 2, -ltP] := by
    rw [conserved3_iff]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, nullMom_neg_right]
    rw [← hp1, ← hp2, ← hP, momRange_two]; abel
  refine (bgAmplitude_three_ppm_gen ![lh 1, lh 2, lP] ![lth 1, lth 2, -ltP] hc qs qa _ _ ?_ ?_ ?_ ?_ ?_ hy1 hy2 hx).trans ?_
  · simp [leftMom, hp1]
  · simp [leftMom, hp2]
  · simp [leftPol, he1]
  · simp [leftPol, he2]
  · simp [leftPol, hε]
  · simp

/-- **The channel term `[1, 2]` with both external gluons of the left factor positive** is the anti-MHV three-point
amplitude times the right amplitude with the internal gluon positive (the other helicity of the internal gluon has an
all-positive left factor, which vanishes). -/
theorem channelTerm_two_ppm (m : ℕ) (p ê : ℕ → Fin 4 → ℂ) (lh lth : ℕ → Fin 2 → ℂ) (lP ltP : Fin 2 → ℂ)
    (qs qa : Fin 2 → ℂ)
    (hp1 : p 1 = nullMom (lh 1) (lth 1)) (hp2 : p 2 = nullMom (lh 2) (lth 2))
    (hP : momRange p 1 2 = nullMom lP ltP)
    (he1 : ê 1 = epsPlus (lh 1) (lth 1) qa) (he2 : ê 2 = epsPlus (lh 2) (lth 2) qa)
    (hy1 : angleBr qa (lth 1) ≠ 0) (hy2 : angleBr qa (lth 2) ≠ 0) (hx : squareBr qs lP ≠ 0) :
    channelTerm m p ê 1 2 lP ltP qs qa =
      squareBr (lh 1) (lh 2) * angleBr qa (-ltP) ^ 2 / (angleBr qa (lth 1) * angleBr qa (lth 2)) *
        bgAmplitude (m - (2 - 1)) (collapse p 1 2 (momRange p 1 2)) (collapse ê 1 2 (epsPlus lP ltP qa)) := by
  have hB : bgAmplitude (2 - 2) (leftMom p 1 2 (-momRange p 1 2)) (leftPol ê 1 2 (epsPlus lP (-ltP) qa)) = 0 :=
    leftAmp_allPlus 2 p ê lh lth lP ltP qa _
      (fun t ht => by
        interval_cases t
        · simpa using he1
        · simpa using he2) rfl _
  unfold channelTerm
  show bgAmplitude (2 - 2) _ _ * _ + bgAmplitude (2 - 2) _ _ * _ = _
  rw [hB, leftAmp_ppm_two p ê lh lth lP ltP qs qa _ hp1 hp2 hP he1 he2 rfl hy1 hy2 hx]
  ring

end Lightlike.SpinorHelicity

import Lightlike.Asymptotics.EPRL.CriticalValue
import Lightlike.Asymptotics.EPRL.Localise
import Lightlike.Asymptotics.EPRL.GaugeFix

/-!
# The maximum set of the coherent amplitude, and the sign symmetry

For the Regge state of a 4-simplex and spins proportional to the triangle areas, the points of
`SU(2)^5` with `|F_n| = 1` and `X₄ = 1` are exactly the sign lifts `X_a = ± c_a` (with `X₄ = 1`)
of the two critical classes `c = critMinus` and `c = critPlus σ` (`norm_eq_one_iff_signLift`).

If the sum of the spins at each node is even, `F_n` is invariant under the change of sign of any
`X_a` (`cohAmp_flip`), hence under every sign pattern (`cohAmp_signLift`); this is what makes all
sixteen sign lifts of a class contribute equally to the asymptotics.
-/

open Matrix Finset

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Regge4

/-- The sign lift `a ↦ (-1)^{s a} c a` of a tuple of matrices. -/
def signLift (c : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (s : Fin 5 → Bool) :
    Fin 5 → Matrix (Fin 2) (Fin 2) ℂ := fun a => if s a then -c a else c a

lemma signLift_apply_true {c : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ} {s : Fin 5 → Bool} {a : Fin 5}
    (h : s a = true) : signLift c s a = -c a := by simp [signLift, h]

lemma signLift_apply_false {c : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ} {s : Fin 5 → Bool} {a : Fin 5}
    (h : s a = false) : signLift c s a = c a := by simp [signLift, h]

/-- A choice of signs from a pointwise `±` description. -/
lemma exists_signLift {c X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ a, X a = c a ∨ X a = -c a) (h4 : X 4 = 1) (hc4 : c 4 = 1) :
    ∃ s : Fin 5 → Bool, s 4 = false ∧ ∀ a, X a = signLift c s a := by
  classical
  refine ⟨fun a => decide (X a = -c a), ?_, fun a => ?_⟩
  · have hne : ¬ ((1 : Matrix (Fin 2) (Fin 2) ℂ) = -1) := fun h1 => by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h1
      simp at this
      have h2 := congr_arg Complex.re this
      norm_num at h2
    simp only [decide_eq_false_iff_not, h4, hc4]
    exact hne
  · by_cases hs : X a = -c a
    · simp [signLift, hs]
    · rcases h a with h | h
      · simp [signLift, hs, h]
      · exact absurd h hs

/-- **The points with `|F_n| = 1` and `X₄ = 1`**: for spins proportional to the triangle areas,
they are the sign lifts `X_a = ± c_a`, `X₄ = 1`, of the two critical classes. -/
theorem norm_eq_one_iff_signLift (σ : Simplex4) (n : Fin 10 → ℕ)
    (hn : ∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e) (X : Fin 5 → SU2)
    (hX4 : (X 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    ‖cohAmp n (reggeState σ) (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ↔
      ∃ s : Fin 5 → Bool, s 4 = false ∧
        ((∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = signLift critMinus s a) ∨
          (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = signLift (critPlus σ) s a)) := by
  have hg := isSU2Data_reggeState σ
  obtain ⟨c, hc, hce⟩ := hn
  have hne : ∀ e, n e ≠ 0 := fun e h0 => by
    have h := hce e
    rw [h0, Nat.cast_zero] at h
    exact (mul_pos hc (triArea_pos σ e)).ne h
  have key := glued_iff_two_classes hg (normalSU2 σ) (glued_one σ) (glued_normal σ)
    (linearIndependent_normalSU2 σ) X
  have hplus4 : critPlus σ 4 = 1 := critPlus_four σ
  have hminus4 : critMinus 4 = 1 := rfl
  rw [norm_cohAmp_eq_one_iff n hg X]
  constructor
  · intro h
    have h1 := key.mp fun e => h e (hne e)
    simp only [hX4, Matrix.one_mul] at h1
    rcases h1 with h1 | h1
    · obtain ⟨s, hs, hs'⟩ := exists_signLift (c := critMinus) (X := fun a => (X a : Matrix _ _ ℂ))
        (fun a => by simpa [critMinus] using h1 a) hX4 hminus4
      exact ⟨s, hs, Or.inl hs'⟩
    · obtain ⟨s, hs, hs'⟩ := exists_signLift (c := critPlus σ)
        (X := fun a => (X a : Matrix _ _ ℂ))
        (fun a => by
          simpa [critPlus, coe_normalSU2, Matrix.mul_assoc] using h1 a) hX4 hplus4
      exact ⟨s, hs, Or.inr hs'⟩
  · rintro ⟨s, -, h | h⟩
    · intro e _
      refine key.mpr (Or.inl fun a => ?_) e
      simp only [hX4]
      by_cases hs : s a = true
      · right; rw [h a, signLift_apply_true hs]; simp [critMinus]
      · left; rw [h a, signLift_apply_false (by simpa using hs)]; simp [critMinus]
    · intro e _
      refine key.mpr (Or.inr fun a => ?_) e
      simp only [hX4, Matrix.one_mul]
      have hc : critPlus σ a = (normalSU2 σ 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * normalSU2 σ a := by
        simp [critPlus, coe_normalSU2]
      by_cases hs : s a = true
      · right; rw [h a, signLift_apply_true hs, hc]
      · left; rw [h a, signLift_apply_false (by simpa using hs), hc]

/-! ## The sign symmetry -/

/-- **A sign change of one node** leaves `F_n` unchanged when the sum of the spins at that node is
even: the propagator of each edge at the node changes sign. -/
theorem cohAmp_flip (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (a : Fin 5) (ha : Even (∑ k, Lightlike.Spin4.k5Spins n a k)) :
    cohAmp n g (Function.update X a (-X a)) = cohAmp n g X := by
  have hp : ∀ e, prop g (Function.update X a (-X a)) e =
      (if edgeSrc e = a ∨ edgeTgt e = a then -1 else 1) * prop g X e := by
    intro e
    have hne : edgeSrc e ≠ edgeTgt e := by revert e; decide
    unfold prop
    by_cases h1 : edgeSrc e = a
    · have h2 : edgeTgt e ≠ a := fun h => hne (h1.trans h.symm)
      simp only [h1, Function.update_self, Function.update_of_ne h2, h2, or_false, ite_true,
        Matrix.conjTranspose_neg]
      simp [Matrix.mul_assoc]
    · by_cases h2 : edgeTgt e = a
      · simp only [h2, Function.update_self, Function.update_of_ne h1, h1, false_or, ite_true]
        simp [Matrix.mul_assoc]
      · simp [h1, h2, Function.update_of_ne]
  unfold cohAmp
  simp_rw [hp, mul_pow, prod_mul_distrib]
  suffices h : ∏ e : Fin 10, ((if edgeSrc e = a ∨ edgeTgt e = a then (-1 : ℂ) else 1) ^ n e) = 1 by
    rw [h, one_mul]
  have hsum : ∑ e : Fin 10, (if edgeSrc e = a ∨ edgeTgt e = a then n e else 0) =
      ∑ k, Lightlike.Spin4.k5Spins n a k := by
    fin_cases a <;>
      simp [Fin.sum_univ_succ, edgeSrc, edgeTgt, Lightlike.Spin4.k5Spins] <;> omega
  have hpow : ∀ e : Fin 10, ((if edgeSrc e = a ∨ edgeTgt e = a then (-1 : ℂ) else 1) ^ n e) =
      (-1 : ℂ) ^ (if edgeSrc e = a ∨ edgeTgt e = a then n e else 0) := fun e => by
    split_ifs <;> simp
  simp_rw [hpow]
  rw [prod_pow_eq_pow_sum, hsum]
  exact ha.neg_one_pow

/-- **Every sign pattern leaves `F_n` unchanged** when the spin sum at each node is even. -/
theorem cohAmp_signLift (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (hn : ∀ a, Even (∑ k, Lightlike.Spin4.k5Spins n a k)) (s : Fin 5 → Bool) :
    cohAmp n g (signLift X s) = cohAmp n g X := by
  classical
  have key : ∀ T : Finset (Fin 5), cohAmp n g (fun a => if a ∈ T then -X a else X a) =
      cohAmp n g X := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert b T hb ih =>
      rw [← ih, ← cohAmp_flip n g _ b (hn b)]
      congr 1
      funext a
      by_cases hab : a = b
      · subst hab; simp [hb]
      · simp [hab]
  have := key (Finset.univ.filter fun a => s a = true)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

end Lightlike.Asymptotics.EPRL

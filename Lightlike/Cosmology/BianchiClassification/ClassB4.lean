import Lightlike.Cosmology.BianchiClassification.ClassB3

/-!
# Class B, part 4: assembly of the normal forms

For `l ∈ {0, ±1}³` with `l_i a_i = 0` and `a ≠ 0`, `BNormalisable l a` holds: the diagonal
bracket is isomorphic to one of the class B normal forms.  The proof permutes the basis (swaps of
two vectors) so as to place the vanishing eigenvalues at the end, then uses the previous files.

## Main results

* `Lightlike.Cosmology.BianchiClassification.bnormalisable_sign`
* `Lightlike.Cosmology.BianchiClassification.exists_classB_normal`: for `l_i a_i = 0` and `a ≠ 0`, the bracket
  `(diag l, a)` is isomorphic to a class B normal form with `a = (0, 0, α)`.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Cosmology.BianchiClassification

open Matrix

private theorem ne2 {a : V3} (ha : a ≠ 0) (h0 : a 0 = 0) (h1 : a 1 = 0) : a 2 ≠ 0 := by
  intro h
  apply ha
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h

private theorem ne1 {a : V3} (ha : a ≠ 0) (h0 : a 0 = 0) (h2 : a 2 = 0) : a 1 ≠ 0 := by
  intro h
  apply ha
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h
  · simpa using h2

private theorem ne0 {a : V3} (ha : a ≠ 0) (h1 : a 1 = 0) (h2 : a 2 = 0) : a 0 ≠ 0 := by
  intro h
  apply ha
  ext i
  fin_cases i
  · simpa using h
  · simpa using h1
  · simpa using h2

/-- One vanishing eigenvalue, in the last place. -/
theorem bnormalisable_one_zero_at2 (s₀ s₁ : ℝ) (h₀ : s₀ = 1 ∨ s₀ = -1) (h₁ : s₁ = 1 ∨ s₁ = -1)
    (a : V3) (a0 : a 0 = 0) (a1 : a 1 = 0) (a2 : a 2 ≠ 0) : BNormalisable ![s₀, s₁, 0] a := by
  have e : a = ![0, 0, a 2] := by
    ext i; fin_cases i
    · simpa using a0
    · simpa using a1
    · simp
  rw [e]
  exact bnormalisable_one_zero s₀ s₁ h₀ h₁ (a 2) a2

/-- One vanishing eigenvalue, in the middle. -/
theorem bnormalisable_one_zero_at1 (s₀ s₂ : ℝ) (h₀ : s₀ = 1 ∨ s₀ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1)
    (a : V3) (a0 : a 0 = 0) (a1 : a 1 ≠ 0) (a2 : a 2 = 0) : BNormalisable ![s₀, 0, s₂] a := by
  have h := bracketIso_swap12 ![s₀, 0, s₂] a
  have e1 : (![(![s₀, 0, s₂] : Fin 3 → ℝ) 0, (![s₀, 0, s₂] : Fin 3 → ℝ) 2,
      (![s₀, 0, s₂] : Fin 3 → ℝ) 1] : Fin 3 → ℝ) = ![s₀, s₂, 0] := by
    ext i; fin_cases i <;> rfl
  refine BNormalisable.of_iso' h e1 rfl
    (bnormalisable_one_zero_at2 s₀ s₂ h₀ h₂ _ ?_ ?_ ?_) <;> simp [a0, a2, a1]

/-- One vanishing eigenvalue, in the first place. -/
theorem bnormalisable_one_zero_at0 (s₁ s₂ : ℝ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1)
    (a : V3) (a0 : a 0 ≠ 0) (a1 : a 1 = 0) (a2 : a 2 = 0) : BNormalisable ![0, s₁, s₂] a := by
  have h := bracketIso_swap01 ![0, s₁, s₂] a
  have e1 : (![(![0, s₁, s₂] : Fin 3 → ℝ) 1, (![0, s₁, s₂] : Fin 3 → ℝ) 0,
      (![0, s₁, s₂] : Fin 3 → ℝ) 2] : Fin 3 → ℝ) = ![s₁, 0, s₂] := by
    ext i; fin_cases i <;> rfl
  refine BNormalisable.of_iso' h e1 rfl
    (bnormalisable_one_zero_at1 s₁ s₂ h₁ h₂ _ ?_ ?_ ?_) <;> simp [a0, a2, a1]

/-- Two vanishing eigenvalues, the nonzero one in the first place. -/
theorem bnormalisable_two_zero_at1 (s : ℝ) (hs : s = 1 ∨ s = -1)
    (a : V3) (a1 : a 1 = 0) (hne : a 0 ≠ 0 ∨ a 2 ≠ 0) : BNormalisable ![0, s, 0] a := by
  have h := bracketIso_swap01 ![0, s, 0] a
  have e1 : (![(![0, s, 0] : Fin 3 → ℝ) 1, (![0, s, 0] : Fin 3 → ℝ) 0,
      (![0, s, 0] : Fin 3 → ℝ) 2] : Fin 3 → ℝ) = ![s, 0, 0] := by
    ext i; fin_cases i <;> rfl
  refine BNormalisable.of_iso' h e1 rfl
    (bnormalisable_two_zero s hs _ ?_ ?_)
  · simpa using a1
  · simpa using hne

/-- Two vanishing eigenvalues, the nonzero one in the last place. -/
theorem bnormalisable_two_zero_at2 (s : ℝ) (hs : s = 1 ∨ s = -1)
    (a : V3) (a2 : a 2 = 0) (hne : a 0 ≠ 0 ∨ a 1 ≠ 0) : BNormalisable ![0, 0, s] a := by
  have h := bracketIso_swap12 ![0, 0, s] a
  have e1 : (![(![0, 0, s] : Fin 3 → ℝ) 0, (![0, 0, s] : Fin 3 → ℝ) 2,
      (![0, 0, s] : Fin 3 → ℝ) 1] : Fin 3 → ℝ) = ![0, s, 0] := by
    ext i; fin_cases i <;> rfl
  refine BNormalisable.of_iso' h e1 rfl
    (bnormalisable_two_zero_at1 s hs _ ?_ ?_)
  · simpa using a2
  · simpa using hne

/-- The key case analysis: `l ∈ {0, ±1}³`, `l_i a_i = 0`, `a ≠ 0`. -/
theorem bnormalisable_sign_aux (s₀ s₁ s₂ : ℝ) (h0 : s₀ = 0 ∨ s₀ = 1 ∨ s₀ = -1)
    (h1 : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = -1) (h2 : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = -1)
    (a : V3) (m0 : s₀ * a 0 = 0) (m1 : s₁ * a 1 = 0) (m2 : s₂ * a 2 = 0) (ha : a ≠ 0) :
    BNormalisable ![s₀, s₁, s₂] a := by
  have pm : ∀ x : ℝ, x ≠ 0 → (x = 0 ∨ x = 1 ∨ x = -1) → (x = 1 ∨ x = -1) :=
    fun x hx h => h.resolve_left hx
  have az : ∀ x y : ℝ, x ≠ 0 → x * y = 0 → y = 0 := fun x y hx h =>
    (mul_eq_zero.mp h).resolve_left hx
  have hn : a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    ext i; fin_cases i
    · simpa using h.1
    · simpa using h.2.1
    · simpa using h.2.2
  by_cases z0 : s₀ = 0 <;> by_cases z1 : s₁ = 0 <;> by_cases z2 : s₂ = 0
  · subst z0 z1 z2
    exact bnormalisable_zero a ha
  · subst z0 z1
    have b2 := az _ _ z2 m2
    refine bnormalisable_two_zero_at2 s₂ (pm _ z2 h2) a b2 ?_
    rcases hn with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd b2 h
  · subst z0 z2
    have b1 := az _ _ z1 m1
    refine bnormalisable_two_zero_at1 s₁ (pm _ z1 h1) a b1 ?_
    rcases hn with h | h | h
    · exact Or.inl h
    · exact absurd b1 h
    · exact Or.inr h
  · subst z0
    have b1 := az _ _ z1 m1
    have b2 := az _ _ z2 m2
    exact bnormalisable_one_zero_at0 s₁ s₂ (pm _ z1 h1) (pm _ z2 h2) a (ne0 ha b1 b2) b1 b2
  · subst z1 z2
    have b0 := az _ _ z0 m0
    refine bnormalisable_two_zero s₀ (pm _ z0 h0) a b0 ?_
    rcases hn with h | h | h
    · exact absurd b0 h
    · exact Or.inl h
    · exact Or.inr h
  · subst z1
    have b0 := az _ _ z0 m0
    have b2 := az _ _ z2 m2
    exact bnormalisable_one_zero_at1 s₀ s₂ (pm _ z0 h0) (pm _ z2 h2) a b0 (ne1 ha b0 b2) b2
  · subst z2
    have b0 := az _ _ z0 m0
    have b1 := az _ _ z1 m1
    exact bnormalisable_one_zero_at2 s₀ s₁ (pm _ z0 h0) (pm _ z1 h1) a b0 b1 (ne2 ha b0 b1)
  · exfalso
    apply ha
    have b0 := az _ _ z0 m0
    have b1 := az _ _ z1 m1
    have b2 := az _ _ z2 m2
    ext i; fin_cases i
    · simpa using b0
    · simpa using b1
    · simpa using b2

/-- `l ∈ {0, ±1}³`, `l_i a_i = 0`, `a ≠ 0`: the bracket `(diag l, a)` is isomorphic to a class B
normal form. -/
theorem bnormalisable_sign (s a : Fin 3 → ℝ) (hs : ∀ i, s i = 0 ∨ s i = 1 ∨ s i = -1)
    (hsa : ∀ i, s i * a i = 0) (ha : a ≠ 0) : BNormalisable s a := by
  have e : (![s 0, s 1, s 2] : Fin 3 → ℝ) = s := by
    ext i; fin_cases i <;> rfl
  have := bnormalisable_sign_aux (s 0) (s 1) (s 2) (hs 0) (hs 1) (hs 2) a (hsa 0) (hsa 1)
    (hsa 2) ha
  rwa [e] at this

/-- **Class B normal form**: if `l_i a_i = 0` for all `i` and `a ≠ 0`, the bracket `(diag l, a)` is
isomorphic to `(diag t, (0, 0, α))` with `(t, α)` one of the class B normal forms (types IV, V,
VI_h, VII_h). -/
theorem exists_classB_normal (l a : Fin 3 → ℝ) (hla : ∀ i, l i * a i = 0) (ha : a ≠ 0) :
    ∃ t α, ClassBNormal t α ∧ BracketIso (diagonal l) a (diagonal t) ![0, 0, α] := by
  obtain ⟨d, s, hd, hs, hcase⟩ := exists_sign_scale l
  have hsc := bracketIso_diagonal_scale l a d hd
  have e1 : (fun i => l i * d i ^ 2 / (d 0 * d 1 * d 2)) = s := funext hs
  rw [e1] at hsc
  have hd3 : d 0 * d 1 * d 2 ≠ 0 := mul_ne_zero (mul_ne_zero (hd 0) (hd 1)) (hd 2)
  have hsa : ∀ i, s i * (fun i => a i / d i) i = 0 := by
    intro i
    show s i * (a i / d i) = 0
    rw [← hs i]
    have : l i * d i ^ 2 / (d 0 * d 1 * d 2) * (a i / d i) =
        (l i * a i) * d i / (d 0 * d 1 * d 2) := by
      field_simp [hd i]
    rw [this, hla i]; simp
  have hne : (fun i => a i / d i) ≠ 0 := by
    intro h
    apply ha
    ext i
    have := congrFun h i
    simp only [Pi.zero_apply, div_eq_zero_iff] at this
    exact this.resolve_right (hd i)
  have hs3 : ∀ i, s i = 0 ∨ s i = 1 ∨ s i = -1 := by
    intro i
    rcases hcase i with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨t, α, hc, hi⟩ := bnormalisable_sign s _ hs3 hsa hne
  exact ⟨t, α, hc, hsc.trans hi⟩

end Lightlike.Cosmology.BianchiClassification

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_one_zero_at0 := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_one_zero_at0
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_one_zero_at1 := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_one_zero_at1
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_one_zero_at2 := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_one_zero_at2
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_sign := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_sign
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_sign_aux := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_sign_aux
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_two_zero_at1 := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_two_zero_at1
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_two_zero_at2 := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_two_zero_at2
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.exists_classB_normal := _root_.Lightlike.Cosmology.BianchiClassification.exists_classB_normal

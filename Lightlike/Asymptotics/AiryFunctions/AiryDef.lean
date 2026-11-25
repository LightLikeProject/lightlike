import Lightlike.Asymptotics.AiryFunctions.EntireSeries

/-!
# Airy power-series coefficients (row G2-019)

`airyCoeff a₀ a₁` are the Taylor coefficients of the solution of `y'' = x y` with
`y(0) = a₀`, `y'(0) = a₁`: `c₀ = a₀`, `c₁ = a₁`, `c₂ = 0`,
`c_{n+3} = c_n / ((n+3)(n+2))`.  We prove they are entire (`airyCoeff_entire`).
-/

noncomputable section

namespace Lightlike.Airy

/-- Taylor coefficients of the solution of `y'' = x y` with `y(0)=a₀`, `y'(0)=a₁`. -/
def airyCoeff (a0 a1 : ℝ) : ℕ → ℝ
  | 0 => a0
  | 1 => a1
  | 2 => 0
  | (n + 3) => airyCoeff a0 a1 n / (((n : ℝ) + 3) * ((n : ℝ) + 2))

@[simp] theorem airyCoeff_zero (a0 a1 : ℝ) : airyCoeff a0 a1 0 = a0 := rfl
@[simp] theorem airyCoeff_one (a0 a1 : ℝ) : airyCoeff a0 a1 1 = a1 := rfl
@[simp] theorem airyCoeff_two (a0 a1 : ℝ) : airyCoeff a0 a1 2 = 0 := rfl
theorem airyCoeff_succ_succ_succ (a0 a1 : ℝ) (n : ℕ) :
    airyCoeff a0 a1 (n + 3) = airyCoeff a0 a1 n / (((n : ℝ) + 3) * ((n : ℝ) + 2)) := rfl

/-- A sequence with `|c (n+3)| ≤ |c n| / ((n+3)(n+2))` is entire. -/
theorem entire_of_rec {c : ℕ → ℝ}
    (h : ∀ n : ℕ, |c (n + 3)| ≤ |c n| / (((n : ℝ) + 3) * ((n : ℝ) + 2))) : Entire c := by
  intro r hr
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r ^ 3 ≤ N := ⟨⌈r ^ 3⌉₊, Nat.le_ceil _⟩
  set a : ℕ → ℝ := fun n => |c n| * r ^ n with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by simp only [ha]; positivity
  have step : ∀ m : ℕ, N ≤ m → a (m + 3) ≤ a m := by
    intro m hm
    have hmN : (N : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hden : (0 : ℝ) < ((m : ℝ) + 3) * ((m : ℝ) + 2) := by positivity
    have hle : r ^ 3 ≤ ((m : ℝ) + 3) * ((m : ℝ) + 2) := by nlinarith
    have h1 := h m
    have hrp : 0 ≤ r ^ m := by positivity
    calc a (m + 3) = |c (m + 3)| * (r ^ m * r ^ 3) := by simp only [ha]; rw [pow_add]
      _ ≤ (|c m| / (((m : ℝ) + 3) * ((m : ℝ) + 2))) * (r ^ m * r ^ 3) := by gcongr
      _ = |c m| * r ^ m * (r ^ 3 / (((m : ℝ) + 3) * ((m : ℝ) + 2))) := by ring
      _ ≤ |c m| * r ^ m * 1 := by
          gcongr
          rw [div_le_one hden]; exact hle
      _ = a m := by simp only [ha]; ring
  refine ⟨∑ i ∈ Finset.range (N + 3), a i, fun n => ?_⟩
  show a n ≤ _
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N + 3
    · exact Finset.single_le_sum (f := a) (fun i _ => ha0 i) (Finset.mem_range.mpr hn)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact (step m (by omega)).trans (ih m (by omega))

/-- The Airy coefficients are entire. -/
theorem airyCoeff_entire (a0 a1 : ℝ) : Entire (airyCoeff a0 a1) := by
  apply entire_of_rec
  intro n
  rw [airyCoeff_succ_succ_succ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 3) * ((n : ℝ) + 2))]

end Lightlike.Airy

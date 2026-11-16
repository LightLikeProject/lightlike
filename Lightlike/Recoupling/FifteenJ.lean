import Lightlike.Recoupling.Ladder

/-!
# The 15j symbol and the 4-simplex

**The 15j symbol of the first kind.**

There is no single "15j symbol": Yutsis, Levinson and Vanagas classify five topologically distinct
ones (Martin-Dussaud, §5.6). The one of the 4-simplex is the **15j symbol of the first kind**, a
sum over one spin `x` of a product of five 6j symbols (Donà and Sarno,
arXiv:1807.03066, eq. (5), following Yutsis–Levinson–Vanagas). Written with three rows
`a, b, c : Fin 5 → ℕ` of five spins each,

`{15j} = (-1)^S Σ_x (2x + 1) Π_{t=1}^{5} {a_t b_t x; b_{t+1} a_{t+1} c_t}`,

with the twisted closure `(a₆, b₆) = (b₁, a₁)` and `S` the sum of all fifteen spins
(`fifteenJ`, doubled units: `x + 1` and `(-1)^(S/2)`). Its graph, the ten triads
`(a_t a_{t+1} c_t)` and `(b_t b_{t+1} c_t)`, is a 10-cycle with five antipodal chords `c_t` (a
Möbius ladder). `S` is even whenever a term is nonzero, so the floor in `S/2` is harmless.

**The 4-simplex.**

The **4-simplex 15j** (`fifteenJSimplex`) contracts five 4-valent intertwiners `fourJ`, one per
vertex `a ∈ {0, …, 4}` (a tetrahedron of the 4-simplex), along the ten edges `ab` (its triangles)
of the complete graph `K₅`:

`Σ_m Π_{a<b} (-1)^{j_ab - m_ab} Π_a ι_a`,

where the edge `ab` with `a < b` carries `m_ab` at `a` and `-m_ab` at `b`, and the legs of the
intertwiner at `a` are ordered `a+1, a+2, a+3, a+4` (mod 5) with virtual spin `i_a` coupling the
pair `(a+1, a+2)`. This cyclic choice of pairings makes the graph (ten 3j symbols) the Möbius ladder
of the first kind, and

`fifteenJSimplex = Π_a √(2i_a + 1) · fifteenJ a b c`,
`a = (i₀, j₀₂, i₂, j₂₄, i₄)`, `b = (j₁₄, i₁, j₁₃, i₃, j₀₃)`, `c = (j₀₁, j₁₂, j₂₃, j₃₄, j₀₄)`

for all spins (`Lightlike.Recoupling.fifteenJSimplex_eq` in `Simplex.lean`); the factor `Π √(2i_a + 1)`
is the normalisation of the intertwiners. The proof writes the 15j symbol as a closed Möbius ladder
of five rungs (`fifteenJ_eq_mobius`, with the transfer operators of `Ladder.lean`) and identifies
the ladder term by term with the contraction.

## Main results

- `fifteenJ`, `fifteenJ_zero`: the 15j symbol of the first kind; all spins zero give `1`.
- `fifteenJ_of_a_zero`: **reduction with a zero spin.** For `a₁ = 0` the sum collapses to
  `x = b₁` and the 15j symbol is a product of three 6j symbols.
- `fifteenJSimplex`, `fifteenJSimplex_zero`: the contraction of five intertwiners on `K₅`.
- `fifteenJ_eq_mobius`: the 15j symbol is `(-1)^{b₀}` times the closed Möbius ladder of five rungs.

## References

- A. P. Yutsis, I. B. Levinson, V. V. Vanagas, *Mathematical Apparatus of the Theory of Angular
  Momentum*, Israel Program for Scientific Translations (1962).
- P. Donà, G. Sarno, *Numerical methods for EPRL spin foam transition amplitudes and Lorentzian
  recoupling theory*, arXiv:1807.03066 (2018), eq. (5).
- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439, §5.6.
- H. Ooguri, *Topological lattice models in four dimensions*, Mod. Phys. Lett. A 7, 2799 (1992).
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.Recoupling

/-- The **15j symbol of the first kind** (doubled units), with rows `a, b, c : Fin 5 → ℕ`:
`(-1)^(S/2) Σ_x (x + 1) Π_t {a_t b_t x; b_{t+1} a_{t+1} c_t}`, closure `(a₅, b₅) = (b₀, a₀)`,
`S = Σ_t (a_t + b_t + c_t)`. The sum runs over `x ≤ a₀ + b₀`, the range of the triad `(a₀ b₀ x)`. -/
noncomputable def fifteenJ (a b c : Fin 5 → ℕ) : ℝ :=
  (-1) ^ ((∑ t, (a t + b t + c t)) / 2) *
    ∑ x ∈ range (a 0 + b 0 + 1), ((x : ℝ) + 1) *
      (sixJSym (a 0) (b 0) x (b 1) (a 1) (c 0) * sixJSym (a 1) (b 1) x (b 2) (a 2) (c 1) *
        sixJSym (a 2) (b 2) x (b 3) (a 3) (c 2) * sixJSym (a 3) (b 3) x (b 4) (a 4) (c 3) *
          sixJSym (a 4) (b 4) x (a 0) (b 0) (c 4))

/-- The **4-simplex 15j**: the contraction of five 4-valent intertwiners on the complete graph
`K₅` (doubled units). Edge `ab` (`a < b`) has spin `j_ab` and projection `m_ab` at `a`, `-m_ab` at
`b`, and sign `(-1)^(j_ab - m_ab)`; the intertwiner at vertex `a` has legs `a+1, a+2, a+3, a+4`
(mod 5) and virtual spin `i_a` on the pair `(a+1, a+2)`. The sums run over all `|m_ab| ≤ j_ab`;
at projections of the wrong parity `edgeSign` is a junk sign, but there the intertwiners vanish. -/
noncomputable def fifteenJSimplex (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ : ℕ) :
    ℝ :=
  ∑ m₀₁ ∈ Icc (-(j₀₁ : ℤ)) j₀₁, ∑ m₀₂ ∈ Icc (-(j₀₂ : ℤ)) j₀₂, ∑ m₀₃ ∈ Icc (-(j₀₃ : ℤ)) j₀₃,
  ∑ m₀₄ ∈ Icc (-(j₀₄ : ℤ)) j₀₄, ∑ m₁₂ ∈ Icc (-(j₁₂ : ℤ)) j₁₂, ∑ m₁₃ ∈ Icc (-(j₁₃ : ℤ)) j₁₃,
  ∑ m₁₄ ∈ Icc (-(j₁₄ : ℤ)) j₁₄, ∑ m₂₃ ∈ Icc (-(j₂₃ : ℤ)) j₂₃, ∑ m₂₄ ∈ Icc (-(j₂₄ : ℤ)) j₂₄,
  ∑ m₃₄ ∈ Icc (-(j₃₄ : ℤ)) j₃₄,
    edgeSign j₀₁ m₀₁ * edgeSign j₀₂ m₀₂ * edgeSign j₀₃ m₀₃ * edgeSign j₀₄ m₀₄ *
      edgeSign j₁₂ m₁₂ * edgeSign j₁₃ m₁₃ * edgeSign j₁₄ m₁₄ * edgeSign j₂₃ m₂₃ *
      edgeSign j₂₄ m₂₄ * edgeSign j₃₄ m₃₄ *
    (fourJ j₀₁ j₀₂ j₀₃ j₀₄ i₀ m₀₁ m₀₂ m₀₃ m₀₄ *
      fourJ j₁₂ j₁₃ j₁₄ j₀₁ i₁ m₁₂ m₁₃ m₁₄ (-m₀₁) *
      fourJ j₂₃ j₂₄ j₀₂ j₁₂ i₂ m₂₃ m₂₄ (-m₀₂) (-m₁₂) *
      fourJ j₃₄ j₀₃ j₁₃ j₂₃ i₃ m₃₄ (-m₀₃) (-m₁₃) (-m₂₃) *
      fourJ j₀₄ j₁₄ j₂₄ j₃₄ i₄ (-m₀₄) (-m₁₄) (-m₂₄) (-m₃₄))

/-- `(0 0 0; 0 0 0) = 1`. -/
lemma threeJ_zero_zero : threeJ 0 0 0 0 0 0 = 1 := by
  rw [threeJ_zero_left]
  norm_num

/-- The intertwiner of four zero spins is `1` at zero projections. -/
lemma fourJ_zero : fourJ 0 0 0 0 0 0 0 0 0 = 1 := by
  unfold fourJ
  simp [threeJ_zero_zero]

/-- **Value check.** The 15j symbol with all spins zero is `1`. -/
theorem fifteenJ_zero : fifteenJ 0 0 0 = 1 := by
  unfold fifteenJ
  simp [Lightlike.SixJAudit.sixJ_000000]

/-- **Value check.** The 4-simplex 15j with all spins zero is `1`. -/
theorem fifteenJSimplex_zero : fifteenJSimplex 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = 1 := by
  unfold fifteenJSimplex edgeSign
  simp [fourJ_zero]

/-- **Reduction with a zero spin.** If `a₀ = 0`, the triads `(0 b₀ x)` force `x = b₀`, and two of
the five 6j symbols take their closed form with a zero spin:
`{15j} = (-1)^(S/2 + (b₀+a₁+b₁)/2 + (b₀+b₄+a₄)/2) / √((a₁+1)(b₄+1)) ·
{a₁ b₁ b₀; b₂ a₂ c₁}{a₂ b₂ b₀; b₃ a₃ c₂}{a₃ b₃ b₀; b₄ a₄ c₃}`
when `c₀ = a₁`, `c₄ = b₄` and `(b₀ a₁ b₁)`, `(b₀ b₄ a₄)` are admissible, and `0` otherwise
(doubled units). -/
theorem fifteenJ_of_a_zero (a b c : Fin 5 → ℕ) (h : a 0 = 0) :
    fifteenJ a b c =
      if c 0 = a 1 ∧ c 4 = b 4 ∧ Tri (b 0) (a 1) (b 1) ∧ Tri (b 0) (b 4) (a 4) then
        (-1) ^ ((∑ t, (a t + b t + c t)) / 2 + (b 0 + a 1 + b 1) / 2 + (b 0 + b 4 + a 4) / 2) /
          Real.sqrt (((a 1 : ℝ) + 1) * ((b 4 : ℝ) + 1)) *
          (sixJSym (a 1) (b 1) (b 0) (b 2) (a 2) (c 1) * sixJSym (a 2) (b 2) (b 0) (b 3) (a 3) (c 2) *
            sixJSym (a 3) (b 3) (b 0) (b 4) (a 4) (c 3))
      else 0 := by
  unfold fifteenJ
  rw [h]
  have h5 : ∀ x : ℕ, sixJSym (a 4) (b 4) x 0 (b 0) (c 4) = sixJSym 0 (b 0) x (a 4) (b 4) (c 4) :=
    fun x => sj_flip12 0 (b 0) x (a 4) (b 4) (c 4)
  simp only [h5]
  rw [sum_eq_single (b 0) (fun x _ hx => by
      rw [sixJSym_zero_left, ite_eq_right (fun h' => hx h'.1)]; ring)
    (fun hb => absurd (mem_range.mpr (by omega)) hb)]
  rw [sixJSym_zero_left, sixJSym_zero_left]
  by_cases hc : c 0 = a 1 ∧ c 4 = b 4 ∧ Tri (b 0) (a 1) (b 1) ∧ Tri (b 0) (b 4) (a 4)
  · obtain ⟨h0, h4, t1, t4⟩ := hc
    rw [ite_eq_left ⟨rfl, h0, t1⟩, ite_eq_left ⟨rfl, h4, t4⟩,
      ite_eq_left ⟨h0, h4, t1, t4⟩, pow_add, pow_add]
    have hb : (0 : ℝ) < (b 0 : ℝ) + 1 := by positivity
    rw [Real.sqrt_mul (by positivity)]
    field_simp
    rw [Real.sq_sqrt hb.le]
  · rw [ite_eq_right hc]
    by_cases h1 : c 0 = a 1 ∧ Tri (b 0) (a 1) (b 1)
    · rw [ite_eq_left ⟨rfl, h1.1, h1.2⟩,
        ite_eq_right (fun h' => hc ⟨h1.1, h'.2.1, h1.2, h'.2.2⟩)]
      ring
    · rw [ite_eq_right (fun h' => h1 ⟨h'.2.1, h'.2.2⟩)]
      ring

/-! ## The 15j symbol as a Möbius ladder -/

/-- The rail `a₀, …, a₄, b₀` of the Möbius ladder of the 15j symbol with rows `a, b`. -/
def railA (a b : Fin 5 → ℕ) (t : ℕ) : ℕ := if h : t < 5 then a ⟨t, h⟩ else b 0

/-- The rail `b₀, …, b₄, a₀` of the Möbius ladder of the 15j symbol with rows `a, b`. -/
def railB (a b : Fin 5 → ℕ) (t : ℕ) : ℕ := if h : t < 5 then b ⟨t, h⟩ else a 0

/-- The rungs `c₀, …, c₄` of the Möbius ladder of the 15j symbol with row `c`. -/
def railC (c : Fin 5 → ℕ) (t : ℕ) : ℕ := if h : t < 5 then c ⟨t, h⟩ else 0


/-- Evaluation of the rails at `0, …, 5`. -/
lemma rail_values (a b c : Fin 5 → ℕ) :
    railA a b 0 = a 0 ∧ railA a b 1 = a 1 ∧ railA a b 2 = a 2 ∧ railA a b 3 = a 3 ∧
      railA a b 4 = a 4 ∧ railA a b 5 = b 0 ∧
    railB a b 0 = b 0 ∧ railB a b 1 = b 1 ∧ railB a b 2 = b 2 ∧ railB a b 3 = b 3 ∧
      railB a b 4 = b 4 ∧ railB a b 5 = a 0 ∧
    railC c 0 = c 0 ∧ railC c 1 = c 1 ∧ railC c 2 = c 2 ∧ railC c 3 = c 3 ∧ railC c 4 = c 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The parity bookkeeping behind `fifteenJ_eq_mobius`: on the support, the phase `(-1)^S` of the
15j symbol equals `(-1)^{b₀}` times the phases of the Möbius ladder. -/
lemma fifteenJ_sign_parity (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 x : ℕ)
    (h1 : (a0 + b0 + x) % 2 = 0) (h2 : (a0 + a1 + c0) % 2 = 0) (h3 : (a1 + b1 + x) % 2 = 0)
    (h4 : (a1 + a2 + c1) % 2 = 0) (h5 : (a2 + b2 + x) % 2 = 0) (h6 : (a2 + a3 + c2) % 2 = 0)
    (h7 : (a3 + b3 + x) % 2 = 0) (h8 : (a3 + a4 + c3) % 2 = 0) (h9 : (a4 + b4 + x) % 2 = 0)
    (h10 : (a4 + b0 + c4) % 2 = 0) :
    ((a0 + b0 + c0 + (a1 + b1 + c1) + (a2 + b2 + c2) + (a3 + b3 + c3) + (a4 + b4 + c4)) / 2) % 2 =
      (b0 + (x + (a1 + b0 + c0 + x) / 2) + (x + (a2 + b1 + c1 + x) / 2) +
        (x + (a3 + b2 + c2 + x) / 2) + (x + (a4 + b3 + c3 + x) / 2) +
        (x + (b0 + b4 + c4 + x) / 2) + (a0 + b0 + x) / 2) % 2 := by
  omega

/-- **The 15j symbol of the first kind is a closed Möbius ladder** of five rungs:
`{15j} = (-1)^{b₀} mobius 5`, with rails `a₀ … a₄ b₀`, `b₀ … b₄ a₀` and rungs `c₀ … c₄`
(doubled units). -/
theorem fifteenJ_eq_mobius (a b c : Fin 5 → ℕ) :
    fifteenJ a b c = (-1) ^ (b 0) * mobius 5 (railA a b) (railB a b) (railC c) := by
  rw [mobius_eq 4 _ _ _ (by simp [railA, railB]) (by simp [railA, railB])]
  unfold fifteenJ
  obtain ⟨A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5, C0, C1, C2, C3, C4⟩ := rail_values a b c
  simp only [prod_range_succ, prod_range_zero, rungFactor, zero_add, Nat.reduceAdd, A0, A1, A2,
    A3, A4, A5, B0, B1, B2, B3, B4, B5, C0, C1, C2, C3, C4, one_mul]
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  set P := sixJSym (a 0) (b 0) x (b 1) (a 1) (c 0) * sixJSym (a 1) (b 1) x (b 2) (a 2) (c 1) *
    sixJSym (a 2) (b 2) x (b 3) (a 3) (c 2) * sixJSym (a 3) (b 3) x (b 4) (a 4) (c 3) *
    sixJSym (a 4) (b 4) x (a 0) (b 0) (c 4) with hP
  have hR : ∀ s₁ s₂ s₃ s₄ s₅ : ℕ, ∀ E : ℝ,
      (-1 : ℝ) ^ b 0 * (((x : ℝ) + 1) * E *
        ((-1) ^ s₁ * sixJSym (a 0) (b 0) x (b 1) (a 1) (c 0) *
          ((-1) ^ s₂ * sixJSym (a 1) (b 1) x (b 2) (a 2) (c 1)) *
          ((-1) ^ s₃ * sixJSym (a 2) (b 2) x (b 3) (a 3) (c 2)) *
          ((-1) ^ s₄ * sixJSym (a 3) (b 3) x (b 4) (a 4) (c 3)) *
          ((-1) ^ s₅ * sixJSym (a 4) (b 4) x (a 0) (b 0) (c 4)))) =
      (-1 : ℝ) ^ (b 0 + s₁ + s₂ + s₃ + s₄ + s₅) * E * (((x : ℝ) + 1) * P) := by
    intro s₁ s₂ s₃ s₄ s₅ E
    rw [hP]; simp only [pow_add]; ring
  rw [hR]
  by_cases h0 : P = 0
  · rw [h0]; ring
  have n5 := right_ne_zero_of_mul h0
  have n4 := right_ne_zero_of_mul (left_ne_zero_of_mul h0)
  have n3 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h0))
  have n2 := right_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h0)))
  have n1 := left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h0)))
  obtain ⟨⟨t1, -⟩, ⟨t2, -⟩, ⟨t3, -⟩, -⟩ := tri_of_sixJSym_ne_zero n1
  obtain ⟨⟨u1, -⟩, ⟨u2, -⟩, ⟨u3, -⟩, -⟩ := tri_of_sixJSym_ne_zero n2
  obtain ⟨⟨v1, -⟩, ⟨v2, -⟩, ⟨v3, -⟩, -⟩ := tri_of_sixJSym_ne_zero n3
  obtain ⟨⟨w1, -⟩, ⟨w2, -⟩, ⟨w3, -⟩, -⟩ := tri_of_sixJSym_ne_zero n4
  obtain ⟨⟨z1, -⟩, ⟨z2, -⟩, ⟨z3, -⟩, -⟩ := tri_of_sixJSym_ne_zero n5
  have htri : Tri (a 0) (b 0) x := (tri_of_sixJSym_ne_zero n1).1
  rw [ite_eq_left htri, ← pow_add]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := _ + _)]
  have key : ((∑ t, (a t + b t + c t)) / 2) % 2 =
      (b 0 + (x + (a 1 + b 0 + c 0 + x) / 2) + (x + (a 2 + b 1 + c 1 + x) / 2) +
        (x + (a 3 + b 2 + c 2 + x) / 2) + (x + (a 4 + b 3 + c 3 + x) / 2) +
        (x + (b 0 + b 4 + c 4 + x) / 2) + (a 0 + b 0 + x) / 2) % 2 := by
    simp only [Fin.sum_univ_five]
    exact fifteenJ_sign_parity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t1 t2 u1 u2 v1 v2 w1 w2 z1 z2
  rw [key]

end Lightlike.Recoupling

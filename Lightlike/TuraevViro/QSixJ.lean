import Lightlike.TuraevViro.QNumber

/-!
# Quantum 6j symbols at a root of unity

The q-Racah formula (Kirillov–Reshetikhin), in doubled spins. For an admissible tetrahedron:

`{j₁ j₂ j₃; j₄ j₅ j₆}_q = Δ(j₁j₂j₃) Δ(j₁j₅j₆) Δ(j₄j₂j₆) Δ(j₄j₅j₃) ·
   Σ_z (-1)^z [z+1]! / ([z-α₁]! [z-α₂]! [z-α₃]! [z-α₄]! [β₁-z]! [β₂-z]! [β₃-z]!)`

* `αᵢ` are the triad sums (halved);
* `βₖ` are the sums of pairs of columns (halved);
* `Δ(a,b,c)² = [s-a]! [s-b]! [s-c]! / [s+1]!`, with `s = (a+b+c)/2`.

It is defined as `0` unless all four triads are admissible at level `r - 2` (`qAdm`).

* `qSixJ_swap12`, `qSixJ_swap23`, `qSixJ_flip12`: the three generating tetrahedral symmetries.
  Each one permutes the triads and the column sums, so the formula is unchanged term by term.
* `qSixJ_ok`: a nonzero q-6j has four admissible triads.

`scripts/tv_check.py` checks the conventions (40-digit arithmetic):
* the classical formula (ordinary factorials) agrees with SymPy's `wigner_6j`;
* at `r = 3, …, 6` the 2-3 move, orthogonality and the 1-4 move hold;
* with integer dimensions instead of quantum ones, all three fail.
-/

open Finset Lightlike.Pentagon

namespace Lightlike.TV

/-- `1/[u]!` for `u ≥ 0`, else `0`. -/
noncomputable def invQFact (r : ℕ) (u : ℤ) : ℝ := if 0 ≤ u then (qfact r u.toNat)⁻¹ else 0

/-- `Δ(a, b, c)` (doubled spins). -/
noncomputable def qDelta (r a b c : ℕ) : ℝ :=
  Real.sqrt (qfact r ((a + b + c) / 2 - a) * qfact r ((a + b + c) / 2 - b) *
    qfact r ((a + b + c) / 2 - c) / qfact r ((a + b + c) / 2 + 1))

lemma qDelta_swap12 (r a b c : ℕ) : qDelta r b a c = qDelta r a b c := by
  unfold qDelta
  rw [show b + a + c = a + b + c by ring]
  congr 1
  ring

lemma qDelta_swap23 (r a b c : ℕ) : qDelta r a c b = qDelta r a b c := by
  unfold qDelta
  rw [show a + c + b = a + b + c by ring]
  congr 1
  ring

lemma qAdm_swap12 {r a b c : ℕ} (h : qAdm r a b c) : qAdm r b a c := by
  unfold qAdm Tri at *; omega

lemma qAdm_swap23 {r a b c : ℕ} (h : qAdm r a b c) : qAdm r a c b := by
  unfold qAdm Tri at *; omega

/-- The summand of the q-Racah formula. -/
noncomputable def qRacahTerm (r : ℕ) (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) (z : ℕ) : ℝ :=
  (-1 : ℝ) ^ z * qfact r (z + 1) *
    (invQFact r (z - α₁) * invQFact r (z - α₂) * invQFact r (z - α₃) * invQFact r (z - α₄) *
      (invQFact r (β₁ - z) * invQFact r (β₂ - z) * invQFact r (β₃ - z)))

/-- The q-Racah sum (the `z`-range covers every nonzero term). -/
noncomputable def qRacahSum (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  ∑ z ∈ range (j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + 1),
    qRacahTerm r (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
      (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z

/-- **The quantum 6j symbol** `{j₁ j₂ j₃; j₄ j₅ j₆}_q` at `q = e^{iπ/r}` (doubled spins). -/
noncomputable def qSixJ (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  if qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃ then
    qDelta r j₁ j₂ j₃ * qDelta r j₁ j₅ j₆ * qDelta r j₄ j₂ j₆ * qDelta r j₄ j₅ j₃ *
      qRacahSum r j₁ j₂ j₃ j₄ j₅ j₆
  else 0

lemma qSixJ_ok {r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : qSixJ r j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0) :
    qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃ := by
  by_contra hc
  exact h (by rw [qSixJ, ite_eq_right hc])

lemma qRacahSum_swap12 (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    qRacahSum r j₂ j₁ j₃ j₅ j₄ j₆ = qRacahSum r j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold qRacahSum
  rw [show j₂ + j₁ + j₃ + j₅ + j₄ + j₆ = j₁ + j₂ + j₃ + j₄ + j₅ + j₆ by ring]
  refine sum_congr rfl fun z _ => ?_
  rw [show j₂ + j₁ + j₃ = j₁ + j₂ + j₃ by ring, show j₂ + j₄ + j₆ = j₄ + j₂ + j₆ by ring,
    show j₅ + j₁ + j₆ = j₁ + j₅ + j₆ by ring, show j₅ + j₄ + j₃ = j₄ + j₅ + j₃ by ring,
    show j₂ + j₁ + j₅ + j₄ = j₁ + j₂ + j₄ + j₅ by ring,
    show j₁ + j₃ + j₄ + j₆ = j₃ + j₁ + j₆ + j₄ by ring,
    show j₃ + j₂ + j₆ + j₅ = j₂ + j₃ + j₅ + j₆ by ring]
  unfold qRacahTerm
  ring

lemma qRacahSum_swap23 (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    qRacahSum r j₁ j₃ j₂ j₄ j₆ j₅ = qRacahSum r j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold qRacahSum
  rw [show j₁ + j₃ + j₂ + j₄ + j₆ + j₅ = j₁ + j₂ + j₃ + j₄ + j₅ + j₆ by ring]
  refine sum_congr rfl fun z _ => ?_
  rw [show j₁ + j₃ + j₂ = j₁ + j₂ + j₃ by ring, show j₁ + j₆ + j₅ = j₁ + j₅ + j₆ by ring,
    show j₄ + j₃ + j₅ = j₄ + j₅ + j₃ by ring, show j₄ + j₆ + j₂ = j₄ + j₂ + j₆ by ring,
    show j₁ + j₃ + j₄ + j₆ = j₃ + j₁ + j₆ + j₄ by ring,
    show j₃ + j₂ + j₆ + j₅ = j₂ + j₃ + j₅ + j₆ by ring,
    show j₂ + j₁ + j₅ + j₄ = j₁ + j₂ + j₄ + j₅ by ring]
  unfold qRacahTerm
  ring

lemma qRacahSum_flip12 (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    qRacahSum r j₄ j₅ j₃ j₁ j₂ j₆ = qRacahSum r j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold qRacahSum
  rw [show j₄ + j₅ + j₃ + j₁ + j₂ + j₆ = j₁ + j₂ + j₃ + j₄ + j₅ + j₆ by ring]
  refine sum_congr rfl fun z _ => ?_
  rw [show j₄ + j₅ + j₁ + j₂ = j₁ + j₂ + j₄ + j₅ by ring,
    show j₅ + j₃ + j₂ + j₆ = j₂ + j₃ + j₅ + j₆ by ring,
    show j₃ + j₄ + j₆ + j₁ = j₃ + j₁ + j₆ + j₄ by ring]
  unfold qRacahTerm
  ring

/-- Symmetry of the q-6j symbol: swapping the first two columns. -/
theorem qSixJ_swap12 (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    qSixJ r j₂ j₁ j₃ j₅ j₄ j₆ = qSixJ r j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold qSixJ
  have hc : (qAdm r j₂ j₁ j₃ ∧ qAdm r j₂ j₄ j₆ ∧ qAdm r j₅ j₁ j₆ ∧ qAdm r j₅ j₄ j₃) ↔
      (qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃) :=
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨qAdm_swap12 h1, qAdm_swap12 h3, qAdm_swap12 h2, qAdm_swap12 h4⟩,
      fun ⟨h1, h2, h3, h4⟩ => ⟨qAdm_swap12 h1, qAdm_swap12 h3, qAdm_swap12 h2, qAdm_swap12 h4⟩⟩
  by_cases h : qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h, qRacahSum_swap12, qDelta_swap12 r j₂ j₁,
      qDelta_swap12 r j₂ j₄, qDelta_swap12 r j₅ j₁, qDelta_swap12 r j₅ j₄]
    ring
  · rw [ite_eq_right (fun h' => h (hc.mp h')), ite_eq_right h]

/-- Symmetry of the q-6j symbol: swapping the last two columns. -/
theorem qSixJ_swap23 (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    qSixJ r j₁ j₃ j₂ j₄ j₆ j₅ = qSixJ r j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold qSixJ
  have hc : (qAdm r j₁ j₃ j₂ ∧ qAdm r j₁ j₆ j₅ ∧ qAdm r j₄ j₃ j₅ ∧ qAdm r j₄ j₆ j₂) ↔
      (qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃) :=
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨qAdm_swap23 h1, qAdm_swap23 h2, qAdm_swap23 h4, qAdm_swap23 h3⟩,
      fun ⟨h1, h2, h3, h4⟩ => ⟨qAdm_swap23 h1, qAdm_swap23 h2, qAdm_swap23 h4, qAdm_swap23 h3⟩⟩
  by_cases h : qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h, qRacahSum_swap23, qDelta_swap23 r j₁ j₃,
      qDelta_swap23 r j₁ j₆, qDelta_swap23 r j₄ j₃, qDelta_swap23 r j₄ j₆]
    ring
  · rw [ite_eq_right (fun h' => h (hc.mp h')), ite_eq_right h]

/-- Symmetry of the q-6j symbol: exchanging upper and lower entries in the first two columns. -/
theorem qSixJ_flip12 (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    qSixJ r j₄ j₅ j₃ j₁ j₂ j₆ = qSixJ r j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold qSixJ
  have hc : (qAdm r j₄ j₅ j₃ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₁ j₂ j₃) ↔
      (qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃) :=
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h3, h2, h1⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h3, h2, h1⟩⟩
  by_cases h : qAdm r j₁ j₂ j₃ ∧ qAdm r j₁ j₅ j₆ ∧ qAdm r j₄ j₂ j₆ ∧ qAdm r j₄ j₅ j₃
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h, qRacahSum_flip12]
    ring
  · rw [ite_eq_right (fun h' => h (hc.mp h')), ite_eq_right h]

end Lightlike.TV

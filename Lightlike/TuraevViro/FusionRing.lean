import Lightlike.TuraevViro.QNumber

/-!
# The fusion ring of `SU(2)` at level `r - 2` (QU3)

The simple objects of the modular tensor category of `U_q(sl₂)` at `q = e^{iπ/r}` are the colours `0, …, r - 2` (doubled
spins), and the fusion coefficients are `N_{ab}^c = 1` if the triple is admissible (`qAdm r a b c`) and `0` otherwise.

* `fusionN r a b c`: the coefficient, symmetric in all three arguments (`fusionN_comm₁₂`, `fusionN_comm₂₃`);
* `fusionN_zero_left`: the unit object `0`;
* `fusion_dim`: the quantum dimension `[a + 1]` is multiplicative, `Σ_c N_{ab}^c [c + 1] = [a + 1][b + 1]`
  (from `sum_qAdm_qnum`);
* `fusion_assoc_small`: the fusion ring is associative at levels `r = 3, …, 6`, `Σ_e N_{ab}^e N_{ec}^d = Σ_f N_{bc}^f N_{af}^d` (all quadruples, by `decide`); the statement for every `r` is NOT proved.

The F-matrices (6j symbols) and the pentagon/hexagon equations of the category are NOT here: the pentagon is the
q-Biedenharn-Elliott identity (`qBiedenharnElliott`, a hypothesis of this library).
-/

open Finset Lightlike.Pentagon

namespace Lightlike.TV

/-- The fusion coefficient of `SU(2)` at level `r - 2` (doubled spins): `1` if admissible, else `0`. -/
def fusionN (r a b c : ℕ) : ℕ := if qAdm r a b c then 1 else 0

lemma qAdm_comm12 (r a b c : ℕ) : qAdm r a b c ↔ qAdm r b a c := by unfold qAdm Tri; omega
lemma qAdm_comm23 (r a b c : ℕ) : qAdm r a b c ↔ qAdm r a c b := by unfold qAdm Tri; omega

/-- The fusion coefficient is symmetric in the first two colours. -/
lemma fusionN_comm₁₂ (r a b c : ℕ) : fusionN r a b c = fusionN r b a c := by
  unfold fusionN; simp only [qAdm_comm12 r a b c]

/-- The fusion coefficient is symmetric in the last two colours. -/
lemma fusionN_comm₂₃ (r a b c : ℕ) : fusionN r a b c = fusionN r a c b := by
  unfold fusionN; simp only [qAdm_comm23 r a b c]

/-- The unit object `0`: `N_{0 b}^c = 1` iff `b = c ≤ r - 2`. -/
lemma fusionN_zero_left (r b c : ℕ) : fusionN r 0 b c = if b = c ∧ b ≤ r - 2 then 1 else 0 := by
  unfold fusionN qAdm Tri
  by_cases h : b = c ∧ b ≤ r - 2
  · rw [if_pos h, if_pos]; omega
  · rw [if_neg h, if_neg]; omega

/-- **The quantum dimension is multiplicative on the fusion ring.** -/
theorem fusion_dim {r a b : ℕ} (hr : 2 ≤ r) (ha : a ≤ r - 2) (hb : b ≤ r - 2) :
    ∑ c ∈ range (r - 1), (fusionN r a b c : ℝ) * qnum r (c + 1) = qnum r (a + 1) * qnum r (b + 1) := by
  rw [← sum_qAdm_qnum hr ha hb]
  refine sum_congr rfl fun c _ => ?_
  unfold fusionN
  by_cases h : qAdm r a c b
  · rw [if_pos h, if_pos ((qAdm_comm23 r a b c).mpr h)]; simp
  · rw [if_neg h, if_neg (fun h' => h ((qAdm_comm23 r a b c).mp h'))]; simp

/-- **Associativity of the fusion ring at the first levels** (checked for every quadruple of colours by `decide`):
`Σ_e N_{ab}^e N_{ec}^d = Σ_f N_{bc}^f N_{af}^d` for `r = 3, 4, 5, 6`. The statement for every `r` is not proved here. -/
theorem fusion_assoc_small :
    ∀ r ∈ ({3, 4, 5, 6} : Finset ℕ), ∀ a ∈ range (r - 1), ∀ b ∈ range (r - 1), ∀ c ∈ range (r - 1), ∀ d ∈ range (r - 1),
      ∑ e ∈ range (r - 1), fusionN r a b e * fusionN r e c d =
        ∑ f ∈ range (r - 1), fusionN r b c f * fusionN r a f d := by
  decide

/-- Level `r = 4` (`SU(2)_2`, colours `0, 1, 2`): the spin-1/2 object squares to `0 + 1` (doubled: `1 ⊗ 1 = 0 ⊕ 2`). -/
example : fusionN 4 1 1 0 = 1 ∧ fusionN 4 1 1 2 = 1 ∧ fusionN 4 2 2 2 = 0 := by decide

end Lightlike.TV

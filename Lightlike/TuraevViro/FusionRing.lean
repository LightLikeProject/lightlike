import Lightlike.TuraevViro.QNumber

/-!
# The fusion ring of `SU(2)` at level `r - 2` (QU3)

The simple objects of the modular tensor category of `U_q(sl₂)` at `q = e^{iπ/r}` are the colours `0, …, r - 2` (doubled
spins), and the fusion coefficients are `N_{ab}^c = 1` if the triple is admissible (`qAdm r a b c`) and `0` otherwise.

* `fusionN r a b c`: the coefficient, symmetric in all three arguments (`fusionN_comm₁₂`, `fusionN_comm₂₃`);
* `fusionN_zero_left`: the unit object `0`;
* `fusion_dim`: the quantum dimension `[a + 1]` is multiplicative, `Σ_c N_{ab}^c [c + 1] = [a + 1][b + 1]`
  (from `sum_qAdm_qnum`);
* `fusion_assoc`: the fusion ring is associative, `Σ_e N_{ab}^e N_{ec}^d = Σ_f N_{bc}^f N_{af}^d`.

The F-matrices (6j symbols) and the pentagon/hexagon equations of the category are NOT here: the pentagon is the
q-Biedenharn-Elliott identity (`qBiedenharnElliott`, a hypothesis of this library).
-/

open Finset Lightlike.Pentagon

namespace Lightlike.TV

/-- The fusion coefficient of `SU(2)` at level `r - 2` (doubled spins): `1` if admissible, else `0`. -/
def fusionN (r a b c : ℕ) : ℕ := if qAdm r a b c then 1 else 0

lemma qAdm_comm12 (r a b c : ℕ) : qAdm r a b c ↔ qAdm r b a c := by unfold qAdm Tri; omega
lemma qAdm_comm23 (r a b c : ℕ) : qAdm r a b c ↔ qAdm r a c b := by unfold qAdm Tri; omega

lemma fusionN_comm₁₂ (r a b c : ℕ) : fusionN r a b c = fusionN r b a c := by
  unfold fusionN; simp only [qAdm_comm12 r a b c]

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

/-- Counting the integers of a given parity in an interval: `#{e ≤ U : e % 2 = p, L ≤ e} = (U + 2 - p)/2 - (L + 1 - p)/2`. -/
lemma card_parity_interval {p : ℕ} (hp : p ≤ 1) (L : ℕ) :
    ∀ U : ℕ, ((range (U + 1)).filter (fun e => e % 2 = p ∧ L ≤ e)).card = (U + 2 - p) / 2 - (L + 1 - p) / 2 := by
  intro U
  induction U with
  | zero =>
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp [filter_singleton]
    · have : ((range 1).filter (fun e => e % 2 = p ∧ L ≤ e)) = ∅ := by
        ext e; simp; omega
      rw [this]; simp; omega
  | succ U ih =>
    rw [range_add_one, filter_insert]
    by_cases h : (U + 1) % 2 = p ∧ L ≤ U + 1
    · rw [if_pos h, card_insert_of_notMem (by simp), ih]; omega
    · rw [if_neg h, ih]; omega

set_option maxHeartbeats 4000000 in
/-- Admissible middle colours of a pair of admissible triples: an arithmetic progression. -/
lemma card_adm_adm (m a b c d : ℕ) :
    ((range (m + 1)).filter (fun e => qAdm (m + 2) a b e ∧ qAdm (m + 2) e c d)).card =
      if (a + b) % 2 = (c + d) % 2 ∧ a + b ≤ 2 * m ∧ c + d ≤ 2 * m then
        (min (min (a + b) (c + d)) (min (2 * m - (a + b)) (2 * m - (c + d))) + 2 - (a + b) % 2) / 2 -
          (max (max (a - b) (b - a)) (max (c - d) (d - c)) + 1 - (a + b) % 2) / 2
      else 0 := by
  split_ifs with hc
  · have hset : (range (m + 1)).filter (fun e => qAdm (m + 2) a b e ∧ qAdm (m + 2) e c d) =
        (range (min (min (a + b) (c + d)) (min (2 * m - (a + b)) (2 * m - (c + d))) + 1)).filter
          (fun e => e % 2 = (a + b) % 2 ∧ max (max (a - b) (b - a)) (max (c - d) (d - c)) ≤ e) := by
      ext e
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_range, qAdm, Tri]
      omega
    rw [hset, card_parity_interval (by omega)]
  · have : (range (m + 1)).filter (fun e => qAdm (m + 2) a b e ∧ qAdm (m + 2) e c d) = ∅ := by
      ext e
      rw [Finset.mem_filter]
      simp only [Finset.mem_range, qAdm, Tri, Finset.notMem_empty]
      omega
    rw [this]; rfl

set_option maxHeartbeats 4000000 in
/-- **The fusion ring of `SU(2)` at level `r - 2` is associative.** -/
theorem fusion_assoc {r : ℕ} (hr : 2 ≤ r) (a b c d : ℕ) :
    ∑ e ∈ range (r - 1), fusionN r a b e * fusionN r e c d =
      ∑ f ∈ range (r - 1), fusionN r b c f * fusionN r a f d := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have e1 : ∀ x y z w : ℕ, ∑ e ∈ range (m + 2 - 1), fusionN (m + 2) x y e * fusionN (m + 2) e z w =
      ((range (m + 1)).filter (fun e => qAdm (m + 2) x y e ∧ qAdm (m + 2) e z w)).card := by
    intro x y z w
    rw [card_filter]
    refine sum_congr (by simp) fun e _ => ?_
    unfold fusionN
    by_cases h1 : qAdm (m + 2) x y e <;> by_cases h2 : qAdm (m + 2) e z w <;> simp [h1, h2]
  have e2 : ∑ f ∈ range (m + 2 - 1), fusionN (m + 2) b c f * fusionN (m + 2) a f d =
      ∑ f ∈ range (m + 2 - 1), fusionN (m + 2) b c f * fusionN (m + 2) f a d := by
    refine sum_congr rfl fun f _ => ?_
    rw [fusionN_comm₁₂ (m + 2) a f d]
  rw [e1, e2, e1, card_adm_adm, card_adm_adm]
  split_ifs <;> first | rfl | omega

/-- Level `r = 4` (`SU(2)_2`, colours `0, 1, 2`): the spin-1/2 object squares to `0 + 1` (doubled: `1 ⊗ 1 = 0 ⊕ 2`). -/
example : fusionN 4 1 1 0 = 1 ∧ fusionN 4 1 1 2 = 1 ∧ fusionN 4 2 2 2 = 0 := by decide

/-- Fusion ring identity at level `r = 4`, as an instance of `fusion_assoc`. -/
example : ∑ e ∈ range 3, fusionN 4 1 1 e * fusionN 4 e 1 1 = ∑ f ∈ range 3, fusionN 4 1 1 f * fusionN 4 1 f 1 :=
  fusion_assoc (by norm_num) 1 1 1 1

end Lightlike.TV

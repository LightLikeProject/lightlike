import Lightlike.GR.FeynmanWard

/-!
# Large-`z` orders of the Berends-Giele currents

`Ord k f` says that `f z` is bounded by a constant times `‖z‖^k` for large `z` (`k : ℤ`). The orders add under products,
`mdot`, and the vertices `vertex3`, `vertex4` of the Feynman rules, and a sum has the largest order. This is the
bookkeeping behind the large-`z` falloff (Elvang-Huang (3.6), (3.11)) of the colour-ordered amplitudes under the
`[−, +⟩` shift.
-/

open Filter Topology Asymptotics

noncomputable section

namespace Lightlike.SpinorHelicity

/-- `f z = O(‖z‖^k)` as `z → ∞`, with an explicit bound constant. -/
def Ord {E : Type*} [SeminormedAddCommGroup E] (k : ℤ) (f : ℂ → E) : Prop :=
  ∃ C : ℝ, ∀ᶠ z in cocompact ℂ, ‖f z‖ ≤ C * ‖z‖ ^ k

/-- Auxiliary statement `eventually_one_le_norm` for the large-z falloff. -/
lemma eventually_one_le_norm : ∀ᶠ z : ℂ in cocompact ℂ, 1 ≤ ‖z‖ := by
  have : ∀ᶠ z : ℂ in cocompact ℂ, z ∉ Metric.closedBall (0 : ℂ) 1 :=
    (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact
  filter_upwards [this] with z hz
  have := (by simpa using hz : 1 < ‖z‖)
  exact this.le

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Auxiliary statement `Ord.mono` for the large-z falloff. -/
lemma Ord.mono {k k' : ℤ} (h : k ≤ k') {f : ℂ → E} (hf : Ord k f) : Ord k' f := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨max C 0, ?_⟩
  filter_upwards [hC, eventually_one_le_norm] with z hz h1
  calc ‖f z‖ ≤ C * ‖z‖ ^ k := hz
    _ ≤ max C 0 * ‖z‖ ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg (norm_nonneg z) _)
    _ ≤ max C 0 * ‖z‖ ^ k' :=
        mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ h1 h) (le_max_right _ _)

/-- Auxiliary statement `Ord.add` for the large-z falloff. -/
lemma Ord.add {k : ℤ} {f g : ℂ → E} (hf : Ord k f) (hg : Ord k g) : Ord k (fun z => f z + g z) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, ?_⟩
  filter_upwards [hC, hD] with z h1 h2
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C * ‖z‖ ^ k + D * ‖z‖ ^ k := add_le_add h1 h2
    _ = (C + D) * ‖z‖ ^ k := by ring

/-- Auxiliary statement `Ord.sum` for the large-z falloff. -/
lemma Ord.sum {k : ℤ} {ι : Type*} (s : Finset ι) {f : ι → ℂ → E} (hf : ∀ i ∈ s, Ord k (f i)) :
    Ord k (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Eventually.of_forall fun z => by simp⟩
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa only [Finset.sum_insert ha] using h1.add h2

/-- Auxiliary statement `Ord.const` for the large-z falloff. -/
lemma Ord.const (c : E) : Ord 0 (fun _ : ℂ => c) :=
  ⟨‖c‖, Eventually.of_forall fun z => by simp⟩

/-- Auxiliary statement `Ord.of_eventuallyEq` for the large-z falloff. -/
lemma Ord.of_eventuallyEq {k : ℤ} {f g : ℂ → E} (hf : Ord k f) (h : ∀ᶠ z in cocompact ℂ, g z = f z) : Ord k g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, by filter_upwards [hC, h] with z h1 h2; rw [h2]; exact h1⟩

/-- Auxiliary statement `Ord.smul` for the large-z falloff. -/
lemma Ord.smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {a b : ℤ} {s : ℂ → ℂ} {v : ℂ → F}
    (hs : Ord a s) (hv : Ord b v) : Ord (a + b) (fun z => s z • v z) := by
  obtain ⟨C, hC⟩ := hs
  obtain ⟨D, hD⟩ := hv
  refine ⟨C * D, ?_⟩
  filter_upwards [hC, hD, eventually_one_le_norm] with z h1 h2 h3
  have hz : ‖z‖ ≠ 0 := by positivity
  rw [norm_smul, zpow_add₀ hz]
  calc ‖s z‖ * ‖v z‖ ≤ (C * ‖z‖ ^ a) * (D * ‖z‖ ^ b) := by
        refine mul_le_mul h1 h2 (norm_nonneg _) ?_
        exact le_trans (norm_nonneg _) h1
    _ = C * D * (‖z‖ ^ a * ‖z‖ ^ b) := by ring

/-- Auxiliary statement `Ord.mul` for the large-z falloff. -/
lemma Ord.mul {a b : ℤ} {s t : ℂ → ℂ} (hs : Ord a s) (ht : Ord b t) : Ord (a + b) (fun z => s z * t z) := by
  simpa using Ord.smul hs ht

/-- Auxiliary statement `Ord.id` for the large-z falloff. -/
lemma Ord.id : Ord 1 (fun z : ℂ => z) := ⟨1, Eventually.of_forall fun z => by simp⟩

/-- Auxiliary statement `Ord.neg` for the large-z falloff. -/
lemma Ord.neg {k : ℤ} {f : ℂ → E} (hf : Ord k f) : Ord k (fun z => -f z) := by
  obtain ⟨C, hC⟩ := hf; exact ⟨C, by filter_upwards [hC] with z h; simpa using h⟩

/-- Auxiliary statement `Ord.const_smul` for the large-z falloff. -/
lemma Ord.const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℤ} (c : ℂ) {v : ℂ → F}
    (hv : Ord k v) : Ord k (fun z => c • v z) := by
  have := Ord.smul (a := 0) (s := fun _ : ℂ => c) (Ord.const c) hv
  simpa using this

/-- Auxiliary statement `norm_mdot_le` for the large-z falloff. -/
lemma norm_mdot_le (u v : Fin 4 → ℂ) : ‖mdot u v‖ ≤ 4 * (‖u‖ * ‖v‖) := by
  have hu : ∀ i, ‖u i‖ ≤ ‖u‖ := fun i => norm_le_pi_norm u i
  have hv : ∀ i, ‖v i‖ ≤ ‖v‖ := fun i => norm_le_pi_norm v i
  have h : ∀ i, ‖u i * v i‖ ≤ ‖u‖ * ‖v‖ := fun i => by
    rw [norm_mul]; exact mul_le_mul (hu i) (hv i) (norm_nonneg _) (norm_nonneg _)
  calc ‖mdot u v‖ = ‖-u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3‖ := rfl
    _ ≤ ‖-u 0 * v 0‖ + ‖u 1 * v 1‖ + ‖u 2 * v 2‖ + ‖u 3 * v 3‖ := by
        have e1 := norm_add_le (-u 0 * v 0 + u 1 * v 1 + u 2 * v 2) (u 3 * v 3)
        have e2 := norm_add_le (-u 0 * v 0 + u 1 * v 1) (u 2 * v 2)
        have e3 := norm_add_le (-u 0 * v 0) (u 1 * v 1)
        linarith
    _ ≤ 4 * (‖u‖ * ‖v‖) := by
        have h0 : ‖-u 0 * v 0‖ ≤ ‖u‖ * ‖v‖ := by rw [neg_mul, norm_neg]; exact h 0
        linarith [h 1, h 2, h 3]

/-- Auxiliary statement `Ord.dot` for the large-z falloff. -/
lemma Ord.dot {a b : ℤ} {u v : ℂ → Fin 4 → ℂ} (hu : Ord a u) (hv : Ord b v) :
    Ord (a + b) (fun z => SpinorHelicity.mdot (u z) (v z)) := by
  obtain ⟨C, hC⟩ := hu
  obtain ⟨D, hD⟩ := hv
  refine ⟨4 * (C * D), ?_⟩
  filter_upwards [hC, hD, eventually_one_le_norm] with z h1 h2 h3
  have hz : ‖z‖ ≠ 0 := by positivity
  rw [zpow_add₀ hz]
  calc ‖SpinorHelicity.mdot (u z) (v z)‖ ≤ 4 * (‖u z‖ * ‖v z‖) := norm_mdot_le _ _
    _ ≤ 4 * ((C * ‖z‖ ^ a) * (D * ‖z‖ ^ b)) := by
        gcongr
        exact le_trans (norm_nonneg _) h1
    _ = 4 * (C * D) * (‖z‖ ^ a * ‖z‖ ^ b) := by ring

/-- Auxiliary statement `Ord.vertex3` for the large-z falloff. -/
lemma Ord.vertex3 {a b c d q : ℤ} {T1 T2 pa pb : ℂ → Fin 4 → ℂ} (h1 : Ord a T1) (h2 : Ord b T2)
    (hc : Ord c pa) (hd : Ord d pb) (hcq : c ≤ q) (hdq : d ≤ q) :
    Ord (a + b + q) (fun z => vertex3 (T1 z) (pa z) (T2 z) (pb z)) := by
  have hpa := hc.mono hcq
  have hpb := hd.mono hdq
  have t1 : Ord (a + b + q) (fun z => SpinorHelicity.mdot (T1 z) (T2 z) • pa z) := by
    have := (h1.dot h2).smul hpa
    exact this
  have t2 : Ord (a + b + q) (fun z => SpinorHelicity.mdot (T1 z) (pb z) • T2 z) := by
    have := ((h1.dot hpb).smul h2).mono (le_of_eq (by ring : a + q + b = a + b + q))
    exact this
  have t3 : Ord (a + b + q) (fun z => SpinorHelicity.mdot (T2 z) (-(pa z + pb z)) • T1 z) := by
    have hneg : Ord q (fun z => -(pa z + pb z)) := (hpa.add hpb).neg
    have := ((h2.dot hneg).smul h1).mono (le_of_eq (by ring : b + q + a = a + b + q))
    exact this
  have := (((t1.add t2).add t3).const_smul (-((Real.sqrt 2 : ℝ) : ℂ)))
  exact this

/-- Auxiliary statement `Ord.vertex4` for the large-z falloff. -/
lemma Ord.vertex4 {a b c : ℤ} {T1 T2 T3 : ℂ → Fin 4 → ℂ} (h1 : Ord a T1) (h2 : Ord b T2) (h3 : Ord c T3) :
    Ord (a + c + b) (fun z => vertex4 (T1 z) (T2 z) (T3 z)) := (h1.dot h3).smul h2

/-- Auxiliary statement `Ord.inv_linear` for the large-z falloff. -/
lemma Ord.inv_linear (A c : ℂ) (hc : c ≠ 0) : Ord (-1) (fun z : ℂ => 1 / (A + z * c)) := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨2 / ‖c‖, ?_⟩
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, 2 * ‖A‖ / ‖c‖ + 1 ≤ ‖z‖ := by
    have : ∀ᶠ z : ℂ in cocompact ℂ, z ∉ Metric.closedBall (0 : ℂ) (2 * ‖A‖ / ‖c‖ + 1) :=
      (isCompact_closedBall (0 : ℂ) _).compl_mem_cocompact
    filter_upwards [this] with z hz
    have : ¬ ‖z‖ ≤ 2 * ‖A‖ / ‖c‖ + 1 := by simpa using hz
    linarith [not_le.1 this]
  filter_upwards [hev] with z hz
  have hz1 : 0 < ‖z‖ := by
    have : 0 ≤ 2 * ‖A‖ / ‖c‖ := by positivity
    linarith
  have h1 : ‖z‖ * ‖c‖ / 2 ≤ ‖A + z * c‖ := by
    have h2 : ‖z * c‖ - ‖A‖ ≤ ‖A + z * c‖ := by
      have := norm_sub_norm_le (z * c) (-A)
      rw [sub_neg_eq_add, norm_neg, add_comm] at this
      exact this
    have h3 : 2 * ‖A‖ ≤ ‖z‖ * ‖c‖ := by
      have := mul_le_mul_of_nonneg_right hz hcpos.le
      rw [add_mul, div_mul_cancel₀ _ hcpos.ne'] at this
      linarith
    rw [norm_mul] at h2
    linarith
  rw [zpow_neg, zpow_one, norm_div, norm_one]
  have hpos : 0 < ‖A + z * c‖ := lt_of_lt_of_le (by positivity) h1
  calc 1 / ‖A + z * c‖ ≤ 1 / (‖z‖ * ‖c‖ / 2) := one_div_le_one_div_of_le (by positivity) h1
    _ = 2 / ‖c‖ * ‖z‖⁻¹ := by field_simp

/-- The shift vector of the legs `0` and `1`: `+r` on leg `0`, `-r` on leg `1`. -/
def shiftVec (r : Fin 4 → ℂ) (t : ℕ) : Fin 4 → ℂ := if t = 0 then r else if t = 1 then -r else 0

/-- Auxiliary statement `momRange_shiftVec` for the large-z falloff. -/
lemma momRange_shiftVec (r : Fin 4 → ℂ) (a b : ℕ) :
    momRange (shiftVec r) a b = (if a = 0 then r else 0) - (if a ≤ 1 ∧ 1 ≤ b then r else 0) := by
  have h : ∀ t, shiftVec r t = (if t = 0 then r else 0) + (if t = 1 then -r else 0) := fun t => by
    unfold shiftVec; split_ifs <;> simp_all
  unfold momRange
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' (Finset.Ico a (b + 1)) 0 (fun _ => r), Finset.sum_ite_eq' (Finset.Ico a (b + 1)) 1 (fun _ => -r)]
  simp only [Finset.mem_Ico]
  have e1 : (a ≤ 0 ∧ 0 < b + 1) ↔ a = 0 := by omega
  have e2 : (a ≤ 1 ∧ 1 < b + 1) ↔ (a ≤ 1 ∧ 1 ≤ b) := by omega
  simp only [e1, e2]
  split_ifs <;> simp

/-- Auxiliary statement `momRange_add_smul` for the large-z falloff. -/
lemma momRange_add_smul (P : ℕ → Fin 4 → ℂ) (w : ℕ → Fin 4 → ℂ) (z : ℂ) (a b : ℕ) :
    momRange (fun t => P t + z • w t) a b = momRange P a b + z • momRange w a b := by
  unfold momRange
  simp [Finset.sum_add_distrib, Finset.smul_sum]

/-- The order of the momentum of the interval `[a, b]` under the shift of the legs `0`, `1`: `1` if exactly one of
the two legs lies in it, else `0`. -/
def ordP (a b : ℕ) : ℤ :=
  if (a = 0 ∧ ¬ (a ≤ 1 ∧ 1 ≤ b)) ∨ (a ≠ 0 ∧ (a ≤ 1 ∧ 1 ≤ b)) then 1 else 0

/-- The order of the current of the interval `[a, b]`: `-1` if it contains a shifted leg, else `0`. -/
def ordJ (a b : ℕ) : ℤ := if a = 0 ∨ (a ≤ 1 ∧ 1 ≤ b) then -1 else 0

/-- The data of the `[0, 1⟩` falloff: momenta shifted linearly on the legs `0`, `1`, polarizations of the order of
`1/z` on these two legs and bounded elsewhere, and the channel propagators nonvanishing. -/
structure FalloffData (m : ℕ) (p e : ℂ → ℕ → Fin 4 → ℂ) (r : Fin 4 → ℂ) : Prop where
  /-- The momenta are shifted by `z r` on leg `0` and `-z r` on leg `1`. -/
  hp : ∀ z t, p z t = p 0 t + z • shiftVec r t
  /-- The shift vector is null. -/
  hr : mdot r r = 0
  /-- The polarization of leg `0` is `O(1/z)`. -/
  he0 : Ord (-1) (fun z => e z 0)
  /-- The polarization of leg `1` is `O(1/z)`. -/
  he1 : Ord (-1) (fun z => e z 1)
  /-- The other polarizations are bounded. -/
  heo : ∀ t, 2 ≤ t → Ord 0 (fun z => e z t)
  /-- The channels `[1, b]` are shifted: `P · r ≠ 0`. -/
  hone : ∀ b, 2 ≤ b → b ≤ m + 1 → mdot (momRange (p 0) 1 b) r ≠ 0
  /-- The other channel propagators do not vanish. -/
  hother : ∀ a b, a < b → b ≤ m + 1 → a ≠ 1 → ¬ (a = 0 ∧ b = m + 1) →
    mdot (momRange (p 0) a b) (momRange (p 0) a b) ≠ 0

variable {m : ℕ} {p e : ℂ → ℕ → Fin 4 → ℂ} {r : Fin 4 → ℂ}

/-- Auxiliary statement `FalloffData.momRange_eq` for the large-z falloff. -/
lemma FalloffData.momRange_eq (h : FalloffData m p e r) (z : ℂ) (a b : ℕ) :
    momRange (p z) a b = momRange (p 0) a b + z • ((if a = 0 then r else 0) - (if a ≤ 1 ∧ 1 ≤ b then r else 0)) := by
  have := momRange_add_smul (p 0) (shiftVec r) z a b
  rw [momRange_shiftVec] at this
  have hz : p z = fun t => p 0 t + z • shiftVec r t := funext (h.hp z)
  rw [hz]; exact this

/-- Auxiliary statement `ord_const_add_smul` for the large-z falloff. -/
lemma ord_const_add_smul (M w : Fin 4 → ℂ) : Ord 1 (fun z : ℂ => M + z • w) :=
  ((Ord.const M).mono (by norm_num)).add ((Ord.id.smul (Ord.const w)).mono (by norm_num))

/-- Auxiliary statement `FalloffData.ord_mom` for the large-z falloff. -/
lemma FalloffData.ord_mom (h : FalloffData m p e r) (a b : ℕ) :
    Ord (ordP a b) (fun z => momRange (p z) a b) := by
  have hz : (fun z => momRange (p z) a b) = fun z => momRange (p 0) a b +
      z • ((if a = 0 then r else 0) - (if a ≤ 1 ∧ 1 ≤ b then r else 0)) := funext fun z => h.momRange_eq z a b
  rw [hz]
  unfold ordP
  by_cases h0 : a = 0 <;> by_cases h1 : a ≤ 1 ∧ 1 ≤ b
  · have : ¬ ((a = 0 ∧ ¬ (a ≤ 1 ∧ 1 ≤ b)) ∨ (a ≠ 0 ∧ (a ≤ 1 ∧ 1 ≤ b))) := by tauto
    rw [if_neg this, if_pos h0, if_pos h1, sub_self]
    simp only [smul_zero, add_zero]
    exact Ord.const (momRange (p 0) a b)
  · have : (a = 0 ∧ ¬ (a ≤ 1 ∧ 1 ≤ b)) ∨ (a ≠ 0 ∧ (a ≤ 1 ∧ 1 ≤ b)) := by tauto
    rw [if_pos this, if_pos h0, if_neg h1, sub_zero]
    exact ord_const_add_smul _ _
  · have : (a = 0 ∧ ¬ (a ≤ 1 ∧ 1 ≤ b)) ∨ (a ≠ 0 ∧ (a ≤ 1 ∧ 1 ≤ b)) := by tauto
    rw [if_pos this, if_neg h0, if_pos h1, zero_sub]
    exact ord_const_add_smul _ _
  · have : ¬ ((a = 0 ∧ ¬ (a ≤ 1 ∧ 1 ≤ b)) ∨ (a ≠ 0 ∧ (a ≤ 1 ∧ 1 ≤ b))) := by tauto
    rw [if_neg this, if_neg h0, if_neg h1, sub_self]
    simp only [smul_zero, add_zero]
    exact Ord.const (momRange (p 0) a b)

/-- The order of the propagator `1/P̂²` of the interval `[a, b]`: `-1` for the shifted channels `[1, b]`, else `0`. -/
def ordPr (a : ℕ) : ℤ := if a = 1 then -1 else 0

/-- Auxiliary statement `FalloffData.ord_prop` for the large-z falloff. -/
lemma FalloffData.ord_prop (h : FalloffData m p e r) {a b : ℕ} (hab : a < b) (hb : b ≤ m + 1) :
    Ord (ordPr a) (fun z => 1 / mdot (momRange (p z) a b) (momRange (p z) a b)) := by
  by_cases ha : a = 1
  · subst ha
    have hb2 : 2 ≤ b := hab
    have hzf : ∀ z, momRange (p z) 1 b = momRange (p 0) 1 b - z • r := fun z => by
      rw [h.momRange_eq z 1 b]; simp [show 1 ≤ b by omega, sub_eq_add_neg]
    have hlin : ∀ z, mdot (momRange (p z) 1 b) (momRange (p z) 1 b) =
        mdot (momRange (p 0) 1 b) (momRange (p 0) 1 b) + z * (-2 * mdot (momRange (p 0) 1 b) r) := fun z => by
      rw [hzf z]
      simp only [sub_eq_add_neg, mdot_add_left, mdot_add_right, mdot_neg_left, mdot_neg_right, mdot_smul_left,
        mdot_smul_right, h.hr, mdot_comm r (momRange (p 0) 1 b)]
      ring
    have hc : (-2 : ℂ) * mdot (momRange (p 0) 1 b) r ≠ 0 :=
      mul_ne_zero (by norm_num) (h.hone b hb2 hb)
    have := Ord.inv_linear (mdot (momRange (p 0) 1 b) (momRange (p 0) 1 b)) _ hc
    have e : (fun z => 1 / mdot (momRange (p z) 1 b) (momRange (p z) 1 b)) =
        fun z => 1 / (mdot (momRange (p 0) 1 b) (momRange (p 0) 1 b) + z * (-2 * mdot (momRange (p 0) 1 b) r)) :=
      funext fun z => by rw [hlin z]
    rw [e]
    simpa [ordPr] using this
  · have hz0 : ∀ z, momRange (p z) a b = momRange (p 0) a b := fun z => by
      rw [h.momRange_eq z a b]
      by_cases h0 : a = 0
      · have h1 : a ≤ 1 ∧ 1 ≤ b := ⟨by omega, by omega⟩
        rw [if_pos h0, if_pos h1]; simp
      · have h1 : ¬ (a ≤ 1 ∧ 1 ≤ b) := fun hh => by omega
        rw [if_neg h0, if_neg h1]; simp
    simp only [ordPr, if_neg ha, hz0]
    exact Ord.const _

/-- Auxiliary statement `v3_ord_le` for the large-z falloff. -/
lemma v3_ord_le (a b c : ℕ) (hac : a ≤ c) (hcb : c < b) :
    ordJ a c + ordJ (c + 1) b + max (ordP a c) (ordP (c + 1) b) ≤ ordJ a b - ordPr a := by
  simp only [ordJ, ordP, ordPr, max_def]
  split_ifs <;> first | omega | simp_all

/-- Auxiliary statement `v4_ord_le` for the large-z falloff. -/
lemma v4_ord_le (a b c d : ℕ) (hac : a ≤ c) (hcd : c < d) (hdb : d < b) :
    ordJ a c + ordJ (d + 1) b + ordJ (c + 1) d ≤ ordJ a b - ordPr a := by
  simp only [ordJ, ordPr]
  split_ifs <;> first | omega | simp_all

/-- Auxiliary statement `FalloffData.ord_current` for the large-z falloff. -/
lemma FalloffData.ord_current (h : FalloffData m p e r) :
    ∀ n a b, b - a ≤ n → a ≤ b → b ≤ m + 1 → Ord (ordJ a b) (fun z => bgCurrent (p z) (e z) a b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab hb
    rcases Nat.lt_or_ge a b with hlt | hge
    · have hrec : (fun z => bgCurrent (p z) (e z) a b) = fun z =>
          (1 / mdot (momRange (p z) a b) (momRange (p z) a b)) • bgVertexSum (bgCurrent (p z) (e z)) (p z) a b :=
        funext fun z => bgCurrent_of_lt (p z) (e z) hlt
      rw [hrec]
      have hprop := h.ord_prop hlt hb
      have hsub : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a →
          Ord (ordJ c d) (fun z => bgCurrent (p z) (e z) c d) := fun c d hac hcd hdb hlen =>
        ih (d - c) (by omega) c d le_rfl hcd (by omega)
      have hv : Ord (ordJ a b - ordPr a) (fun z => bgVertexSum (bgCurrent (p z) (e z)) (p z) a b) := by
        unfold bgVertexSum
        refine Ord.add (Ord.sum _ fun c hc => ?_) (Ord.sum _ fun c hc => Ord.sum _ fun d hd => ?_)
        · have hc := Finset.mem_Ico.1 hc
          have := Ord.vertex3 (hsub a c le_rfl (by omega) (by omega) (by omega))
            (hsub (c + 1) b (by omega) (by omega) le_rfl (by omega)) (h.ord_mom a c) (h.ord_mom (c + 1) b)
            (le_max_left (ordP a c) (ordP (c + 1) b)) (le_max_right (ordP a c) (ordP (c + 1) b))
          exact this.mono (v3_ord_le a b c (by omega) (by omega))
        · have hc := Finset.mem_Ico.1 hc
          have hd := Finset.mem_Ico.1 hd
          have := Ord.vertex4 (hsub a c le_rfl (by omega) (by omega) (by omega))
            (hsub (c + 1) d (by omega) (by omega) (by omega) (by omega))
            (hsub (d + 1) b (by omega) (by omega) le_rfl (by omega))
          exact this.mono (v4_ord_le a b c d (by omega) (by omega) (by omega))
      have := hprop.smul hv
      simpa using this
    · have hab' : a = b := le_antisymm hab hge
      subst hab'
      simp only [bgCurrent_self, ordJ]
      by_cases h0 : a = 0
      · subst h0; simpa using h.he0
      · by_cases h1 : a = 1
        · subst h1; simpa using h.he1
        · have : ¬ (a = 0 ∨ (a ≤ 1 ∧ 1 ≤ a)) := by omega
          rw [if_neg this]; exact h.heo a (by omega)

/-- Auxiliary statement `FalloffData.ord_vsum` for the large-z falloff. -/
lemma FalloffData.ord_vsum (h : FalloffData m p e r) {a b : ℕ} (hlt : a < b) (hb : b ≤ m + 1) :
    Ord (ordJ a b - ordPr a) (fun z => bgVertexSum (bgCurrent (p z) (e z)) (p z) a b) := by
  have hsub : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a →
      Ord (ordJ c d) (fun z => bgCurrent (p z) (e z) c d) := fun c d hac hcd hdb hlen =>
    h.ord_current (d - c) c d le_rfl hcd (by omega)
  unfold bgVertexSum
  refine Ord.add (Ord.sum _ fun c hc => ?_) (Ord.sum _ fun c hc => Ord.sum _ fun d hd => ?_)
  · have hc := Finset.mem_Ico.1 hc
    have := Ord.vertex3 (hsub a c le_rfl (by omega) (by omega) (by omega))
      (hsub (c + 1) b (by omega) (by omega) le_rfl (by omega)) (h.ord_mom a c) (h.ord_mom (c + 1) b)
      (le_max_left (ordP a c) (ordP (c + 1) b)) (le_max_right (ordP a c) (ordP (c + 1) b))
    exact this.mono (v3_ord_le a b c (by omega) (by omega))
  · have hc := Finset.mem_Ico.1 hc
    have hd := Finset.mem_Ico.1 hd
    have := Ord.vertex4 (hsub a c le_rfl (by omega) (by omega) (by omega))
      (hsub (c + 1) d (by omega) (by omega) (by omega) (by omega))
      (hsub (d + 1) b (by omega) (by omega) le_rfl (by omega))
    exact this.mono (v4_ord_le a b c d (by omega) (by omega) (by omega))

/-- Auxiliary statement `Ord.tendsto_zero` for the large-z falloff. -/
lemma Ord.tendsto_zero {f : ℂ → ℂ} (hf : Ord (-1) f) : Tendsto f (cocompact ℂ) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun z : ℂ => C * ‖z‖ ^ (-1 : ℤ)) (cocompact ℂ) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop
    simpa using this.const_mul C
  exact squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) hC h1

/-- **The large-`z` falloff** (Elvang-Huang (3.6), (3.11)): under the `[0, 1⟩` shift with `1/z` polarizations on the
shifted legs, the Feynman amplitude tends to `0` at infinity. -/
theorem FalloffData.tendsto_amplitude (h : FalloffData m p e r) :
    Tendsto (fun z => bgAmplitude m (p z) (e z)) (cocompact ℂ) (𝓝 0) := by
  have hv := h.ord_vsum (a := 0) (b := m + 1) (by omega) le_rfl
  have he := h.heo (m + 2) (by omega)
  have := he.dot hv
  have h0 : (0 : ℤ) + (ordJ 0 (m + 1) - ordPr 0) = -1 := by simp [ordJ, ordPr]
  rw [h0] at this
  exact Ord.tendsto_zero this

/-- The channel momentum of `[1, b]` is `P − z r`. -/
lemma FalloffData.momRange_one (h : FalloffData m p e r) {b : ℕ} (hb : 2 ≤ b) (z : ℂ) :
    momRange (p z) 1 b = momRange (p 0) 1 b - z • r := by
  rw [h.momRange_eq z 1 b]; simp [show 1 ≤ b by omega, sub_eq_add_neg]

/-- **The shifted propagator is linear in `z`**: `P̂²_{[1,b]} = P² − 2 z P·r`. -/
lemma FalloffData.mdot_one (h : FalloffData m p e r) {b : ℕ} (hb : 2 ≤ b) (z : ℂ) :
    mdot (momRange (p z) 1 b) (momRange (p z) 1 b) =
      mdot (momRange (p 0) 1 b) (momRange (p 0) 1 b) + z * (-2 * mdot (momRange (p 0) 1 b) r) := by
  rw [h.momRange_one hb z]
  simp only [sub_eq_add_neg, mdot_add_left, mdot_add_right, mdot_neg_left, mdot_neg_right, mdot_smul_left,
    mdot_smul_right, h.hr, mdot_comm r (momRange (p 0) 1 b)]
  ring

/-- The other channels are not shifted. -/
lemma FalloffData.momRange_const (h : FalloffData m p e r) {a b : ℕ} (hab : a < b) (ha : a ≠ 1) (z : ℂ) :
    momRange (p z) a b = momRange (p 0) a b := by
  rw [h.momRange_eq z a b]
  by_cases h0 : a = 0
  · have h1 : a ≤ 1 ∧ 1 ≤ b := ⟨by omega, by omega⟩
    rw [if_pos h0, if_pos h1]; simp
  · have h1 : ¬ (a ≤ 1 ∧ 1 ≤ b) := fun hh => by omega
    rw [if_neg h0, if_neg h1]; simp

end Lightlike.SpinorHelicity

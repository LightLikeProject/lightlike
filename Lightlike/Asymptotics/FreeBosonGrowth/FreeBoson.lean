import Mathlib

/-!
# The free boson spectrum: Laplace transform is the Euler product

Combinatorial half of the free-boson trust check of SP3. With `p(n)` the number of partitions
of `n`, we show (for `0 ≤ q < 1`) that
`∑_n #(restricted n (· ≤ N)) q^n = ∏_{k=1}^{N} (1 - q^k)⁻¹`
(`tsum_restricted_card`), using Mathlib's `Nat.Partition.hasProd_powerSeriesMk_card_restricted`
and Cauchy products of absolutely summable series.
No catalogue entry: supporting lemmas.
-/

open PowerSeries Finset Filter Topology
open scoped PowerSeries.WithPiTopology

noncomputable section

namespace Lightlike.SP3Row

/-- Product of two power series with weighted-absolutely-summable coefficients. -/
lemma summable_tsum_mul {q : ℝ} {A B : PowerSeries ℝ}
    (hA : Summable fun n => ‖coeff n A * q ^ n‖) (hB : Summable fun n => ‖coeff n B * q ^ n‖) :
    Summable (fun n => ‖coeff n (A * B) * q ^ n‖) ∧
      ∑' n, coeff n (A * B) * q ^ n = (∑' n, coeff n A * q ^ n) * ∑' n, coeff n B * q ^ n := by
  have key : ∀ n, coeff n (A * B) * q ^ n =
      ∑ p ∈ antidiagonal n, (coeff p.1 A * q ^ p.1) * (coeff p.2 B * q ^ p.2) := by
    intro n
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp, pow_add]; ring
  refine ⟨?_, ?_⟩
  · have h1 := summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => coeff n A * q ^ n) (g := fun n => coeff n B * q ^ n) hA hB
    refine h1.congr fun n => ?_
    rw [key n]
  · have h2 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (f := fun n => coeff n A * q ^ n) (g := fun n => coeff n B * q ^ n) hA hB
    rw [h2]
    exact tsum_congr fun n => key n

/-- The geometric power series `∑_j X^{m j}`. -/
def geomX (m : ℕ) : PowerSeries ℝ := ∑' j : ℕ, (X : PowerSeries ℝ) ^ (m * j)

lemma coeff_geomX {m : ℕ} (hm : 0 < m) (n : ℕ) :
    coeff n (geomX m) = if m ∣ n then 1 else 0 := by
  have hs : Summable (fun j : ℕ => (X : PowerSeries ℝ) ^ (m * j)) := by
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero
      (f := (X : PowerSeries ℝ) ^ m) (by simp [hm.ne'])
  have h := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℝ |>.1 hs.hasSum) n
  simp only [coeff_X_pow] at h
  have h2 : HasSum (fun j : ℕ => if n = m * j then (1 : ℝ) else 0) (if m ∣ n then 1 else 0) := by
    by_cases hd : m ∣ n
    · obtain ⟨k, hk⟩ := hd
      have hc : m ∣ n := ⟨k, hk⟩
      simp only [hc, ↓reduceIte]
      convert hasSum_ite_eq k (1 : ℝ) using 1
      ext j
      by_cases hj : j = k
      · subst hj; simp [hk]
      · have : n ≠ m * j := by
          rw [hk]; intro h; exact hj (Nat.eq_of_mul_eq_mul_left hm h).symm
        simp [this, hj]
    · simp only [hd, ↓reduceIte]
      convert hasSum_zero using 1
      ext j
      have : n ≠ m * j := fun h => hd ⟨j, h⟩
      simp [this]
  exact h.unique h2

/-- Weighted summability and the value of `∑ coeff n (geomX m) q^n = (1 - q^m)⁻¹`. -/
lemma geomX_ev {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {m : ℕ} (hm : 0 < m) :
    Summable (fun n => ‖coeff n (geomX m) * q ^ n‖) ∧
      ∑' n, coeff n (geomX m) * q ^ n = (1 - q ^ m)⁻¹ := by
  have hf : ∀ n, coeff n (geomX m) * q ^ n = if m ∣ n then q ^ n else 0 := by
    intro n; rw [coeff_geomX hm]; split_ifs <;> simp
  have hinj : Function.Injective (fun j : ℕ => m * j) := fun a b h => Nat.eq_of_mul_eq_mul_left hm h
  have hz : ∀ n, n ∉ Set.range (fun j : ℕ => m * j) → (if m ∣ n then q ^ n else 0) = 0 := by
    intro n hn
    have hc : ¬ m ∣ n := by
      rintro ⟨j, hj⟩
      exact hn ⟨j, hj.symm⟩
    simp only [hc, ↓reduceIte]
  have hgeo : Summable (fun j : ℕ => (q ^ m) ^ j) :=
    summable_geometric_of_lt_one (pow_nonneg hq0 _) (pow_lt_one₀ hq0 hq1 hm.ne')
  have hcomp : (fun n : ℕ => if m ∣ n then q ^ n else 0) ∘ (fun j : ℕ => m * j) =
      fun j => (q ^ m) ^ j := by
    ext j; simp [pow_mul]
  have hsum : Summable (fun n : ℕ => if m ∣ n then q ^ n else 0) := by
    rw [← hinj.summable_iff hz, hcomp]; exact hgeo
  refine ⟨?_, ?_⟩
  · simp_rw [hf]
    refine hsum.norm.congr fun n => ?_
    split_ifs <;> simp
  · simp_rw [hf]
    have := hinj.tsum_eq (f := fun n : ℕ => if m ∣ n then q ^ n else 0) (by
      intro n hn
      by_contra h
      exact hn (hz n h))
    rw [← this]
    have h2 : (fun j : ℕ => if m ∣ m * j then q ^ (m * j) else 0) = fun j => (q ^ m) ^ j := by
      ext j; simp [pow_mul]
    rw [h2]
    exact tsum_geometric_of_lt_one (pow_nonneg hq0 _) (pow_lt_one₀ hq0 hq1 hm.ne')

/-- The product of the first `N` geometric series. -/
def prodGeom (N : ℕ) : PowerSeries ℝ := ∏ i ∈ range N, geomX (i + 1)

lemma prodGeom_ev {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    Summable (fun n => ‖coeff n (prodGeom N) * q ^ n‖) ∧
      ∑' n, coeff n (prodGeom N) * q ^ n = ∏ i ∈ range N, (1 - q ^ (i + 1))⁻¹ := by
  induction N with
  | zero =>
    have hf : ∀ n, coeff n (prodGeom 0) * q ^ n = if n = 0 then 1 else 0 := by
      intro n; simp [prodGeom, coeff_one]; split_ifs with h <;> simp [h]
    refine ⟨?_, ?_⟩
    · simp_rw [hf]
      refine (hasSum_ite_eq 0 (1 : ℝ)).summable.norm.congr fun n => ?_
      split_ifs <;> simp
    · simp_rw [hf]
      simp
  | succ N ih =>
    have e : prodGeom (N + 1) = prodGeom N * geomX (N + 1) := by
      simp [prodGeom, Finset.prod_range_succ]
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := geomX_ev hq0 hq1 (Nat.succ_pos N)
    obtain ⟨h5, h6⟩ := summable_tsum_mul h1 h3
    rw [e]
    refine ⟨h5, ?_⟩
    rw [h6, h2, h4, Finset.prod_range_succ]

/-- Coefficients of `prodGeom N` count partitions with all parts `≤ N`. -/
lemma coeff_prodGeom (N n : ℕ) :
    coeff n (prodGeom N) = (#(Nat.Partition.restricted n (· ≤ N)) : ℝ) := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℝ (fun k => k ≤ N)
  have h2 := h.tprod_eq
  rw [tprod_eq_prod (s := range N)] at h2
  · have h3 : (∏ i ∈ range N, if i + 1 ≤ N then ∑' j : ℕ, (X : PowerSeries ℝ) ^ ((i + 1) * j)
        else 1) = prodGeom N := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hc : i + 1 ≤ N := by have := Finset.mem_range.1 hi; omega
      simp only [hc, ↓reduceIte]; rfl
    rw [h3] at h2
    rw [h2]; simp
  · intro i hi
    have := Finset.mem_range.not.1 hi
    have hc : ¬ (i + 1 ≤ N) := by omega
    simp only [hc, ↓reduceIte]

end Lightlike.SP3Row

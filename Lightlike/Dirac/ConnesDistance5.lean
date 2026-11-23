import Mathlib
import Lightlike.Dirac.ConnesDistance4

/-!
# Connes' distance on the circle: the general formula

Extends `circConnesDist_eq` (short arcs, `|p - q| ≤ L/2`) to all pairs of points:
the spectral distance on `ℝ / Lℤ` is the geodesic distance `⨅ m : ℤ, |p - q - m L|`
(`= min (|p-q|, L - |p-q|)` after reduction to `|p - q| ≤ L`).

Only `Lightlike.Dirac.circConnesDist` of `ConnesDistance4.lean` is used.
-/

open Real

namespace Lightlike.Dirac

/-- The circle distance is invariant under translating the first point by a period. -/
lemma circConnesDist_add_int_mul (L p q : ℝ) (m : ℤ) :
    circConnesDist L (p + m * L) q = circConnesDist L p q := by
  unfold circConnesDist
  congr 1
  ext r
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, by rw [hf.1.int_mul m p]⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, by rw [hf.1.int_mul m p]⟩

/-- The circle distance is invariant under translating the second point by a period. -/
lemma circConnesDist_add_int_mul' (L p q : ℝ) (m : ℤ) :
    circConnesDist L p (q + m * L) = circConnesDist L p q := by
  rw [circConnesDist_comm, circConnesDist_add_int_mul, circConnesDist_comm]

/-- Any two points can be brought within `L / 2` by an integer period shift. -/
lemma exists_int_abs_le_half {L : ℝ} (hL : 0 < L) (p q : ℝ) :
    ∃ m : ℤ, |p - q - m * L| ≤ L / 2 := by
  refine ⟨round ((p - q) / L), ?_⟩
  have h := abs_sub_round ((p - q) / L)
  have e : p - q - (round ((p - q) / L) : ℝ) * L = ((p - q) / L - round ((p - q) / L)) * L := by
    field_simp
  rw [e, abs_mul, abs_of_pos hL]
  nlinarith

/-- **Connes' distance on the circle, all pairs**: the spectral distance on `ℝ / Lℤ` (Dirac operator
`D = γ d/dx`) is the geodesic distance `⨅ m : ℤ, |p - q - m L|`. -/
theorem circConnesDist_eq_iInf {L : ℝ} (hL : 0 < L) (p q : ℝ) :
    circConnesDist L p q = ⨅ m : ℤ, |p - q - m * L| := by
  obtain ⟨m, hm⟩ := exists_int_abs_le_half hL p q
  have hshift : circConnesDist L p q = |p - q - m * L| := by
    have h1 := circConnesDist_add_int_mul L (p - m * L) q m
    have e : p - m * L + m * L = p := by ring
    rw [e] at h1
    have h2 : |p - m * L - q| ≤ L / 2 := by rwa [sub_right_comm]
    rw [h1, circConnesDist_eq hL h2, sub_right_comm]
  refine le_antisymm ?_ ?_
  · exact le_ciInf fun m' => circConnesDist_le p q m'
  · rw [hshift]
    exact ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact abs_nonneg _⟩ m

/-- Corollary: the circle distance is attained and is at most `L / 2`. -/
theorem circConnesDist_le_half {L : ℝ} (hL : 0 < L) (p q : ℝ) :
    circConnesDist L p q ≤ L / 2 := by
  obtain ⟨m, hm⟩ := exists_int_abs_le_half hL p q
  exact (circConnesDist_le p q m).trans hm

end Lightlike.Dirac

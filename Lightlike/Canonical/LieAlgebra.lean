import Mathlib

/-!
# The commutator of Lie derivatives of a covariant 2-tensor: the algebra of jets

The pointwise identity behind `{D[ξ], D[η]} = D[[ξ,η]]`, on the 2-jets of the data at one point: for arrays
`h0 = h_ab`, `h1 = ∂_k h_ab`, `h2 = ∂_k ∂_l h_ab` (symmetric in `k l`) and the jets of two vector fields,
`ℒ_ξ ℒ_η h − ℒ_η ℒ_ξ h = ℒ_[ξ,η] h`, where the Lie derivative of the Lie derivative uses the derivative of
the Lie derivative (`lie1`). Pure algebra over `Fin d`.
-/

open Finset

namespace Lightlike.Canonical.LieAlgebra

variable {d : ℕ}

/-- `(ℒ_ξ h)_ij` from the 1-jets. -/
def lie (ξ0 : Fin d → ℝ) (ξ1 : Fin d → Fin d → ℝ) (h0 : Fin d → Fin d → ℝ)
    (h1 : Fin d → Fin d → Fin d → ℝ) (i j : Fin d) : ℝ :=
  ∑ k, ξ0 k * h1 k i j + ∑ k, h0 k j * ξ1 i k + ∑ k, h0 i k * ξ1 j k

/-- `∂_m (ℒ_ξ h)_ij` from the 2-jets. -/
def lie1 (ξ0 : Fin d → ℝ) (ξ1 : Fin d → Fin d → ℝ) (ξ2 : Fin d → Fin d → Fin d → ℝ)
    (h0 : Fin d → Fin d → ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (h2 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (m i j : Fin d) : ℝ :=
  ∑ k, (ξ1 m k * h1 k i j + ξ0 k * h2 m k i j) + ∑ k, (h1 m k j * ξ1 i k + h0 k j * ξ2 m i k) +
    ∑ k, (h1 m i k * ξ1 j k + h0 i k * ξ2 m j k)

/-- The Lie bracket `[ξ,η]^k` from the 1-jets. -/
def br0 (ξ0 η0 : Fin d → ℝ) (ξ1 η1 : Fin d → Fin d → ℝ) (k : Fin d) : ℝ :=
  ∑ l, (ξ0 l * η1 l k - η0 l * ξ1 l k)

/-- `∂_i [ξ,η]^k` from the 2-jets. -/
def br1 (ξ0 η0 : Fin d → ℝ) (ξ1 η1 : Fin d → Fin d → ℝ) (ξ2 η2 : Fin d → Fin d → Fin d → ℝ)
    (i k : Fin d) : ℝ :=
  ∑ l, (ξ1 i l * η1 l k + ξ0 l * η2 i l k - η1 i l * ξ1 l k - η0 l * ξ2 i l k)

/-- The summand of `ℒ_ξ ℒ_η h` as a double sum over `(k, l)`. -/
def Aterm (ξ0 η0 : Fin d → ℝ) (ξ1 η1 : Fin d → Fin d → ℝ) (η2 : Fin d → Fin d → Fin d → ℝ)
    (h0 : Fin d → Fin d → ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (h2 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (i j k l : Fin d) : ℝ :=
  ξ0 k * (η1 k l * h1 l i j + η0 l * h2 k l i j + h1 k l j * η1 i l + h0 l j * η2 k i l +
      h1 k i l * η1 j l + h0 i l * η2 k j l) +
    (η0 l * h1 l k j + h0 l j * η1 k l + h0 k l * η1 j l) * ξ1 i k +
    (η0 l * h1 l i k + h0 l k * η1 i l + h0 i l * η1 k l) * ξ1 j k

theorem lie_lie_eq (ξ0 η0 : Fin d → ℝ) (ξ1 η1 : Fin d → Fin d → ℝ) (η2 : Fin d → Fin d → Fin d → ℝ)
    (h0 : Fin d → Fin d → ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (h2 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (i j : Fin d) :
    lie ξ0 ξ1 (lie η0 η1 h0 h1) (lie1 η0 η1 η2 h0 h1 h2) i j =
      ∑ k, ∑ l, Aterm ξ0 η0 ξ1 η1 η2 h0 h1 h2 i j k l := by
  simp only [lie, lie1, Aterm, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- The summand of `ℒ_[ξ,η] h` as a double sum over `(k, l)`. -/
def Rterm (ξ0 η0 : Fin d → ℝ) (ξ1 η1 : Fin d → Fin d → ℝ) (ξ2 η2 : Fin d → Fin d → Fin d → ℝ)
    (h0 : Fin d → Fin d → ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (i j k l : Fin d) : ℝ :=
  (ξ0 l * η1 l k - η0 l * ξ1 l k) * h1 k i j +
    h0 k j * (ξ1 i l * η1 l k + ξ0 l * η2 i l k - η1 i l * ξ1 l k - η0 l * ξ2 i l k) +
    h0 i k * (ξ1 j l * η1 l k + ξ0 l * η2 j l k - η1 j l * ξ1 l k - η0 l * ξ2 j l k)

theorem lie_br_eq (ξ0 η0 : Fin d → ℝ) (ξ1 η1 : Fin d → Fin d → ℝ) (ξ2 η2 : Fin d → Fin d → Fin d → ℝ)
    (h0 : Fin d → Fin d → ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (i j : Fin d) :
    lie (br0 ξ0 η0 ξ1 η1) (br1 ξ0 η0 ξ1 η1 ξ2 η2) h0 h1 i j =
      ∑ k, ∑ l, Rterm ξ0 η0 ξ1 η1 ξ2 η2 h0 h1 i j k l := by
  simp only [lie, br0, br1, Rterm, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

/-- **The commutator of Lie derivatives of a 2-tensor**, on 2-jets:
`ℒ_ξ ℒ_η h − ℒ_η ℒ_ξ h = ℒ_[ξ,η] h` (needs only the symmetry of the second derivatives). -/
theorem lie_lie_sub (ξ0 η0 : Fin d → ℝ) (ξ1 η1 : Fin d → Fin d → ℝ) (ξ2 η2 : Fin d → Fin d → Fin d → ℝ)
    (h0 : Fin d → Fin d → ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (h2 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (hξ : ∀ m i k, ξ2 m i k = ξ2 i m k) (hη : ∀ m i k, η2 m i k = η2 i m k)
    (hh : ∀ k l a b, h2 k l a b = h2 l k a b) (i j : Fin d) :
    lie ξ0 ξ1 (lie η0 η1 h0 h1) (lie1 η0 η1 η2 h0 h1 h2) i j -
        lie η0 η1 (lie ξ0 ξ1 h0 h1) (lie1 ξ0 ξ1 ξ2 h0 h1 h2) i j =
      lie (br0 ξ0 η0 ξ1 η1) (br1 ξ0 η0 ξ1 η1 ξ2 η2) h0 h1 i j := by
  rw [lie_lie_eq, lie_lie_eq, lie_br_eq, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  -- Rterm k l = (A - B)(l, k) - (the second-derivative terms of h)
  let u : Fin d → Fin d → ℝ := fun k l =>
    ξ0 k * h1 k l j * η1 i l + ξ0 k * h1 k i l * η1 j l - η0 k * h1 k l j * ξ1 i l -
      η0 k * h1 k i l * ξ1 j l + ξ1 i k * η1 j l * h0 k l - η1 i k * ξ1 j l * h0 k l
  have key : ∀ k l, Rterm ξ0 η0 ξ1 η1 ξ2 η2 h0 h1 i j k l =
      (Aterm ξ0 η0 ξ1 η1 η2 h0 h1 h2 i j l k - Aterm η0 ξ0 η1 ξ1 ξ2 h0 h1 h2 i j l k) -
        (ξ0 l * η0 k - η0 l * ξ0 k) * h2 l k i j + (u k l - u l k) := by
    intro k l
    simp only [Rterm, Aterm, u]
    linear_combination (-(ξ0 l * h0 k j)) * hη l i k + (-(ξ0 l * h0 i k)) * hη l j k +
      (η0 l * h0 k j) * hξ l i k + (η0 l * h0 i k) * hξ l j k
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hs : ∑ k, ∑ l, (ξ0 l * η0 k - η0 l * ξ0 k) * h2 l k i j = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun k l => η0 l * ξ0 k * h2 l k i j)]
    refine sub_eq_zero.mpr (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_)
    rw [hh k l i j]; ring
  have hu : ∑ k, ∑ l, u k l = ∑ k, ∑ l, u l k := Finset.sum_comm
  have hA : ∑ k, ∑ l, Aterm ξ0 η0 ξ1 η1 η2 h0 h1 h2 i j k l =
      ∑ k, ∑ l, Aterm ξ0 η0 ξ1 η1 η2 h0 h1 h2 i j l k := Finset.sum_comm
  have hB : ∑ k, ∑ l, Aterm η0 ξ0 η1 ξ1 ξ2 h0 h1 h2 i j k l =
      ∑ k, ∑ l, Aterm η0 ξ0 η1 ξ1 ξ2 h0 h1 h2 i j l k := Finset.sum_comm
  linarith

end Lightlike.Canonical.LieAlgebra

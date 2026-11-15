import Lightlike.Spin4.Vertex
import Lightlike.SpinFoam.Tetrahedron

/-!
# The edge pairing of the `K₅` contraction

The `K₅` contraction `Lightlike.Spin4.k5Contract` pairs the two ends of an edge of spin `n / 2`
(doubled spin `n`) with the form `edgeSign n μ = (-1)^((n - μ)/2)` on the projections
`μ ∈ {-n, -n + 2, …, n}`. The coherent states of `Lightlike.Spin4.cohState` are vectors on
`Fin (n + 1)`, where the index `a` is the number of lowered spins, i.e. the projection `μ = n - 2a`.
This file translates between the two: `projVec` places a vector on its projections, and
`edgePair_eq` shows that the `edgeSign` pairing of two vectors is the bilinear form
`u ⬝ᵥ (W v)` with `W = spinMat n w` the spin-`n/2` matrix of the structure map `w` (`Wm`).
-/

open Finset Matrix Lightlike.Recoupling
open scoped BigOperators

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SpinFoam

/-- A vector on `Fin (n + 1)` as a function of the projection `μ = n - 2a`; it is `0` at every
integer that is not of this form. -/
def projVec (n : ℕ) (u : Fin (n + 1) → ℂ) (μ : ℤ) : ℂ :=
  ∑ a : Fin (n + 1), if μ = (n : ℤ) - 2 * (a : ℕ) then u a else 0

/-- `projVec` at the projection `n - 2a` is the component `u a`. -/
theorem projVec_apply (n : ℕ) (u : Fin (n + 1) → ℂ) (a : Fin (n + 1)) :
    projVec n u ((n : ℤ) - 2 * (a : ℕ)) = u a := by
  unfold projVec
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    refine ite_eq_right_iff.mpr fun h => ?_
    exfalso
    apply hb
    apply Fin.ext
    omega
  · intro h; exact absurd (mem_univ a) h

/-- `projVec` vanishes at a projection that is not `n - 2a`. -/
theorem projVec_eq_zero (n : ℕ) (u : Fin (n + 1) → ℂ) (μ : ℤ)
    (h : ∀ a : Fin (n + 1), μ ≠ (n : ℤ) - 2 * (a : ℕ)) : projVec n u μ = 0 := by
  unfold projVec
  exact Finset.sum_eq_zero fun a _ => ite_eq_right_iff.mpr fun h' => absurd h' (h a)

/-- **The edge pairing in components.** The `edgeSign` pairing of two vectors on the projections
`μ ∈ [-n, n]` is `Σ_a (-1)^a u_a v_{n-a}`. -/
theorem edgePair_eq_sum (n : ℕ) (u v : Fin (n + 1) → ℂ) :
    ∑ μ ∈ Finset.Icc (-(n : ℤ)) n, (edgeSign n μ : ℂ) * projVec n u μ * projVec n v (-μ) =
      ∑ a : Fin (n + 1), (-1 : ℂ) ^ (a : ℕ) * u a * v (Fin.rev a) := by
  have hinj : Function.Injective fun a : Fin (n + 1) => (n : ℤ) - 2 * (a : ℕ) := by
    intro a b h
    apply Fin.ext
    simp only at h
    omega
  have hsub : (Finset.univ.image fun a : Fin (n + 1) => (n : ℤ) - 2 * (a : ℕ)) ⊆
      Finset.Icc (-(n : ℤ)) n := by
    intro μ hμ
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hμ
    have := a.2
    rw [Finset.mem_Icc]
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image fun a _ b _ h => hinj h]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hneg : -((n : ℤ) - 2 * (a : ℕ)) = (n : ℤ) - 2 * ((Fin.rev a : Fin (n + 1)) : ℕ) := by
      rw [Fin.val_rev]
      have := a.2
      omega
    rw [hneg, projVec_apply, projVec_apply]
    have : edgeSign n ((n : ℤ) - 2 * (a : ℕ)) = (-1) ^ (a : ℕ) := by
      unfold edgeSign
      have : ((n : ℤ) - ((n : ℤ) - 2 * (a : ℕ))) / 2 = (a : ℕ) := by omega
      rw [this, zpow_natCast]
    rw [this]
    push_cast
    ring
  · intro μ _ hμ
    have : ∀ a : Fin (n + 1), μ ≠ (n : ℤ) - 2 * (a : ℕ) := fun a h =>
      hμ (Finset.mem_image.mpr ⟨a, mem_univ _, h.symm⟩)
    rw [projVec_eq_zero n u μ this]
    ring

/-- **The edge pairing is the bilinear form of the structure map**:
`Σ_μ edgeSign(n, μ) u(μ) v(-μ) = u ⬝ᵥ (W v)` with `W = spinMat n w`. -/
theorem edgePair_eq (n : ℕ) (u v : Fin (n + 1) → ℂ) :
    ∑ μ ∈ Finset.Icc (-(n : ℤ)) n, (edgeSign n μ : ℂ) * projVec n u μ * projVec n v (-μ) =
      u ⬝ᵥ (Wm n *ᵥ v) := by
  rw [edgePair_eq_sum]
  unfold dotProduct mulVec dotProduct
  refine Finset.sum_congr rfl fun a _ => ?_
  have : ∑ c, Wm n a c * v c = (-1 : ℂ) ^ (a : ℕ) * v (Fin.rev a) := by
    simp only [Wm_apply]
    rw [Finset.sum_eq_single (Fin.rev a)]
    · rw [ite_eq_left (by rw [Fin.val_rev]; omega)]
    · intro c _ hc
      rw [ite_eq_right, zero_mul]
      intro h
      apply hc
      apply Fin.ext
      rw [Fin.val_rev]
      have := a.2
      omega
    · intro h; exact absurd (mem_univ _) h
  rw [this]
  ring

/-! ### Trust checks -/

/-- Control: at `n = 1` the pairing of `(1, 0)` with `(0, 1)` is `+1` and that of `(0, 1)` with
`(1, 0)` is `-1`, so the form is antisymmetric on odd spins and not the plain dot product. -/
theorem edgePair_antisymm_one :
    (![1, 0] : Fin 2 → ℂ) ⬝ᵥ (Wm 1 *ᵥ ![0, 1]) = 1 ∧
      (![0, 1] : Fin 2 → ℂ) ⬝ᵥ (Wm 1 *ᵥ ![1, 0]) = -1 := by
  simp [dotProduct, mulVec, Fin.sum_univ_two, Wm_apply]

end Lightlike.Asymptotics.EPRL

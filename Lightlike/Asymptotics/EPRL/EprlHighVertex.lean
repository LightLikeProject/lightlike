import Lightlike.Asymptotics.EPRL.EprlHighNode
import Lightlike.Asymptotics.EPRL.EprlCoherentVertex

/-!
# The coherent EPRL vertex for `γ > 1`

The node tensor of the lowest Clebsch–Gordan component, contracted with the coherent boundary
intertwiners of `SU(2)` spin `k = n - m`. As for `γ < 1` the coefficient of the coherent intertwiner of
a node in the basis `ι_z` is `nodeSign * ⟨ι_z, homForm ι⟩`, so the vertex sum collapses to the `K₅`
contraction of the coherent node tensors (`eprlVertexHigh_coherent`), and each coherent node tensor is,
at the projections of two components, a signed matrix entry of a Spin(4) average
(`eprlCohNodeHigh_integral`). The statement is exact at every spin. Unlike `γ < 1` the node tensor does
not factorize into two `SU(2)` coherent node tensors. The sign `(-1)^χ'` of the source's equation is not
compared with these conventions.

## Main results

* `eprlIntertwinerLow_sum_smul`: the EPRL map for `γ > 1` is linear on intertwiners.
* `eprlVertexHigh`, `eprlCohNodeHigh`: the vertex amplitude and the coherent node tensor.
* `eprlCohNodeHigh_projOf`, `eprlCohNodeHigh_integral`: the node tensor at the projections of two
  components, as the Hom-form image and as a Spin(4) integral.
* `eprlVertexHigh_coherent`: the vertex sum with coherent boundary data.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4.
-/

open Matrix Finset
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

/-- The EPRL map for `γ > 1` on intertwiners is linear. -/
theorem eprlIntertwinerLow_sum_smul (n m : Fin 4 → ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (T : ι → Matrix (Idx (n 0 - m 0) (n 1 - m 1)) (Idx (n 2 - m 2) (n 3 - m 3)) ℂ) :
    eprlIntertwinerLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) (∑ i ∈ s, c i • T i) =
      ∑ i ∈ s, c i • eprlIntertwinerLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) (T i) := by
  unfold eprlIntertwinerLow projSpin4 eprlLiftLow
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hsInner_sum_right,
    hsInner_smul_right, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_smul]

/-- **The EPRL vertex amplitude for `γ > 1`**: the Spin(4) contraction along `K₅` of the five node
tensors `Φ(ι_{z_a})` of the lowest Clebsch–Gordan component; the `SU(2)` spins of the legs are
`n - m`. -/
noncomputable def eprlVertexHigh (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) : ℂ :=
  k5Contract4 n m fun a => eprlNodeLow (k5Spins n a) (k5Spins m a) (z a)
/-- **The coherent EPRL node tensor for `γ > 1`**: `Σ_z c_z eprlNodeLow n m z`, where `c_z` are the
coefficients of the `SU(2)` coherent intertwiner `ι_{n-m}(g)` in the `fourJ` basis. -/
noncomputable def eprlCohNodeHigh (n m : Fin 4 → ℕ) (g : Fin 4 → SU2) (μ ν : Fin 4 → ℤ) : ℂ :=
  ∑ z ∈ channel (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3),
    (nodeSign (n - m) *
      hsInner (ivec (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3) z)
        (homForm (n - m) (cohInt (n - m) g))) * eprlNodeLow n m z μ ν

/-- The EPRL image of the `SU(2)` coherent intertwiner in the basis `ι_z`, entrywise. -/
theorem eprlIntertwinerLow_homForm_expand (n m : Fin 4 → ℕ) (g : Fin 4 → SU2)
    (P : Idx (n 0) (n 1) × Idx (m 0) (m 1)) (Q : Idx (n 2) (n 3) × Idx (m 2) (m 3)) :
    eprlIntertwinerLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
        (homForm (n - m) (cohInt (n - m) g)) P Q =
      ∑ z ∈ channel (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3),
        hsInner (ivec (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3) z)
          (homForm (n - m) (cohInt (n - m) g)) *
        eprlIntertwinerLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
          (ivec (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3) z) P Q := by
  have hi := homForm_isIntertwiner (n - m) (cohInt_isInvariantN (J := n - m) g)
  have e := eq_sum_ivec hi
  simp only [Pi.sub_apply] at e
  have hlin := eprlIntertwinerLow_sum_smul n m
    (channel (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3))
    (fun z => hsInner (ivec (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3) z)
        (homForm (n - m) (cohInt (n - m) g)))
    (fun z => ivec (n 0 - m 0) (n 1 - m 1) (n 2 - m 2) (n 3 - m 3) z)
  conv_lhs => rw [e]
  rw [hlin]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- **The coherent node tensor for `γ > 1` at the projections of two components**: `nodeSign` times the
signs of the bridge times the Hom-form EPRL image of the coherent intertwiner. -/
theorem eprlCohNodeHigh_projOf {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ} (g : Fin 4 → SU2)
    (P : Idx n₁ n₂ × Idx m₁ m₂) (Q : Idx n₃ n₄ × Idx m₃ m₄) :
    eprlCohNodeHigh ![n₁, n₂, n₃, n₄] ![m₁, m₂, m₃, m₄] g
        ![(n₁ : ℤ) - 2 * (P.1.1 : ℕ), (n₂ : ℤ) - 2 * (P.1.2 : ℕ), 2 * (Q.1.1 : ℕ) - n₃,
          2 * (Q.1.2 : ℕ) - n₄]
        ![(m₁ : ℤ) - 2 * (P.2.1 : ℕ), (m₂ : ℤ) - 2 * (P.2.2 : ℕ), 2 * (Q.2.1 : ℕ) - m₃,
          2 * (Q.2.2 : ℕ) - m₄] =
      nodeSign (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄]) *
        ((-1 : ℂ) ^ (n₂ + n₄ + (P.1.1 : ℕ) + P.1.2) * (-1 : ℂ) ^ (m₂ + m₄ + (P.2.1 : ℕ) + P.2.2)) *
        eprlIntertwinerLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄
          (homForm (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄])
            (cohInt (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄]) g)) P Q := by
  rw [show eprlIntertwinerLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄
      (homForm (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄])
        (cohInt (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄]) g)) P Q = _ from
    eprlIntertwinerLow_homForm_expand ![n₁, n₂, n₃, n₄] ![m₁, m₂, m₃, m₄] g P Q, Finset.mul_sum]
  unfold eprlCohNodeHigh
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [eprlNodeLow_eq_eprlIntertwinerLow]
  simp only [Matrix.cons_val]
  ring

/-- **The coherent node tensor for `γ > 1` at the projections is a Spin(4) integral**: `nodeSign`
times the signs of the bridge times the matrix entry of the Spin(4) average of the conjugates of the
lifted rank-one tensor. -/
theorem eprlCohNodeHigh_integral {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ} (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂)
    (h₃ : m₃ ≤ n₃) (h₄ : m₄ ≤ n₄) (g : Fin 4 → SU2)
    (P : Idx n₁ n₂ × Idx m₁ m₂) (Q : Idx n₃ n₄ × Idx m₃ m₄) :
    eprlCohNodeHigh ![n₁, n₂, n₃, n₄] ![m₁, m₂, m₃, m₄] g
        ![(n₁ : ℤ) - 2 * (P.1.1 : ℕ), (n₂ : ℤ) - 2 * (P.1.2 : ℕ), 2 * (Q.1.1 : ℕ) - n₃,
          2 * (Q.1.2 : ℕ) - n₄]
        ![(m₁ : ℤ) - 2 * (P.2.1 : ℕ), (m₂ : ℤ) - 2 * (P.2.2 : ℕ), 2 * (Q.2.1 : ℕ) - m₃,
          2 * (Q.2.2 : ℕ) - m₄] =
      nodeSign (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄]) *
        ((-1 : ℂ) ^ (n₂ + n₄ + (P.1.1 : ℕ) + P.1.2) * (-1 : ℂ) ^ (m₂ + m₄ + (P.2.1 : ℕ) + P.2.2)) *
        matInt4 (fun G => act4 n₁ n₂ m₁ m₂ G *
          eprlLiftLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄
            (homForm (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄])
              (prodVec (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄]) fun l =>
                cohState ((![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄]) l) (g l))) *
          (act4 n₃ n₄ m₃ m₄ G)ᴴ) P Q := by
  have hmn : ∀ l, (![m₁, m₂, m₃, m₄] : Fin 4 → ℕ) l ≤ (![n₁, n₂, n₃, n₄] : Fin 4 → ℕ) l := by
    intro l; fin_cases l <;> assumption
  rw [eprlCohNodeHigh_projOf]
  rw [show eprlIntertwinerLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄
      (homForm (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄])
        (cohInt (![n₁, n₂, n₃, n₄] - ![m₁, m₂, m₃, m₄]) g)) = _ from
    eprlIntertwinerLow_homForm_cohInt ![n₁, n₂, n₃, n₄] ![m₁, m₂, m₃, m₄] hmn g]
  rfl

/-- **The EPRL vertex for `γ > 1`, contracted with the coherent boundary intertwiners, is the `K₅`
contraction of the coherent node tensors.** The coefficient of the coherent intertwiner of node `a`
in the basis `ι_z` is `nodeSign * ⟨ι_z, homForm ι⟩` (`vec_eq_sum`), as for `γ < 1`. -/
theorem eprlVertexHigh_coherent (n m : Fin 10 → ℕ) (g : Fin 10 → Fin 2 → SU2) :
    ∑ P ∈ Fintype.piFinset (fun a : Fin 5 =>
        channel (k5Spins n a 0 - k5Spins m a 0) (k5Spins n a 1 - k5Spins m a 1)
          (k5Spins n a 2 - k5Spins m a 2) (k5Spins n a 3 - k5Spins m a 3)),
      (∏ a, (nodeSign (k5Spins n a - k5Spins m a) *
        hsInner (ivec (k5Spins n a 0 - k5Spins m a 0) (k5Spins n a 1 - k5Spins m a 1)
          (k5Spins n a 2 - k5Spins m a 2) (k5Spins n a 3 - k5Spins m a 3) (P a))
          (homForm (k5Spins n a - k5Spins m a)
            (cohInt (k5Spins n a - k5Spins m a) (nodeBdry g a))))) * eprlVertexHigh n m P =
      k5Contract4 n m (fun a μ ν => eprlCohNodeHigh (k5Spins n a) (k5Spins m a) (nodeBdry g a) μ ν) := by
  unfold eprlCohNodeHigh eprlVertexHigh
  rw [k5Contract4_sum]

end Lightlike.Asymptotics.EPRL

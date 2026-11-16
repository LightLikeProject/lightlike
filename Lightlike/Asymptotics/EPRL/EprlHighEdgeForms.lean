import Lightlike.Asymptotics.EPRL.EprlHighLegs
import Lightlike.Asymptotics.EPRL.EprlHighEdge

/-!
# The `γ > 1` vertex as a `Spin(4)⁵` integral of edge forms

The coherent node tensor of the lowest Clebsch–Gordan component is the `Spin(4)` integral of a product
over its four legs (`eprlCohNodeHigh_legs`). Together with the contraction by edges
(`k5Contract4_prod`) and Fubini over `Spin(4)⁵` (`k5Contract4_integral`) this writes the vertex sum with
coherent boundary data as `(∏_a c_a)` times the `Spin(4)⁵` integral of the product over the ten edges of
the edge forms `Σ_{μ,ν} ε_n(μ) ε_m(ν) f_src(μ, ν) f_tgt(-μ, -ν)` (`eprlVertexHigh_edgeForms`).

The statement is exact at every spin. The leg functions keep `Y_low` as it is (the image of a coherent
state is a superposition); the closed form of the edge form through the leg amplitude, the comparison with
the integrand of the source and the sign `(-1)^χ'` are not part of this file.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4, eqs. (17)–(19).
-/

open Matrix Finset MeasureTheory
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

/-- **The coherent node tensor for `γ > 1` is the Spin(4) integral of a product over the four legs**,
for every pair of projection tuples. -/
theorem eprlCohNodeHigh_legs (n m : Fin 4 → ℕ) (hmn : ∀ l, m l ≤ n l) (g : Fin 4 → SU2)
    (μ ν : Fin 4 → ℤ) :
    eprlCohNodeHigh n m g μ ν = nodeSign (n - m) * (-1 : ℂ) ^ (n 1 + n 3 + m 1 + m 3) *
      ∫ G, nodeLeg n m g G μ ν ∂haarSpin4 := by
  by_cases hA : ∃ k : LIdx n, ∃ l : LIdx m, μ = projOf n k ∧ ν = projOf m l
  · obtain ⟨k, l, rfl, rfl⟩ := hA
    obtain ⟨n₁, n₂, n₃, n₄, rfl⟩ : ∃ n₁ n₂ n₃ n₄, n = ![n₁, n₂, n₃, n₄] :=
      ⟨n 0, n 1, n 2, n 3, by ext i; fin_cases i <;> rfl⟩
    obtain ⟨m₁, m₂, m₃, m₄, rfl⟩ : ∃ m₁ m₂ m₃ m₄, m = ![m₁, m₂, m₃, m₄] :=
      ⟨m 0, m 1, m 2, m 3, by ext i; fin_cases i <;> rfl⟩
    have key := eprlCohNodeHigh_integral (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) (n₄ := n₄)
      (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) (m₄ := m₄) (hmn 0) (hmn 1) (hmn 2) (hmn 3) g
      ((k 0, k 1), (l 0, l 1)) ((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3)))
    have hμ : projOf ![n₁, n₂, n₃, n₄] k =
        ![(n₁ : ℤ) - 2 * ((((k 0, k 1), (l 0, l 1)) : Idx n₁ n₂ × Idx m₁ m₂).1.1 : ℕ),
          (n₂ : ℤ) - 2 * ((((k 0, k 1), (l 0, l 1)) : Idx n₁ n₂ × Idx m₁ m₂).1.2 : ℕ),
          2 * ((((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) :
            Idx n₃ n₄ × Idx m₃ m₄).1.1 : ℕ) - n₃,
          2 * ((((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) :
            Idx n₃ n₄ × Idx m₃ m₄).1.2 : ℕ) - n₄] := by
      have r2 := Fin.val_rev (k 2)
      have r3 := Fin.val_rev (k 3)
      have b2 := (k 2).isLt
      have b3 := (k 3).isLt
      simp only [Matrix.cons_val] at r2 r3 b2 b3
      funext i
      fin_cases i <;> simp [projOf] <;> omega
    have hν : projOf ![m₁, m₂, m₃, m₄] l =
        ![(m₁ : ℤ) - 2 * ((((k 0, k 1), (l 0, l 1)) : Idx n₁ n₂ × Idx m₁ m₂).2.1 : ℕ),
          (m₂ : ℤ) - 2 * ((((k 0, k 1), (l 0, l 1)) : Idx n₁ n₂ × Idx m₁ m₂).2.2 : ℕ),
          2 * ((((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) :
            Idx n₃ n₄ × Idx m₃ m₄).2.1 : ℕ) - m₃,
          2 * ((((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) :
            Idx n₃ n₄ × Idx m₃ m₄).2.2 : ℕ) - m₄] := by
      have r2 := Fin.val_rev (l 2)
      have r3 := Fin.val_rev (l 3)
      have b2 := (l 2).isLt
      have b3 := (l 3).isLt
      simp only [Matrix.cons_val] at r2 r3 b2 b3
      funext i
      fin_cases i <;> simp [projOf] <;> omega
    simp only [nodeLeg_projOf _ _ (hmn 2) (hmn 3)]
    rw [integral_const_mul]
    conv_lhs => rw [hμ, hν, key]
    simp only [matInt4_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    have gen : ∀ (N : ℂ) (I : ℂ), N * ((-1 : ℂ) ^ (n₂ + n₄ + (k 0 : ℕ) + (k 1 : ℕ)) *
        (-1 : ℂ) ^ (m₂ + m₄ + (l 0 : ℕ) + (l 1 : ℕ))) * I =
        N * (-1 : ℂ) ^ (n₂ + n₄ + m₂ + m₄) *
          ((-1 : ℂ) ^ ((k 0 : ℕ) + (k 1 : ℕ) + (l 0 : ℕ) + (l 1 : ℕ)) * I) := by
      intro N I
      ring
    exact gen _ _
  · have hL : eprlCohNodeHigh n m g μ ν = 0 := by
      unfold eprlCohNodeHigh
      refine Finset.sum_eq_zero fun z _ => ?_
      have hz : eprlNodeLow n m z μ ν = 0 := by
        unfold eprlNodeLow
        refine Finset.sum_eq_zero fun p _ => ?_
        by_cases h1 : fourJNode n p.1 μ = 0
        · rw [h1]; ring
        · by_cases h2 : fourJNode m p.2 ν = 0
          · rw [h2]; ring
          · obtain ⟨k, hk⟩ := exists_projOf_of_fourJNode_ne_zero n _ _ h1
            obtain ⟨l, hl⟩ := exists_projOf_of_fourJNode_ne_zero m _ _ h2
            exact absurd ⟨k, l, hk, hl⟩ hA
      rw [hz, mul_zero]
    have hR : ∀ G, nodeLeg n m g G μ ν = 0 := by
      intro G
      by_contra hne
      unfold nodeLeg at hne
      have h01 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
      have h02 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
      have h03 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
      have h04 := right_ne_zero_of_mul hne
      obtain ⟨a0, b0, e0, f0⟩ := exists_of_legFun_ne_zero _ _ _ _ _ (right_ne_zero_of_mul h01)
      obtain ⟨a1, b1, e1, f1⟩ := exists_of_legFun_ne_zero _ _ _ _ _ (right_ne_zero_of_mul h02)
      obtain ⟨a2, b2, e2, f2⟩ := exists_of_legFun_ne_zero _ _ _ _ _ h03
      obtain ⟨a3, b3, e3, f3⟩ := exists_of_legFun_ne_zero _ _ _ _ _ h04
      apply hA
      refine ⟨(legEquiv n).symm ((a0, a1), (Fin.rev a2, Fin.rev a3)),
        (legEquiv m).symm ((b0, b1), (Fin.rev b2, Fin.rev b3)), ?_, ?_⟩
      · funext i
        fin_cases i
        · simpa [projOf] using e0
        · simpa [projOf] using e1
        · have := a2.isLt
          simp only [projOf]
          simp
          omega
        · have := a3.isLt
          simp only [projOf]
          simp
          omega
      · funext i
        fin_cases i
        · simpa [projOf] using f0
        · simpa [projOf] using f1
        · have := b2.isLt
          simp only [projOf]
          simp
          omega
        · have := b3.isLt
          simp only [projOf]
          simp
          omega
    simp only [hR, integral_zero, mul_zero, hL]

/-- The constant of node `a`: `nodeSign` times the signs of the bridge. -/
noncomputable def nodeConst (n m : Fin 4 → ℕ) : ℂ :=
  nodeSign (n - m) * (-1 : ℂ) ^ (n 1 + n 3 + m 1 + m 3)

/-- A constant at each node factors out of the contraction. -/
theorem k5Contract4_const_mul (n m : Fin 10 → ℕ) (c : Fin 5 → ℂ)
    (T : Fin 5 → (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ) :
    k5Contract4 n m (fun a μ ν => c a * T a μ ν) = (∏ a, c a) * k5Contract4 n m T := by
  unfold k5Contract4
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- **The `γ > 1` vertex with coherent boundary data is a `Spin(4)⁵` integral of edge forms.** The
vertex sum collapses (`eprlVertexHigh_coherent`) to the contraction of the coherent node tensors, each
node tensor is the `Spin(4)` integral of a product over its four legs (`eprlCohNodeHigh_legs`), the
five node integrals combine into one over `Spin(4)⁵` (`k5Contract4_integral`, the `∫_{Spin(4)⁵} ∏ dG_c`
of BDFGH eq. (19)), and the contraction of the products over legs is the product over the ten edges of
the edge forms (`k5Contract4_prod`). Exact at every spin, with the leg functions `legFam` in which
`Y_low` is kept as it is; the comparison with the source's integrand, and `(-1)^χ'`, are not made. -/
theorem eprlVertexHigh_edgeForms (n m : Fin 10 → ℕ) (hmn : ∀ e, m e ≤ n e)
    (g : Fin 10 → Fin 2 → SU2) :
    ∑ P ∈ Fintype.piFinset (fun a : Fin 5 =>
        channel (k5Spins n a 0 - k5Spins m a 0) (k5Spins n a 1 - k5Spins m a 1)
          (k5Spins n a 2 - k5Spins m a 2) (k5Spins n a 3 - k5Spins m a 3)),
      (∏ a, (nodeSign (k5Spins n a - k5Spins m a) *
        hsInner (ivec (k5Spins n a 0 - k5Spins m a 0) (k5Spins n a 1 - k5Spins m a 1)
          (k5Spins n a 2 - k5Spins m a 2) (k5Spins n a 3 - k5Spins m a 3) (P a))
          (homForm (k5Spins n a - k5Spins m a)
            (cohInt (k5Spins n a - k5Spins m a) (nodeBdry g a))))) * eprlVertexHigh n m P =
      (∏ a, nodeConst (k5Spins n a) (k5Spins m a)) *
        ∫ X : Fin 5 → Spin4, ∏ e : Fin 10,
          ∑ μ ∈ Finset.Icc (-(n e : ℤ)) (n e), ∑ ν ∈ Finset.Icc (-(m e : ℤ)) (m e),
            ((edgeSign (n e) μ * edgeSign (m e) ν : ℝ) : ℂ) *
              (legFam (k5Spins n (edgeSrc e)) (k5Spins m (edgeSrc e)) (nodeBdry g (edgeSrc e))
                  (X (edgeSrc e)) (srcLeg e) μ ν *
                legFam (k5Spins n (edgeTgt e)) (k5Spins m (edgeTgt e)) (nodeBdry g (edgeTgt e))
                  (X (edgeTgt e)) (tgtLeg e) (-μ) (-ν))
          ∂(Measure.pi fun _ => haarSpin4) := by
  have hmn' : ∀ a l, k5Spins m a l ≤ k5Spins n a l := by
    intro a l
    fin_cases a <;> fin_cases l <;> simp [k5Spins] <;> exact hmn _
  rw [eprlVertexHigh_coherent]
  have hnode : ∀ a μ ν, eprlCohNodeHigh (k5Spins n a) (k5Spins m a) (nodeBdry g a) μ ν =
      ∫ G, nodeConst (k5Spins n a) (k5Spins m a) * ∏ l, legFam (k5Spins n a) (k5Spins m a)
        (nodeBdry g a) G l (μ l) (ν l) ∂haarSpin4 := by
    intro a μ ν
    rw [eprlCohNodeHigh_legs _ _ (hmn' a) _ μ ν, integral_const_mul, nodeConst]
    simp only [nodeLeg_eq_prod]
  simp only [hnode]
  rw [k5Contract4_integral _ _ (fun a G μ ν => nodeConst (k5Spins n a) (k5Spins m a) *
      ∏ l, legFam (k5Spins n a) (k5Spins m a) (nodeBdry g a) G l (μ l) (ν l))
    (fun a μ ν => continuous_const.mul (by
      simp only [← nodeLeg_eq_prod]
      exact continuous_nodeLeg _ _ _ _ _))]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [k5Contract4_const_mul, k5Contract4_prod]

end Lightlike.Asymptotics.EPRL

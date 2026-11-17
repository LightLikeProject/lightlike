import Lightlike.Asymptotics.EPRL.EprlHighProj
import Lightlike.Asymptotics.EPRL.HomFormExpansion

/-!
# The coherent intertwiner under the EPRL map for `γ > 1`

In Hom form the EPRL image of the `SU(2)` coherent intertwiner `ι_{n-m}(g)` is the Spin(4) average of the
conjugates of the lifted rank-one tensor `⊗_l |k_l, g_l⟩` (`eprlIntertwinerLow_homForm_cohInt`): the
`SU(2)` group average defining `ι` is absorbed into the Spin(4) average, because the lift is
equivariant for the diagonal `SU(2)` and `projSpin4` pairs with Spin(4) intertwiners invariantly
(`projSpin4_eq_integral`). Unlike `γ < 1` the lift of a coherent state is not a product of coherent
states, so no factorization is claimed.

## Main results

* `homForm_avgP_eq_matInt`: the group average of a four-leg tensor in Hom form is the average of the
  conjugation.
* `projSpin4_matInt`: `projSpin4` commutes with the `SU(2)` integral.
* `eprlIntertwinerLow_homForm_cohInt`: `Φ(ι_{n-m}(g)) = ∫ D(G) Φ̃(⊗_l |k_l, g_l⟩) D'(G)ᴴ dG`.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4 (the vertex for `γ > 1`).
-/

open Matrix Finset MeasureTheory
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam

section SU2Lin

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ]

lemma hsInner_matInt (R : Matrix ι κ ℂ) (F : SU2 → Matrix ι κ ℂ)
    (hF : ∀ i j, Continuous fun G => F G i j) :
    hsInner R (matInt F) = ∫ G, hsInner R (F G) ∂haarSU2 := by
  unfold hsInner
  simp only [matInt_apply]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_of_continuous
      (f := fun G => star (R i j) * F G i j) (continuous_const.mul (hF i j))]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
  · exact integrable_finsetSum _ fun j _ => integrable_of_continuous
      (f := fun G => star (R i j) * F G i j) (continuous_const.mul (hF i j))

lemma matInt_mul_left' [Fintype μ] (A : Matrix μ ι ℂ) (F : SU2 → Matrix ι κ ℂ)
    (hF : ∀ i j, Continuous fun G => F G i j) :
    A * matInt F = matInt fun G => A * F G := by
  ext i j
  simp only [Matrix.mul_apply, matInt_apply]
  rw [integral_finsetSum _ fun k _ => integrable_of_continuous
    (f := fun G => A i k * F G k j) (continuous_const.mul (hF k j))]
  exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm

lemma matInt_mul_right' [Fintype μ] (A : Matrix κ μ ℂ) (F : SU2 → Matrix ι κ ℂ)
    (hF : ∀ i j, Continuous fun G => F G i j) :
    matInt F * A = matInt fun G => F G * A := by
  ext i j
  simp only [Matrix.mul_apply, matInt_apply]
  rw [integral_finsetSum _ fun k _ => integrable_of_continuous
    (f := fun G => F G i k * A k j) ((hF i k).mul continuous_const)]
  exact Finset.sum_congr rfl fun k _ => (integral_mul_const _ _).symm

end SU2Lin

/-- **The group average of a four-leg tensor in Hom form is the average of the conjugation**:
`homForm (P u) = ∫ D₀₁(X) (homForm u) D₂₃(X)ᴴ dX`. -/
theorem homForm_avgP_eq_matInt (J : Fin 4 → ℕ) (u : LIdx J → ℂ) :
    homForm J (avgP J *ᵥ u) = matInt fun X : SU2 =>
      pairMat (J 0) (J 1) X * homForm J u * (pairMat (J 2) (J 3) X)ᴴ := by
  ext p q
  have hav : ∀ k : LIdx J, (avgP J *ᵥ u) k =
      ∫ X : SU2, (rhoN J (X : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ u) k ∂haarSU2 := by
    intro k
    unfold avgP
    rw [matInt_mulVec _ _ continuous_rhoN_apply]
  rw [matInt_apply]
  simp only [← homForm_rhoN]
  simp only [homForm_apply, hav]
  rw [integral_const_mul]


section Node

variable {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ}

lemma continuous_pairMat (a b : ℕ) :
    Continuous fun X : SU2 => pairMat a b X :=
  continuous_matrix fun i j => by
    obtain ⟨i1, i2⟩ := i
    obtain ⟨j1, j2⟩ := j
    simp only [pairMat, kroneckerMap_apply]
    exact (continuous_spinMat_apply a _ _).mul (continuous_spinMat_apply b _ _)

/-- `projSpin4` commutes with the `SU(2)` integral. -/
theorem projSpin4_matInt (F : SU2 → Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ)
    (hF : ∀ i j, Continuous fun X => F X i j) :
    projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (matInt F) = matInt fun X => projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (F X) := by
  ext i j
  unfold projSpin4
  have hcont : ∀ p : ℕ × ℕ, Continuous fun X : SU2 =>
      hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) (F X) *
        ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2 i j := fun p =>
    (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_const.mul (hF a b)).mul continuous_const
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matInt_apply]
  rw [integral_finsetSum _ fun p _ => integrable_of_continuous (hcont p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hsInner_matInt _ _ hF, ← integral_mul_const]

/-- **The EPRL map for `γ > 1` sends the `SU(2)` coherent intertwiner to a Spin(4) integral**: in Hom
form, `Φ(ι_{n-m}(g)) = ∫_{Spin(4)} D(G) Φ̃(⊗_l |k_l, g_l⟩) D'(G)ᴴ dG`, with `Φ̃` the lift before projection
and `⊗_l |k_l, g_l⟩` in Hom form. The SU(2) average of the coherent intertwiner is absorbed into the
Spin(4) average (the diagonal subgroup). -/
theorem eprlIntertwinerLow_homForm_cohInt (n m : Fin 4 → ℕ) (hmn : ∀ l, m l ≤ n l)
    (g : Fin 4 → SU2) :
    eprlIntertwinerLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
        (homForm (n - m) (cohInt (n - m) g)) =
      matInt4 fun G => act4 (n 0) (n 1) (m 0) (m 1) G *
        eprlLiftLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
          (homForm (n - m) (prodVec (n - m) fun l => cohState ((n - m) l) (g l))) *
        (act4 (n 2) (n 3) (m 2) (m 3) G)ᴴ := by
  set S := homForm (n - m) (prodVec (n - m) fun l => cohState ((n - m) l) (g l)) with hS
  set W := eprlLiftLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) S with hW
  have hT : homForm (n - m) (cohInt (n - m) g) = matInt fun X : SU2 =>
      pairMat ((n - m) 0) ((n - m) 1) X * S * (pairMat ((n - m) 2) ((n - m) 3) X)ᴴ :=
    homForm_avgP_eq_matInt (n - m) _
  have hY1 : ∀ X : SU2, eprlPairLow (n 0) (m 0) (n 1) (m 1) * pairMat ((n - m) 0) ((n - m) 1) X =
      act4 (n 0) (n 1) (m 0) (m 1) (X, X) * eprlPairLow (n 0) (m 0) (n 1) (m 1) := fun X =>
    (eprlPairLow_equivariant (hmn 0) (hmn 1) X).symm
  have hY2 : ∀ X : SU2, (pairMat ((n - m) 2) ((n - m) 3) X)ᴴ * (eprlPairLow (n 2) (m 2) (n 3) (m 3))ᴴ =
      (eprlPairLow (n 2) (m 2) (n 3) (m 3))ᴴ * (act4 (n 2) (n 3) (m 2) (m 3) (X, X))ᴴ := fun X => by
    have := congrArg Matrix.conjTranspose (eprlPairLow_equivariant (hmn 2) (hmn 3) X)
    simpa [Matrix.conjTranspose_mul] using this.symm
  have hZ : ∀ X : SU2, eprlLiftLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
      (pairMat ((n - m) 0) ((n - m) 1) X * S * (pairMat ((n - m) 2) ((n - m) 3) X)ᴴ) =
      act4 (n 0) (n 1) (m 0) (m 1) (X, X) * W * (act4 (n 2) (n 3) (m 2) (m 3) (X, X))ᴴ := by
    intro X
    unfold eprlLiftLow
    rw [hW, eprlLiftLow]
    calc _ = (eprlPairLow (n 0) (m 0) (n 1) (m 1) * pairMat ((n - m) 0) ((n - m) 1) X) * S *
          ((pairMat ((n - m) 2) ((n - m) 3) X)ᴴ * (eprlPairLow (n 2) (m 2) (n 3) (m 3))ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hY1, hY2]; simp only [Matrix.mul_assoc]
  have hFmat : Continuous fun X : SU2 =>
      pairMat ((n - m) 0) ((n - m) 1) X * S * (pairMat ((n - m) 2) ((n - m) 3) X)ᴴ :=
    ((continuous_pairMat _ _).matrix_mul continuous_const).matrix_mul
      (continuous_pairMat _ _).matrix_conjTranspose
  have hZmat : Continuous fun X : SU2 =>
      act4 (n 0) (n 1) (m 0) (m 1) (X, X) * W * (act4 (n 2) (n 3) (m 2) (m 3) (X, X))ᴴ :=
    (((continuous_act4_matrix _ _ _ _).comp (continuous_id.prodMk continuous_id)).matrix_mul
      continuous_const).matrix_mul
      ((continuous_act4_matrix _ _ _ _).comp (continuous_id.prodMk continuous_id)).matrix_conjTranspose
  have hlift : eprlLiftLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
      (matInt fun X : SU2 => pairMat ((n - m) 0) ((n - m) 1) X * S *
        (pairMat ((n - m) 2) ((n - m) 3) X)ᴴ) =
      matInt fun X : SU2 => act4 (n 0) (n 1) (m 0) (m 1) (X, X) * W *
        (act4 (n 2) (n 3) (m 2) (m 3) (X, X))ᴴ := by
    unfold eprlLiftLow
    rw [matInt_mul_left' _ _ (fun i j => (hFmat.matrix_elem i j)),
      matInt_mul_right' _ _ (fun i j => (continuous_const.matrix_mul hFmat).matrix_elem i j)]
    congr 1
    funext X
    have := hZ X
    unfold eprlLiftLow at this
    simpa [hW, eprlLiftLow, Matrix.mul_assoc] using this
  unfold eprlIntertwinerLow
  rw [hT, hlift, projSpin4_matInt _ (fun i j => hZmat.matrix_elem i j)]
  have hconst : ∀ X : SU2, projSpin4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
      (act4 (n 0) (n 1) (m 0) (m 1) (X, X) * W * (act4 (n 2) (n 3) (m 2) (m 3) (X, X))ᴴ) =
      projSpin4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) W := by
    intro X
    unfold projSpin4
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hsInner_conj_of_intertwines (act4_unitary _ _ _ _ (X, X)) (act4_unitary _ _ _ _ (X, X))
      (ivec4_isSpin4Intertwiner hp (X, X)) W]
  simp only [hconst]
  rw [matInt_const, projSpin4_eq_integral]

end Node

end Lightlike.Asymptotics.EPRL
